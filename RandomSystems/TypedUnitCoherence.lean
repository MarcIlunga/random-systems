/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedAction
import RandomSystems.ResourceView

namespace RandomSystems.CR18
open PFunConverter
open scoped PFunDDS

attribute [local instance] Classical.propDecidable

universe u v
variable {X : Type u} {Y : Type v}

def unitTag (history : List X) : List (Unit × X) :=
  history.map fun query => ((), query)

@[simp] theorem unitTag_nil : unitTag ([] : List X) = [] := rfl

@[simp] theorem unitTag_append (left right : List X) :
    unitTag (left ++ right) = unitTag left ++ unitTag right := by
  simp [unitTag]

@[simp] theorem unitTag_singleton (query : X) :
    unitTag [query] = [((), query)] := rfl

@[simp] theorem unitTag_cons (query : X) (history : List X) :
    unitTag (query :: history) = ((), query) :: unitTag history := by
  simp [unitTag]

@[simp] theorem unitTag_map_snd (history : List (Unit × X)) :
    unitTag (history.map Prod.snd) = history := by
  induction history with
  | nil => rfl
  | cons head tail induction =>
      rcases head with ⟨unit, query⟩
      rcases unit
      simp [induction]

theorem output_unit_resource_kept
    (system : PFunDDS.DDS X Y) (history : List X) (query : X) :
    PFunDDS.output
        (PFunDDS.fullyDefined (PFunDDS.toUnitResource system))
        (unitTag (PFunDDS.keptPrefix system history) ++ [((), query)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined system) (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  rw [PFunDDS.output_fullyDefined, PFunDDS.output_fullyDefined]
  simp only [List.dropLast_concat, List.getLast_concat]
  have keptLive :
      unitTag (PFunDDS.keptPrefix system history) ∈
          PFunDDS.dom (PFunDDS.toUnitResource system) ∨
        unitTag (PFunDDS.keptPrefix system history) = [] := by
    rcases PFunDDS.keptPrefix_mem_or system history with member | empty
    · left
      change (system.val
        ((unitTag (PFunDDS.keptPrefix system history)).map Prod.snd)).Dom
      have mapped :
          (unitTag (PFunDDS.keptPrefix system history)).map Prod.snd =
            PFunDDS.keptPrefix system history := by
        simp [unitTag]
      rw [mapped]
      exact member
    · right
      rw [empty]
      rfl
  have dropLeft :
      (unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).dropLast =
        unitTag (PFunDDS.keptPrefix system history) := by simp
  have lastLeft :
      (unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).getLast
          (by simp) = ((), query) := by simp
  have dropRight : (history ++ [query]).dropLast = history := by simp
  have lastRight : (history ++ [query]).getLast (by simp) = query := by simp
  simp only [PFunDDS.keptPrefix_eq_self_of_mem_or_empty _ keptLive]
  by_cases member : PFunDDS.keptPrefix system history ++ [query] ∈
      PFunDDS.dom system
  · have taggedMember :
        unitTag (PFunDDS.keptPrefix system history) ++ [((), query)] ∈
          PFunDDS.dom (PFunDDS.toUnitResource system) := by
      change (system.val
        ((unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).map
          Prod.snd)).Dom
      have mapped :
          (unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).map
              Prod.snd = PFunDDS.keptPrefix system history ++ [query] := by
        simp [unitTag]
      rw [mapped]
      exact member
    rw [dif_pos member, dif_pos taggedMember]
    congr 1
    exact PFunDDS.output_congr system (by simp [unitTag]) _ _
  · have taggedNotMember :
        unitTag (PFunDDS.keptPrefix system history) ++ [((), query)] ∉
          PFunDDS.dom (PFunDDS.toUnitResource system) := by
      intro taggedMember
      apply member
      change (system.val
        ((unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).map
          Prod.snd)).Dom at taggedMember
      have mapped :
          (unitTag (PFunDDS.keptPrefix system history) ++ [((), query)]).map
              Prod.snd = PFunDDS.keptPrefix system history ++ [query] := by
        simp [unitTag]
      rw [mapped] at taggedMember
      exact taggedMember
    rw [dif_neg member, dif_neg taggedNotMember]

noncomputable def unitState (system : PFunDDS.DDS X Y)
    (state : List (DDC.CIn X Y) × List X) :
    List (DDC.CIn X Y) × List (Unit × X) :=
  (state.1, unitTag (PFunDDS.keptPrefix system state.2))

@[simp] theorem unitState_empty (system : PFunDDS.DDS X Y) :
    unitState system ([], []) = ([], []) := by
  simp [unitState, PFunDDS.keptPrefix]

noncomputable def unitOutcome (system : PFunDDS.DDS X Y) :
    (Y × (List (DDC.CIn X Y) × List X)) ⊕
        (List (DDC.CIn X Y) × List X) →
      (Y × (List (DDC.CIn X Y) × List (Unit × X))) ⊕
        (List (DDC.CIn X Y) × List (Unit × X))
  | Sum.inl (answer, state) => Sum.inl (answer, unitState system state)
  | Sum.inr state => Sum.inr (unitState system state)

theorem attachStep_unit_eq_map (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    (state : List (DDC.CIn X Y) × List X) :
    PFunConverter.General.attachStep () alpha
        (PFunDDS.toUnitResource system) (unitState system state) =
      (PFunConverter.DDC.connStep alpha system state).map
        (unitOutcome system) := by
  unfold PFunConverter.General.attachStep PFunConverter.DDC.connStep
  rw [Part.map_bind]
  change (alpha.val state.1).bind _ = (alpha.val state.1).bind _
  apply congrArg (Part.bind (alpha.val state.1))
  funext move
  rcases move with ⟨label, answer⟩ | ⟨label, query⟩ <;> cases label
  · simp [unitOutcome]
  · rfl
  · simp only [unitState]
    rw [output_unit_resource_kept system state.2 query]
    simp only [Part.map_some, unitOutcome, unitState]
    rw [PFunDDS.keptPrefix_append_singleton]
    by_cases member : PFunDDS.keptPrefix system state.2 ++ [query] ∈
        PFunDDS.dom system
    · rw [if_pos member,
        PFunConverter.output_fullyDefined_append_keptPrefix_of_mem
          system state.2 query member]
      simp [unitOutcome, unitState, unitTag]
    · rw [if_neg member]
      have outputNone :
          PFunDDS.output (PFunDDS.fullyDefined system)
              (state.2 ++ [query])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
        rw [PFunDDS.output_fullyDefined]
        simp only [List.dropLast_concat, List.getLast_concat]
        rw [dif_neg member]
      rw [outputNone]
  · simp [unitOutcome]

noncomputable def unitResult (system : PFunDDS.DDS X Y) :
    Y × (List (DDC.CIn X Y) × List X) →
      Y × (List (DDC.CIn X Y) × List (Unit × X)) :=
  fun result => (result.1, unitState system result.2)

theorem resolve_unit_forward (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    {state : List (DDC.CIn X Y) × List X}
    {result : Y × (List (DDC.CIn X Y) × List X)}
    (member : result ∈ DDC.resolve alpha system state) :
    unitResult system result ∈
      General.attachResolve () alpha (PFunDDS.toUnitResource system)
        (unitState system state) := by
  let rawStep := DDC.connStep alpha system
  let taggedStep :=
    General.attachStep () alpha (PFunDDS.toUnitResource system)
  let relation :
      (List (DDC.CIn X Y) × List X) →
        (List (DDC.CIn X Y) × List (Unit × X)) → Prop :=
    fun raw tagged => tagged = unitState system raw
  let outputRelation :
      (Y × (List (DDC.CIn X Y) × List X)) →
        (Y × (List (DDC.CIn X Y) × List (Unit × X))) → Prop :=
    fun raw tagged => tagged = unitResult system raw
  have stop : ∀ raw tagged, relation raw tagged → ∀ output,
      Sum.inl output ∈ rawStep raw →
        ∃ taggedOutput, Sum.inl taggedOutput ∈ taggedStep tagged ∧
          outputRelation output taggedOutput := by
    intro raw tagged related output outputMember
    subst tagged
    refine ⟨unitResult system output, ?_, rfl⟩
    change Sum.inl (unitResult system output) ∈
      General.attachStep () alpha (PFunDDS.toUnitResource system)
        (unitState system raw)
    rw [attachStep_unit_eq_map]
    exact (Part.mem_map_iff _).mpr ⟨Sum.inl output, outputMember, rfl⟩
  have step : ∀ raw tagged, relation raw tagged → ∀ next,
      Sum.inr next ∈ rawStep raw →
        ∃ taggedNext, Sum.inr taggedNext ∈ taggedStep tagged ∧
          relation next taggedNext := by
    intro raw tagged related next nextMember
    subst tagged
    refine ⟨unitState system next, ?_, rfl⟩
    change Sum.inr (unitState system next) ∈
      General.attachStep () alpha (PFunDDS.toUnitResource system)
        (unitState system raw)
    rw [attachStep_unit_eq_map]
    exact (Part.mem_map_iff _).mpr ⟨Sum.inr next, nextMember, rfl⟩
  obtain ⟨taggedResult, taggedMember, related⟩ :=
    PFun.fix_bisim stop step member (unitState system state) rfl
  simpa [outputRelation] using related ▸ taggedMember

theorem resolve_unit_backward (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    {state : List (DDC.CIn X Y) × List X}
    {taggedResult : Y × (List (DDC.CIn X Y) × List (Unit × X))}
    (member : taggedResult ∈
      General.attachResolve () alpha (PFunDDS.toUnitResource system)
        (unitState system state)) :
    ∃ result, result ∈ DDC.resolve alpha system state ∧
      taggedResult = unitResult system result := by
  let rawStep := DDC.connStep alpha system
  let taggedStep :=
    General.attachStep () alpha (PFunDDS.toUnitResource system)
  let relation :
      (List (DDC.CIn X Y) × List (Unit × X)) →
        (List (DDC.CIn X Y) × List X) → Prop :=
    fun tagged raw => tagged = unitState system raw
  let outputRelation :
      (Y × (List (DDC.CIn X Y) × List (Unit × X))) →
        (Y × (List (DDC.CIn X Y) × List X)) → Prop :=
    fun tagged raw => tagged = unitResult system raw
  have stop : ∀ tagged raw, relation tagged raw → ∀ output,
      Sum.inl output ∈ taggedStep tagged →
        ∃ rawOutput, Sum.inl rawOutput ∈ rawStep raw ∧
          outputRelation output rawOutput := by
    intro tagged raw related output outputMember
    subst tagged
    change Sum.inl output ∈
      General.attachStep () alpha (PFunDDS.toUnitResource system)
        (unitState system raw) at outputMember
    rw [attachStep_unit_eq_map] at outputMember
    obtain ⟨candidate, candidateMember, candidateEquation⟩ :=
      (Part.mem_map_iff _).mp outputMember
    rcases candidate with rawOutput | rawNext
    · refine ⟨rawOutput, candidateMember, ?_⟩
      simpa [outputRelation, unitOutcome, unitResult] using candidateEquation.symm
    · simp [unitOutcome] at candidateEquation
  have step : ∀ tagged raw, relation tagged raw → ∀ next,
      Sum.inr next ∈ taggedStep tagged →
        ∃ rawNext, Sum.inr rawNext ∈ rawStep raw ∧
          relation next rawNext := by
    intro tagged raw related next nextMember
    subst tagged
    change Sum.inr next ∈
      General.attachStep () alpha (PFunDDS.toUnitResource system)
        (unitState system raw) at nextMember
    rw [attachStep_unit_eq_map] at nextMember
    obtain ⟨candidate, candidateMember, candidateEquation⟩ :=
      (Part.mem_map_iff _).mp nextMember
    rcases candidate with rawOutput | rawNext
    · simp [unitOutcome] at candidateEquation
    · refine ⟨rawNext, candidateMember, ?_⟩
      simpa [relation, unitOutcome] using candidateEquation.symm
  obtain ⟨result, resultMember, related⟩ :=
    PFun.fix_bisim stop step member state rfl
  exact ⟨result, resultMember, related⟩

theorem attachResolve_unit_eq_map (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    (state : List (DDC.CIn X Y) × List X) :
    General.attachResolve () alpha (PFunDDS.toUnitResource system)
        (unitState system state) =
      (DDC.resolve alpha system state).map (unitResult system) := by
  apply Part.ext
  intro taggedResult
  constructor
  · intro member
    obtain ⟨result, resultMember, equation⟩ :=
      resolve_unit_backward alpha system member
    exact (Part.mem_map_iff _).mpr ⟨result, resultMember, equation.symm⟩
  · intro member
    obtain ⟨result, resultMember, equation⟩ :=
      (Part.mem_map_iff _).mp member
    rw [← equation]
    exact resolve_unit_forward alpha system resultMember

theorem attachEntryStep_unit_eq_map (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    (state : List (DDC.CIn X Y) × List X) (query : X) :
    General.attachEntryStep () alpha (PFunDDS.toUnitResource system)
        (unitState system state) ((), query) =
      (DDC.resolve alpha system
        (state.1 ++ [Sum.inl (InLabel.outside, query)], state.2)).map
          (unitResult system) := by
  simp only [General.attachEntryStep, if_pos rfl, unitState]
  exact attachResolve_unit_eq_map alpha system
    (state.1 ++ [Sum.inl (InLabel.outside, query)], state.2)

noncomputable def unitDriveResult (system : PFunDDS.DDS X Y) :
    (List Y × (List (DDC.CIn X Y) × List X)) →
      List Y × (List (DDC.CIn X Y) × List (Unit × X)) :=
  fun result => (result.1, unitState system result.2)

theorem attachDrive_unit_eq_map (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y)
    (state : List (DDC.CIn X Y) × List X) (inputs : List X) :
    General.attachDrive () alpha (PFunDDS.toUnitResource system)
        (unitState system state) (unitTag inputs) =
      (DDC.driveFrom alpha system state inputs).map
        (unitDriveResult system) := by
  induction inputs generalizing state with
  | nil =>
      simp [General.attachDrive, DDC.driveFrom, unitDriveResult]
  | cons query rest induction =>
      rw [unitTag_cons, General.attachDrive, DDC.driveFrom,
        attachEntryStep_unit_eq_map]
      rw [Part.map_bind, Part.bind_map]
      apply congrArg
      funext result
      simp only [unitResult]
      rw [induction]
      simp [unitResult, unitDriveResult, Part.map_map, Function.comp_def]

theorem attachRaw_unitTag_eq (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y) (inputs : List X) :
    General.attachRaw () alpha (PFunDDS.toUnitResource system)
        (unitTag inputs) =
      DDC.applyRaw alpha system inputs := by
  unfold General.attachRaw DDC.applyRaw
  have driveEquation :=
    attachDrive_unit_eq_map alpha system ([], []) inputs
  simp only [unitState_empty] at driveEquation
  rw [driveEquation]
  rw [Part.bind_map]
  apply congrArg
  funext result
  simp [unitDriveResult]

theorem attachRaw_unit_eq (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y) (inputs : List (Unit × X)) :
    General.attachRaw () alpha (PFunDDS.toUnitResource system) inputs =
      DDC.applyRaw alpha system (inputs.map Prod.snd) := by
  conv_lhs =>
    rw [← unitTag_map_snd inputs]
  exact attachRaw_unitTag_eq alpha system (inputs.map Prod.snd)

/-- On a genuine one-interface resource, CR18 general attachment is exactly
ordinary serial converter application.  This is the coherence theorem used by
the typed AC action; it applies to arbitrary stateful deterministic converters,
not a CBC-specific subclass. -/
theorem attachAt_unit_eq_toUnitResource_apply (alpha : DDC X Y X Y)
    (system : PFunDDS.DDS X Y) :
    General.attachAt () alpha (PFunDDS.toUnitResource system) =
      PFunDDS.toUnitResource (DDC.apply alpha system) := by
  apply Subtype.ext
  funext inputs
  exact attachRaw_unit_eq alpha system inputs

end RandomSystems.CR18

namespace RandomSystems.CR18.TypedResource

open PFunConverter

universe c u v

variable {U : SignatureUniverse.{c, u, v}} [DecidableEq U.Code]

/-- Read a native one-interface dependent resource at its advertised local
signature, erasing the unique `Unit` interface tag. -/
def DependentDDS.unitView {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code)) :
    PFunDDS.DDS (U.input code) (U.output code) :=
  ⟨(fun history =>
      (⟨history.map (fun input => (⟨(), input⟩ : Query U (fun _ : Unit => code))) ∈
          system.domain,
        fun member => system.output
          (history.map fun input =>
            (⟨(), input⟩ : Query U (fun _ : Unit => code)))
          (by
            intro empty
            have historyEmpty : history = [] := List.map_eq_nil_iff.mp empty
            subst history
            exact system.empty_not_mem member) member⟩ : Part (U.output code))),
    ⟨by
      intro member
      exact system.empty_not_mem member,
     by
      intro left right hprefix nonempty member
      change right.map (fun input =>
        (⟨(), input⟩ : Query U (fun _ : Unit => code))) ∈
          system.domain at member
      change left.map (fun input =>
        (⟨(), input⟩ : Query U (fun _ : Unit => code))) ∈
          system.domain
      exact system.prefix_closed (hprefix.map _) (by simpa) member⟩⟩

@[simp]
theorem DependentDDS.unit_view_domain {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code)) :
    PFunDDS.dom system.unitView =
      {history | history.map (fun input =>
        (⟨(), input⟩ : Query U (fun _ : Unit => code))) ∈ system.domain} :=
  rfl

def encodeInputAt (code : U.Code) (input : U.input code) : AmbientInput U :=
  ⟨code, input⟩

def encodeOutputAt (code : U.Code) (output : U.output code) : AmbientOutput U :=
  ⟨code, output⟩

theorem DependentDDS.ofUnitResource_embed_apply_encoded {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code))
    (history : List (U.input code)) :
    (PFunDDS.ofUnitResource system.embed).val
        (history.map (encodeInputAt code)) =
      (system.unitView.val history).map (encodeOutputAt code) := by
  have encoded := system.embed_apply_encoded
    (history.map fun input =>
      (⟨(), input⟩ : Query U (fun _ : Unit => code)))
  change system.embed.val
      ((history.map (encodeInputAt code)).map fun input => ((), input)) = _
  rw [show
    (history.map (encodeInputAt code)).map (fun input => ((), input)) =
      (history.map fun input =>
        (⟨(), input⟩ : Query U (fun _ : Unit => code))).map encodeQuery by
          simp [encodeInputAt, encodeQuery]]
  rw [encoded]
  apply Part.ext'
  · rfl
  · intro left right
    rfl

theorem DependentDDS.unit_view_dom_encoded_iff {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code))
    (history : List (U.input code)) :
    history.map (encodeInputAt code) ∈
        PFunDDS.dom (PFunDDS.ofUnitResource system.embed) ↔
      history ∈ PFunDDS.dom system.unitView := by
  change ((PFunDDS.ofUnitResource system.embed).val
      (history.map (encodeInputAt code))).Dom ↔
    (system.unitView.val history).Dom
  rw [system.ofUnitResource_embed_apply_encoded history]
  rfl

theorem DependentDDS.kept_prefix_ofUnitResource_embed_encoded {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code))
    (history : List (U.input code)) :
    PFunDDS.keptPrefix (PFunDDS.ofUnitResource system.embed)
        (history.map (encodeInputAt code)) =
      (PFunDDS.keptPrefix system.unitView history).map
        (encodeInputAt code) := by
  induction history using List.reverseRecOn with
  | nil => rfl
  | append_singleton history query induction =>
      rw [List.map_append, List.map_singleton,
        RandomSystems.CR18.PFunDDS.keptPrefix_append_singleton,
        RandomSystems.CR18.PFunDDS.keptPrefix_append_singleton, induction]
      have domainEquation := system.unit_view_dom_encoded_iff
        (PFunDDS.keptPrefix system.unitView history ++ [query])
      simp only [List.map_append, List.map_singleton] at domainEquation
      by_cases member :
          PFunDDS.keptPrefix system.unitView history ++ [query] ∈
            PFunDDS.dom system.unitView
      · rw [if_pos member, if_pos (domainEquation.mpr member),
          List.map_append, List.map_singleton]
      · rw [if_neg member, if_neg (fun encodedMember =>
          member (domainEquation.mp encodedMember))]

theorem DependentDDS.output_ofUnitResource_embed_encoded {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code))
    (history : List (U.input code))
    (member : history ∈ PFunDDS.dom system.unitView) :
    PFunDDS.output (PFunDDS.ofUnitResource system.embed)
        (history.map (encodeInputAt code))
        ((system.unit_view_dom_encoded_iff history).mpr member) =
      encodeOutputAt code
        (PFunDDS.output system.unitView history member) := by
  apply Part.mem_unique
    (Part.get_mem
      ((system.unit_view_dom_encoded_iff history).mpr member))
  rw [system.ofUnitResource_embed_apply_encoded history]
  exact Part.mem_map _ (Part.get_mem member)

theorem DependentDDS.output_fullyDefined_ofUnitResource_embed_encoded
    {code : U.Code}
    (system : DependentDDS U (fun _ : Unit => code))
    (history : List (U.input code)) (query : U.input code) :
    PFunDDS.output
        (PFunDDS.fullyDefined (PFunDDS.ofUnitResource system.embed))
        ((history ++ [query]).map (encodeInputAt code))
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      (PFunDDS.output (PFunDDS.fullyDefined system.unitView)
        (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp)).map
          (encodeOutputAt code) := by
  simp only [List.map_append, List.map_singleton]
  let candidate := PFunDDS.keptPrefix system.unitView history ++ [query]
  have ambientCandidateEquation :
      PFunDDS.keptPrefix (PFunDDS.ofUnitResource system.embed)
          (history.map (encodeInputAt code)) ++ [encodeInputAt code query] =
        candidate.map (encodeInputAt code) := by
    rw [system.kept_prefix_ofUnitResource_embed_encoded history]
    simp [candidate]
  have candidateMap :
      (PFunDDS.keptPrefix system.unitView history).map
          (encodeInputAt code) ++ [encodeInputAt code query] =
        candidate.map (encodeInputAt code) := by
    simp [candidate]
  have domainEquation := system.unit_view_dom_encoded_iff candidate
  by_cases member : candidate ∈ PFunDDS.dom system.unitView
  · have encodedMember := domainEquation.mpr member
    have ambientMember :
        PFunDDS.keptPrefix (PFunDDS.ofUnitResource system.embed)
            (history.map (encodeInputAt code)) ++ [encodeInputAt code query] ∈
          PFunDDS.dom (PFunDDS.ofUnitResource system.embed) := by
      rw [ambientCandidateEquation]
      exact encodedMember
    rw [PFunConverter.output_fullyDefined_append_keptPrefix_of_mem
        (PFunDDS.ofUnitResource system.embed)
          (history.map (encodeInputAt code)) (encodeInputAt code query)
          ambientMember,
      PFunConverter.output_fullyDefined_append_keptPrefix_of_mem
        system.unitView history query member,
      Option.map_some]
    congr 1
    calc
      PFunDDS.output (PFunDDS.ofUnitResource system.embed)
          (PFunDDS.keptPrefix (PFunDDS.ofUnitResource system.embed)
            (history.map (encodeInputAt code)) ++ [encodeInputAt code query])
          ambientMember =
        PFunDDS.output (PFunDDS.ofUnitResource system.embed)
          (candidate.map (encodeInputAt code)) encodedMember :=
            PFunDDS.output_congr (PFunDDS.ofUnitResource system.embed)
              ambientCandidateEquation _ _
      _ = encodeOutputAt code
          (PFunDDS.output system.unitView candidate member) :=
        system.output_ofUnitResource_embed_encoded candidate member
  · have encodedNotMember :
        candidate.map (encodeInputAt code) ∉
          PFunDDS.dom (PFunDDS.ofUnitResource system.embed) :=
      fun encodedMember => member (domainEquation.mp encodedMember)
    have ambientNotMember :
        PFunDDS.keptPrefix (PFunDDS.ofUnitResource system.embed)
            (history.map (encodeInputAt code)) ++ [encodeInputAt code query] ∉
          PFunDDS.dom (PFunDDS.ofUnitResource system.embed) := by
      rw [ambientCandidateEquation]
      exact encodedNotMember
    have ambientNone :
        PFunDDS.output
          (PFunDDS.fullyDefined (PFunDDS.ofUnitResource system.embed))
          (history.map (encodeInputAt code) ++ [encodeInputAt code query])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rw [PFunDDS.output_fullyDefined]
      dsimp only
      split_ifs with defined
      · exfalso
        apply ambientNotMember
        simpa only [List.dropLast_concat, List.getLast_concat] using defined
      · rfl
    have localNone :
        PFunDDS.output (PFunDDS.fullyDefined system.unitView)
          (history ++ [query])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      rw [PFunDDS.output_fullyDefined]
      dsimp only
      split_ifs with defined
      · exfalso
        apply member
        simpa only [List.dropLast_concat, List.getLast_concat] using defined
      · rfl
    rw [ambientNone, localNone, Option.map_none]

def encodeOptionalOutputAt (code : U.Code) :
    Option (U.output code) → Option (AmbientOutput U) :=
  Option.map (encodeOutputAt code)

def encodeDriveResult (source target : U.Code) :
    (U.output target × List (U.input source) ×
        List (Option (U.output source))) →
      (AmbientOutput U × List (AmbientInput U) ×
        List (Option (AmbientOutput U))) :=
  fun result =>
    (encodeOutputAt target result.1,
      result.2.1.map (encodeInputAt source),
      result.2.2.map (encodeOptionalOutputAt source))

theorem DeterministicConverter.drive_embedded_encoded
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source)) :
    ∀ (fuel : Nat) (outsideInputs : List (U.input target))
      (innerInputs : List (U.input source))
      (innerAnswers : List (Option (U.output source))),
      PFunConverter.drive converter.embeddedProtocol
          (PFunDDS.ofUnitResource system.embed) fuel
          (outsideInputs.map (encodeInputAt target))
          (innerInputs.map (encodeInputAt source))
          (innerAnswers.map (encodeOptionalOutputAt source)) =
        (PFunConverter.drive converter.protocol system.unitView fuel
          outsideInputs innerInputs innerAnswers).map
            (encodeDriveResult source target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro outsideInputs innerInputs innerAnswers
      simp [PFunConverter.drive]
  | succ remaining induction =>
      intro outsideInputs innerInputs innerAnswers
      simp only [PFunConverter.drive]
      have protocolEquation :
          converter.embeddedProtocol
              (outsideInputs.map (encodeInputAt target),
                innerAnswers.map (encodeOptionalOutputAt source)) =
            (converter.protocol (outsideInputs, innerAnswers)).map
              (encodeMove source target) := by
        simpa [encodeInputAt, encodeOptionalOutputAt, encodeOutputAt] using
          converter.embedded_protocol_apply_encoded
            outsideInputs innerAnswers
      rw [protocolEquation]
      rw [Part.bind_map, Part.map_bind]
      apply congrArg
      funext move
      cases move with
      | inl query =>
          simp only [encodeMove]
          have outputEquation :
              PFunDDS.output
                  (PFunDDS.fullyDefined
                    (PFunDDS.ofUnitResource system.embed))
                  (innerInputs.map (encodeInputAt source) ++
                    [(⟨source, query⟩ : AmbientInput U)])
                  (by rw [PFunDDS.dom_fullyDefined]; simp) =
                (PFunDDS.output
                    (PFunDDS.fullyDefined system.unitView)
                    (innerInputs ++ [query])
                    (by rw [PFunDDS.dom_fullyDefined]; simp)).map
                  (encodeOutputAt source) := by
            simpa [encodeInputAt] using
              system.output_fullyDefined_ofUnitResource_embed_encoded
                innerInputs query
          rw [outputEquation]
          simpa only [List.map_append, List.map_singleton,
            encodeOptionalOutputAt, Option.map_map,
            Function.comp_def] using
              induction (outsideInputs := outsideInputs)
                (innerInputs := innerInputs ++ [query])
                (innerAnswers := innerAnswers ++
                  [PFunDDS.output (PFunDDS.fullyDefined system.unitView)
                    (innerInputs ++ [query])
                    (by rw [PFunDDS.dom_fullyDefined]; simp)])
      | inr answer =>
          simp [encodeMove, encodeDriveResult, encodeOutputAt]

def encodeDriveOuterResult (source target : U.Code) :
    (List (U.output target) × List (U.input source) ×
        List (Option (U.output source))) →
      (List (AmbientOutput U) × List (AmbientInput U) ×
        List (Option (AmbientOutput U))) :=
  fun result =>
    (result.1.map (encodeOutputAt target),
      result.2.1.map (encodeInputAt source),
      result.2.2.map (encodeOptionalOutputAt source))

theorem DeterministicConverter.driveOuter_embedded_encoded
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source))
    (fuel : Nat) :
    ∀ (outsidePrefix outsideRest : List (U.input target))
      (innerInputs : List (U.input source))
      (innerAnswers : List (Option (U.output source))),
      PFunConverter.driveOuter converter.embeddedProtocol
          (PFunDDS.ofUnitResource system.embed) fuel
          (outsidePrefix.map (encodeInputAt target))
          (innerInputs.map (encodeInputAt source))
          (innerAnswers.map (encodeOptionalOutputAt source))
          (outsideRest.map (encodeInputAt target)) =
        (PFunConverter.driveOuter converter.protocol system.unitView fuel
          outsidePrefix innerInputs innerAnswers outsideRest).map
            (encodeDriveOuterResult source target) := by
  intro outsidePrefix outsideRest innerInputs innerAnswers
  induction outsideRest generalizing outsidePrefix innerInputs innerAnswers with
  | nil =>
      simp [PFunConverter.driveOuter, encodeDriveOuterResult]
  | cons outsideInput rest induction =>
      simp only [List.map_cons, PFunConverter.driveOuter]
      have roundEquation := converter.drive_embedded_encoded system fuel
        (outsidePrefix ++ [outsideInput]) innerInputs innerAnswers
      simp only [List.map_append, List.map_singleton] at roundEquation
      rw [roundEquation, Part.bind_map, Part.map_bind]
      apply congrArg
      funext roundResult
      simp only [encodeDriveResult]
      have tailEquation := induction (outsidePrefix ++ [outsideInput])
        roundResult.2.1 roundResult.2.2
      simp only [List.map_append, List.map_singleton] at tailEquation
      rw [tailEquation]
      simp [encodeDriveOuterResult, Part.map_map, Function.comp_def,
        List.map_cons]

theorem DeterministicConverter.applyRawAt_embedded_encoded
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source))
    (fuel : Nat) (outsideInputs : List (U.input target)) :
    PFunConverter.applyRawAt converter.embeddedProtocol
        (PFunDDS.ofUnitResource system.embed) fuel
        (outsideInputs.map (encodeInputAt target)) =
      (PFunConverter.applyRawAt converter.protocol system.unitView fuel
        outsideInputs).map (encodeOutputAt target) := by
  unfold PFunConverter.applyRawAt
  have outerEquation := converter.driveOuter_embedded_encoded system fuel
    ([] : List (U.input target)) outsideInputs [] []
  simp only [List.map_nil] at outerEquation
  rw [outerEquation, Part.bind_map, Part.map_bind]
  apply congrArg
  funext result
  simp only [encodeDriveOuterResult, List.getLast?_map]
  generalize result.1.getLast? = lastOutput
  cases lastOutput <;> simp [encodeOutputAt]

theorem DeterministicConverter.applyRaw_embedded_encoded
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source))
    (outsideInputs : List (U.input target)) :
    PFunConverter.applyRaw converter.embeddedProtocol
        (PFunDDS.ofUnitResource system.embed)
        (outsideInputs.map (encodeInputAt target)) =
      (PFunConverter.applyRaw converter.protocol system.unitView
        outsideInputs).map (encodeOutputAt target) := by
  apply Part.ext
  intro ambientOutput
  constructor
  · intro member
    rw [PFunConverter.mem_applyRaw] at member
    obtain ⟨fuel, member⟩ := member
    rw [converter.applyRawAt_embedded_encoded system fuel outsideInputs]
      at member
    obtain ⟨localOutput, localMember, outputEquation⟩ :=
      (Part.mem_map_iff _).mp member
    exact (Part.mem_map_iff _).mpr
      ⟨localOutput,
        (PFunConverter.mem_applyRaw _ _ _ _).mpr ⟨fuel, localMember⟩,
        outputEquation⟩
  · intro member
    obtain ⟨localOutput, localMember, outputEquation⟩ :=
      (Part.mem_map_iff _).mp member
    rw [PFunConverter.mem_applyRaw] at localMember
    obtain ⟨fuel, localMember⟩ := localMember
    rw [PFunConverter.mem_applyRaw]
    refine ⟨fuel, ?_⟩
    rw [converter.applyRawAt_embedded_encoded system fuel outsideInputs]
    exact (Part.mem_map_iff _).mpr
      ⟨localOutput, localMember, outputEquation⟩

theorem replaceBoundary_unit_eq (source target : U.Code) :
    replaceBoundary (fun _ : Unit => source) () target =
      (fun _ : Unit => target) := by
  funext interface
  cases interface
  exact replace_boundary_same _ _ _

/-- The result of a typed attachment at the unique interface, transported to
the definitionally constant target boundary used by the local view. -/
noncomputable def DependentDDS.attachUnit
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source)) :
    DependentDDS U (fun _ : Unit => target) :=
  cast (congrArg (fun boundary => DependentDDS U boundary)
    (replaceBoundary_unit_eq source target))
    (system.attach () converter rfl)

@[simp]
theorem DependentDDS.attachUnit_embed
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source)) :
    (system.attachUnit converter).embed =
      converter.attachAmbient () system := by
  unfold DependentDDS.attachUnit
  rw [DependentDDS.embed_transport, DependentDDS.embed_attach]
  exact replaceBoundary_unit_eq source target

theorem DependentDDS.ofUnitResource_attachUnit_embed
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source)) :
    PFunDDS.ofUnitResource (system.attachUnit converter).embed =
      PFunConverter.apply converter.embeddedProtocol
        (PFunDDS.ofUnitResource system.embed) := by
  rw [system.attachUnit_embed]
  unfold DeterministicConverter.attachAmbient
  have baseEquation : system.embed = PFunDDS.toUnitResource
      (PFunDDS.ofUnitResource system.embed) :=
    (PFunDDS.unitResourceEquiv.right_inv system.embed).symm
  conv_lhs => rw [baseEquation]
  rw [RandomSystems.CR18.attachAt_unit_eq_toUnitResource_apply]
  calc
    PFunDDS.ofUnitResource
        (PFunDDS.toUnitResource
          (DDC.apply converter.embeddedDDC
            (PFunDDS.ofUnitResource system.embed))) =
      DDC.apply converter.embeddedDDC
        (PFunDDS.ofUnitResource system.embed) :=
          PFunDDS.unitResourceEquiv.left_inv _
    _ = PFunConverter.apply converter.embeddedProtocol
        (PFunDDS.ofUnitResource system.embed) := by
      exact PFunConverter.apply_toDDC _ _

private theorem part_map_injective {A B : Type*} {function : A → B}
    (injective : Function.Injective function) :
    Function.Injective (Part.map function) := by
  intro left right equal
  apply Part.ext
  intro value
  constructor
  · intro member
    have mappedMember : function value ∈ left.map function :=
      Part.mem_map function member
    rw [equal] at mappedMember
    obtain ⟨other, otherMember, same⟩ :=
      (Part.mem_map_iff function).mp mappedMember
    exact injective same ▸ otherMember
  · intro member
    have mappedMember : function value ∈ right.map function :=
      Part.mem_map function member
    rw [← equal] at mappedMember
    obtain ⟨other, otherMember, same⟩ :=
      (Part.mem_map_iff function).mp mappedMember
    exact injective same ▸ otherMember

theorem encodeOutputAt_injective (code : U.Code) :
    Function.Injective (encodeOutputAt code) := by
  intro left right equal
  exact eq_of_heq (Sigma.mk.inj equal).2

/-- The dependent typed attachment used by the AC action is exactly ordinary
local protocol application at a one-interface boundary. -/
theorem DependentDDS.unitView_attachUnit
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentDDS U (fun _ : Unit => source)) :
    (system.attachUnit converter).unitView =
      PFunConverter.apply converter.protocol system.unitView := by
  apply Subtype.ext
  funext outsideInputs
  apply part_map_injective (encodeOutputAt_injective target)
  rw [← (system.attachUnit converter).ofUnitResource_embed_apply_encoded
      outsideInputs]
  rw [system.ofUnitResource_attachUnit_embed converter]
  exact converter.applyRaw_embedded_encoded system outsideInputs

namespace DependentPDS

/-- Probability-law local view of a native one-interface dependent law. -/
noncomputable def unitView {code : U.Code}
    (system : DependentPDS U (fun _ : Unit => code)) :
    PFunPDS (U.input code) (U.output code) :=
  Dist.fTransform DependentDDS.unitView system

/-- Typed law attachment at the unique interface, transported to the constant
target boundary. -/
noncomputable def attachUnit {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentPDS U (fun _ : Unit => source)) :
    DependentPDS U (fun _ : Unit => target) :=
  cast (congrArg (fun boundary => DependentPDS U boundary)
    (replaceBoundary_unit_eq source target))
    (DependentPDS.attach () converter rfl system)

theorem attachUnit_eq_transform {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentPDS U (fun _ : Unit => source)) :
    attachUnit converter system =
      Dist.fTransform (fun deterministic =>
        deterministic.attachUnit converter) system := by
  unfold attachUnit DependentPDS.attach DependentDDS.attachUnit
  generalize boundaryEquation : replaceBoundary_unit_eq source target = same
  cases same
  rfl

theorem unitView_attachUnit {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (system : DependentPDS U (fun _ : Unit => source)) :
    unitView (attachUnit converter system) =
      StrictContext.applyLaw converter.protocol (unitView system) := by
  rw [attachUnit_eq_transform]
  unfold unitView StrictContext.applyLaw
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact deterministic.unitView_attachUnit converter

end DependentPDS

end RandomSystems.CR18.TypedResource

