/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedResource
import RandomSystems.ComposeRealization
import RandomSystems.SemanticRegistry

/-!
# Arbitrary stateful attachment at typed interfaces

This is the pure-random-systems half of the generic finite-interface AC
instance.  It contains no Abstract Crypto dependency.

The public boundary remains `TypedResource.DependentDDS`: queries and proper
answers have genuinely dependent fibres and one deterministic resource sees
the complete interleaved history.  The uniform alphabets below are only an
internal implementation chart used to reuse the already proved arbitrary
stateful `PFunConverter.General.attachAt` theorem.  A code mismatch is
rejection, never a default value.

The converter class is exactly the selected deterministic class: an arbitrary
typed `ProtocolFn` together with `IsDDC`.  No memorylessness, one-query bound,
endorelabelling, `Emulable`, or framed-compatibility hypothesis occurs in the
carrier.
-/

namespace RandomSystems.CR18

namespace TypedResource

open PFunConverter

universe c i u v

/-! ## Boundary changes and the selected typed converter class -/

/-- Replace exactly one component of a typed resource boundary. -/
def replaceBoundary {I : Type i} {U : SignatureUniverse}
    [DecidableEq I] (boundary : Boundary U I) (interface : I)
    (code : U.Code) : Boundary U I :=
  Function.update boundary interface code

@[simp]
theorem replace_boundary_same {I : Type i} {U : SignatureUniverse}
    [DecidableEq I] (boundary : Boundary U I) (interface : I)
    (code : U.Code) :
    replaceBoundary boundary interface code interface = code := by
  simp [replaceBoundary]

@[simp]
theorem replace_boundary_ne {I : Type i} {U : SignatureUniverse}
    [DecidableEq I] (boundary : Boundary U I) {interface other : I}
    (different : other ≠ interface) (code : U.Code) :
    replaceBoundary boundary interface code other = boundary other := by
  simp [replaceBoundary, different]

/-- Installing the code an interface already advertises changes nothing:
the boundary update is the identity.  (This is what makes the identity
converter's boundary move invisible — `DependentDDS.attach_ofFunctions_id_heq`,
`TypedFraming.lean`.) -/
theorem replace_boundary_self {I : Type i} {U : SignatureUniverse}
    [DecidableEq I] (boundary : Boundary U I) (interface : I) :
    replaceBoundary boundary interface (boundary interface) = boundary :=
  Function.update_eq_self interface boundary

/-- Changes at distinct interfaces commute literally. -/
theorem replace_boundary_comm {I : Type i} {U : SignatureUniverse}
    [DecidableEq I] (boundary : Boundary U I) {left right : I}
    (different : left ≠ right) (leftCode rightCode : U.Code) :
    replaceBoundary (replaceBoundary boundary right rightCode) left leftCode =
      replaceBoundary (replaceBoundary boundary left leftCode) right rightCode := by
  funext interface
  by_cases hleft : interface = left
  · subst interface
    simp [replaceBoundary, different]
  · by_cases hright : interface = right
    · subst interface
      simp [replaceBoundary, hleft, different]
    · simp [replaceBoundary, hleft, hright]

/-- An arbitrary deterministic typed converter from `source` to `target`.
`IsDDC` is the native causal/alphabet and finite-query discipline; contextual
closure is proved by the strict observation model rather than stored as an
additional field. -/
@[rs_rule "rs.typed.admissible" rs_typed_admissible random_systems]
structure DeterministicConverter (U : SignatureUniverse)
    (source target : U.Code) where
  protocol : ProtocolFn
    (U.input target) (U.output target)
    (U.input source) (U.output source)
  isDDC : IsDDC protocol

namespace DeterministicConverter

variable {U : SignatureUniverse} {source target : U.Code}

/-- Package an arbitrary history-sensitive deterministic protocol.  This is
the full converter constructor: the callback may inspect its complete outside
query and inside-answer histories; the only obligation is the causal finite-
query judgment `IsDDC`. -/
def ofHistory
    (protocol : ProtocolFn
      (U.input target) (U.output target)
      (U.input source) (U.output source))
    (isDDC : IsDDC protocol) :
    DeterministicConverter U source target :=
  ⟨protocol, isDDC⟩

/-- The common one-query converter syntax.  `query` translates the outside
query to the source-resource query and `answer` translates the source answer
back to the advertised target answer. -/
def ofFunctions
    (query : U.input target → U.input source)
    (answer : U.output source → U.output target) :
    DeterministicConverter U source target :=
  ⟨simpleFn query answer, isDDC_simpleFn query answer⟩

@[simp]
theorem of_history_protocol
    (protocol : ProtocolFn
      (U.input target) (U.output target)
      (U.input source) (U.output source))
    (isDDC : IsDDC protocol) :
    (ofHistory protocol isDDC).protocol = protocol :=
  rfl

@[simp]
theorem of_functions_protocol
    (query : U.input target → U.input source)
    (answer : U.output source → U.output target) :
    (ofFunctions query answer).protocol = simpleFn query answer :=
  rfl

end DeterministicConverter

/-! ## Internal uniform-alphabet chart -/

/-- The disjoint union of every input alphabet in the controlled universe. -/
abbrev AmbientInput (U : SignatureUniverse) :=
  Σ code, U.input code

/-- The disjoint union of every proper-output alphabet in the universe. -/
abbrev AmbientOutput (U : SignatureUniverse) :=
  Σ code, U.output code

/-- The uniform query alphabet expected by `PFunConverter.General`: an
interface together with a universe-coded payload. -/
abbrev AmbientQuery (I : Type i) (U : SignatureUniverse) :=
  I × AmbientInput U

/-- Encode a boundary-typed query in the uniform internal chart. -/
def encodeQuery {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} : Query U boundary → AmbientQuery I U
  | ⟨interface, query⟩ => (interface, ⟨boundary interface, query⟩)

/-- Encode a boundary-typed proper answer by its signature code.  Its owning
interface remains recoverable from the active query. -/
def encodeAnswer {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} : FlatAnswer U boundary → AmbientOutput U
  | ⟨interface, answer⟩ => ⟨boundary interface, answer⟩

/-- A uniform query conforms to a boundary when its payload code is the code
advertised at its interface. -/
def QueryConforms {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (query : AmbientQuery I U) : Prop :=
  query.2.1 = boundary query.1

/-- Decode one conforming uniform query. -/
def decodeQuery {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (query : AmbientQuery I U)
    (conforms : QueryConforms boundary query) : Query U boundary :=
  ⟨query.1, Eq.mp (congrArg U.input conforms) query.2.2⟩

@[simp]
theorem query_conforms_encode {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (query : Query U boundary) :
    QueryConforms boundary (encodeQuery query) := by
  cases query
  rfl

@[simp]
theorem decode_query_encode {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (query : Query U boundary) :
    decodeQuery boundary (encodeQuery query) (query_conforms_encode query) = query := by
  cases query
  rfl

/-- Encoding after a proof-directed decode recovers the original uniform
query. -/
@[simp]
theorem encode_query_decode {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (query : AmbientQuery I U)
    (conforms : QueryConforms boundary query) :
    encodeQuery (decodeQuery boundary query conforms) = query := by
  rcases query with ⟨interface, code, value⟩
  change code = boundary interface at conforms
  subst code
  rfl

/-- Every query in a uniform history conforms to the advertised boundary. -/
def HistoryConforms {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (history : List (AmbientQuery I U)) : Prop :=
  ∀ query ∈ history, QueryConforms boundary query

/-- Decode a uniformly coded history once its boundary conformance has been
established. -/
def decodeHistory {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (history : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary history) : List (Query U boundary) :=
  match history with
  | [] => []
  | query :: rest =>
      decodeQuery boundary query (conforms query (by simp)) ::
        decodeHistory boundary rest (fun candidate member =>
          conforms candidate (by simp [member]))

@[simp]
theorem history_conforms_encode {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (history : List (Query U boundary)) :
    HistoryConforms boundary (history.map encodeQuery) := by
  intro query member
  rw [List.mem_map] at member
  obtain ⟨typed, _, rfl⟩ := member
  exact query_conforms_encode typed

@[simp]
theorem decode_history_encode {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (history : List (Query U boundary)) :
    decodeHistory boundary (history.map encodeQuery)
      (history_conforms_encode history) = history := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      simp only [List.map_cons, decodeHistory, decode_query_encode]
      exact congrArg (List.cons query) induction

/-- Encoding a conforming decoded uniform history is an exact inverse. -/
@[simp]
theorem encode_history_decode {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (history : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary history) :
    (decodeHistory boundary history conforms).map encodeQuery = history := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      simp only [decodeHistory, List.map_cons, encode_query_decode]
      exact congrArg (List.cons query) (induction _)

/-- Decoding preserves the length of a conforming history. -/
@[simp]
theorem decode_history_length {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (history : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary history) :
    (decodeHistory boundary history conforms).length = history.length := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      simp only [decodeHistory, List.length_cons]
      exact congrArg Nat.succ (induction _)

/-- Decoding changes only the dependent payload, never the interface. -/
theorem decode_history_interfaces {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (history : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary history) :
    (decodeHistory boundary history conforms).map Sigma.fst =
      history.map Prod.fst := by
  induction history with
  | nil => rfl
  | cons query rest induction =>
      simp only [decodeHistory, List.map_cons]
      congr 1
      exact induction _

/-- In particular, decoding preserves the active interface. -/
theorem decode_history_getLast_interface {I : Type i}
    {U : SignatureUniverse} (boundary : Boundary U I)
    (history : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary history) (nonempty : history ≠ []) :
    ((decodeHistory boundary history conforms).getLast
        (by
          intro empty
          have lengths := decode_history_length history conforms
          rw [empty] at lengths
          exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm))).1 =
      (history.getLast nonempty).1 := by
  have decodedNonempty : decodeHistory boundary history conforms ≠ [] := by
    intro empty
    have lengths := decode_history_length history conforms
    rw [empty] at lengths
    exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm)
  have interfaces := congrArg List.getLast?
    (decode_history_interfaces boundary history conforms)
  rw [List.getLast?_map,
    List.getLast?_eq_some_getLast decodedNonempty,
    List.getLast?_map,
    List.getLast?_eq_some_getLast nonempty] at interfaces
  exact Option.some.inj interfaces

/-- Conformance is inherited by every prefix. -/
theorem history_conforms_of_prefix {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} {left right : List (AmbientQuery I U)}
    (hprefix : left <+: right) (conforms : HistoryConforms boundary right) :
    HistoryConforms boundary left := by
  intro query member
  exact conforms query (hprefix.subset member)

/-- Decoding distributes over concatenation. -/
theorem decode_history_append {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I) (left right : List (AmbientQuery I U))
    (conforms : HistoryConforms boundary (left ++ right)) :
    decodeHistory boundary (left ++ right) conforms =
      decodeHistory boundary left
          (history_conforms_of_prefix (List.prefix_append left right) conforms) ++
        decodeHistory boundary right (fun query member =>
          conforms query (List.mem_append_right left member)) := by
  induction left with
  | nil => rfl
  | cons query rest induction =>
      simp only [List.cons_append, decodeHistory, List.cons_append]
      exact congrArg (List.cons _) (induction _)

/-- Decoding a prefix gives a prefix of the decoded history. -/
theorem decode_history_prefix {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} {left right : List (AmbientQuery I U)}
    (hprefix : left <+: right) (conforms : HistoryConforms boundary right) :
    decodeHistory boundary left (history_conforms_of_prefix hprefix conforms) <+:
      decodeHistory boundary right conforms := by
  obtain ⟨suffix, rfl⟩ := hprefix
  rw [decode_history_append]
  exact List.prefix_append _ _

/-! ## Embedding dependent resources in the uniform chart -/

/-- The domain used by the uniform implementation chart.  The universal
quantifier makes the proposition independent of proof terms witnessing code
conformance. -/
def EmbeddedDomain {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (system : DependentDDS U boundary)
    (history : List (AmbientQuery I U)) : Prop :=
  HistoryConforms boundary history ∧
    ∀ conforms : HistoryConforms boundary history,
      decodeHistory boundary history conforms ∈ system.domain

/-- Embed a native dependent deterministic resource into the uniform
`(I × AmbientInput, AmbientOutput)` chart used by general attachment. -/
def DependentDDS.embed {I : Type i} {U : SignatureUniverse}
    {boundary : Boundary U I} (system : DependentDDS U boundary) :
    PFunDDS.Resource I (AmbientInput U) (AmbientOutput U) :=
  ⟨(fun history =>
      (⟨EmbeddedDomain system history, fun member =>
        let typedHistory := decodeHistory boundary history member.1
        let typedMember : typedHistory ∈ PFunDDS.dom system.flatten :=
          member.2 member.1
        encodeAnswer (PFunDDS.output system.flatten typedHistory typedMember)⟩ :
        Part (AmbientOutput U))),
    ⟨by
      intro member
      exact system.empty_not_mem (member.2 member.1),
     by
      intro left right hprefix nonempty member
      have leftConforms : HistoryConforms boundary left :=
        history_conforms_of_prefix hprefix member.1
      refine ⟨leftConforms, fun leftConforms' => ?_⟩
      have decodedPrefix : decodeHistory boundary left leftConforms' <+:
          decodeHistory boundary right member.1 := by
        simpa only [proof_irrel_heq] using
          decode_history_prefix hprefix member.1
      have decodedNonempty : decodeHistory boundary left leftConforms' ≠ [] := by
        intro empty
        have lengths := decode_history_length left leftConforms'
        rw [empty] at lengths
        exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm)
      exact system.prefix_closed decodedPrefix decodedNonempty
        (member.2 member.1)⟩⟩

/-- The uniform embedding has exactly the native action on encoded histories. -/
theorem DependentDDS.embed_apply_encoded {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : DependentDDS U boundary) (history : List (Query U boundary)) :
    system.embed.1 (history.map encodeQuery) =
      (system.flatten.1 history).map encodeAnswer := by
  apply Part.ext'
  · change EmbeddedDomain system (history.map encodeQuery) ↔
      history ∈ PFunDDS.dom system.flatten
    constructor
    · intro member
      simpa only [decode_history_encode] using
        member.2 (history_conforms_encode history)
    · intro member
      refine ⟨history_conforms_encode history, fun conforms => ?_⟩
      simpa only [decode_history_encode, proof_irrel_heq] using member
  · intro left right
    change encodeAnswer (PFunDDS.output system.flatten
        (decodeHistory boundary (history.map encodeQuery) left.1)
        (left.2 left.1)) =
      encodeAnswer (PFunDDS.output system.flatten history right)
    congr 1
    exact PFunDDS.output_congr system.flatten
      (decode_history_encode history) _ _

/-- A uniform-chart resource is confined to a dependent boundary when it is
undefined on every ill-coded query history and every proper answer carries
the code selected by the active query. -/
def AmbientWellTyped {I : Type i} {U : SignatureUniverse}
    (boundary : Boundary U I)
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U)) : Prop :=
  ∀ history answer, answer ∈ system.1 history →
    HistoryConforms boundary history ∧
      ∀ nonempty : history ≠ [],
        answer.1 = boundary (history.getLast nonempty).1

/-- Native embedding lands in the boundary-confined part of the uniform
chart. -/
theorem DependentDDS.embed_well_typed {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : DependentDDS U boundary) :
    AmbientWellTyped boundary system.embed := by
  intro history answer member
  rcases member with ⟨embedded, rfl⟩
  refine ⟨embedded.1, fun nonempty => ?_⟩
  change
    (encodeAnswer (PFunDDS.output system.flatten
      (decodeHistory boundary history embedded.1)
      (embedded.2 embedded.1))).1 =
        boundary (history.getLast nonempty).1
  change boundary
      ((decodeHistory boundary history embedded.1).getLast
        (by
          intro empty
          have lengths := decode_history_length history embedded.1
          rw [empty] at lengths
          exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm))).1 =
    boundary (history.getLast nonempty).1
  exact congrArg boundary
    (decode_history_getLast_interface boundary history embedded.1 nonempty)

/-- Restrict a boundary-confined uniform-chart resource back to its native
dependent boundary.  No default output is introduced: the ambient answer's
proved code equality transports its payload into the active output fibre. -/
noncomputable def DependentDDS.ofAmbient {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    (wellTyped : AmbientWellTyped boundary system) :
    DependentDDS U boundary where
  domain := {history | history.map encodeQuery ∈ PFunDDS.dom system}
  empty_not_mem := by
    intro member
    exact PFunDDS.empty_not_mem system member
  prefix_closed := by
    intro left right hprefix nonempty member
    apply PFunDDS.prefix_closed system (hprefix.map encodeQuery) _ member
    intro encodedEmpty
    apply nonempty
    have lengths := congrArg List.length encodedEmpty
    simp only [List.length_map, List.length_nil] at lengths
    exact List.eq_nil_of_length_eq_zero lengths
  output := fun history nonempty member =>
    let encodedHistory := history.map encodeQuery
    let ambientAnswer := PFunDDS.output system encodedHistory member
    have ambientMember : ambientAnswer ∈ system.1 encodedHistory :=
      Part.get_mem _
    have encodedNonempty : encodedHistory ≠ [] := by
      simpa [encodedHistory] using nonempty
    have codeEquation : ambientAnswer.1 =
        boundary (history.getLast nonempty).1 := by
      have confined := (wellTyped encodedHistory ambientAnswer ambientMember).2
        encodedNonempty
      simpa only [encodedHistory, List.getLast_map] using confined
    Eq.mp (congrArg U.output codeEquation) ambientAnswer.2

/-- **Attachment preserves schedule-agnosticity.**  `ofAmbient` pulls its
domain back along `List.map encodeQuery`, and `map` preserves permutations, so
a converter attached to an order-blind resource yields an order-blind resource.

This is what carries `DependentDDS.ScheduleAgnostic` from a bare resource to
the `π • R` that endpoints are actually stated about: without it the receipts
would only cover the assumed and ideal resources in isolation, not the systems
a distinguisher really sees. -/
theorem DependentDDS.scheduleAgnostic_ofAmbient {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    (wellTyped : AmbientWellTyped boundary system)
    (ambient : ∀ {left right : List (I × AmbientInput U)}, left.Perm right →
      (left ∈ PFunDDS.dom system ↔ right ∈ PFunDDS.dom system)) :
    DependentDDS.ScheduleAgnostic (DependentDDS.ofAmbient system wellTyped) :=
  fun perm => ambient (perm.map _)

@[simp]
theorem DependentDDS.of_ambient_domain {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    (wellTyped : AmbientWellTyped boundary system) :
    (DependentDDS.ofAmbient system wellTyped).domain =
      {history | history.map encodeQuery ∈ PFunDDS.dom system} :=
  rfl

/-- Rebuilding a dependent ambient output along its proved code equality is
the original sigma value. -/
private theorem ambient_output_rebuild {U : SignatureUniverse}
    (answer : AmbientOutput U) (code : U.Code)
    (same : answer.1 = code) :
    (⟨code, Eq.mp (congrArg U.output same) answer.2⟩ : AmbientOutput U) =
      answer := by
  rcases answer with ⟨actual, value⟩
  subst code
  rfl

/-- Restriction and uniform embedding are inverse on every boundary-confined
ambient resource.  This is the chart-coherence theorem used to transport the
already proved uniform attachment laws to the native dependent carrier. -/
theorem DependentDDS.embed_ofAmbient {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I}
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    (wellTyped : AmbientWellTyped boundary system) :
    (DependentDDS.ofAmbient system wellTyped).embed = system := by
  apply Subtype.ext
  funext history
  apply Part.ext'
  · change EmbeddedDomain (DependentDDS.ofAmbient system wellTyped) history ↔
      history ∈ PFunDDS.dom system
    constructor
    · intro member
      have decodedMember := member.2 member.1
      change (decodeHistory boundary history member.1).map encodeQuery ∈
        PFunDDS.dom system at decodedMember
      simpa only [encode_history_decode] using decodedMember
    · intro member
      let answer := PFunDDS.output system history member
      have answerMember : answer ∈ system.1 history := Part.get_mem _
      have conforms := (wellTyped history answer answerMember).1
      refine ⟨conforms, fun conforms' => ?_⟩
      change (decodeHistory boundary history conforms').map encodeQuery ∈
        PFunDDS.dom system
      simpa only [encode_history_decode] using member
  · intro left right
    let typedHistory := decodeHistory boundary history left.1
    have typedNonempty : typedHistory ≠ [] := by
      intro empty
      have lengths := decode_history_length history left.1
      change typedHistory.length = history.length at lengths
      rw [empty] at lengths
      have historyEmpty := List.eq_nil_of_length_eq_zero lengths.symm
      subst history
      exact PFunDDS.empty_not_mem system right
    have typedMember : typedHistory.map encodeQuery ∈ PFunDDS.dom system := by
      exact left.2 left.1
    let ambientAnswer := PFunDDS.output system
      (typedHistory.map encodeQuery) typedMember
    have ambientMember : ambientAnswer ∈
        system.1 (typedHistory.map encodeQuery) := Part.get_mem _
    have codeEquation : ambientAnswer.1 =
        boundary (typedHistory.getLast typedNonempty).1 := by
      have confined := (wellTyped (typedHistory.map encodeQuery)
        ambientAnswer ambientMember).2 (by simpa using typedNonempty)
      simpa only [List.getLast_map] using confined
    change
      (⟨boundary (typedHistory.getLast typedNonempty).1,
        Eq.mp (congrArg U.output codeEquation) ambientAnswer.2⟩ :
          AmbientOutput U) = PFunDDS.output system history right
    calc
      _ = ambientAnswer :=
        ambient_output_rebuild ambientAnswer
          (boundary (typedHistory.getLast typedNonempty).1) codeEquation
      _ = PFunDDS.output system history right :=
        PFunDDS.output_congr system
          (encode_history_decode boundary history left.1) typedMember right

/-- At one fixed boundary, the uniform implementation chart forgets no
native resource information.  Although `encodeAnswer` omits the interface
tag, both flat answers at a fixed history carry the active query's tag, so
equality of their ambient encodings reflects equality of the native answers. -/
theorem DependentDDS.embed_injective {I : Type i}
    {U : SignatureUniverse} {boundary : Boundary U I} :
    Function.Injective
      (DependentDDS.embed : DependentDDS U boundary →
        PFunDDS.Resource I (AmbientInput U) (AmbientOutput U)) := by
  intro left right same
  apply DependentDDS.flatten_injective
  apply Subtype.ext
  funext history
  apply Part.ext'
  · have point := congrArg (fun system =>
        (system.1 (history.map encodeQuery)).Dom) same
    simpa [DependentDDS.embed, EmbeddedDomain] using point
  · intro leftMember rightMember
    let leftAnswer := PFunDDS.output left.flatten history leftMember
    let rightAnswer := PFunDDS.output right.flatten history rightMember
    have tagEqual : leftAnswer.1 = rightAnswer.1 :=
      (left.flatten_tag_faithful history leftMember).trans
        (right.flatten_tag_faithful history rightMember).symm
    have leftEncoded :
        encodeAnswer leftAnswer ∈ left.embed.1 (history.map encodeQuery) := by
      rw [left.embed_apply_encoded history]
      exact Part.mem_map _ (Part.get_mem _)
    have rightEncoded :
        encodeAnswer rightAnswer ∈ right.embed.1 (history.map encodeQuery) := by
      rw [right.embed_apply_encoded history]
      exact Part.mem_map _ (Part.get_mem _)
    have leftInRight :
        encodeAnswer leftAnswer ∈ right.embed.1 (history.map encodeQuery) := by
      rw [← same]
      exact leftEncoded
    have encodedEqual : encodeAnswer leftAnswer = encodeAnswer rightAnswer :=
      Part.mem_unique leftInRight rightEncoded
    change leftAnswer = rightAnswer
    rcases leftAnswer with ⟨leftTag, leftValue⟩
    rcases rightAnswer with ⟨rightTag, rightValue⟩
    dsimp only at tagEqual
    subst rightTag
    simp only [encodeAnswer] at encodedEqual
    have valueEqual : leftValue = rightValue :=
      eq_of_heq (Sigma.mk.inj encodedEqual).2
    subst rightValue
    rfl

/-- Transporting a native resource along equality of boundaries is invisible
in the boundary-independent ambient implementation chart. -/
@[simp]
theorem DependentDDS.embed_transport {I : Type i}
    {U : SignatureUniverse} {left right : Boundary U I}
    (same : left = right) (system : DependentDDS U left) :
    (cast (congrArg (fun boundary => DependentDDS U boundary) same)
      system).embed = system.embed := by
  cases same
  rfl

/-- Equality of boundaries together with equality in the ambient chart
reflects heterogeneous equality of native dependent resources. -/
theorem DependentDDS.heq_of_boundary_eq_of_embed_eq {I : Type i}
    {U : SignatureUniverse} {leftBoundary rightBoundary : Boundary U I}
    {left : DependentDDS U leftBoundary}
    {right : DependentDDS U rightBoundary}
    (boundaryEqual : leftBoundary = rightBoundary)
    (embedEqual : left.embed = right.embed) : HEq left right := by
  subst rightBoundary
  exact heq_of_eq (DependentDDS.embed_injective embedEqual)

/-! ## Recoding arbitrary typed converters in the uniform chart -/

section ConverterEncoding

variable {U : SignatureUniverse} [DecidableEq U.Code]

/-- Decode an ambient input precisely when it carries the requested code. -/
def decodeInputAt (code : U.Code) : AmbientInput U → Option (U.input code)
  | ⟨actual, value⟩ =>
      if same : actual = code then
        some (Eq.mp (congrArg U.input same) value)
      else
        none

/-- Decode an ambient proper answer precisely at the requested code. -/
def decodeOutputAt (code : U.Code) : AmbientOutput U → Option (U.output code)
  | ⟨actual, value⟩ =>
      if same : actual = code then
        some (Eq.mp (congrArg U.output same) value)
      else
        none

@[simp]
theorem decode_input_at_encoded (code : U.Code) (value : U.input code) :
    decodeInputAt code (⟨code, value⟩ : AmbientInput U) = some value := by
  simp [decodeInputAt]

@[simp]
theorem decode_output_at_encoded (code : U.Code) (value : U.output code) :
    decodeOutputAt code (⟨code, value⟩ : AmbientOutput U) = some value := by
  simp [decodeOutputAt]

/-- Decode a whole outside-input history at one signature code. -/
def decodeInputsAt (code : U.Code) :
    List (AmbientInput U) → Option (List (U.input code)) :=
  List.mapM (decodeInputAt code)

/-- Decode the completed inner-answer history at one code.  `none` is
preserved rather than assigned an invented tag. -/
def decodeAnswersAt (code : U.Code) :
    List (Option (AmbientOutput U)) → Option (List (Option (U.output code))) :=
  List.mapM fun
    | none => some none
    | some value => (decodeOutputAt code value).map some

/-- A successful `Option`-valued `mapM` preserves list length.  (The general
statement lives with the proper-segment calculus, `StepRealization.lean`.) -/
private theorem mapM_eq_some_length {A B : Type*} (f : A → Option B)
    {values : List A} {decoded : List B}
    (equation : values.mapM f = some decoded) :
    decoded.length = values.length :=
  RandomSystems.CR18.mapM_length f equation

/-- Successful `Option`-valued `mapM` restricts to every prefix. -/
private theorem mapM_take_of_eq_some {A B : Type*} (f : A → Option B)
    {values : List A} {decoded : List B}
    (equation : values.mapM f = some decoded) (count : ℕ) :
    (values.take count).mapM f = some (decoded.take count) := by
  induction values generalizing decoded count with
  | nil =>
      change some [] = some decoded at equation
      have decodedEquation : ([] : List B) = decoded :=
        Option.some.inj equation
      subst decoded
      simp
  | cons value rest induction =>
      simp only [List.mapM_cons] at equation
      cases headEquation : f value with
      | none => simp [headEquation] at equation
      | some head =>
          simp only [headEquation, Option.bind_some] at equation
          cases tailEquation : rest.mapM f with
          | none => simp [tailEquation] at equation
          | some tail =>
              rw [tailEquation] at equation
              change some (head :: tail) = some decoded at equation
              have decodedEquation : head :: tail = decoded :=
                Option.some.inj equation
              subst decoded
              cases count with
              | zero => simp
              | succ count =>
                  simp only [List.take_succ_cons, List.mapM_cons,
                    headEquation]
                  rw [induction tailEquation count]
                  change some (head :: tail.take count) =
                    some (head :: tail.take count)
                  rfl

@[simp]
theorem decode_inputs_at_encoded (code : U.Code)
    (values : List (U.input code)) :
    decodeInputsAt code (values.map fun value =>
      (⟨code, value⟩ : AmbientInput U)) = some values := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      change List.mapM (decodeInputAt code)
          (List.map (fun value => (⟨code, value⟩ : AmbientInput U)) rest) =
        some rest at induction
      simp [decodeInputsAt, induction]

/-- Successful decoding certifies the code of every ambient outside input. -/
theorem code_eq_of_mem_decode_inputs_at
    (code : U.Code) {values : List (AmbientInput U)}
    {decoded : List (U.input code)}
    (equation : decodeInputsAt code values = some decoded)
    {value : AmbientInput U} (contains : value ∈ values) :
    value.1 = code := by
  induction values generalizing decoded with
  | nil => simp at contains
  | cons head rest induction =>
      simp only [decodeInputsAt, List.mapM_cons] at equation
      cases headEquation : decodeInputAt code head with
      | none => simp [headEquation] at equation
      | some decodedHead =>
          simp only [headEquation, Option.bind_some] at equation
          cases tailEquation : List.mapM (decodeInputAt code) rest with
          | none => simp [tailEquation] at equation
          | some decodedTail =>
              rw [tailEquation] at equation
              change some (decodedHead :: decodedTail) = some decoded at equation
              have decodedEquation : decodedHead :: decodedTail = decoded :=
                Option.some.inj equation
              subst decoded
              simp only [List.mem_cons] at contains
              rcases contains with same | contains
              · subst value
                rcases head with ⟨actual, payload⟩
                simp only [decodeInputAt] at headEquation
                split at headEquation
                · assumption
                · simp at headEquation
              · exact induction tailEquation contains

@[simp]
theorem decode_answers_at_encoded (code : U.Code)
    (values : List (Option (U.output code))) :
    decodeAnswersAt code (values.map fun value =>
      value.map fun answer => (⟨code, answer⟩ : AmbientOutput U)) =
        some values := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      cases value with
      | none =>
          simp only [List.map_cons, Option.map_none, decodeAnswersAt,
            List.mapM_cons, Option.bind_some]
          change (decodeAnswersAt code
            (rest.map fun value => value.map fun answer =>
              (⟨code, answer⟩ : AmbientOutput U))).bind
                (fun tail => some (none :: tail)) = some (none :: rest)
          rw [induction]
          rfl
      | some value =>
          simp only [List.map_cons, Option.map_some, decodeAnswersAt,
            List.mapM_cons, decode_output_at_encoded, Option.map_some,
            Option.bind_some]
          change (decodeAnswersAt code
            (rest.map fun value => value.map fun answer =>
              (⟨code, answer⟩ : AmbientOutput U))).bind
                (fun tail => some (some value :: tail)) =
              some (some value :: rest)
          rw [induction]
          rfl

/-- Outside-history decoding is compatible with appending one input. -/
theorem decode_inputs_at_append (code : U.Code)
    (values : List (AmbientInput U)) (value : AmbientInput U) :
    decodeInputsAt code (values ++ [value]) = (do
      let decoded ← decodeInputsAt code values
      let last ← decodeInputAt code value
      pure (decoded ++ [last])) := by
  rw [decodeInputsAt, List.mapM_append]
  cases decoded : List.mapM (decodeInputAt code) values <;>
    cases last : decodeInputAt code value <;> simp [decoded, last]

/-- Completed-answer decoding is compatible with appending one response. -/
theorem decode_answers_at_append (code : U.Code)
    (values : List (Option (AmbientOutput U)))
    (value : Option (AmbientOutput U)) :
    decodeAnswersAt code (values ++ [value]) = (do
      let decoded ← decodeAnswersAt code values
      let last ← match value with
        | none => some none
        | some answer => (decodeOutputAt code answer).map some
      pure (decoded ++ [last])) := by
  rw [decodeAnswersAt, List.mapM_append]
  cases decoded : List.mapM (fun
      | none => some none
      | some value => (decodeOutputAt code value).map some) values <;>
    cases value with
    | none => simp [decoded]
    | some answer =>
        cases last : decodeOutputAt code answer <;> simp [decoded, last]

/-- Completed-answer decoding distributes over concatenation. -/
theorem decode_answers_at_append_lists (code : U.Code)
    (left right : List (Option (AmbientOutput U))) :
    decodeAnswersAt code (left ++ right) = (do
      let decodedLeft ← decodeAnswersAt code left
      let decodedRight ← decodeAnswersAt code right
      pure (decodedLeft ++ decodedRight)) := by
  rw [decodeAnswersAt, List.mapM_append]

/-- Successful decoding of a concatenation exposes independently decoded
left and right parts. -/
theorem decode_answers_at_append_lists_eq_some_iff (code : U.Code)
    (left right : List (Option (AmbientOutput U)))
    (decoded : List (Option (U.output code))) :
    decodeAnswersAt code (left ++ right) = some decoded ↔
      ∃ decodedLeft decodedRight,
        decodeAnswersAt code left = some decodedLeft ∧
        decodeAnswersAt code right = some decodedRight ∧
        decoded = decodedLeft ++ decodedRight := by
  rw [decode_answers_at_append_lists]
  cases leftEquation : decodeAnswersAt code left <;>
    cases rightEquation : decodeAnswersAt code right <;>
    simp [leftEquation, rightEquation, eq_comm]

/-- Successful completed-answer decoding preserves length. -/
theorem decode_answers_at_eq_some_length (code : U.Code)
    {values : List (Option (AmbientOutput U))}
    {decoded : List (Option (U.output code))}
    (equation : decodeAnswersAt code values = some decoded) :
    decoded.length = values.length := by
  exact mapM_eq_some_length _ equation

/-- Successful completed-answer decoding restricts to every prefix. -/
theorem decode_answers_at_take (code : U.Code)
    {values : List (Option (AmbientOutput U))}
    {decoded : List (Option (U.output code))}
    (equation : decodeAnswersAt code values = some decoded) (count : ℕ) :
    decodeAnswersAt code (values.take count) = some (decoded.take count) := by
  exact mapM_take_of_eq_some _ equation count

/-- Successful decoding after one appended outside input exposes the decoded
prefix and the decoded last input. -/
theorem decode_inputs_at_append_eq_some_iff (code : U.Code)
    (values : List (AmbientInput U)) (value : AmbientInput U)
    (decoded : List (U.input code)) :
    decodeInputsAt code (values ++ [value]) = some decoded ↔
      ∃ decodedPrefix last,
        decodeInputsAt code values = some decodedPrefix ∧
        decodeInputAt code value = some last ∧
        decoded = decodedPrefix ++ [last] := by
  rw [decode_inputs_at_append]
  cases hp : decodeInputsAt code values <;>
    cases hl : decodeInputAt code value <;> simp [hp, hl, eq_comm]

/-- Successful decoding after one appended completed answer exposes the
decoded prefix and last response. -/
theorem decode_answers_at_append_eq_some_iff (code : U.Code)
    (values : List (Option (AmbientOutput U)))
    (value : Option (AmbientOutput U))
    (decoded : List (Option (U.output code))) :
    decodeAnswersAt code (values ++ [value]) = some decoded ↔
      ∃ decodedPrefix last,
        decodeAnswersAt code values = some decodedPrefix ∧
        (match value with
          | none => some none
          | some answer => (decodeOutputAt code answer).map some) = some last ∧
        decoded = decodedPrefix ++ [last] := by
  rw [decode_answers_at_append]
  cases hp : decodeAnswersAt code values <;>
    cases value with
    | none => simp [hp, eq_comm]
    | some answer =>
        cases hl : decodeOutputAt code answer <;> simp [hp, hl, eq_comm]

/-- Decoding cannot erase an explicit rejection marker. -/
theorem none_mem_of_decode_answers_at_eq_some (code : U.Code)
    {values : List (Option (AmbientOutput U))}
    {decoded : List (Option (U.output code))}
    (equation : decodeAnswersAt code values = some decoded)
    (contains : none ∈ values) : none ∈ decoded := by
  induction values generalizing decoded with
  | nil => simp at contains
  | cons value rest induction =>
      cases value with
      | none =>
          have equation' : (decodeAnswersAt code rest).bind
              (fun tail => some (none :: tail)) = some decoded := by
            simpa only [decodeAnswersAt, List.mapM_cons,
              Option.bind_some] using equation
          cases tailEquation : decodeAnswersAt code rest with
          | none => simp [tailEquation] at equation'
          | some tail =>
            simp [tailEquation] at equation'
            subst decoded
            simp
      | some answer =>
          cases headEquation : decodeOutputAt code answer with
          | none =>
              simp [decodeAnswersAt, headEquation] at equation
          | some head =>
              have equation' : (decodeAnswersAt code rest).bind
                  (fun tail => some (some head :: tail)) = some decoded := by
                simpa only [decodeAnswersAt, List.mapM_cons,
                  headEquation, Option.map_some, Option.bind_some] using equation
              cases tailEquation : decodeAnswersAt code rest with
              | none => simp [tailEquation] at equation'
              | some tail =>
                  simp [tailEquation] at equation'
                  subst decoded
                  simp only [List.mem_cons, Option.some.injEq, reduceCtorEq]
                    at contains ⊢
                  have containsRest : none ∈ rest := by
                    simpa using contains
                  exact Or.inr (induction tailEquation containsRest)

/-- Map a local protocol move into the uniform implementation chart. -/
def encodeMove (source target : U.Code) :
    U.input source ⊕ U.output target → AmbientInput U ⊕ AmbientOutput U
  | Sum.inl query => Sum.inl ⟨source, query⟩
  | Sum.inr answer => Sum.inr ⟨target, answer⟩

/-- An encoded inner-query move remembers its local payload. -/
theorem encode_move_eq_query_iff (source target : U.Code)
    (localMove : U.input source ⊕ U.output target)
    (ambientQuery : AmbientInput U) :
    encodeMove source target localMove = Sum.inl ambientQuery ↔
      ∃ query, localMove = Sum.inl query ∧
        ambientQuery = ⟨source, query⟩ := by
  cases localMove <;> simp [encodeMove, eq_comm]

/-- An encoded outside-answer move remembers its local payload. -/
theorem encode_move_eq_answer_iff (source target : U.Code)
    (localMove : U.input source ⊕ U.output target)
    (ambientAnswer : AmbientOutput U) :
    encodeMove source target localMove = Sum.inr ambientAnswer ↔
      ∃ answer, localMove = Sum.inr answer ∧
        ambientAnswer = ⟨target, answer⟩ := by
  cases localMove <;> simp [encodeMove, eq_comm]

/-- The code-confined uniform presentation of an arbitrary typed protocol.
Off-code outside inputs and wrong-code proper answers are rejected. -/
def DeterministicConverter.embeddedProtocol {source target : U.Code}
    (converter : DeterministicConverter U source target) :
    ProtocolFn (AmbientInput U) (AmbientOutput U)
      (AmbientInput U) (AmbientOutput U) :=
  fun pair =>
    match decodeInputsAt target pair.1, decodeAnswersAt source pair.2 with
    | some outsideInputs, some innerAnswers =>
        (converter.protocol (outsideInputs, innerAnswers)).map
          (encodeMove source target)
    | _, _ => Part.none

/-- Membership in the embedded protocol is exactly membership in the local
protocol after successful code decoding. -/
theorem DeterministicConverter.mem_embedded_protocol_iff
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (pair : List (AmbientInput U) × List (Option (AmbientOutput U)))
    (move : AmbientInput U ⊕ AmbientOutput U) :
    move ∈ converter.embeddedProtocol pair ↔
      ∃ outsideInputs innerAnswers localMove,
        decodeInputsAt target pair.1 = some outsideInputs ∧
        decodeAnswersAt source pair.2 = some innerAnswers ∧
        localMove ∈ converter.protocol (outsideInputs, innerAnswers) ∧
        encodeMove source target localMove = move := by
  unfold DeterministicConverter.embeddedProtocol
  cases outside : decodeInputsAt target pair.1 <;>
    cases answers : decodeAnswersAt source pair.2 <;>
    simp [outside, answers, Part.mem_map_iff]

/-- Every reachable, defined pair of the embedded protocol decodes to a
reachable pair of the original arbitrary typed protocol.  This is the central
wrong-tag/`none` discipline lemma for the implementation chart. -/
theorem DeterministicConverter.reach_of_embedded_reach_and_dom
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    {pair : List (AmbientInput U) × List (Option (AmbientOutput U))}
    (reachable : Reach converter.embeddedProtocol pair)
    (defined : (converter.embeddedProtocol pair).Dom) :
    ∃ outsideInputs innerAnswers,
      decodeInputsAt target pair.1 = some outsideInputs ∧
      decodeAnswersAt source pair.2 = some innerAnswers ∧
      Reach converter.protocol (outsideInputs, innerAnswers) := by
  induction reachable with
  | first outsideInput =>
      obtain ⟨ambientMove, moveMember⟩ := Part.dom_iff_mem.mp defined
      obtain ⟨outsideInputs, innerAnswers, localMove,
        inputsEquation, answersEquation, _localMember, _moveEquation⟩ :=
        (converter.mem_embedded_protocol_iff _ ambientMove).mp moveMember
      obtain ⟨decodedPrefix, lastInput, prefixEquation, _lastEquation,
          outsideInputsEquation⟩ :=
        (decode_inputs_at_append_eq_some_iff target [] outsideInput
          outsideInputs).mp inputsEquation
      have decodedPrefixEmpty : decodedPrefix = [] := by
        simpa [decodeInputsAt] using Option.some.inj prefixEquation
      have innerAnswersEmpty : innerAnswers = [] := by
        simpa [decodeAnswersAt] using Option.some.inj answersEquation
      subst decodedPrefix
      subst innerAnswers
      subst outsideInputs
      exact ⟨[lastInput], [], inputsEquation, answersEquation,
        Reach.first lastInput⟩
  | answer previousReach queryMember suppliedAnswer induction =>
      rename_i ambientInputs ambientAnswers ambientQuery
      let previousPair := (ambientInputs, ambientAnswers)
      have previousDefined :
          (converter.embeddedProtocol previousPair).Dom :=
        Part.dom_iff_mem.mpr ⟨Sum.inl ambientQuery, queryMember⟩
      obtain ⟨previousInputs, previousAnswers,
          previousInputsEquation, previousAnswersEquation,
          previousReachable⟩ := induction previousDefined
      obtain ⟨moveInputs, moveAnswers, localMove,
          moveInputsEquation, moveAnswersEquation, localMoveMember,
          encodedMoveEquation⟩ :=
        (converter.mem_embedded_protocol_iff previousPair
          (Sum.inl ambientQuery)).mp queryMember
      have moveInputsEq : moveInputs = previousInputs :=
        Option.some.inj (moveInputsEquation.symm.trans previousInputsEquation)
      have moveAnswersEq : moveAnswers = previousAnswers :=
        Option.some.inj (moveAnswersEquation.symm.trans previousAnswersEquation)
      subst moveInputs
      subst moveAnswers
      obtain ⟨localQuery, rfl, ambientQueryEquation⟩ :=
        (encode_move_eq_query_iff source target localMove ambientQuery).mp
          encodedMoveEquation
      obtain ⟨ambientMove, finalMoveMember⟩ := Part.dom_iff_mem.mp defined
      obtain ⟨finalInputs, finalAnswers, _finalLocalMove,
          finalInputsEquation, finalAnswersEquation, _finalLocalMember,
          _finalMoveEquation⟩ :=
        (converter.mem_embedded_protocol_iff _ ambientMove).mp finalMoveMember
      have finalInputsEq : finalInputs = previousInputs :=
        Option.some.inj (finalInputsEquation.symm.trans previousInputsEquation)
      obtain ⟨decodedPrefix, lastAnswer, prefixEquation, _lastEquation,
          finalAnswersShape⟩ :=
        (decode_answers_at_append_eq_some_iff source previousPair.2
          suppliedAnswer finalAnswers).mp finalAnswersEquation
      have prefixEq : decodedPrefix = previousAnswers :=
        Option.some.inj (prefixEquation.symm.trans previousAnswersEquation)
      subst finalInputs
      subst decodedPrefix
      subst finalAnswers
      exact ⟨previousInputs, previousAnswers ++ [lastAnswer],
        finalInputsEquation, finalAnswersEquation,
        Reach.answer previousReachable localMoveMember lastAnswer⟩
  | next previousReach answerMember nextInput induction =>
      rename_i ambientInputs ambientAnswers ambientAnswer
      let previousPair := (ambientInputs, ambientAnswers)
      have previousDefined :
          (converter.embeddedProtocol previousPair).Dom :=
        Part.dom_iff_mem.mpr ⟨Sum.inr ambientAnswer, answerMember⟩
      obtain ⟨previousInputs, previousAnswers,
          previousInputsEquation, previousAnswersEquation,
          previousReachable⟩ := induction previousDefined
      obtain ⟨moveInputs, moveAnswers, localMove,
          moveInputsEquation, moveAnswersEquation, localMoveMember,
          encodedMoveEquation⟩ :=
        (converter.mem_embedded_protocol_iff previousPair
          (Sum.inr ambientAnswer)).mp answerMember
      have moveInputsEq : moveInputs = previousInputs :=
        Option.some.inj (moveInputsEquation.symm.trans previousInputsEquation)
      have moveAnswersEq : moveAnswers = previousAnswers :=
        Option.some.inj (moveAnswersEquation.symm.trans previousAnswersEquation)
      subst moveInputs
      subst moveAnswers
      obtain ⟨localAnswer, rfl, ambientAnswerEquation⟩ :=
        (encode_move_eq_answer_iff source target localMove ambientAnswer).mp
          encodedMoveEquation
      obtain ⟨ambientMove, finalMoveMember⟩ := Part.dom_iff_mem.mp defined
      obtain ⟨finalInputs, finalAnswers, _finalLocalMove,
          finalInputsEquation, finalAnswersEquation, _finalLocalMember,
          _finalMoveEquation⟩ :=
        (converter.mem_embedded_protocol_iff _ ambientMove).mp finalMoveMember
      obtain ⟨decodedPrefix, lastInput, prefixEquation, _lastEquation,
          finalInputsShape⟩ :=
        (decode_inputs_at_append_eq_some_iff target previousPair.1
          nextInput finalInputs).mp finalInputsEquation
      have prefixEq : decodedPrefix = previousInputs :=
        Option.some.inj (prefixEquation.symm.trans previousInputsEquation)
      have finalAnswersEq : finalAnswers = previousAnswers :=
        Option.some.inj (finalAnswersEquation.symm.trans previousAnswersEquation)
      subst decodedPrefix
      subst finalInputs
      subst finalAnswers
      exact ⟨previousInputs ++ [lastInput], previousAnswers,
        finalInputsEquation, finalAnswersEquation,
        Reach.next previousReachable localMoveMember lastInput⟩

/-- Definedness in the uniform chart reflects definedness of the decoded
local protocol state.  This is deliberately stated separately from reach:
the former is a code-decoding fact, while the latter is a trace-tree fact. -/
theorem DeterministicConverter.local_dom_of_embedded_dom
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    {pair : List (AmbientInput U) × List (Option (AmbientOutput U))}
    {outsideInputs : List (U.input target)}
    {innerAnswers : List (Option (U.output source))}
    (inputsEquation : decodeInputsAt target pair.1 = some outsideInputs)
    (answersEquation : decodeAnswersAt source pair.2 = some innerAnswers)
    (defined : (converter.embeddedProtocol pair).Dom) :
    (converter.protocol (outsideInputs, innerAnswers)).Dom := by
  obtain ⟨ambientMove, ambientMember⟩ := Part.dom_iff_mem.mp defined
  obtain ⟨decodedInputs, decodedAnswers, localMove,
      decodedInputsEquation, decodedAnswersEquation, localMember, _⟩ :=
    (converter.mem_embedded_protocol_iff pair ambientMove).mp ambientMember
  have decodedInputsEq : decodedInputs = outsideInputs :=
    Option.some.inj (decodedInputsEquation.symm.trans inputsEquation)
  have decodedAnswersEq : decodedAnswers = innerAnswers :=
    Option.some.inj (decodedAnswersEquation.symm.trans answersEquation)
  subst decodedInputs
  subst decodedAnswers
  exact Part.dom_iff_mem.mpr ⟨localMove, localMember⟩

/-- The uniform recoding preserves the `none`-stopping half of `IsDDC`.
Wrong-code answers cannot disappear during decoding, and an explicit `none`
is preserved literally. -/
theorem DeterministicConverter.embedded_protocol_answers_in_y
    {source target : U.Code}
    (converter : DeterministicConverter U source target) :
    AnswersInY converter.embeddedProtocol := by
  intro pair reachable contains defined
  obtain ⟨outsideInputs, innerAnswers, inputsEquation, answersEquation,
      localReach⟩ :=
    converter.reach_of_embedded_reach_and_dom reachable defined
  have localContains : none ∈ innerAnswers :=
    none_mem_of_decode_answers_at_eq_some source answersEquation contains
  have localDefined :
      (converter.protocol (outsideInputs, innerAnswers)).Dom :=
    converter.local_dom_of_embedded_dom inputsEquation answersEquation defined
  exact converter.isDDC.1 (outsideInputs, innerAnswers) localReach
    localContains localDefined

/-- Uniform recoding preserves the finite consecutive-query condition.  One
extra ambient prefix is used only to certify that the first `B` completed
answers all decode; it does not add a local converter query. -/
theorem DeterministicConverter.embedded_protocol_answers_within
    {source target : U.Code}
    (converter : DeterministicConverter U source target) {B : ℕ}
    (localBound : AnswersWithin converter.protocol B) :
    AnswersWithin converter.embeddedProtocol (B + 1) := by
  intro pair reachable extension extensionLong allQueries
  have extensionPositive : 0 < extension.length := by omega
  obtain ⟨ambientBaseQuery, ambientBaseQueryMember⟩ :=
    allQueries 0 extensionPositive
  have baseQueryMember :
      Sum.inl ambientBaseQuery ∈ converter.embeddedProtocol pair := by
    simpa using ambientBaseQueryMember
  have baseDefined : (converter.embeddedProtocol pair).Dom :=
    Part.dom_iff_mem.mpr ⟨Sum.inl ambientBaseQuery, baseQueryMember⟩
  obtain ⟨outsideInputs, innerAnswers, inputsEquation, answersEquation,
      localReach⟩ :=
    converter.reach_of_embedded_reach_and_dom reachable baseDefined

  have boundIndex : B < extension.length := by omega
  obtain ⟨ambientBoundQuery, ambientBoundQueryMember⟩ :=
    allQueries B boundIndex
  obtain ⟨boundInputs, boundAnswers, boundLocalMove,
      boundInputsEquation, boundAnswersEquation, boundLocalMember,
      boundMoveEquation⟩ :=
    (converter.mem_embedded_protocol_iff
      (pair.1, pair.2 ++ extension.take B)
      (Sum.inl ambientBoundQuery)).mp ambientBoundQueryMember
  obtain ⟨decodedBaseAnswers, localExtension,
      decodedBaseAnswersEquation, localExtensionEquation,
      boundAnswersShape⟩ :=
    (decode_answers_at_append_lists_eq_some_iff source pair.2
      (extension.take B) boundAnswers).mp boundAnswersEquation
  have decodedBaseAnswersEq : decodedBaseAnswers = innerAnswers :=
    Option.some.inj
      (decodedBaseAnswersEquation.symm.trans answersEquation)
  subst decodedBaseAnswers
  have localExtensionLength : localExtension.length = B := by
    rw [decode_answers_at_eq_some_length source localExtensionEquation,
      List.length_take]
    omega

  apply localBound (outsideInputs, innerAnswers) localReach localExtension
    (by omega)
  intro k kLess
  have kGlobal : k < extension.length := by omega
  obtain ⟨ambientQuery, ambientQueryMember⟩ := allQueries k kGlobal
  obtain ⟨queryInputs, queryAnswers, localMove,
      queryInputsEquation, queryAnswersEquation, localMoveMember,
      encodedMoveEquation⟩ :=
    (converter.mem_embedded_protocol_iff
      (pair.1, pair.2 ++ extension.take k)
      (Sum.inl ambientQuery)).mp ambientQueryMember
  have queryInputsEq : queryInputs = outsideInputs :=
    Option.some.inj (queryInputsEquation.symm.trans inputsEquation)
  subst queryInputs
  have localPrefixEquationRaw :=
    decode_answers_at_take source localExtensionEquation k
  have kLessBound : k < B := by omega
  have localPrefixEquation :
      decodeAnswersAt source (extension.take k) =
        some (localExtension.take k) := by
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt kLessBound)] using
      localPrefixEquationRaw
  have expectedAnswersEquation :
      decodeAnswersAt source (pair.2 ++ extension.take k) =
        some (innerAnswers ++ localExtension.take k) := by
    rw [decode_answers_at_append_lists, answersEquation,
      localPrefixEquation]
    change some (innerAnswers ++ localExtension.take k) =
      some (innerAnswers ++ localExtension.take k)
    rfl
  have queryAnswersEq :
      queryAnswers = innerAnswers ++ localExtension.take k :=
    Option.some.inj
      (queryAnswersEquation.symm.trans expectedAnswersEquation)
  subst queryAnswers
  obtain ⟨localQuery, rfl, _ambientQueryEquation⟩ :=
    (encode_move_eq_query_iff source target localMove ambientQuery).mp
      encodedMoveEquation
  exact ⟨localQuery, localMoveMember⟩

/-- Uniform recoding preserves the complete deterministic-discrete-converter
certificate. -/
theorem DeterministicConverter.embedded_protocol_is_ddc
    {source target : U.Code}
    (converter : DeterministicConverter U source target) :
    IsDDC converter.embeddedProtocol := by
  obtain ⟨bound, localBound⟩ := converter.isDDC.2
  exact ⟨converter.embedded_protocol_answers_in_y,
    bound + 1, converter.embedded_protocol_answers_within localBound⟩

/-- On encoded local histories the uniform presentation exposes exactly the
encoded local move. -/
theorem DeterministicConverter.embedded_protocol_apply_encoded
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (outsideInputs : List (U.input target))
    (innerAnswers : List (Option (U.output source))) :
    converter.embeddedProtocol
        (outsideInputs.map fun value =>
            (⟨target, value⟩ : AmbientInput U),
          innerAnswers.map fun value =>
            value.map fun answer =>
              (⟨source, answer⟩ : AmbientOutput U)) =
      (converter.protocol (outsideInputs, innerAnswers)).map
      (encodeMove source target) := by
  simp [DeterministicConverter.embeddedProtocol]

/-- Parsing a canonical DDC history never removes outside inputs already
present in the accumulated protocol-function state. -/
private theorem parses_to_aux_outside_fst_subset
    (protocol : ProtocolFn (AmbientInput U) (AmbientOutput U)
      (AmbientInput U) (AmbientOutput U)) :
    ∀ {state converterHistory pair},
      ParsesToAux protocol state converterHistory pair →
        ∀ value ∈ state.1, value ∈ pair.1 := by
  intro state converterHistory
  induction converterHistory generalizing state with
  | nil =>
      intro pair parsed value contains
      change pair = state at parsed
      subst pair
      exact contains
  | cons entry rest induction =>
      intro pair parsed value contains
      rcases entry with ⟨label, input⟩ | ⟨label, answer⟩ <;> cases label
      · exact parsed.elim
      · exact induction parsed.2 value
          (List.mem_append_left [input] contains)
      · exact induction parsed.2 value contains
      · exact parsed.elim

/-- Every outside input appearing in a parsed canonical DDC history occurs in
the final outside-input list supplied to its protocol function. -/
private theorem parses_to_aux_outside_mem_fst
    (protocol : ProtocolFn (AmbientInput U) (AmbientOutput U)
      (AmbientInput U) (AmbientOutput U)) :
    ∀ {converterHistory state pair value},
      ParsesToAux protocol state converterHistory pair →
        Sum.inl (InLabel.outside, value) ∈ converterHistory →
          value ∈ pair.1 := by
  intro converterHistory
  induction converterHistory with
  | nil => simp
  | cons entry rest induction =>
      intro state pair value parsed contains
      rcases entry with ⟨label, input⟩ | ⟨label, answer⟩ <;> cases label
      · exact parsed.elim
      · simp only [List.mem_cons, Sum.inl.injEq, Prod.mk.injEq,
          true_and] at contains
        rcases contains with same | contains
        · subst value
          exact parses_to_aux_outside_fst_subset protocol parsed.2 input
            (List.mem_append_right _ (List.mem_singleton_self input))
        · exact induction parsed.2 contains
      · simp only [List.mem_cons, reduceCtorEq, false_or] at contains
        exact induction parsed.2 contains
      · exact parsed.elim

/-- Outside inputs of a fully parsed canonical DDC history are precisely
accounted for by the resulting protocol-function input state. -/
private theorem parses_to_outside_mem_fst
    (protocol : ProtocolFn (AmbientInput U) (AmbientOutput U)
      (AmbientInput U) (AmbientOutput U))
    {converterHistory pair value}
    (parsed : ParsesTo protocol converterHistory pair)
    (contains : Sum.inl (InLabel.outside, value) ∈ converterHistory) :
    value ∈ pair.1 := by
  cases converterHistory with
  | nil => exact parsed.elim
  | cons entry rest =>
      rcases entry with ⟨label, input⟩ | ⟨label, answer⟩ <;> cases label
      · exact parsed.elim
      · change ParsesToAux protocol ([input], []) rest pair at parsed
        simp only [List.mem_cons, Sum.inl.injEq, Prod.mk.injEq,
          true_and] at contains
        rcases contains with same | contains
        · subst value
          exact parses_to_aux_outside_fst_subset protocol parsed input (by simp)
        · exact parses_to_aux_outside_mem_fst protocol parsed contains
      · exact parsed.elim
      · exact parsed.elim

/-- The DDC consumed by general stateful interface attachment. -/
noncomputable def DeterministicConverter.embeddedDDC {source target : U.Code}
    (converter : DeterministicConverter U source target) :
    DDC (AmbientInput U) (AmbientOutput U)
      (AmbientInput U) (AmbientOutput U) :=
  toDDC converter.embeddedProtocol

/-- Every proper outside answer of the recoded DDC carries the advertised
target code, independently of the converter-history representation. -/
theorem DeterministicConverter.embedded_ddc_outside_code
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    {history : List (DDC.CIn (AmbientInput U) (AmbientOutput U))}
    {answer : AmbientOutput U}
    (member : Sum.inl (InLabel.outside, answer) ∈
      converter.embeddedDDC.1 history) :
    answer.1 = target := by
  change Sum.inl (InLabel.outside, answer) ∈
    (toDDC converter.embeddedProtocol).1 history at member
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at member
  obtain ⟨pair, _parsed, localMove, localMember, moveEquation⟩ := member
  have localMoveEquation : localMove = Sum.inr answer :=
    (moveOf_eq_out_iff.mp moveEquation.symm)
  subst localMove
  obtain ⟨outsideInputs, innerAnswers, decodedMove,
      _inputsEquation, _answersEquation, _decodedMember,
      encodedMoveEquation⟩ :=
    (converter.mem_embedded_protocol_iff pair (Sum.inr answer)).mp
      localMember
  obtain ⟨localAnswer, rfl, ambientAnswerEquation⟩ :=
    (encode_move_eq_answer_iff source target decodedMove answer).mp
      encodedMoveEquation
  rw [ambientAnswerEquation]

/-- Every proper inside query of the recoded DDC carries the advertised
source code. -/
theorem DeterministicConverter.embedded_ddc_inside_code
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    {history : List (DDC.CIn (AmbientInput U) (AmbientOutput U))}
    {query : AmbientInput U}
    (member : Sum.inr (InLabel.inside, query) ∈
      converter.embeddedDDC.1 history) :
    query.1 = source := by
  change Sum.inr (InLabel.inside, query) ∈
    (toDDC converter.embeddedProtocol).1 history at member
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at member
  obtain ⟨pair, _parsed, localMove, localMember, moveEquation⟩ := member
  have localMoveEquation : localMove = Sum.inl query :=
    (moveOf_eq_in_iff.mp moveEquation.symm)
  subst localMove
  obtain ⟨outsideInputs, innerAnswers, decodedMove,
      _inputsEquation, _answersEquation, _decodedMember,
      encodedMoveEquation⟩ :=
    (converter.mem_embedded_protocol_iff pair (Sum.inl query)).mp localMember
  obtain ⟨localQuery, rfl, ambientQueryEquation⟩ :=
    (encode_move_eq_query_iff source target decodedMove query).mp
      encodedMoveEquation
  rw [ambientQueryEquation]

/-- Every outside input occurring in a defined recoded-DDC history carries
the converter's advertised target code.  This is stronger than merely typing
the final outside answer: it rules out accepting an ill-coded query and then
recovering later in the same stateful round. -/
theorem DeterministicConverter.embedded_ddc_outside_input_code
    {source target : U.Code}
    (converter : DeterministicConverter U source target)
    {history : List (DDC.CIn (AmbientInput U) (AmbientOutput U))}
    {move : DDC.COut (AmbientOutput U) (AmbientInput U)}
    (member : move ∈ converter.embeddedDDC.1 history)
    {input : AmbientInput U}
    (contains : Sum.inl (InLabel.outside, input) ∈ history) :
    input.1 = target := by
  change move ∈ (toDDC converter.embeddedProtocol).1 history at member
  rw [toDDC_toPFun, mem_toDDCRaw_iff] at member
  obtain ⟨pair, parsed, ambientMove, ambientMember, _moveEquation⟩ := member
  have inputInPair : input ∈ pair.1 :=
    parses_to_outside_mem_fst converter.embeddedProtocol parsed contains
  obtain ⟨outsideInputs, _innerAnswers, _localMove,
      inputsEquation, _answersEquation, _localMember,
      _encodedMoveEquation⟩ :=
    (converter.mem_embedded_protocol_iff pair ambientMove).mp ambientMember
  exact code_eq_of_mem_decode_inputs_at target inputsEquation inputInPair

end ConverterEncoding

/-! ## Native typed attachment through the uniform chart

The ambient chart is not the public resource type.  In particular, malformed
ambient proper outputs can carry the wrong signature code.  We pull the
general attachment back to the dependent target boundary by retaining exactly
the histories whose every nonempty prefix produces a decodable answer.  The
hereditary condition makes validity structural; the later coherence theorem
shows that on embedded typed systems it is precisely the intended operation.
-/

section NativeAttachment

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]

/-- The internal arbitrary-stateful attachment before it is pulled back to a
dependent target boundary. -/
noncomputable def DeterministicConverter.attachAmbient
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (system : DependentDDS U boundary) :
    PFunDDS.Resource I (AmbientInput U) (AmbientOutput U) :=
  PFunConverter.General.attachAt interface converter.embeddedDDC system.embed

/-- A successful resolving round of the embedded converter can terminate only
with a target-coded proper answer. -/
theorem DeterministicConverter.attach_resolve_outside_code
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    {state : List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
      List (AmbientQuery I U)}
    {result : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (member : result ∈ PFunConverter.General.attachResolve interface
      converter.embeddedDDC system state) :
    result.1.1 = target := by
  change result ∈
    (PFunConverter.General.attachStep interface converter.embeddedDDC system).fix
      state at member
  refine PFun.fixInduction member
    (C := fun _ => result.1.1 = target) ?_
  intro current fixed induction
  rw [PFun.mem_fix_iff] at fixed
  rcases fixed with stopped | ⟨next, stepped, _continued⟩
  · rw [PFunConverter.General.attachStep_mem_inl] at stopped
    exact converter.embedded_ddc_outside_code stopped.1
  · exact induction next stepped

/-- A successful resolving round certifies the code of the outside input that
opened it.  Continuation steps append only inside answers, so the opening
input remains present in every DDC history inspected by the fixed point. -/
theorem DeterministicConverter.attach_resolve_input_code
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    {state : List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
      List (AmbientQuery I U)}
    {input : AmbientInput U}
    {result : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (member : result ∈ PFunConverter.General.attachResolve interface
      converter.embeddedDDC system
        (state.1 ++ [Sum.inl (InLabel.outside, input)], state.2)) :
    input.1 = target := by
  change result ∈
    (PFunConverter.General.attachStep interface converter.embeddedDDC system).fix
      (state.1 ++ [Sum.inl (InLabel.outside, input)], state.2) at member
  refine PFun.fixInduction member
    (C := fun current =>
      Sum.inl (InLabel.outside, input) ∈ current.1 → input.1 = target) ?_
    (List.mem_append_right _ (List.mem_singleton_self _))
  intro current fixed induction contains
  rw [PFun.mem_fix_iff] at fixed
  rcases fixed with stopped | ⟨next, stepped, _continued⟩
  · rw [PFunConverter.General.attachStep_mem_inl] at stopped
    exact converter.embedded_ddc_outside_input_code stopped.1 contains
  · apply induction next stepped
    rw [PFunConverter.General.attachStep_mem_inr] at stepped
    obtain ⟨query, _queryMember, rfl⟩ := stepped
    exact List.mem_append_left _ contains

/-- Starting from a boundary-conforming base-resource history, one complete
converter round preserves that conformance.  The only possible extension is
an inside query emitted by the converter, whose source code is enforced by
`embedded_ddc_inside_code`; rejected resource queries leave the base history
unchanged, exactly as in `s⊥`. -/
theorem DeterministicConverter.attach_resolve_base_conforms
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))
    {state : List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
      List (AmbientQuery I U)}
    (stateConforms : HistoryConforms boundary state.2)
    {result : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (member : result ∈ PFunConverter.General.attachResolve interface
      converter.embeddedDDC system state) :
    HistoryConforms boundary result.2.2 := by
  change result ∈
    (PFunConverter.General.attachStep interface converter.embeddedDDC system).fix
      state at member
  refine PFun.fixInduction member
    (C := fun current => HistoryConforms boundary current.2 →
      HistoryConforms boundary result.2.2) ?_ stateConforms
  intro current fixed induction currentConforms
  rw [PFun.mem_fix_iff] at fixed
  rcases fixed with stopped | ⟨next, stepped, _continued⟩
  · rw [PFunConverter.General.attachStep_mem_inl] at stopped
    rw [stopped.2]
    exact currentConforms
  · apply induction next stepped
    rw [PFunConverter.General.attachStep_mem_inr] at stepped
    obtain ⟨query, queryMember, rfl⟩ := stepped
    have queryCode : query.1 = boundary interface :=
      (converter.embedded_ddc_inside_code queryMember).trans
        sourceMatches.symm
    cases answerEquation :
        PFunDDS.output (PFunDDS.fullyDefined system)
          (current.2 ++ [(interface, query)])
          (by rw [PFunDDS.dom_fullyDefined]; simp) with
    | none =>
        change HistoryConforms boundary current.2
        exact currentConforms
    | some answer =>
        change HistoryConforms boundary (current.2 ++ [(interface, query)])
        intro candidate contains
        rw [List.mem_append] at contains
        rcases contains with old | latest
        · exact currentConforms candidate old
        · simp only [List.mem_singleton] at latest
          subst candidate
          exact queryCode

/-- One successful outer driver entry is fully typed: the consumed outside
query conforms to the target boundary, the threaded base-resource history
still conforms to the source boundary, and the returned proper answer has the
code selected by that outside query. -/
theorem DeterministicConverter.attach_entry_typed
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {state : List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
      List (AmbientQuery I U)}
    (stateConforms : HistoryConforms boundary state.2)
    (entry : AmbientQuery I U)
    {result : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (member : result ∈ PFunConverter.General.attachEntryStep interface
      converter.embeddedDDC system.embed state entry) :
    QueryConforms (replaceBoundary boundary interface target) entry ∧
      HistoryConforms boundary result.2.2 ∧
      result.1.1 =
        replaceBoundary boundary interface target entry.1 := by
  by_cases same : entry.1 = interface
  · rw [PFunConverter.General.attachEntryStep, if_pos same] at member
    refine ⟨?_, ?_, ?_⟩
    · change entry.2.1 = replaceBoundary boundary interface target entry.1
      rw [same, replace_boundary_same]
      exact converter.attach_resolve_input_code interface system.embed member
    · exact converter.attach_resolve_base_conforms interface sourceMatches
        system.embed
        (state :=
          (state.1 ++ [Sum.inl (InLabel.outside, entry.2)], state.2))
        stateConforms member
    · rw [same, replace_boundary_same]
      exact converter.attach_resolve_outside_code interface system.embed member
  · rw [PFunConverter.General.attachEntryStep, if_neg same,
      Part.mem_map_iff] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    have confined := system.embed_well_typed (state.2 ++ [entry]) answer
      answerMember
    have entryConforms : QueryConforms boundary entry :=
      confined.1 entry
        (List.mem_append_right _ (List.mem_singleton_self entry))
    refine ⟨?_, confined.1, ?_⟩
    · change entry.2.1 = replaceBoundary boundary interface target entry.1
      rw [replace_boundary_ne boundary same target]
      exact entryConforms
    · change answer.1 = replaceBoundary boundary interface target entry.1
      rw [replace_boundary_ne boundary same target]
      have outputCode := confined.2 (by simp : state.2 ++ [entry] ≠ [])
      simpa only [List.getLast_append_singleton] using outputCode

/-- The complete stateful driver preserves both boundaries pointwise.  Its
answer-code list is aligned with the outside-query list, while its hidden
base-resource history remains confined to the source boundary. -/
theorem DeterministicConverter.attach_drive_typed
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    ∀ {outsideHistory : List (AmbientQuery I U)}
      {state : List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)},
      HistoryConforms boundary state.2 →
      ∀ {result : List (AmbientOutput U) ×
        (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
          List (AmbientQuery I U))},
        result ∈ PFunConverter.General.attachDrive interface
          converter.embeddedDDC system.embed state outsideHistory →
        HistoryConforms (replaceBoundary boundary interface target)
            outsideHistory ∧
          HistoryConforms boundary result.2.2 ∧
          result.1.map Sigma.fst = outsideHistory.map fun query =>
            replaceBoundary boundary interface target query.1 := by
  intro outsideHistory
  induction outsideHistory with
  | nil =>
      intro state stateConforms result member
      simp only [PFunConverter.General.attachDrive, Part.mem_some_iff] at member
      subst result
      exact ⟨by simp [HistoryConforms], stateConforms, rfl⟩
  | cons entry rest induction =>
      intro state stateConforms result member
      simp only [PFunConverter.General.attachDrive, Part.mem_bind_iff,
        Part.mem_map_iff] at member
      obtain ⟨entryResult, entryMember, restResult, restMember, rfl⟩ := member
      have entryTyped := converter.attach_entry_typed interface sourceMatches
        system stateConforms entry entryMember
      have restTyped := induction entryTyped.2.1 restMember
      refine ⟨?_, restTyped.2.1, ?_⟩
      · intro candidate contains
        simp only [List.mem_cons] at contains
        rcases contains with rfl | contains
        · exact entryTyped.1
        · exact restTyped.1 candidate contains
      · simp only [List.map_cons]
        rw [entryTyped.2.2, restTyped.2.2]

/-- General stateful attachment of an admissible typed converter to an
embedded dependent resource remains confined to the updated boundary. -/
theorem DeterministicConverter.attach_ambient_well_typed
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    AmbientWellTyped (replaceBoundary boundary interface target)
      (converter.attachAmbient interface system) := by
  intro outsideHistory answer member
  change answer ∈ PFunConverter.General.attachRaw interface
    converter.embeddedDDC system.embed outsideHistory at member
  simp only [PFunConverter.General.attachRaw, Part.mem_bind_iff] at member
  obtain ⟨result, driveMember, lastMember⟩ := member
  have driven := converter.attach_drive_typed interface sourceMatches system
    (state := ([], [])) (by simp [HistoryConforms]) driveMember
  refine ⟨driven.1, fun outsideNonempty => ?_⟩
  have driveLength := PFunConverter.General.attachDrive_length interface
    converter.embeddedDDC system.embed ([], []) outsideHistory driveMember
  have outputsNonempty : result.1 ≠ [] := by
    intro empty
    apply outsideNonempty
    apply List.eq_nil_of_length_eq_zero
    rw [← driveLength, empty]
    rfl
  rw [List.getLast?_eq_some_getLast outputsNonempty] at lastMember
  have answerEquation : answer = result.1.getLast outputsNonempty := by
    simpa only [Part.mem_some_iff] using lastMember
  have codeEquation := congrArg List.getLast? driven.2.2
  rw [List.getLast?_map,
    List.getLast?_eq_some_getLast outputsNonempty,
    List.getLast?_map,
    List.getLast?_eq_some_getLast outsideNonempty] at codeEquation
  simp only [Option.map_some, Option.some.injEq] at codeEquation
  rw [answerEquation]
  exact codeEquation

/-- Attach an arbitrary stateful typed converter at one interface of a native
shared-state dependent resource.  The source equality is part of the public
typing judgment; no exact-global-boundary gate and no invented fallback output
is used.  The public operation is the native restriction of the now-proved
boundary-confined ambient attachment. -/
noncomputable def DependentDDS.attach
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    DependentDDS U (replaceBoundary boundary interface target) :=
  DependentDDS.ofAmbient (converter.attachAmbient interface system)
    (converter.attach_ambient_well_typed interface sourceMatches system)

@[simp]
theorem DependentDDS.attach_domain
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    (system.attach interface converter sourceMatches).domain =
      {history | history.map encodeQuery ∈
        PFunDDS.dom (converter.attachAmbient interface system)} :=
  rfl

/-- Native typed attachment embeds exactly as the established arbitrary
stateful uniform attachment.  This is the main system-embedding coherence
obligation for the AC instantiation. -/
theorem DependentDDS.embed_attach
    {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    (system.attach interface converter sourceMatches).embed =
      converter.attachAmbient interface system := by
  exact DependentDDS.embed_ofAmbient _ _

/-- Native attachments at distinct interfaces commute after crossing to the
boundary-independent ambient chart.  This is the arbitrary-stateful typed
form of `PFunConverter.General.attachAt_comm`; no converter-subclass
assumption occurs. -/
theorem DependentDDS.embed_attach_comm
    {source₁ target₁ source₂ target₂ : U.Code}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : DeterministicConverter U source₁ target₁)
    (converter₂ : DeterministicConverter U source₂ target₂)
    {boundary : Boundary U I}
    (matches₁ : boundary interface₁ = source₁)
    (matches₂ : boundary interface₂ = source₂)
    (system : DependentDDS U boundary) :
    ((system.attach interface₂ converter₂ matches₂).attach
      interface₁ converter₁
        (by simpa [replaceBoundary, different] using matches₁)).embed =
    ((system.attach interface₁ converter₁ matches₁).attach
      interface₂ converter₂
        (by
          have reverse : interface₂ ≠ interface₁ := Ne.symm different
          simpa [replaceBoundary, reverse] using matches₂)).embed := by
  rw [DependentDDS.embed_attach, DependentDDS.embed_attach]
  unfold DeterministicConverter.attachAmbient
  rw [DependentDDS.embed_attach, DependentDDS.embed_attach]
  exact PFunConverter.General.attachAt_comm
    interface₁ converter₁.embeddedDDC
    interface₂ converter₂.embeddedDDC system.embed different

/-- Native arbitrary-stateful attachments at distinct interfaces form the
typed interchange square.  The sole transport identifies the two literally
commuting boundary updates; after embedding, the result is the established
raw general-attachment commutation theorem. -/
theorem DependentDDS.attach_comm
    {source₁ target₁ source₂ target₂ : U.Code}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : DeterministicConverter U source₁ target₁)
    (converter₂ : DeterministicConverter U source₂ target₂)
    {boundary : Boundary U I}
    (matches₁ : boundary interface₁ = source₁)
    (matches₂ : boundary interface₂ = source₂)
    (system : DependentDDS U boundary) :
    let left :=
      (system.attach interface₂ converter₂ matches₂).attach
        interface₁ converter₁
          (by simpa [replaceBoundary, different] using matches₁)
    let right :=
      (system.attach interface₁ converter₁ matches₁).attach
        interface₂ converter₂
          (by
            have reverse : interface₂ ≠ interface₁ := Ne.symm different
            simpa [replaceBoundary, reverse] using matches₂)
    HEq left right := by
  dsimp only
  apply DependentDDS.heq_of_boundary_eq_of_embed_eq
    (replace_boundary_comm boundary different target₁ target₂)
  exact system.embed_attach_comm different converter₁ converter₂
    matches₁ matches₂

end NativeAttachment

end TypedResource

end RandomSystems.CR18
