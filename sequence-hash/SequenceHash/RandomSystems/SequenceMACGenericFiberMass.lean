import SequenceHash.RandomSystems.SequenceMACGenericFiber
import SequenceHash.RandomSystems.Finite
import Mathlib.Data.List.Nodup

/-!
# SequenceFunction real and programmed-ideal reveal fibers

This module defines the representative reveal maps used by the R4
ideal-compression comparison.  The ideal reveal uses the facade's dummy keys
and programs only the output field of the final outer compression entry with
the corresponding ideal-function reply.  All preceding compression calls are
the genuine calls made with the sampled compression table.

The final-output programming is the per-call reduction behind the eventual
fiber-mass identity: on a good reveal, the real world's fresh final compression
coordinate is exchanged with the ideal world's fresh evaluation-function
coordinate.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel

open RandomSystems
open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique.IdealCompression

universe uBlock

/-! ## Evaluation slots in a tagged transcript -/

/-- Evaluation requests in visible query order. -/
def sequenceFunctionVisibleEvalRequests {Block : Type uBlock} {L : U128}
    {users p q : ℕ}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) :
    List (Fin users × InputSequence) :=
  t.1.toList.filterMap fun query =>
    match query with
    | .prim _ => none
    | .eval request => some request

/-- The request assigned to one of the facade's `q` evaluation reveal slots. -/
def sequenceFunctionEvalRequestAt? {Block : Type uBlock} {L : U128}
    {users p q : ℕ}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) (slot : Fin q) :
    Option (Fin users × InputSequence) :=
  (sequenceFunctionVisibleEvalRequests t)[slot.val]?

/-- The filtered evaluation-request list has the same cardinality as the
facade's tag counter. -/
theorem sequenceFunctionVisibleEvalRequests_length_eq_evalCount
    {Block : Type uBlock} {L : U128} {users p q : ℕ}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) :
    (sequenceFunctionVisibleEvalRequests t).length = evalCount t.1 := by
  have evalCount_cons : ∀ {n : ℕ}
      (query : SequenceFunctionICQuery Block L users)
      (queries : List.Vector (SequenceFunctionICQuery Block L users) n),
      evalCount (query ::ᵥ queries) =
        (match query with | .prim _ => 0 | .eval _ => 1) +
          evalCount queries := by
    classical
    intro n query queries
    unfold evalCount
    simp only [Finset.card_filter]
    rw [Fin.sum_univ_succ]
    cases query <;> simp [List.Vector.get_cons_succ]
  have length_eq : ∀ {n : ℕ}
      (queries : List.Vector (SequenceFunctionICQuery Block L users) n),
      (queries.toList.filterMap fun query =>
        match query with
        | .prim _ => none
        | .eval request => some request).length = evalCount queries := by
    intro n
    induction n with
    | zero =>
        intro queries
        simp [evalCount]
    | succ n ih =>
        intro queries
        rw [← queries.cons_head_tail]
        cases queries.head <;>
          simp [evalCount_cons]
        all_goals
          have htail := ih queries.tail
          omega
  exact length_eq t.1

/-- A budget-respecting length-`p+q` tagged transcript uses both budgets
exactly: every slot is either primitive or evaluation, so the two upper
bounds cannot leave slack. -/
theorem sequenceFunctionTaggedBudgetRespects_counts
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users t) :
    primCount t.1 = p ∧ evalCount t.1 = q := by
  classical
  let isPrim : Fin (p + q) → Prop := fun i =>
    match t.1.get i with | .prim _ => True | .eval _ => False
  let prims := (Finset.univ : Finset (Fin (p + q))).filter isPrim
  let evals := (Finset.univ : Finset (Fin (p + q))).filter fun i => ¬ isPrim i
  have hpartition : prims.card + evals.card = p + q := by
    simpa [prims, evals] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (p + q)))) isPrim
  have hprim : primCount t.1 = prims.card := by
    unfold primCount prims isPrim
    congr 1
    ext i
    cases hquery : t.1.get i <;> simp [hquery]
  have heval : evalCount t.1 = evals.card := by
    unfold evalCount evals isPrim
    congr 1
    ext i
    cases hquery : t.1.get i <;> simp [hquery]
  have hsum : primCount t.1 + evalCount t.1 = p + q := by
    rw [hprim, heval]
    exact hpartition
  have hp := hbudget.1
  have hq := hbudget.2.1
  exact ⟨by omega, by omega⟩

/-- Every evaluation reveal slot is populated when a length-`p+q` tagged
transcript respects the separate `p`/`q` budgets. -/
theorem sequenceFunctionEvalRequestAt?_exists_of_budget
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users t) (slot : Fin q) :
    ∃ request, sequenceFunctionEvalRequestAt? t slot = some request := by
  have hlen : (sequenceFunctionVisibleEvalRequests t).length = q := by
    rw [sequenceFunctionVisibleEvalRequests_length_eq_evalCount]
    exact (sequenceFunctionTaggedBudgetRespects_counts t hbudget).2
  have hslot : slot.val < (sequenceFunctionVisibleEvalRequests t).length := by
    omega
  refine ⟨(sequenceFunctionVisibleEvalRequests t)[slot.val], ?_⟩
  simp [sequenceFunctionEvalRequestAt?, List.getElem?_eq_getElem hslot]

/-! ## Programming the terminal compression output -/

/-- Replace only the output field of a nonempty trace's final entry.  Empty
traces remain empty. -/
def programFinalCompressionOutput {Role State Block : Type*}
    (output : State) (trace : List (TraceEntry Role State Block)) :
    List (TraceEntry Role State Block) :=
  if htrace : trace = [] then [] else
    trace.dropLast ++ [{ trace.getLast htrace with output := output }]

theorem programFinalCompressionOutput_eq_nil {Role State Block : Type*}
    (output : State) :
    programFinalCompressionOutput output
      ([] : List (TraceEntry Role State Block)) = [] := by
  simp [programFinalCompressionOutput]

theorem programFinalCompressionOutput_eq_dropLast_append
    {Role State Block : Type*} (output : State)
    (trace : List (TraceEntry Role State Block)) (htrace : trace ≠ []) :
    programFinalCompressionOutput output trace =
      trace.dropLast ++ [{ trace.getLast htrace with output := output }] := by
  simp [programFinalCompressionOutput, htrace]

@[simp]
theorem programFinalCompressionOutput_length {Role State Block : Type*}
    (output : State) (trace : List (TraceEntry Role State Block)) :
    (programFinalCompressionOutput output trace).length = trace.length := by
  by_cases htrace : trace = []
  · simp [programFinalCompressionOutput, htrace]
  · rw [programFinalCompressionOutput_eq_dropLast_append output trace htrace]
    simpa using congrArg List.length
      (List.dropLast_append_getLast (l := trace) htrace)

@[simp]
theorem programFinalCompressionOutput_inputs {Role State Block : Type*}
    (output : State) (trace : List (TraceEntry Role State Block)) :
    (programFinalCompressionOutput output trace).map TraceEntry.input =
      trace.map TraceEntry.input := by
  by_cases htrace : trace = []
  · simp [programFinalCompressionOutput, htrace]
  · rw [programFinalCompressionOutput_eq_dropLast_append output trace htrace]
    simpa using congrArg (List.map TraceEntry.input)
      (List.dropLast_append_getLast (l := trace) htrace)

theorem programFinalCompressionOutput_getLast?
    {Role State Block : Type*} (output : State)
    (trace : List (TraceEntry Role State Block)) (htrace : trace ≠ []) :
    (programFinalCompressionOutput output trace).getLast? =
      some { trace.getLast htrace with output := output } := by
  rw [programFinalCompressionOutput_eq_dropLast_append output trace htrace]
  simp

/-- Programming the terminal output leaves the complete honest prefix
unchanged.  This is the list-level honest-prefix agreement used before the
terminal uniform-coordinate swap in the representative mass proof. -/
theorem programFinalCompressionOutput_dropLast
    {Role State Block : Type*} (output : State)
    (trace : List (TraceEntry Role State Block)) :
    (programFinalCompressionOutput output trace).dropLast = trace.dropLast := by
  by_cases htrace : trace = []
  · simp [programFinalCompressionOutput, htrace]
  · rw [programFinalCompressionOutput_eq_dropLast_append output trace htrace]
    simp

/-- Reprogramming an already programmed nonempty trace replaces, rather than
stacks, the terminal output. -/
theorem programFinalCompressionOutput_programFinalCompressionOutput
    {Role State Block : Type*} (output output' : State)
    (trace : List (TraceEntry Role State Block)) :
    programFinalCompressionOutput output
        (programFinalCompressionOutput output' trace) =
      programFinalCompressionOutput output trace := by
  by_cases htrace : trace = []
  · subst trace
    simp only [programFinalCompressionOutput_eq_nil]
  · rw [programFinalCompressionOutput_eq_dropLast_append output'
      trace htrace]
    rw [programFinalCompressionOutput_eq_dropLast_append output]
    · simp [programFinalCompressionOutput_eq_dropLast_append output trace htrace]
    · simp

/-- Programming a nonempty trace with its existing terminal output is the
identity. -/
theorem programFinalCompressionOutput_getLast_output
    {Role State Block : Type*}
    (trace : List (TraceEntry Role State Block)) (htrace : trace ≠ []) :
    programFinalCompressionOutput (trace.getLast htrace).output trace =
      trace := by
  rw [programFinalCompressionOutput_eq_dropLast_append _ trace htrace]
  have hupdate :
      { trace.getLast htrace with output := (trace.getLast htrace).output } =
        trace.getLast htrace := by
    cases trace.getLast htrace
    rfl
  rw [hupdate, List.dropLast_append_getLast]

/-- Every padded non-terminal entry is identical before and after terminal
programming.  The bound is stated against `dropLast`, so it selects precisely
the honest prefix and is independent of the programmed value. -/
theorem padCompressionTrace_programFinalCompressionOutput_of_lt_dropLast
    {Role State Block : Type*} {lambda : ℕ} (output : State)
    (trace : List (TraceEntry Role State Block)) (i : Fin lambda)
    (hi : i.val < trace.dropLast.length) :
    padCompressionTrace lambda (programFinalCompressionOutput output trace) i =
      padCompressionTrace lambda trace i := by
  have htrace : trace ≠ [] := by
    intro hnil
    simp [hnil] at hi
  have hiTrace : i.val < trace.length := by
    simp only [List.length_dropLast] at hi
    omega
  rw [padCompressionTrace_eq_some_of_lt trace i hiTrace]
  have hiProgrammed : i.val <
      (programFinalCompressionOutput output trace).length := by
    simpa using hiTrace
  rw [padCompressionTrace_eq_some_of_lt _ i hiProgrammed]
  apply congrArg some
  simp only [List.get_eq_getElem]
  simp [programFinalCompressionOutput_eq_dropLast_append output trace htrace,
    List.getElem_append_left hi, List.getElem_dropLast hi]

/-! ## Call-by-call compression-table reduction -/

/-- Every call recorded by an MD trace is an honest compression-table
evaluation. -/
theorem mdCompressionTraceBlocks_output_eq {State : Type*}
    {Block : Type uBlock} (h : CompressionFunction State Block)
    (state : State) (blocks : List Block)
    (call : MDCompressionCall State Block)
    (hcall : call ∈ mdCompressionTraceBlocks h state blocks) :
    call.output = h call.input.1 call.input.2 := by
  induction blocks generalizing state with
  | nil => simp [mdCompressionTraceBlocks] at hcall
  | cons block blocks ih =>
      simp only [mdCompressionTraceBlocks, List.mem_cons] at hcall
      rcases hcall with rfl | hcall
      · rfl
      · exact ih (h state block) hcall

/-- Every call recorded by an `mdHash` trace is an honest compression-table
evaluation. -/
theorem mdCompressionTrace_output_eq {State : Type*}
    {Block : Type uBlock} (codec : MDCodec Block)
    (h : CompressionFunction State Block) (iv : State) (input : List Byte)
    (call : MDCompressionCall State Block)
    (hcall : call ∈ mdCompressionTrace codec h iv input) :
    call.output = h call.input.1 call.input.2 :=
  mdCompressionTraceBlocks_output_eq h iv (codec.blockify input) call hcall

/-- Role tagging preserves the honest compression-table equation. -/
theorem tagMDCompressionTrace_output_eq {State : Type*}
    {Block : Type uBlock} (h : CompressionFunction State Block)
    (role : SequenceFunctionCompressionRole)
    (trace : List (MDCompressionCall State Block))
    (htrace : ∀ call ∈ trace,
      call.output = h call.input.1 call.input.2)
    (entry : TraceEntry SequenceFunctionCompressionRole State Block)
    (hentry : entry ∈ tagMDCompressionTrace role trace) :
    entry.output = h entry.input.1 entry.input.2 := by
  obtain ⟨call, hcall, rfl⟩ := List.mem_map.mp hentry
  exact htrace call hcall

/-- Every entry of the canonical SequenceFunction trace is an honest
compression-table evaluation. -/
theorem sequenceFunctionCompressionTrace_output_eq
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence)
    (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block)
    (hentry : entry ∈ sequenceFunctionCompressionTrace model b S h K M) :
    entry.output = h entry.input.1 entry.input.2 := by
  have htag : ∀ (role : SequenceFunctionCompressionRole) (input : List Byte)
      (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block),
      entry ∈ tagMDCompressionTrace role
          (mdCompressionTrace model.codec h model.iv input) →
        entry.output = h entry.input.1 entry.input.2 := by
    intro role input entry hentry
    exact tagMDCompressionTrace_output_eq h role _
      (fun call hcall =>
        mdCompressionTrace_output_eq model.codec h model.iv input call hcall)
      entry hentry
  simp only [sequenceFunctionCompressionTrace] at hentry
  grind

/-- **Per-call reduction.**  In a programmed ideal trace, every entry before
the final one is an honest sampled-compression evaluation; the sole remaining
possibility is the final entry with its output replaced by `output`.

This is the local mass-preserving swap used by the CBC transcript-fiber
template: on `¬ Bad_SEQ`, final construction inputs are fresh, so each such
coordinate can be exchanged with its independent ideal-evaluation coordinate. -/
theorem sequenceFunctionProgrammedTrace_call_reduction
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) (output : HashOutput L)
    (htrace : sequenceFunctionCompressionTrace model b S h K M ≠ [])
    (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block)
    (hentry : entry ∈ programFinalCompressionOutput output
      (sequenceFunctionCompressionTrace model b S h K M)) :
    (entry ∈ (sequenceFunctionCompressionTrace model b S h K M).dropLast ∧
      entry.output = h entry.input.1 entry.input.2) ∨
    entry = {
      (sequenceFunctionCompressionTrace model b S h K M).getLast htrace with
      output := output } := by
  rw [programFinalCompressionOutput_eq_dropLast_append _ _ htrace,
    List.mem_append, List.mem_singleton] at hentry
  rcases hentry with hentry | hentry
  · exact Or.inl ⟨hentry, sequenceFunctionCompressionTrace_output_eq
      model b S h K M entry (List.mem_of_mem_dropLast hentry)⟩
  · exact Or.inr hentry

/-- Output backing identifies the programmed trace's terminal entry with the
ideal evaluation reply, without changing its outer role or input. -/
theorem sequenceFunctionProgrammedTrace_final_output
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) (output : HashOutput L) :
    ∃ input : HashOutput L × Block,
      (programFinalCompressionOutput output
        (sequenceFunctionCompressionTrace model b S h K M)).getLast? =
          some ⟨SequenceFunctionCompressionRole.outer, input, output⟩ := by
  obtain ⟨input, hlast⟩ :=
    sequenceFunctionCompressionTrace_final_output backed h K M
  have htrace : sequenceFunctionCompressionTrace model b S h K M ≠ [] := by
    intro hempty
    simp [hempty] at hlast
  rw [programFinalCompressionOutput_getLast? output _ htrace]
  have hget :
      (sequenceFunctionCompressionTrace model b S h K M).getLast htrace =
        ⟨SequenceFunctionCompressionRole.outer, input,
          sequenceFunctionICEval model b S h K M⟩ := by
    simpa [List.getLast?_eq_getLast_of_ne_nil htrace] using hlast
  simp [hget]

/-- Output backing makes every canonical evaluation compression trace
nonempty. -/
theorem sequenceFunctionCompressionTrace_ne_nil
    {Block : Type uBlock} {L : U128}
    {model : SequenceFunctionCompressionModel Block L}
    {b : BlockSize} {S : ByteString}
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence) :
    sequenceFunctionCompressionTrace model b S h K M ≠ [] := by
  obtain ⟨_, hlast⟩ :=
    sequenceFunctionCompressionTrace_final_output backed h K M
  exact fun hempty => by simp [hempty] at hlast

/-! ## Representative reveal maps -/

/-- The real reveal exposes the sampled keys and the honest canonical
compression trace for each visible evaluation slot. -/
def sequenceFunctionICRealReveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) :
    SequenceFunctionICRealRevealMap SequenceFunctionCompressionRole Block L
      users p q lambda :=
  fun coins t =>
    { keys := coins.2
      evalTraces := fun slot =>
        match sequenceFunctionEvalRequestAt? t slot with
        | none => fun _ => none
        | some request =>
            padCompressionTrace lambda
              (sequenceFunctionCompressionTrace model b S coins.1
                (coins.2 request.1) request.2) }

/-- The ideal reveal exposes the facade's dummy keys.  Its preceding calls
are evaluated with the sampled compression table, while the terminal outer
output is programmed to the independent ideal-function reply. -/
def sequenceFunctionICIdealReveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString) :
    SequenceFunctionICIdealRevealMap SequenceFunctionCompressionRole Block L
      users p q lambda :=
  fun coins t =>
    { keys := coins.2.1
      evalTraces := fun slot =>
        match sequenceFunctionEvalRequestAt? t slot with
        | none => fun _ => none
        | some request =>
            padCompressionTrace lambda
              (programFinalCompressionOutput
                (coins.2.2 request.1 request.2)
                (sequenceFunctionCompressionTrace model b S coins.1
                  (coins.2.1 request.1) request.2)) }

@[simp]
theorem sequenceFunctionICRealReveal_keys
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (coins : SequenceFunctionICRealCoins Block L users)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) :
    (sequenceFunctionICRealReveal (lambda := lambda) model b S coins t).keys =
      coins.2 :=
  rfl

@[simp]
theorem sequenceFunctionICIdealReveal_keys
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (coins : SequenceFunctionICIdealCoins Block L users)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q)) :
    (sequenceFunctionICIdealReveal (lambda := lambda) model b S coins t).keys =
      coins.2.1 :=
  rfl

/-! ## Honest-prefix agreement -/

/-- The real and ideal reveal maps agree entry-for-entry on the honest prefix
of every populated evaluation trace.  Only the terminal entry is excluded;
its output is the independent ideal-function coordinate and is the remaining
mass-swap step.

The ideal coins are written with the same compression table and keys as the
real coins.  The theorem is pointwise in the independent ideal function, so
the honest-prefix event is independent of that coordinate. -/
theorem sequenceFunctionICReveal_honestPrefix_agreement
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (evalSlot : Fin q) (request : Fin users × InputSequence)
    (hrequest : sequenceFunctionEvalRequestAt? t evalSlot = some request)
    (callSlot : Fin lambda)
    (hprefix : callSlot.val <
      (sequenceFunctionCompressionTrace model b S h
        (keys request.1) request.2).dropLast.length) :
    (sequenceFunctionICRealReveal (lambda := lambda) model b S (h, keys) t).evalTraces
        evalSlot callSlot =
      (sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (h, keys, idealEval) t).evalTraces evalSlot callSlot := by
  simp only [sequenceFunctionICRealReveal, sequenceFunctionICIdealReveal,
    hrequest]
  exact (padCompressionTrace_programFinalCompressionOutput_of_lt_dropLast
    (idealEval request.1 request.2)
    (sequenceFunctionCompressionTrace model b S h
      (keys request.1) request.2) callSlot hprefix).symm

/-- Agreement of two ideal evaluation functions on every visible evaluation
request preserves the ideal system rectangle event. -/
theorem sequenceFunctionICIdeal_transcriptSystemEvent_congr
    {Block : Type uBlock} {L : U128} {users p q : ℕ}
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval idealEval' : Fin users → InputSequence → HashOutput L)
    (hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests t,
      idealEval request.1 request.2 = idealEval' request.1 request.2) :
    PFunPDE.transcriptSystemEvent sequenceFunctionICIdealF t.1 t.2
        (h, keys, idealEval) ↔
      PFunPDE.transcriptSystemEvent sequenceFunctionICIdealF t.1 t.2
        (h, keys, idealEval') := by
  unfold sequenceFunctionICIdealF
    RandomSystems.HTechnique.IdealCompression.idealF
  rw [transcriptSystemEvent_functionEvaluatorRV_iff,
    transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor <;> intro hevent i <;> specialize hevent i
  · cases hquery : t.1.get i with
    | prim input => simpa [idealFunction, hquery] using hevent
    | eval request =>
        have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
          unfold sequenceFunctionVisibleEvalRequests
          apply List.mem_filterMap.mpr
          exact ⟨t.1.get i, List.get_mem _ _, by simp [hquery]⟩
        simpa [idealFunction, hquery, hagree request hmem] using hevent
  · cases hquery : t.1.get i with
    | prim input => simpa [idealFunction, hquery] using hevent
    | eval request =>
        have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
          unfold sequenceFunctionVisibleEvalRequests
          apply List.mem_filterMap.mpr
          exact ⟨t.1.get i, List.get_mem _ _, by simp [hquery]⟩
        simpa [idealFunction, hquery, (hagree request hmem).symm] using hevent

/-- Agreement of two ideal evaluation functions on every visible evaluation
request preserves the programmed ideal reveal. -/
theorem sequenceFunctionICIdealReveal_congr
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval idealEval' : Fin users → InputSequence → HashOutput L)
    (hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests t,
      idealEval request.1 request.2 = idealEval' request.1 request.2) :
    sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (h, keys, idealEval) t =
      sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (h, keys, idealEval') t := by
  unfold sequenceFunctionICIdealReveal
  rw [Reveal.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext slot callSlot
  ·
    cases hrequest : sequenceFunctionEvalRequestAt? t slot with
    | none => simp [sequenceFunctionICIdealReveal, hrequest]
    | some request =>
        have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
          rw [sequenceFunctionEvalRequestAt?, List.getElem?_eq_some_iff]
            at hrequest
          simpa [hrequest.2] using List.getElem_mem hrequest.1
        simp [sequenceFunctionICIdealReveal, hrequest, hagree request hmem]

/-- If the ideal evaluation table agrees with the real SequenceFunction on
every visible evaluation request, the real and ideal system rectangle events
coincide. -/
theorem sequenceFunctionIC_transcriptSystemEvent_real_ideal_iff
    {Block : Type uBlock} {L : U128} {users p q : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests t,
      idealEval request.1 request.2 =
        sequenceFunctionICEval model b S h (keys request.1) request.2) :
    PFunPDE.transcriptSystemEvent (sequenceFunctionICRealF model b S)
        t.1 t.2 (h, keys) ↔
      PFunPDE.transcriptSystemEvent sequenceFunctionICIdealF
        t.1 t.2 (h, keys, idealEval) := by
  unfold sequenceFunctionICRealF sequenceFunctionICIdealF
    RandomSystems.HTechnique.IdealCompression.realF
    RandomSystems.HTechnique.IdealCompression.idealF
  rw [transcriptSystemEvent_functionEvaluatorRV_iff,
    transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor <;> intro hevent i <;> specialize hevent i
  · cases hquery : t.1.get i with
    | prim input => simpa [realFunction, idealFunction, hquery] using hevent
    | eval request =>
        have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
          unfold sequenceFunctionVisibleEvalRequests
          apply List.mem_filterMap.mpr
          exact ⟨t.1.get i, List.get_mem _ _, by simp [hquery]⟩
        simpa [realFunction, idealFunction, hquery,
          hagree request hmem] using hevent
  · cases hquery : t.1.get i with
    | prim input => simpa [realFunction, idealFunction, hquery] using hevent
    | eval request =>
        have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
          unfold sequenceFunctionVisibleEvalRequests
          apply List.mem_filterMap.mpr
          exact ⟨t.1.get i, List.get_mem _ _, by simp [hquery]⟩
        simpa [realFunction, idealFunction, hquery,
          (hagree request hmem).symm] using hevent

/-- Under the same visible-request agreement, terminal programming is the
identity and the ideal reveal is the honest real reveal. -/
theorem sequenceFunctionICReveal_real_ideal_eq
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests t,
      idealEval request.1 request.2 =
        sequenceFunctionICEval model b S h (keys request.1) request.2) :
    sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (h, keys, idealEval) t =
      sequenceFunctionICRealReveal (lambda := lambda) model b S
        (h, keys) t := by
  unfold sequenceFunctionICIdealReveal sequenceFunctionICRealReveal
  rw [Reveal.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext slot callSlot
  cases hrequest : sequenceFunctionEvalRequestAt? t slot with
  | none => simp [hrequest]
  | some request =>
      have hmem : request ∈ sequenceFunctionVisibleEvalRequests t := by
        rw [sequenceFunctionEvalRequestAt?, List.getElem?_eq_some_iff]
          at hrequest
        simpa [hrequest.2] using List.getElem_mem hrequest.1
      let trace := sequenceFunctionCompressionTrace model b S h
        (keys request.1) request.2
      have htrace : trace ≠ [] :=
        sequenceFunctionCompressionTrace_ne_nil backed h
          (keys request.1) request.2
      obtain ⟨input, hlast⟩ :=
        sequenceFunctionCompressionTrace_final_output backed h
          (keys request.1) request.2
      have houtput : (trace.getLast htrace).output =
          sequenceFunctionICEval model b S h (keys request.1) request.2 := by
        have hlast' : some (trace.getLast htrace) =
            some ⟨SequenceFunctionCompressionRole.outer, input,
              sequenceFunctionICEval model b S h
                (keys request.1) request.2⟩ := by
          simpa [trace, List.getLast?_eq_getLast_of_ne_nil htrace] using hlast
        exact congrArg TraceEntry.output (Option.some.inj hlast')
      simp only [hrequest]
      rw [hagree request hmem, ← houtput,
        programFinalCompressionOutput_getLast_output trace htrace]

/-! ## Terminal-coordinate re-randomization -/

/-- The fixed-length byte-vector presentation of a `HashOutput`.  The shift
below uses the additive group on byte vectors only as a counting action; it
does not add algebraic structure to the SequenceFunction construction. -/
def sequenceFunctionHashOutputCoordinates (L : U128) :
    HashOutput L ≃ (Fin L.val → Byte) :=
  Equiv.vectorEquivFin Byte L.val

/-- Terminal entries of the populated revealed evaluation traces, in reveal
slot order.  This is the common indexed carrier for the fixed real terminal
table outputs and the programmed ideal-function outputs. -/
def sequenceFunctionRevealedTerminalEntries
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    List (TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block) :=
  (List.ofFn fun evalSlot : Fin q =>
      (List.ofFn fun callSlot : Fin lambda =>
        z.evalTraces evalSlot callSlot).filterMap id |>.getLast?).filterMap id

/-- Terminal inputs of the populated revealed evaluation traces, in reveal
slot order.  `getLast?` deliberately ignores empty/padded-only slots. -/
def sequenceFunctionRevealedTerminalInputs
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    List (HashOutput L × Block) :=
  (List.ofFn fun evalSlot : Fin q =>
      (((List.ofFn fun callSlot : Fin lambda =>
          z.evalTraces evalSlot callSlot).filterMap id).getLast?).map
      TraceEntry.input).filterMap id

theorem sequenceFunctionRevealedTerminalInputs_eq_map_entries
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    sequenceFunctionRevealedTerminalInputs z =
      (sequenceFunctionRevealedTerminalEntries z).map TraceEntry.input := by
  unfold sequenceFunctionRevealedTerminalInputs
    sequenceFunctionRevealedTerminalEntries
  rw [List.ofFn_comp', List.filterMap_map]
  exact (List.map_filterMap
    (f := id) (g := TraceEntry.input)).symm

@[simp]
theorem sequenceFunctionRevealedTerminalInputs_length
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    (sequenceFunctionRevealedTerminalInputs z).length =
      (sequenceFunctionRevealedTerminalEntries z).length := by
  rw [sequenceFunctionRevealedTerminalInputs_eq_map_entries, List.length_map]

/-- The sampled compression-table values at the revealed terminal inputs,
indexed by the fixed revealed terminal-entry list. -/
def sequenceFunctionRealTerminalCoordinate
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (h : CompressionFunction (HashOutput L) Block) :
    Fin (sequenceFunctionRevealedTerminalEntries z).length → HashOutput L :=
  fun i =>
    let input := (sequenceFunctionRevealedTerminalInputs z).get
      (Fin.cast (sequenceFunctionRevealedTerminalInputs_length z).symm i)
    h input.1 input.2

/-- The fixed terminal outputs carried by the reveal. -/
def sequenceFunctionRevealedTerminalCoordinate
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    Fin (sequenceFunctionRevealedTerminalEntries z).length → HashOutput L :=
  fun i => ((sequenceFunctionRevealedTerminalEntries z).get i).output

/-- The ideal-function replies at the slot-aligned visible evaluation
requests, reindexed by a proof that every terminal reveal slot is populated. -/
def sequenceFunctionIdealTerminalCoordinate
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (requestOf : Fin q → Fin users × InputSequence)
    (hlen : (sequenceFunctionRevealedTerminalEntries tz.2).length = q)
    (idealEval : Fin users → InputSequence → HashOutput L) :
    Fin (sequenceFunctionRevealedTerminalEntries tz.2).length → HashOutput L :=
  fun i =>
    let request := requestOf (Fin.cast hlen i)
    idealEval request.1 request.2

theorem sequenceFunctionRealTerminalCoordinate_eq_iff
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (h : CompressionFunction (HashOutput L) Block) :
    sequenceFunctionRealTerminalCoordinate z h =
        sequenceFunctionRevealedTerminalCoordinate z ↔
      ∀ i : Fin (sequenceFunctionRevealedTerminalInputs z).length,
        let input := (sequenceFunctionRevealedTerminalInputs z).get i
        h input.1 input.2 =
          ((sequenceFunctionRevealedTerminalEntries z).get
            (Fin.cast (sequenceFunctionRevealedTerminalInputs_length z) i)).output := by
  constructor
  · intro heq i
    simpa [sequenceFunctionRealTerminalCoordinate,
      sequenceFunctionRevealedTerminalCoordinate] using
      congrFun heq
        (Fin.cast (sequenceFunctionRevealedTerminalInputs_length z) i)
  · intro heq
    funext i
    simpa [sequenceFunctionRealTerminalCoordinate,
      sequenceFunctionRevealedTerminalCoordinate] using
      heq (Fin.cast
        (sequenceFunctionRevealedTerminalInputs_length z).symm i)

/-- Pointwise `some` values pass through `filterMap id` over `List.ofFn`. -/
theorem filterMap_id_ofFn_eq_of_some {A : Type*} {n : ℕ}
    (f : Fin n → Option A) (g : Fin n → A)
    (h : ∀ i, f i = some (g i)) :
    (List.ofFn f).filterMap id = List.ofFn g := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.filterMap_cons_some (show id (f 0) = some (g 0) by simpa using h 0)]
      congr 1
      exact ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)

/-- Selecting the last element of each nonempty row, applying a map, and
concatenating the results is a sublist of mapping the flattened rows. -/
theorem filterMap_getLast_map_sublist_flatten_map {A B : Type*}
    (f : A → B) (rows : List (List A)) :
    (((rows.map fun row => row.getLast?).map (Option.map f)).filterMap id).Sublist
      (rows.flatten.map f) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      cases hlast : row.getLast? with
      | none =>
          have hrow : row = [] := List.getLast?_eq_none_iff.mp hlast
          subst row
          simpa only [List.getLast?_nil, Option.map_none,
            List.filterMap_cons_none, List.flatten_cons, List.nil_append]
            using ih
      | some last =>
          have hmem : last ∈ row :=
            List.mem_of_mem_getLast? (by simp [hlast])
          simpa [hlast] using
            (List.singleton_sublist.mpr (List.mem_map.mpr ⟨last, hmem, rfl⟩)).append ih

/-- Every revealed terminal input is selected from the globally ordered list
of revealed construction inputs. -/
theorem sequenceFunctionRevealedTerminalInputs_sublist_constructionInputs
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    (sequenceFunctionRevealedTerminalInputs z).Sublist
      (sequenceFunctionRevealedConstructionInputs z) := by
  unfold sequenceFunctionRevealedTerminalInputs
    sequenceFunctionRevealedConstructionInputs
    sequenceFunctionRevealedConstructionCalls
  rw [List.ofFn_comp', List.ofFn_comp']
  exact filterMap_getLast_map_sublist_flatten_map TraceEntry.input
    (List.ofFn fun evalSlot : Fin q =>
      (List.ofFn fun callSlot : Fin lambda =>
        z.evalTraces evalSlot callSlot).filterMap id)

/-- The global construction-input `Nodup` furnished by `¬ Bad_SEQ` restricts
to the revealed terminal coordinates used by the shift. -/
theorem sequenceFunctionRevealedTerminalInputs_nodup_of_not_Bad_SEQ
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hgood : ¬ Bad_SEQ tz) :
    (sequenceFunctionRevealedTerminalInputs tz.2).Nodup := by
  exact ((not_Bad_SEQ_iff_compressionFresh tz).1 hgood).2.sublist
    (sequenceFunctionRevealedTerminalInputs_sublist_constructionInputs tz.2)

/-- Re-randomize the compression-table values at the revealed terminal
construction coordinates.  The terminal sites are fixed by the reveal, so
the action composes on the nose; freshness is needed only to read off one
specified coordinate without interference from another terminal site. -/
noncomputable def sequenceFunctionTerminalShift
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block) :
    CompressionFunction (HashOutput L) Block :=
  fun state block =>
    let e := sequenceFunctionHashOutputCoordinates L
    e.symm (e (h state block) +
      ∑ i, if (sequenceFunctionRevealedTerminalInputs z).get i = (state, block)
        then delta i else 0)

/-- **State shift.**  At a fresh terminal coordinate the shifted table value
is translated by exactly the requested byte-vector delta. -/
theorem sequenceFunctionTerminalShift_state
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block)
    (hfresh : (sequenceFunctionRevealedTerminalInputs z).Nodup)
    (i : Fin (sequenceFunctionRevealedTerminalInputs z).length) :
    let input := (sequenceFunctionRevealedTerminalInputs z).get i
    sequenceFunctionHashOutputCoordinates L
        (sequenceFunctionTerminalShift z delta h input.1 input.2) =
      sequenceFunctionHashOutputCoordinates L (h input.1 input.2) + delta i := by
  dsimp only
  rw [sequenceFunctionTerminalShift]
  simp only [Equiv.apply_symm_apply]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    exact fun hget => hji (hfresh.injective_get hget)
  · intro hi
    simp at hi

/-- Terminal shifts over one fixed reveal compose additively. -/
theorem sequenceFunctionTerminalShift_compose
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta delta' : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block) :
    sequenceFunctionTerminalShift z delta'
        (sequenceFunctionTerminalShift z delta h) =
      sequenceFunctionTerminalShift z (delta + delta') h := by
  funext state block
  apply (sequenceFunctionHashOutputCoordinates L).injective
  simp only [sequenceFunctionTerminalShift, Equiv.apply_symm_apply]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    split_ifs <;> rfl

/-- The zero terminal shift is the identity compression table. -/
theorem sequenceFunctionTerminalShift_zero
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (h : CompressionFunction (HashOutput L) Block) :
    sequenceFunctionTerminalShift z 0 h = h := by
  funext state block
  apply (sequenceFunctionHashOutputCoordinates L).injective
  simp [sequenceFunctionTerminalShift]

/-- Away from the revealed terminal sites, the terminal shift leaves the
compression table unchanged. -/
theorem sequenceFunctionTerminalShift_eq_of_not_mem
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block)
    (input : HashOutput L × Block)
    (hinput : input ∉ sequenceFunctionRevealedTerminalInputs z) :
    sequenceFunctionTerminalShift z delta h input.1 input.2 =
      h input.1 input.2 := by
  apply (sequenceFunctionHashOutputCoordinates L).injective
  simp only [sequenceFunctionTerminalShift, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [if_neg]
    intro heq
    have hmem := List.get_mem (sequenceFunctionRevealedTerminalInputs z) i
    rw [heq] at hmem
    exact hinput (by simpa using hmem)

/-- A terminal shift also fixes a table point when every terminal occurrence
of that point carries the zero delta.  This is the form needed when a final
construction point is already occupied by a visible primitive query: the
point is retained, rather than declared bad, and its compression coordinate
must not be re-randomized. -/
theorem sequenceFunctionTerminalShift_eq_of_zero_on_hits
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block)
    (input : HashOutput L × Block)
    (hzero : ∀ i,
      (sequenceFunctionRevealedTerminalInputs z).get i = input →
        delta i = 0) :
    sequenceFunctionTerminalShift z delta h input.1 input.2 =
      h input.1 input.2 := by
  apply (sequenceFunctionHashOutputCoordinates L).injective
  simp only [sequenceFunctionTerminalShift, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i _
    by_cases hit :
        (sequenceFunctionRevealedTerminalInputs z).get i = input
    · rw [if_pos hit, hzero i hit]
    · rw [if_neg hit]

/-! ### Trace stability under an off-trace table change -/

/-- An MD compression trace is unchanged when the second table agrees at
every input in the original trace. -/
theorem mdCompressionTraceBlocks_congr_of_eq_on_trace
    {State : Type*} {Block : Type uBlock}
    (h h' : CompressionFunction State Block) (state : State)
    (blocks : List Block)
    (heq : ∀ call ∈ mdCompressionTraceBlocks h state blocks,
      h' call.input.1 call.input.2 = h call.input.1 call.input.2) :
    mdCompressionTraceBlocks h' state blocks =
      mdCompressionTraceBlocks h state blocks := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block blocks ih =>
      have hhead : h' state block = h state block :=
        heq ⟨(state, block), h state block⟩ (by
          simp [mdCompressionTraceBlocks])
      simp only [mdCompressionTraceBlocks]
      rw [hhead]
      congr 1
      apply ih
      intro call hcall
      exact heq call (by simp [mdCompressionTraceBlocks, hcall])

/-- The corresponding `mdHash` values agree under the same trace-local table
agreement hypothesis. -/
theorem mdHash_congr_of_eq_on_trace
    {State : Type*} {Block : Type uBlock}
    (codec : MDCodec Block) (h h' : CompressionFunction State Block)
    (iv : State) (input : List Byte)
    (heq : ∀ call ∈ mdCompressionTrace codec h iv input,
      h' call.input.1 call.input.2 = h call.input.1 call.input.2) :
    mdHash codec h' iv input = mdHash codec h iv input := by
  have htrace := mdCompressionTraceBlocks_congr_of_eq_on_trace h h' iv
    (codec.blockify input) heq
  have htrace' : mdCompressionTrace codec h' iv input =
      mdCompressionTrace codec h iv input := by
    simpa [mdCompressionTrace] using htrace
  rw [mdCompressionTrace_reconstruct, mdCompressionTrace_reconstruct, htrace']

/-- If two compression tables agree on every non-terminal input of a
nonempty MD trace, the second trace has the same entries except for its final
output. -/
theorem mdCompressionTraceBlocks_eq_programFinal_of_eq_on_dropLast
    {State : Type*} {Block : Type uBlock}
    (h h' : CompressionFunction State Block) (state : State)
    (blocks : List Block) (last : MDCompressionCall State Block)
    (hlast : (mdCompressionTraceBlocks h state blocks).getLast? = some last)
    (heq : ∀ call ∈ (mdCompressionTraceBlocks h state blocks).dropLast,
      h' call.input.1 call.input.2 = h call.input.1 call.input.2) :
    mdCompressionTraceBlocks h' state blocks =
      (mdCompressionTraceBlocks h state blocks).dropLast ++
        [{last with output := h' last.input.1 last.input.2}] := by
  induction blocks generalizing state last with
  | nil => simp [mdCompressionTraceBlocks] at hlast
  | cons block blocks ih =>
      cases blocks with
      | nil =>
          simp [mdCompressionTraceBlocks] at hlast
          subst last
          simp [mdCompressionTraceBlocks]
      | cons next rest =>
          have hhead : h' state block = h state block :=
            heq ⟨(state, block), h state block⟩ (by
              simp [mdCompressionTraceBlocks])
          have hlastTail :
              (mdCompressionTraceBlocks h (h state block)
                (next :: rest)).getLast? = some last := by
            simpa [mdCompressionTraceBlocks] using hlast
          have htail := ih (h state block) last hlastTail (by
            intro call hcall
            apply heq call
            simpa [mdCompressionTraceBlocks] using Or.inr hcall)
          change
            ({ input := (state, block), output := h' state block } ::
                mdCompressionTraceBlocks h' (h' state block) (next :: rest)) =
              ({ input := (state, block), output := h state block } ::
                  mdCompressionTraceBlocks h (h state block) (next :: rest)).dropLast ++
                [{last with output := h' last.input.1 last.input.2}]
          rw [hhead, htail]
          rfl

/-- Dropping the last element of an append with a nonempty right operand
acts only on that right operand. -/
theorem dropLast_append_of_right_ne_nil {A : Type*}
    (left right : List A) (hright : right ≠ []) :
    (left ++ right).dropLast = left ++ right.dropLast := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      have hne : tail ++ right ≠ [] :=
        List.append_ne_nil_of_right_ne_nil tail hright
      cases htail : tail ++ right with
      | nil => exact (hne htail).elim
      | cons next rest =>
          simpa [htail] using congrArg (List.cons head) ih

/-- **SequenceFunction trace stability.**  If a second compression table
agrees with the first at every non-terminal input of the canonical trace,
then all derive, inner, and non-terminal outer entries are reproduced and
only the final outer output can change. -/
theorem sequenceFunctionCompressionTrace_eq_programFinal_of_eq_on_dropLast
    {Block : Type uBlock} {L : U128}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (h h' : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence)
    (heq : ∀ entry ∈
      (sequenceFunctionCompressionTrace model b S h K M).dropLast,
      h' entry.input.1 entry.input.2 = h entry.input.1 entry.input.2) :
    sequenceFunctionCompressionTrace model b S h' K M =
      programFinalCompressionOutput
        (sequenceFunctionICEval model b S h' K M)
        (sequenceFunctionCompressionTrace model b S h K M) := by
  classical
  let H := mdHash model.codec h model.iv
  let H' := mdHash model.codec h' model.iv
  let derivedK := derive K.1.val H b
  let derivedS := derive S.val H b
  let innerInput := sequenceFunctionInnerInput b fSeqMac K.1 derivedK M
  let inner := H innerInput
  let outerInput := sequenceFunctionOuterInput b fSeqMac K.1 S M
    derivedK derivedS inner
  let outerTrace := mdCompressionTrace model.codec h model.iv outerInput
  have houterTrace : outerTrace ≠ [] := by
    exact (mdCompressionTrace_nonempty_iff model.codec h model.iv outerInput).2
      (backed K M derivedK derivedS inner)
  have htagOuter : tagMDCompressionTrace
      SequenceFunctionCompressionRole.outer outerTrace ≠ [] := by
    simp [tagMDCompressionTrace, houterTrace]
  have hdropLast :
      (sequenceFunctionCompressionTrace model b S h K M).dropLast =
        ((if K.1.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveKey
              (mdCompressionTrace model.codec h model.iv K.1.val)) ++
          (if S.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveCustomization
              (mdCompressionTrace model.codec h model.iv S.val)) ++
          tagMDCompressionTrace .inner
            (mdCompressionTrace model.codec h model.iv innerInput)) ++
          (tagMDCompressionTrace .outer outerTrace).dropLast := by
    change
      (((if K.1.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveKey
              (mdCompressionTrace model.codec h model.iv K.1.val)) ++
          (if S.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveCustomization
              (mdCompressionTrace model.codec h model.iv S.val)) ++
          tagMDCompressionTrace .inner
            (mdCompressionTrace model.codec h model.iv innerInput)) ++
          tagMDCompressionTrace .outer outerTrace).dropLast = _
    exact dropLast_append_of_right_ne_nil _ _ htagOuter
  have hterminalPrefix : ∀
      (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block),
      entry ∈
        ((if K.1.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveKey
              (mdCompressionTrace model.codec h model.iv K.1.val)) ++
          (if S.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveCustomization
              (mdCompressionTrace model.codec h model.iv S.val)) ++
          tagMDCompressionTrace .inner
            (mdCompressionTrace model.codec h model.iv innerInput) ++
          (tagMDCompressionTrace .outer outerTrace).dropLast) →
        h' entry.input.1 entry.input.2 =
          h entry.input.1 entry.input.2 := by
    intro entry hentry
    apply heq entry
    rw [hdropLast]
    exact hentry
  have hkeyTrace : ¬ K.1.val.length ≤ b.val →
      mdCompressionTrace model.codec h' model.iv K.1.val =
        mdCompressionTrace model.codec h model.iv K.1.val := by
    intro hlong
    apply mdCompressionTraceBlocks_congr_of_eq_on_trace
    intro call hcall
    exact hterminalPrefix ⟨.deriveKey, call.input, call.output⟩ (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (by
        rw [if_neg hlong]
        exact List.mem_map.mpr ⟨call, hcall, rfl⟩))))
  have hderivedK : derive K.1.val H' b = derivedK := by
    by_cases hshort : K.1.val.length ≤ b.val
    · simp [derive, hshort, derivedK]
    · simp only [derive, hshort, if_false, derivedK]
      congr 2
      change mdHash model.codec h' model.iv K.1.val =
        mdHash model.codec h model.iv K.1.val
      rw [mdCompressionTrace_reconstruct, mdCompressionTrace_reconstruct,
        hkeyTrace hshort]
  have hcustomTrace : ¬ S.val.length ≤ b.val →
      mdCompressionTrace model.codec h' model.iv S.val =
        mdCompressionTrace model.codec h model.iv S.val := by
    intro hlong
    apply mdCompressionTraceBlocks_congr_of_eq_on_trace
    intro call hcall
    exact hterminalPrefix ⟨.deriveCustomization, call.input, call.output⟩ (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (by
        rw [if_neg hlong]
        exact List.mem_map.mpr ⟨call, hcall, rfl⟩))))
  have hderivedS : derive S.val H' b = derivedS := by
    by_cases hshort : S.val.length ≤ b.val
    · simp [derive, hshort, derivedS]
    · simp only [derive, hshort, if_false, derivedS]
      congr 2
      change mdHash model.codec h' model.iv S.val =
        mdHash model.codec h model.iv S.val
      rw [mdCompressionTrace_reconstruct, mdCompressionTrace_reconstruct,
        hcustomTrace hshort]
  have hinnerTrace :
      mdCompressionTrace model.codec h' model.iv innerInput =
        mdCompressionTrace model.codec h model.iv innerInput := by
    apply mdCompressionTraceBlocks_congr_of_eq_on_trace
    intro call hcall
    exact hterminalPrefix ⟨.inner, call.input, call.output⟩ (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨call, hcall, rfl⟩)))
  have hinner : H' innerInput = inner := by
    change mdHash model.codec h' model.iv innerInput =
      mdHash model.codec h model.iv innerInput
    rw [mdCompressionTrace_reconstruct, mdCompressionTrace_reconstruct,
      hinnerTrace]
  have houter :
      mdCompressionTrace model.codec h' model.iv outerInput =
        outerTrace.dropLast ++
          [{ outerTrace.getLast houterTrace with
            output := h' (outerTrace.getLast houterTrace).input.1
              (outerTrace.getLast houterTrace).input.2 }] := by
    apply mdCompressionTraceBlocks_eq_programFinal_of_eq_on_dropLast
      (last := outerTrace.getLast houterTrace)
    · exact List.getLast?_eq_getLast_of_ne_nil houterTrace
    · intro call hcall
      exact hterminalPrefix ⟨.outer, call.input, call.output⟩ (by
        simp only [List.mem_append]
        exact Or.inr (by
          unfold tagMDCompressionTrace
          rw [← List.map_dropLast]
          exact List.mem_map.mpr ⟨call, hcall, rfl⟩))
  have hlastOutput :
      h' (outerTrace.getLast houterTrace).input.1
          (outerTrace.getLast houterTrace).input.2 =
        sequenceFunctionICEval model b S h' K M := by
    have hmd : H' outerInput =
        h' (outerTrace.getLast houterTrace).input.1
          (outerTrace.getLast houterTrace).input.2 := by
      change mdHash model.codec h' model.iv outerInput = _
      rw [mdCompressionTrace_reconstruct, houter]
      simp
    rw [← hmd]
    simp [sequenceFunctionICEval, sequenceFunction, H', hderivedK,
      hderivedS, hinner, innerInput, outerInput]
  obtain ⟨terminalInput, hterminal⟩ :=
    sequenceFunctionCompressionTrace_final_output backed h K M
  have hfull : sequenceFunctionCompressionTrace model b S h K M ≠ [] := by
    intro hempty
    simp [hempty] at hterminal
  rw [programFinalCompressionOutput_eq_dropLast_append _ _ hfull, hdropLast]
  have hlastFull :
      (sequenceFunctionCompressionTrace model b S h K M).getLast hfull =
        ⟨SequenceFunctionCompressionRole.outer,
          (outerTrace.getLast houterTrace).input,
          (outerTrace.getLast houterTrace).output⟩ := by
    change
      ((((if K.1.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveKey
              (mdCompressionTrace model.codec h model.iv K.1.val)) ++
          (if S.val.length ≤ b.val then [] else
            tagMDCompressionTrace .deriveCustomization
              (mdCompressionTrace model.codec h model.iv S.val)) ++
          tagMDCompressionTrace .inner
            (mdCompressionTrace model.codec h model.iv innerInput)) ++
          tagMDCompressionTrace .outer outerTrace).getLast hfull) = _
    rw [List.getLast_append_of_right_ne_nil _ _ htagOuter]
    simp [tagMDCompressionTrace, List.getLast_map]
  rw [hlastFull]
  by_cases hshortK : K.1.val.length ≤ b.val <;>
    by_cases hshortS : S.val.length ≤ b.val
  all_goals
    simp only [sequenceFunctionCompressionTrace, hshortK, hshortS,
      if_pos, H, H', derivedK, derivedS, innerInput, inner,
      hderivedK, hderivedS, hinner]
    rw [hinnerTrace, houter]
    try rw [hkeyTrace hshortK]
    try rw [hcustomTrace hshortS]
    simp [tagMDCompressionTrace, hlastOutput, List.map_dropLast,
      List.append_assoc, show innerInput =
        sequenceFunctionInnerInput b fSeqMac K.1
          (derive K.1.val (mdHash model.codec h model.iv) b) M from rfl]

/-- **Terminal-shift trace stability.**  Once the global `Nodup` argument has
identified every non-terminal input as disjoint from the revealed terminal
coordinates, the shift reproduces all derive, inner, and non-terminal outer
entries and changes only the terminal outer output. -/
theorem sequenceFunctionCompressionTrace_terminalShift
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [DecidableEq Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    (h : CompressionFunction (HashOutput L) Block)
    (K : SequenceMACKey) (M : InputSequence)
    (hprefixFresh : ∀ entry ∈
      (sequenceFunctionCompressionTrace model b S h K M).dropLast,
      entry.input ∉ sequenceFunctionRevealedTerminalInputs z) :
    sequenceFunctionCompressionTrace model b S
        (sequenceFunctionTerminalShift z delta h) K M =
      programFinalCompressionOutput
        (sequenceFunctionICEval model b S
          (sequenceFunctionTerminalShift z delta h) K M)
        (sequenceFunctionCompressionTrace model b S h K M) := by
  apply sequenceFunctionCompressionTrace_eq_programFinal_of_eq_on_dropLast
    model b S backed
  intro entry hentry
  exact sequenceFunctionTerminalShift_eq_of_not_mem z delta h entry.input
    (hprefixFresh entry hentry)

/-- **Balanced terminal fibers.**  For any shift-stable predicate on
compression tables whose revealed terminal inputs are fresh, the terminal
table values are jointly uniform.  This is the SequenceFunction terminal
coordinate analogue of `cbc_fiber_card`; the counting argument itself is
exactly `Counting.card_filter_shift_univ`. -/
theorem sequenceFunction_fiber_card
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (P : CompressionFunction (HashOutput L) Block → Prop) [DecidablePred P]
    (hPfresh : ∀ h, P h →
      (sequenceFunctionRevealedTerminalInputs z).Nodup)
    (hPshift : ∀
      (delta : Fin (sequenceFunctionRevealedTerminalInputs z).length →
        Fin L.val → Byte)
      (h : CompressionFunction (HashOutput L) Block),
      P h → P (sequenceFunctionTerminalShift z delta h))
    (a : Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte) :
    (Finset.univ.filter fun h : CompressionFunction (HashOutput L) Block =>
        (∀ i,
          sequenceFunctionHashOutputCoordinates L
              (h ((sequenceFunctionRevealedTerminalInputs z).get i).1
                ((sequenceFunctionRevealedTerminalInputs z).get i).2) = a i) ∧
          P h).card *
        Fintype.card (HashOutput L) ^
          (sequenceFunctionRevealedTerminalInputs z).length =
      (Finset.univ.filter fun h : CompressionFunction (HashOutput L) Block =>
        P h).card := by
  classical
  have key := Counting.card_filter_shift_univ
    (A := Fin (sequenceFunctionRevealedTerminalInputs z).length →
      Fin L.val → Byte)
    P
    (fun h i => sequenceFunctionHashOutputCoordinates L
      (h ((sequenceFunctionRevealedTerminalInputs z).get i).1
        ((sequenceFunctionRevealedTerminalInputs z).get i).2))
    (fun delta h => sequenceFunctionTerminalShift z delta h)
    (fun delta h hP => hPshift delta h hP)
    (fun delta h hP => funext fun i =>
      sequenceFunctionTerminalShift_state z delta h (hPfresh h hP) i)
    (fun delta delta' h _ =>
      sequenceFunctionTerminalShift_compose z delta delta' h)
    (fun h _ => sequenceFunctionTerminalShift_zero z h) a
  have hcard :
      Fintype.card
          (Fin (sequenceFunctionRevealedTerminalInputs z).length →
            Fin L.val → Byte) =
        Fintype.card (HashOutput L) ^
          (sequenceFunctionRevealedTerminalInputs z).length := by
    rw [Fintype.card_fun, Fintype.card_fin,
      Fintype.card_congr (sequenceFunctionHashOutputCoordinates L).symm]
  rw [hcard] at key
  simpa only [funext_iff] using key

/-- The balanced-fiber factorization specialized to the freshness supplied
by `¬ Bad_SEQ`; only shift-stability of the terminal-free skeleton remains
for an application to provide. -/
theorem sequenceFunction_fiber_card_of_not_Bad_SEQ
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hgood : ¬ Bad_SEQ tz)
    (P : CompressionFunction (HashOutput L) Block → Prop) [DecidablePred P]
    (hPshift : ∀
      (delta : Fin
          (sequenceFunctionRevealedTerminalInputs tz.2).length →
        Fin L.val → Byte)
      (h : CompressionFunction (HashOutput L) Block),
      P h → P (sequenceFunctionTerminalShift tz.2 delta h))
    (a : Fin (sequenceFunctionRevealedTerminalInputs tz.2).length →
      Fin L.val → Byte) :
    (Finset.univ.filter fun h : CompressionFunction (HashOutput L) Block =>
        (∀ i,
          sequenceFunctionHashOutputCoordinates L
              (h ((sequenceFunctionRevealedTerminalInputs tz.2).get i).1
                ((sequenceFunctionRevealedTerminalInputs tz.2).get i).2) = a i) ∧
          P h).card *
        Fintype.card (HashOutput L) ^
          (sequenceFunctionRevealedTerminalInputs tz.2).length =
      (Finset.univ.filter fun h : CompressionFunction (HashOutput L) Block =>
        P h).card := by
  exact sequenceFunction_fiber_card tz.2 P
    (fun _ _ =>
      sequenceFunctionRevealedTerminalInputs_nodup_of_not_Bad_SEQ tz hgood)
    hPshift a

/-! ## Terminal-free representative skeleton -/

/-- Construction inputs grouped by revealed evaluation slot.  This is only a
grouped view of `sequenceFunctionRevealedConstructionInputs`; it exposes the
row structure needed to separate a row's honest prefix from every revealed
terminal coordinate. -/
def sequenceFunctionRevealedConstructionInputRows
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) : List (List (HashOutput L × Block)) :=
  List.ofFn fun evalSlot : Fin q =>
    ((List.ofFn fun callSlot : Fin lambda =>
      z.evalTraces evalSlot callSlot).filterMap id).map TraceEntry.input

theorem sequenceFunctionRevealedConstructionInputs_eq_flatten_rows
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    sequenceFunctionRevealedConstructionInputs z =
      (sequenceFunctionRevealedConstructionInputRows z).flatten := by
  unfold sequenceFunctionRevealedConstructionInputs
    sequenceFunctionRevealedConstructionCalls
    sequenceFunctionRevealedConstructionInputRows
  simp only [List.map_flatten, List.map_map, List.ofFn_comp']

theorem sequenceFunctionRevealedTerminalInputs_eq_filterMap_getLast_rows
    {Block : Type uBlock} {L : U128} {users q lambda : ℕ}
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda) :
    sequenceFunctionRevealedTerminalInputs z =
      ((sequenceFunctionRevealedConstructionInputRows z).map
        List.getLast?).filterMap id := by
  unfold sequenceFunctionRevealedTerminalInputs
    sequenceFunctionRevealedConstructionInputRows
  simp only [List.ofFn_comp', List.filterMap_map, Function.comp_def]
  congr 2
  ext evalSlot
  simp

/-- In a globally `Nodup` flattened family of rows, an honest-prefix entry of
one row cannot be the terminal entry of that or any other row. -/
theorem mem_dropLast_not_mem_filterMap_getLast_of_nodup_flatten
    {A : Type*} (rows : List (List A)) (row : List A)
    (hrows : rows.flatten.Nodup) (hrow : row ∈ rows) (a : A)
    (ha : a ∈ row.dropLast) :
    a ∉ (rows.map List.getLast?).filterMap id := by
  intro hterminal
  simp only [List.mem_filterMap, List.mem_map] at hterminal
  obtain ⟨_, ⟨row', hrow', rfl⟩, hlast⟩ := hterminal
  simp only [id_eq] at hlast
  have hparts := List.nodup_flatten.mp hrows
  by_cases heq : row = row'
  · subst row'
    have hne : row ≠ [] := by
      exact fun hnil => by simp [hnil] at ha
    have hlastGet : row.getLast hne = a := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hne] using hlast
    exact (hparts.1 row hrow).rel_dropLast_getLast ha hlastGet.symm
  · have hdisjoint : List.Disjoint row row' :=
      hparts.2.forall (fun _ _ h => List.disjoint_comm.mp h) hrow hrow' heq
    exact (List.disjoint_left.mp hdisjoint)
      (List.mem_of_mem_dropLast ha)
      (List.mem_of_mem_getLast? (by simp [hlast]))

/-- Padding followed by omission of the padding recovers the original trace. -/
theorem filterMap_ofFn_padCompressionTrace_eq
    {Role State Block : Type*} {lambda : ℕ}
    (trace : List (TraceEntry Role State Block)) (hle : trace.length ≤ lambda) :
    (List.ofFn fun i : Fin lambda =>
      padCompressionTrace lambda trace i).filterMap id = trace := by
  induction lambda generalizing trace with
  | zero =>
      have hnil : trace = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
      subst trace
      simp
  | succ lambda ih =>
      cases trace with
      | nil => simp [padCompressionTrace]
      | cons entry trace =>
          have htail : trace.length ≤ lambda := by simp at hle; omega
          rw [List.ofFn_succ]
          simp only [padCompressionTrace, List.length_cons,
            List.get_eq_getElem]
          simpa [padCompressionTrace, Function.comp_def] using ih trace htail

/-- A budget-respecting visible evaluation slot has enough room for its
complete canonical compression trace. -/
theorem sequenceFunctionCompressionTrace_length_le_of_evalRequestAt
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users t)
    (evalSlot : Fin q) (request : Fin users × InputSequence)
    (hrequest : sequenceFunctionEvalRequestAt? t evalSlot = some request)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey) :
    (sequenceFunctionCompressionTrace model b S h
      (keys request.1) request.2).length ≤ lambda := by
  have hrequestMem : request ∈ sequenceFunctionVisibleEvalRequests t := by
    rw [sequenceFunctionEvalRequestAt?, List.getElem?_eq_some_iff] at hrequest
    simpa [hrequest.2] using List.getElem_mem hrequest.1
  unfold sequenceFunctionVisibleEvalRequests at hrequestMem
  simp only [List.mem_filterMap] at hrequestMem
  obtain ⟨query, hquery, hqueryEval⟩ := hrequestMem
  cases query with
  | prim input => simp at hqueryEval
  | eval request' =>
      simp only [Option.some.injEq] at hqueryEval
      subst request'
      obtain ⟨i, hi⟩ := List.get_of_mem hquery
      have hi' : t.1.get (Fin.cast (by simp) i) =
          TaggedQuery.eval request := by
        simpa using hi
      exact (sequenceFunctionCompressionTrace_length_le_evalCost
        model b S h (keys request.1) request.2 request.1).trans
          (hbudget.2.2 _ request hi')

/-- With fixed ideal coins realizing the reveal, the revealed terminal-entry
list is exactly the slot-ordered list of canonical final entries programmed
with the corresponding ideal-function replies. -/
theorem sequenceFunctionRevealedTerminalEntries_eq_of_ideal_reveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (requestOf : Fin q → Fin users × InputSequence)
    (hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot))
    (hreveal : sequenceFunctionICIdealReveal (lambda := lambda) model b S
      (h, keys, idealEval) tz.1 = tz.2) :
    sequenceFunctionRevealedTerminalEntries tz.2 =
      List.ofFn fun slot : Fin q =>
        { (sequenceFunctionCompressionTrace model b S h
            (keys (requestOf slot).1) (requestOf slot).2).getLast
              (sequenceFunctionCompressionTrace_ne_nil backed h
                (keys (requestOf slot).1) (requestOf slot).2) with
          output := idealEval (requestOf slot).1 (requestOf slot).2 } := by
  rw [← hreveal]
  unfold sequenceFunctionRevealedTerminalEntries
  apply filterMap_id_ofFn_eq_of_some
  intro slot
  simp only [sequenceFunctionICIdealReveal, hrequest]
  let trace := sequenceFunctionCompressionTrace model b S h
    (keys (requestOf slot).1) (requestOf slot).2
  have hlength : trace.length ≤ lambda :=
    sequenceFunctionCompressionTrace_length_le_of_evalRequestAt
      model b S tz.1 hbudget slot (requestOf slot) (hrequest slot) h keys
  have hprogramLength :
      (programFinalCompressionOutput
        (idealEval (requestOf slot).1 (requestOf slot).2) trace).length ≤
          lambda := by simpa using hlength
  rw [filterMap_ofFn_padCompressionTrace_eq _ hprogramLength]
  exact programFinalCompressionOutput_getLast?
    (idealEval (requestOf slot).1 (requestOf slot).2) trace
    (sequenceFunctionCompressionTrace_ne_nil backed h
      (keys (requestOf slot).1) (requestOf slot).2)

/-- A budget-saturated ideal reveal has exactly one populated terminal entry
for each of its `q` evaluation slots. -/
theorem sequenceFunctionRevealedTerminalEntries_length_eq_of_ideal_reveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (requestOf : Fin q → Fin users × InputSequence)
    (hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot))
    (hreveal : sequenceFunctionICIdealReveal (lambda := lambda) model b S
      (h, keys, idealEval) tz.1 = tz.2) :
    (sequenceFunctionRevealedTerminalEntries tz.2).length = q := by
  rw [sequenceFunctionRevealedTerminalEntries_eq_of_ideal_reveal
    model b S backed tz hbudget h keys idealEval requestOf hrequest hreveal,
    List.length_ofFn]

/-- The revealed terminal input in a populated evaluation slot is the final
input of that slot's canonical honest compression trace. -/
theorem sequenceFunctionRevealedTerminalInput_of_ideal_reveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (requestOf : Fin q → Fin users × InputSequence)
    (hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot))
    (hreveal : sequenceFunctionICIdealReveal (lambda := lambda) model b S
      (h, keys, idealEval) tz.1 = tz.2)
    (hlen : (sequenceFunctionRevealedTerminalEntries tz.2).length = q)
    (slot : Fin q) :
    (sequenceFunctionRevealedTerminalInputs tz.2).get
        (Fin.cast (sequenceFunctionRevealedTerminalInputs_length tz.2).symm
          (Fin.cast hlen.symm slot)) =
      ((sequenceFunctionCompressionTrace model b S h
        (keys (requestOf slot).1) (requestOf slot).2).getLast
          (sequenceFunctionCompressionTrace_ne_nil backed h
            (keys (requestOf slot).1) (requestOf slot).2)).input := by
  let trace := sequenceFunctionCompressionTrace model b S h
    (keys (requestOf slot).1) (requestOf slot).2
  have hentries := sequenceFunctionRevealedTerminalEntries_eq_of_ideal_reveal
    model b S backed tz hbudget h keys idealEval requestOf hrequest hreveal
  have hentryOpt :
      (sequenceFunctionRevealedTerminalEntries tz.2)[slot.val]? =
        some { (sequenceFunctionCompressionTrace model b S h
            (keys (requestOf slot).1) (requestOf slot).2).getLast
              (sequenceFunctionCompressionTrace_ne_nil backed h
                (keys (requestOf slot).1) (requestOf slot).2) with
          output := idealEval (requestOf slot).1 (requestOf slot).2 } := by
    simpa using congrArg (fun entries => entries[slot.val]?) hentries
  have hinputOpt := congrArg (fun inputs => inputs[slot.val]?)
    (sequenceFunctionRevealedTerminalInputs_eq_map_entries tz.2)
  dsimp only at hinputOpt
  rw [List.getElem?_eq_getElem (by
    rw [sequenceFunctionRevealedTerminalInputs_length, hlen]
    exact slot.isLt)] at hinputOpt
  simp only [List.getElem?_map, hentryOpt, Option.map_some] at hinputOpt
  simpa [trace] using Option.some.inj hinputOpt

/-- At each populated evaluation slot, the fixed reveal coordinate is the
programmed ideal reply, while the sampled table coordinate at the same
terminal input is the honest real SequenceFunction reply. -/
theorem sequenceFunctionTerminalCoordinates_of_ideal_reveal
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (requestOf : Fin q → Fin users × InputSequence)
    (hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot))
    (hreveal : sequenceFunctionICIdealReveal (lambda := lambda) model b S
      (h, keys, idealEval) tz.1 = tz.2)
    (hlen : (sequenceFunctionRevealedTerminalEntries tz.2).length = q)
    (slot : Fin q) :
    let i := Fin.cast hlen.symm slot
    sequenceFunctionRealTerminalCoordinate tz.2 h i =
        sequenceFunctionICEval model b S h
          (keys (requestOf slot).1) (requestOf slot).2 ∧
      sequenceFunctionRevealedTerminalCoordinate tz.2 i =
        idealEval (requestOf slot).1 (requestOf slot).2 := by
  let trace := sequenceFunctionCompressionTrace model b S h
    (keys (requestOf slot).1) (requestOf slot).2
  have htrace : trace ≠ [] := sequenceFunctionCompressionTrace_ne_nil
    backed h (keys (requestOf slot).1) (requestOf slot).2
  have hentries := sequenceFunctionRevealedTerminalEntries_eq_of_ideal_reveal
    model b S backed tz hbudget h keys idealEval requestOf hrequest hreveal
  have hentryOpt :
      (sequenceFunctionRevealedTerminalEntries tz.2)[slot.val]? =
        some { trace.getLast htrace with
          output := idealEval (requestOf slot).1 (requestOf slot).2 } := by
    simpa [trace] using congrArg (fun entries => entries[slot.val]?) hentries
  have hentry :
      (sequenceFunctionRevealedTerminalEntries tz.2).get
          (Fin.cast hlen.symm slot) =
        { trace.getLast htrace with
          output := idealEval (requestOf slot).1 (requestOf slot).2 } := by
    rw [List.getElem?_eq_getElem (by omega)] at hentryOpt
    exact Option.some.inj hentryOpt
  have hhonest : h (trace.getLast htrace).input.1
      (trace.getLast htrace).input.2 =
        sequenceFunctionICEval model b S h
          (keys (requestOf slot).1) (requestOf slot).2 := by
    have heval := sequenceFunctionCompressionTrace_output_eq model b S h
      (keys (requestOf slot).1) (requestOf slot).2 (trace.getLast htrace)
      (List.getLast_mem htrace)
    obtain ⟨input, hlast⟩ :=
      sequenceFunctionCompressionTrace_final_output backed h
        (keys (requestOf slot).1) (requestOf slot).2
    have hlast' : trace.getLast htrace =
        ⟨SequenceFunctionCompressionRole.outer, input,
          sequenceFunctionICEval model b S h
            (keys (requestOf slot).1) (requestOf slot).2⟩ := by
      apply Option.some.inj
      simpa [trace, List.getLast?_eq_getLast_of_ne_nil htrace] using hlast
    rw [← heval, hlast']
  constructor
  · unfold sequenceFunctionRealTerminalCoordinate
    have hinputOpt := congrArg (fun inputs => inputs[slot.val]?)
      (sequenceFunctionRevealedTerminalInputs_eq_map_entries tz.2)
    have hinput :
        (sequenceFunctionRevealedTerminalInputs tz.2).get
            (Fin.cast (sequenceFunctionRevealedTerminalInputs_length tz.2).symm
              (Fin.cast hlen.symm slot)) =
          (trace.getLast htrace).input := by
      dsimp only at hinputOpt
      rw [List.getElem?_eq_getElem (by
        rw [sequenceFunctionRevealedTerminalInputs_length, hlen]
        exact slot.isLt)] at hinputOpt
      simp only [List.getElem?_map, hentryOpt, Option.map_some] at hinputOpt
      exact Option.some.inj hinputOpt
    rw [hinput]
    exact hhonest
  · unfold sequenceFunctionRevealedTerminalCoordinate
    rw [hentry]

/-- Distinct saturated evaluation slots name distinct ideal-function
coordinates on `¬ Bad_SEQ`.  Repeating the same request would repeat its
canonical terminal compression input, contradicting construction freshness. -/
theorem sequenceFunctionEvalRequests_injective_of_not_Bad_SEQ
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hgood : ¬ Bad_SEQ tz)
    (h : CompressionFunction (HashOutput L) Block)
    (keys : Fin users → SequenceMACKey)
    (idealEval : Fin users → InputSequence → HashOutput L)
    (requestOf : Fin q → Fin users × InputSequence)
    (hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot))
    (hreveal : sequenceFunctionICIdealReveal (lambda := lambda) model b S
      (h, keys, idealEval) tz.1 = tz.2)
    (hlen : (sequenceFunctionRevealedTerminalEntries tz.2).length = q) :
    Function.Injective requestOf := by
  intro i j hij
  have hi := sequenceFunctionRevealedTerminalInput_of_ideal_reveal
    model b S backed tz hbudget h keys idealEval requestOf hrequest hreveal hlen i
  have hj := sequenceFunctionRevealedTerminalInput_of_ideal_reveal
    model b S backed tz hbudget h keys idealEval requestOf hrequest hreveal hlen j
  have huser : (requestOf i).1 = (requestOf j).1 :=
    congrArg (fun request => request.1) hij
  have hmessage : (requestOf i).2 = (requestOf j).2 :=
    congrArg (fun request => request.2) hij
  have hlast :
      (sequenceFunctionCompressionTrace model b S h
        (keys (requestOf i).1) (requestOf i).2).getLast
          (sequenceFunctionCompressionTrace_ne_nil backed h
            (keys (requestOf i).1) (requestOf i).2) =
      (sequenceFunctionCompressionTrace model b S h
        (keys (requestOf j).1) (requestOf j).2).getLast
          (sequenceFunctionCompressionTrace_ne_nil backed h
            (keys (requestOf j).1) (requestOf j).2) := by
    rw [huser, hmessage]
  have hindex :=
    (sequenceFunctionRevealedTerminalInputs_nodup_of_not_Bad_SEQ tz hgood).injective_get
      (hi.trans ((congrArg TraceEntry.input hlast).trans hj.symm))
  apply Fin.ext
  simpa using congrArg Fin.val hindex

/-- The terminal-free skeleton is the projection of the ideal representative
event to the sampled compression table and dummy keys.  The independent ideal
evaluation function is existentially forgotten; consequently the predicate
contains primitive replies, dummy keys, and every honest trace prefix, but no
terminal random-function coordinate. -/
def SequenceFunctionTerminalFreeSkeleton
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (t : TranscriptPrefix (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q))
    (z : SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
      users q lambda)
    (keys : Fin users → SequenceMACKey)
    (h : CompressionFunction (HashOutput L) Block) : Prop :=
  ∃ idealEval : Fin users → InputSequence → HashOutput L,
    PFunPDE.transcriptSystemEvent sequenceFunctionICIdealF t.1 t.2
        (h, keys, idealEval) ∧
      sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (h, keys, idealEval) t = z

/-- Directly from the global construction-input `Nodup`: every honest prefix
input of a skeleton witness is disjoint from every revealed terminal input.
No byte-level domain-separation theorem is used here. -/
theorem sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint_of_nodup
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hconstruction :
      (sequenceFunctionRevealedConstructionInputs tz.2).Nodup)
    (keys : Fin users → SequenceMACKey)
    (h : CompressionFunction (HashOutput L) Block)
    (hskeleton : SequenceFunctionTerminalFreeSkeleton
      model b S tz.1 tz.2 keys h)
    (evalSlot : Fin q) (request : Fin users × InputSequence)
    (hrequest : sequenceFunctionEvalRequestAt? tz.1 evalSlot = some request)
    (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block)
    (hentry : entry ∈
      (sequenceFunctionCompressionTrace model b S h
        (keys request.1) request.2).dropLast) :
    entry.input ∉ sequenceFunctionRevealedTerminalInputs tz.2 := by
  obtain ⟨idealEval, _, hreveal⟩ := hskeleton
  let trace := sequenceFunctionCompressionTrace model b S h
    (keys request.1) request.2
  have htraceLength : trace.length ≤ lambda :=
    sequenceFunctionCompressionTrace_length_le_of_evalRequestAt
      model b S tz.1 hbudget evalSlot request hrequest h keys
  let row := ((List.ofFn fun callSlot : Fin lambda =>
    tz.2.evalTraces evalSlot callSlot).filterMap id).map TraceEntry.input
  have hrow : row = trace.map TraceEntry.input := by
    unfold row
    rw [← hreveal]
    simp only [sequenceFunctionICIdealReveal, hrequest]
    rw [filterMap_ofFn_padCompressionTrace_eq _ (by simpa using htraceLength),
      programFinalCompressionOutput_inputs]
  have hrowMem : row ∈ sequenceFunctionRevealedConstructionInputRows tz.2 := by
    unfold sequenceFunctionRevealedConstructionInputRows row
    exact List.mem_ofFn.mpr ⟨evalSlot, rfl⟩
  have hentryRow : entry.input ∈ row.dropLast := by
    rw [hrow]
    rw [← List.map_dropLast]
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  rw [sequenceFunctionRevealedTerminalInputs_eq_filterMap_getLast_rows]
  apply mem_dropLast_not_mem_filterMap_getLast_of_nodup_flatten
    (sequenceFunctionRevealedConstructionInputRows tz.2) row
  · rw [← sequenceFunctionRevealedConstructionInputs_eq_flatten_rows]
    exact hconstruction
  · exact hrowMem
  · exact hentryRow

/-- Compatibility wrapper for the original all-fresh event. -/
theorem sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hgood : ¬ Bad_SEQ tz)
    (keys : Fin users → SequenceMACKey)
    (h : CompressionFunction (HashOutput L) Block)
    (hskeleton : SequenceFunctionTerminalFreeSkeleton
      model b S tz.1 tz.2 keys h)
    (evalSlot : Fin q) (request : Fin users × InputSequence)
    (hrequest : sequenceFunctionEvalRequestAt? tz.1 evalSlot = some request)
    (entry : TraceEntry SequenceFunctionCompressionRole (HashOutput L) Block)
    (hentry : entry ∈
      (sequenceFunctionCompressionTrace model b S h
        (keys request.1) request.2).dropLast) :
    entry.input ∉ sequenceFunctionRevealedTerminalInputs tz.2 := by
  exact
    sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint_of_nodup
      model b S tz hbudget
      ((not_Bad_SEQ_iff_compressionFresh tz).1 hgood).2 keys h hskeleton
      evalSlot request hrequest entry hentry

/-- The terminal shift fixes the complete terminal-free representative
skeleton.  Global construction freshness keeps every shifted terminal site
away from visible primitive queries and from every honest non-terminal
construction call; terminal programming then erases the shift's only
remaining observable effect. -/
theorem sequenceFunctionTerminalFreeSkeleton_terminalShift_of_nodup_of_visible_zero
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hconstruction :
      (sequenceFunctionRevealedConstructionInputs tz.2).Nodup)
    (keys : Fin users → SequenceMACKey)
    (h : CompressionFunction (HashOutput L) Block)
    (hskeleton : SequenceFunctionTerminalFreeSkeleton
      model b S tz.1 tz.2 keys h)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs tz.2).length →
      Fin L.val → Byte)
    (hvisibleZero : ∀ input ∈ sequenceFunctionVisiblePrimInputs tz.1,
      ∀ i, (sequenceFunctionRevealedTerminalInputs tz.2).get i = input →
        delta i = 0) :
    SequenceFunctionTerminalFreeSkeleton model b S tz.1 tz.2 keys
      (sequenceFunctionTerminalShift tz.2 delta h) := by
  classical
  obtain ⟨idealEval, htranscript, hreveal⟩ := hskeleton
  refine ⟨idealEval, ?_, ?_⟩
  · unfold sequenceFunctionICIdealF
      RandomSystems.HTechnique.IdealCompression.idealF at htranscript ⊢
    rw [transcriptSystemEvent_functionEvaluatorRV_iff] at htranscript ⊢
    intro i
    specialize htranscript i
    cases hquery : tz.1.1.get i with
    | prim input =>
        have hprim : input ∈ sequenceFunctionVisiblePrimInputs tz.1 := by
          unfold sequenceFunctionVisiblePrimInputs
          apply List.mem_filterMap.mpr
          exact ⟨tz.1.1.get i, List.get_mem _ _, by simp [hquery]⟩
        simpa [sequenceFunctionICIdealF,
          RandomSystems.HTechnique.IdealCompression.idealF,
          idealFunction, hquery,
          sequenceFunctionTerminalShift_eq_of_zero_on_hits tz.2 delta h input
            (hvisibleZero input hprim)] using htranscript
    | eval request =>
        simpa [sequenceFunctionICIdealF,
          RandomSystems.HTechnique.IdealCompression.idealF,
          idealFunction, hquery] using
          htranscript
  · have hkeys := congrArg Reveal.keys hreveal
    have htraces :
        (sequenceFunctionICIdealReveal (lambda := lambda) model b S
          (sequenceFunctionTerminalShift tz.2 delta h, keys, idealEval)
          tz.1).evalTraces = tz.2.evalTraces := by
      funext evalSlot callSlot
      cases hrequest : sequenceFunctionEvalRequestAt? tz.1 evalSlot with
      | none =>
          simpa [sequenceFunctionICIdealReveal, hrequest] using
            congrArg (fun z => z.evalTraces evalSlot callSlot) hreveal
      | some request =>
          have hprefixFresh : ∀ entry ∈
              (sequenceFunctionCompressionTrace model b S h
                (keys request.1) request.2).dropLast,
              entry.input ∉ sequenceFunctionRevealedTerminalInputs tz.2 :=
            fun entry hentry =>
              sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint_of_nodup
                model b S tz hbudget hconstruction keys h
                ⟨idealEval, htranscript, hreveal⟩ evalSlot request hrequest
                entry hentry
          have htrace := sequenceFunctionCompressionTrace_terminalShift
            model b S backed tz.2 delta h (keys request.1) request.2
            hprefixFresh
          simpa [sequenceFunctionICIdealReveal, hrequest, htrace,
            programFinalCompressionOutput_programFinalCompressionOutput]
            using congrArg (fun z => z.evalTraces evalSlot callSlot) hreveal
    generalize hleft :
      sequenceFunctionICIdealReveal (lambda := lambda) model b S
        (sequenceFunctionTerminalShift tz.2 delta h, keys, idealEval) tz.1 =
          left at htraces ⊢
    cases left with
    | mk leftKeys leftTraces =>
        cases hright : tz.2 with
        | mk rightKeys rightTraces =>
            rw [Reveal.mk.injEq]
            constructor
            · have hleftKeys : keys = leftKeys := by
                simpa [sequenceFunctionICIdealReveal] using
                  congrArg Reveal.keys hleft
              have hrightKeys : keys = rightKeys := by
                simpa [hright] using hkeys
              exact hleftKeys.symm.trans hrightKeys
            · simpa [hleft, hright] using htraces

/-- Compatibility wrapper for the original event, where every terminal point
is disjoint from the visible primitive transcript and hence the visible-zero
premise is vacuous. -/
theorem sequenceFunctionTerminalFreeSkeleton_terminalShift
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hgood : ¬ Bad_SEQ tz)
    (keys : Fin users → SequenceMACKey)
    (h : CompressionFunction (HashOutput L) Block)
    (hskeleton : SequenceFunctionTerminalFreeSkeleton
      model b S tz.1 tz.2 keys h)
    (delta : Fin (sequenceFunctionRevealedTerminalInputs tz.2).length →
      Fin L.val → Byte) :
    SequenceFunctionTerminalFreeSkeleton model b S tz.1 tz.2 keys
      (sequenceFunctionTerminalShift tz.2 delta h) := by
  apply
    sequenceFunctionTerminalFreeSkeleton_terminalShift_of_nodup_of_visible_zero
      model b S backed tz hbudget
      ((not_Bad_SEQ_iff_compressionFresh tz).1 hgood).2 keys h hskeleton delta
  intro input hvisible i hit
  exfalso
  exact ((not_Bad_SEQ_iff_compressionFresh tz).1 hgood).1 input
    ((sequenceFunctionRevealedTerminalInputs_sublist_constructionInputs
      tz.2).mem (List.get_mem _ i))
    (by simpa [hit] using hvisible)

set_option maxHeartbeats 2000000 in
/-- On a budget-respecting `Bad_SEQ`-free representative transcript, the
real terminal compression coordinate and the independent ideal-function
coordinate have exactly the same extended fixed-query mass. -/
theorem sequenceFunctionIC_extFixedQueryTranscriptDistRep_eq_on_good
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (xs : Fin (p + q) → SequenceFunctionICQuery Block L users)
    (tz : TranscriptPrefix (SequenceFunctionICQuery Block L users)
        (SequenceFunctionICReply L) (p + q) ×
      SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
        users q lambda)
    (hbudget : SequenceFunctionTaggedBudgetRespects
      model b S p q lambda users tz.1)
    (hgood : ¬ Bad_SEQ tz) :
    extFixedQueryTranscriptDistRep
        (sequenceFunctionICRealP (Block := Block) (L := L) users keysP)
        (sequenceFunctionICRealF model b S)
        (sequenceFunctionICRealReveal (lambda := lambda) model b S) xs tz =
      extFixedQueryTranscriptDistRep
        (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
        sequenceFunctionICIdealF
        (sequenceFunctionICIdealReveal (lambda := lambda) model b S) xs tz := by
  classical
  unfold extFixedQueryTranscriptDistRep
  rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply]
  congr 1
  unfold extSysFactorRep
  letI : Fintype SequenceMACKey := Fintype.ofFinite SequenceMACKey
  letI : Nonempty SequenceMACKey :=
    ⟨⟨⟨List.replicate 32 0, by norm_num [u128Modulus]⟩, by simp⟩⟩
  let requestOf : Fin q → Fin users × InputSequence := fun slot =>
    Classical.choose (sequenceFunctionEvalRequestAt?_exists_of_budget
      tz.1 hbudget slot)
  have hrequest : ∀ slot, sequenceFunctionEvalRequestAt? tz.1 slot =
      some (requestOf slot) := fun slot =>
    Classical.choose_spec (sequenceFunctionEvalRequestAt?_exists_of_budget
      tz.1 hbudget slot)
  have hslot : ∀ request ∈ sequenceFunctionVisibleEvalRequests tz.1,
      ∃ slot, requestOf slot = request := by
    intro request hmem
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    have hiq : i.val < q := by
      have hlenVisible := sequenceFunctionVisibleEvalRequests_length_eq_evalCount
        tz.1
      rw [(sequenceFunctionTaggedBudgetRespects_counts tz.1 hbudget).2]
        at hlenVisible
      simpa [hlenVisible] using i.isLt
    let slot : Fin q := ⟨i.val, hiq⟩
    have hat : sequenceFunctionEvalRequestAt? tz.1 slot = some request := by
      unfold sequenceFunctionEvalRequestAt?
      rw [List.getElem?_eq_getElem (by simpa [slot] using i.isLt)]
      simpa [slot] using hi
    exact ⟨slot, Option.some.inj ((hrequest slot).symm.trans hat)⟩
  let P : (Fin users → SequenceMACKey) →
      CompressionFunction (HashOutput L) Block → Prop := fun keys h =>
    SequenceFunctionTerminalFreeSkeleton model b S tz.1 tz.2 keys h
  by_cases hex : ∃ keys h, P keys h
  · obtain ⟨keys0, h0, idealEval0, hevent0, hreveal0⟩ := hex
    have hlen : (sequenceFunctionRevealedTerminalEntries tz.2).length = q :=
      sequenceFunctionRevealedTerminalEntries_length_eq_of_ideal_reveal
        model b S backed tz hbudget h0 keys0 idealEval0 requestOf hrequest
        hreveal0
    let coordF := sequenceFunctionRealTerminalCoordinate tz.2
    let coordG := sequenceFunctionIdealTerminalCoordinate tz requestOf hlen
    let a := sequenceFunctionRevealedTerminalCoordinate tz.2
    let R : CompressionFunction (HashOutput L) Block →
        (Fin users → SequenceMACKey) → Prop := fun h keys =>
      PFunPDE.transcriptSystemEvent (sequenceFunctionICRealF model b S)
          tz.1.1 tz.1.2 (h, keys) ∧
        sequenceFunctionICRealReveal (lambda := lambda) model b S
          (h, keys) tz.1 = tz.2
    let I : CompressionFunction (HashOutput L) Block →
        (Fin users → SequenceMACKey) →
        (Fin users → InputSequence → HashOutput L) → Prop :=
      fun h keys idealEval =>
        PFunPDE.transcriptSystemEvent sequenceFunctionICIdealF
            tz.1.1 tz.1.2 (h, keys, idealEval) ∧
          sequenceFunctionICIdealReveal (lambda := lambda) model b S
            (h, keys, idealEval) tz.1 = tz.2
    have hR : ∀ h keys, R h keys ↔ coordF h = a ∧ P keys h := by
      intro h keys
      constructor
      · rintro ⟨hevent, hreveal⟩
        let realIdeal : Fin users → InputSequence → HashOutput L :=
          fun user message =>
            sequenceFunctionICEval model b S h (keys user) message
        have hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests tz.1,
            realIdeal request.1 request.2 =
              sequenceFunctionICEval model b S h
                (keys request.1) request.2 := by intros; rfl
        have hidealEvent :=
          (sequenceFunctionIC_transcriptSystemEvent_real_ideal_iff
            model b S tz.1 h keys realIdeal hagree).mp hevent
        have hidealReveal : sequenceFunctionICIdealReveal (lambda := lambda)
            model b S (h, keys, realIdeal) tz.1 = tz.2 := by
          rw [sequenceFunctionICReveal_real_ideal_eq
            model b S backed tz.1 h keys realIdeal hagree, hreveal]
        refine ⟨?_, ⟨realIdeal, hidealEvent, hidealReveal⟩⟩
        funext i
        let slot : Fin q := Fin.cast hlen i
        have hc := sequenceFunctionTerminalCoordinates_of_ideal_reveal
          model b S backed tz hbudget h keys realIdeal requestOf hrequest
          hidealReveal hlen slot
        exact hc.1.trans hc.2.symm
      · rintro ⟨hcoord, idealEval, hidealEvent, hidealReveal⟩
        have hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests tz.1,
            idealEval request.1 request.2 =
              sequenceFunctionICEval model b S h
                (keys request.1) request.2 := by
          intro request hmem
          obtain ⟨slot, hslotEq⟩ := hslot request hmem
          have hc := sequenceFunctionTerminalCoordinates_of_ideal_reveal
            model b S backed tz hbudget h keys idealEval requestOf hrequest
            hidealReveal hlen slot
          have hca := congrFun hcoord (Fin.cast hlen.symm slot)
          simpa [hslotEq] using hc.2.symm.trans (hca.symm.trans hc.1)
        exact ⟨
          (sequenceFunctionIC_transcriptSystemEvent_real_ideal_iff
            model b S tz.1 h keys idealEval hagree).mpr hidealEvent,
          (sequenceFunctionICReveal_real_ideal_eq
            model b S backed tz.1 h keys idealEval hagree).symm.trans
              hidealReveal⟩
    have hI : ∀ h keys idealEval, I h keys idealEval ↔
        coordG idealEval = a ∧ P keys h := by
      intro h keys idealEval
      constructor
      · rintro ⟨hevent, hreveal⟩
        refine ⟨?_, ⟨idealEval, hevent, hreveal⟩⟩
        funext i
        let slot : Fin q := Fin.cast hlen i
        have hc := sequenceFunctionTerminalCoordinates_of_ideal_reveal
          model b S backed tz hbudget h keys idealEval requestOf hrequest
          hreveal hlen slot
        simpa [coordG, a, sequenceFunctionIdealTerminalCoordinate, slot]
          using hc.2.symm
      · rintro ⟨hcoord, idealEval0, hevent0, hreveal0⟩
        have hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests tz.1,
            idealEval0 request.1 request.2 =
              idealEval request.1 request.2 := by
          intro request hmem
          obtain ⟨slot, hslotEq⟩ := hslot request hmem
          have hc := sequenceFunctionTerminalCoordinates_of_ideal_reveal
            model b S backed tz hbudget h keys idealEval0 requestOf hrequest
            hreveal0 hlen slot
          have hca := congrFun hcoord (Fin.cast hlen.symm slot)
          rw [← hslotEq]
          exact hc.2.symm.trans hca.symm
        exact ⟨
          (sequenceFunctionICIdeal_transcriptSystemEvent_congr tz.1 h keys
            idealEval0 idealEval hagree).mp hevent0,
          (sequenceFunctionICIdealReveal_congr model b S tz.1 h keys
            idealEval0 idealEval hagree).symm.trans hreveal0⟩
    have hF : ∀ keys,
        (Finset.univ.filter fun h => coordF h = a ∧ P keys h).card *
            Fintype.card (Fin (sequenceFunctionRevealedTerminalEntries tz.2).length →
              HashOutput L) =
          (Finset.univ.filter fun h => P keys h).card := by
      intro keys
      have hcardfilter :
          (Finset.univ.filter fun h : CompressionFunction (HashOutput L) Block =>
            coordF h = a ∧ P keys h).card =
          (Finset.univ.filter fun h =>
            (∀ i : Fin (sequenceFunctionRevealedTerminalInputs tz.2).length,
              let input := (sequenceFunctionRevealedTerminalInputs tz.2).get i
              h input.1 input.2 =
                ((sequenceFunctionRevealedTerminalEntries tz.2).get
                  (Fin.cast
                    (sequenceFunctionRevealedTerminalInputs_length tz.2)
                    i)).output) ∧ P keys h).card := by
        congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_congr
          (sequenceFunctionRealTerminalCoordinate_eq_iff tz.2 h) Iff.rfl
      rw [hcardfilter]
      have hfiber := sequenceFunction_fiber_card_of_not_Bad_SEQ tz hgood
        (P keys)
        (fun delta h hskeleton =>
          sequenceFunctionTerminalFreeSkeleton_terminalShift model b S backed
            tz hbudget hgood keys h hskeleton delta)
        (fun i => sequenceFunctionHashOutputCoordinates L
          ((sequenceFunctionRevealedTerminalEntries tz.2).get
            (Fin.cast (sequenceFunctionRevealedTerminalInputs_length tz.2) i)).output)
      simpa [Fintype.card_fun, Fintype.card_fin,
        Fintype.card_congr (sequenceFunctionHashOutputCoordinates L).symm]
        using hfiber
    have hG :
        (Finset.univ.filter fun g => coordG g = a).card *
            Fintype.card (Fin (sequenceFunctionRevealedTerminalEntries tz.2).length →
              HashOutput L) =
          Fintype.card (Fin users → InputSequence → HashOutput L) := by
      have hrequestInjective : Function.Injective requestOf :=
        sequenceFunctionEvalRequests_injective_of_not_Bad_SEQ
          model b S backed tz hbudget hgood h0 keys0 idealEval0 requestOf
            hrequest hreveal0 hlen
      let ys : Fin q → HashOutput L := fun slot =>
        idealEval0 (requestOf slot).1 (requestOf slot).2
      have ha (slot : Fin q) :
          a (Fin.cast hlen.symm slot) = ys slot := by
        have hc := sequenceFunctionTerminalCoordinates_of_ideal_reveal
          model b S backed tz hbudget h0 keys0 idealEval0 requestOf hrequest
          hreveal0 hlen slot
        simpa [a, ys] using hc.2
      have hfilter :
          (Finset.univ.filter fun g => coordG g = a) =
            Finset.univ.filter (fun g : Fin users → InputSequence → HashOutput L =>
              (fun slot : Fin q => g (requestOf slot).1 (requestOf slot).2) = ys) := by
        apply Finset.filter_congr
        intro g _
        constructor
        · intro hg
          funext slot
          have hc := congrFun hg (Fin.cast hlen.symm slot)
          simpa [coordG, sequenceFunctionIdealTerminalCoordinate, ha slot] using hc
        · intro hg
          funext i
          let slot : Fin q := Fin.cast hlen i
          calc
            coordG g i = g (requestOf slot).1 (requestOf slot).2 := by
              rfl
            _ = ys slot := congrFun hg slot
            _ = a i := by simpa [slot] using (ha slot).symm
      rw [hfilter]
      simpa [hlen] using
        (Counting.card_curried_function_fiber_multipoint_mul
          requestOf ys hrequestInjective)
    have hrealLaw : (sequenceFunctionICRealP (Block := Block) (L := L)
          users keysP).val =
        Dist.prod (Dist.uniform (CompressionFunction (HashOutput L) Block))
          keysP.val := by
      unfold sequenceFunctionICRealP
        RandomSystems.HTechnique.IdealCompression.realP compressionP
      simp only [Dist.prodProbDist_val]
      congr 1
      apply Dist.uniform_eq_of_fintype_instances
    have hidealLaw : (sequenceFunctionICIdealP (Block := Block) (L := L)
          users keysP).val =
        Dist.prod (Dist.uniform (CompressionFunction (HashOutput L) Block))
          (Dist.prod keysP.val
            (Dist.uniform (Fin users → InputSequence → HashOutput L))) := by
      unfold sequenceFunctionICIdealP
        RandomSystems.HTechnique.IdealCompression.idealP compressionP
      simp only [Dist.prodProbDist_val]
      congr 1
      · apply Dist.uniform_eq_of_fintype_instances
      · congr 1
        apply Dist.uniform_eq_of_fintype_instances
    rw [hrealLaw, hidealLaw]
    exact Dist.mass_prod_uniform_coordinate_exchange keysP.val R I P
      coordF coordG a hR hI hF hG
  · trans 0
    · apply RandomSystems.Dist.mass_eq_zero_of_forall_not
      rintro ⟨h, keys⟩ ⟨hevent, hreveal⟩
      apply hex
      refine ⟨keys, h, ?_⟩
      let realIdeal : Fin users → InputSequence → HashOutput L :=
        fun user message =>
          sequenceFunctionICEval model b S h (keys user) message
      have hagree : ∀ request ∈ sequenceFunctionVisibleEvalRequests tz.1,
          realIdeal request.1 request.2 =
            sequenceFunctionICEval model b S h
              (keys request.1) request.2 := by intros; rfl
      refine ⟨realIdeal,
        (sequenceFunctionIC_transcriptSystemEvent_real_ideal_iff
          model b S tz.1 h keys realIdeal hagree).mp hevent, ?_⟩
      exact (sequenceFunctionICReveal_real_ideal_eq
        model b S backed tz.1 h keys realIdeal hagree).trans hreveal
    · symm
      apply RandomSystems.Dist.mass_eq_zero_of_forall_not
      rintro ⟨h, keys, idealEval⟩ ⟨hevent, hreveal⟩
      exact hex ⟨keys, h, idealEval, hevent, hreveal⟩

/-- R4 equality-on-good packaged at the filtered representative endpoint. -/
theorem sequenceFunctionIC_r4_equality_on_good
    {Block : Type uBlock} {L : U128} {users p q lambda : ℕ}
    [Fintype Block] [DecidableEq Block]
    (model : SequenceFunctionCompressionModel Block L)
    (b : BlockSize) (S : ByteString)
    (backed : SequenceFunctionOutputCompressionBacked model b S)
    (keysP : Dist.ProbDist (Fin users → SequenceMACKey))
    (deltaBad : NNReal)
    (hBad : ∀ E : QQueryEnvironment
        (SequenceFunctionICQuery Block L users) (SequenceFunctionICReply L)
        (p + q),
      EnvRespects (SequenceFunctionTaggedBudgetRespects
        model b S p q lambda users) E →
      probBad (extendedTranscriptDistRep (q := p + q)
        (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
        sequenceFunctionICIdealF
        (sequenceFunctionICIdealReveal (p := p) (q := q) (lambda := lambda)
          model b S) E.1)
        (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤ deltaBad) :
    filteredAdaptiveTranscriptAdvantage
        (SequenceFunctionTaggedBudgetRespects model b S p q lambda users)
        (sequenceFunctionICReal model b S users keysP)
        (sequenceFunctionICIdeal (Block := Block) (L := L) users keysP) ≤
      (deltaBad : ℝ) := by
  classical
  apply adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter
    (SequenceFunctionTaggedBudgetRespects model b S p q lambda users)
    (sequenceFunctionICRealP (Block := Block) (L := L) users keysP)
    (sequenceFunctionICRealF model b S)
    (sequenceFunctionICIdealP (Block := Block) (L := L) users keysP)
    sequenceFunctionICIdealF
    (sequenceFunctionICRealReveal (p := p) (q := q) (lambda := lambda)
      model b S)
    (sequenceFunctionICIdealReveal (p := p) (q := q) (lambda := lambda)
      model b S)
    (Bad_SEQ (p := p) (q := q) (lambda := lambda)) deltaBad
  · exact sequenceFunctionICReal_KStepTotal model b S users (p + q) keysP
  · exact sequenceFunctionICIdeal_KStepTotal users (p + q) keysP
  · exact fun xs tz hbudget hgood =>
      sequenceFunctionIC_extFixedQueryTranscriptDistRep_eq_on_good
        model b S backed keysP xs tz hbudget hgood
  · exact hBad

end RandomSystemsModel
end SequenceHash
