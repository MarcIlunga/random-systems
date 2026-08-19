import RandomSystems.BlindConverter
import RandomSystems.GameOf
import RandomSystems.Lemma415

/-!
# Seeded history-aware condition-C games

`seededConditionCGame` covers a seed-indexed function evaluator.  Stateful
resources instead compute the next answer from the complete nonempty query
history.  This module provides the corresponding condition-C wrapper and the
same filtered blind-game endpoint.
-/

noncomputable section

namespace RandomSystems.CR18

open RandomSystems (Dist)
open CondEquiv
open scoped RandomSystems.CR18

universe u v w

variable {A : Type u} {I : Type v} {O : Type w}

/-! ## Fixed schedules of blind winners -/

/-- Optional query issued by a blind winner at a fixed round. -/
def historyBlindQueryVector (winner : PFunDDS.Winner I O) (q : ℕ) :
    Fin q → Option I :=
  fun index => winner (List.replicate index.1 (none : Option O))

/-- Issued queries in a blind winner's fixed schedule, omitting stopped
rounds. -/
def historyBlindQueryList (winner : PFunDDS.Winner I O) (q : ℕ) : List I :=
  ((List.finRange q).map fun index =>
    historyBlindQueryVector winner q index).reduceOption

theorem historyBlindQueryList_length_le
    (winner : PFunDDS.Winner I O) (q : ℕ) :
    (historyBlindQueryList winner q).length ≤ q :=
  le_trans (List.reduceOption_length_le _) (by simp)

/-- A schedule-consistent accepted query list is a prefix of the complete
fixed schedule. -/
theorem isPrefix_historyBlindQueryList
    (winner : PFunDDS.Winner I O) (q : ℕ) (queries : List I)
    (lengthBound : queries.length ≤ q)
    (schedule : ∀ index : Fin queries.length,
      historyBlindQueryVector winner q
        ⟨index.1, lt_of_lt_of_le index.2 lengthBound⟩ =
          some (queries.get index)) :
    queries <+: historyBlindQueryList winner q := by
  classical
  have takeSchedule :
      ((List.finRange q).map fun index =>
        historyBlindQueryVector winner q index).take queries.length =
          queries.map some := by
    apply List.ext_getElem
    · simp [lengthBound]
    · intro n firstBound secondBound
      have nBound : n < queries.length := by simpa using secondBound
      have atN := schedule ⟨n, nBound⟩
      simp only [List.getElem_take, List.getElem_map,
        List.getElem_finRange]
      simpa [List.get_eq_getElem] using atN
  have reduceSome : (queries.map some).reduceOption = queries := by
    simp [List.reduceOption, List.filterMap_map]
  refine ⟨(((List.finRange q).map fun index =>
    historyBlindQueryVector winner q index).drop queries.length).reduceOption,
      ?_⟩
  unfold historyBlindQueryList
  conv_rhs => rw [← List.take_append_drop queries.length
    ((List.finRange q).map _)]
  rw [List.reduceOption_append, takeSchedule, reduceSome]

/-! ## Generic run extraction used by the history wrapper -/

/-- Every input in a concrete interaction transcript was issued by the
environment after the preceding output prefix. -/
theorem history_transcript_input_get?_eq_env
    (system : PFunDDS.DDS I O) (environment : PFunDDS.DDE I O)
    (rounds index : ℕ) {query : I}
    (lookup : (PFunDDS.transcriptInputs
      (PFunDDS.transcript system environment rounds))[index]? = some query) :
    environment
      (PFunDDS.transcriptOutputs
        ((PFunDDS.transcript system environment rounds).take index)) =
        some query := by
  induction rounds generalizing index with
  | zero => simp at lookup
  | succ rounds inductionHypothesis =>
      by_cases stopped :
          environment (PFunDDS.transcriptOutputs
            (PFunDDS.transcript system environment rounds)) = none
      · rw [transcript_succ_stall stopped] at lookup ⊢
        exact inductionHypothesis index lookup
      · rcases issued :
          environment (PFunDDS.transcriptOutputs
            (PFunDDS.transcript system environment rounds)) with
        _ | nextQuery
        · exact False.elim (stopped issued)
        · rw [transcript_succ_fire issued] at lookup ⊢
          by_cases earlier : index <
              (PFunDDS.transcript system environment rounds).length
          · have earlierLookup :
                (PFunDDS.transcriptInputs
                  (PFunDDS.transcript system environment rounds))[index]? =
                    some query := by
              rw [transcriptInputs_append] at lookup
              rw [List.getElem?_append_left
                (by simpa [transcriptInputs_length] using earlier)]
                at lookup
              exact lookup
            have takeEquality :
                (PFunDDS.transcript system environment rounds ++
                    [(nextQuery, PFunDDS.output (PFunDDS.fullyDefined system)
                      (PFunDDS.transcriptInputs
                        (PFunDDS.transcript system environment rounds) ++
                          [nextQuery]) (by simp [PFunDDS.fullyDefined,
                          PFunDDS.dom]))]).take index =
                  (PFunDDS.transcript system environment rounds).take index := by
              rw [List.take_append_of_le_length]
              exact earlier.le
            rw [takeEquality]
            exact inductionHypothesis index earlierLookup
          · have atEnd : index =
                (PFunDDS.transcript system environment rounds).length := by
              have bound : index <
                  (PFunDDS.transcript system environment rounds).length + 1 := by
                obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
                simpa [transcriptInputs_append,
                  transcriptInputs_length] using bound
              omega
            subst atEnd
            have equalQuery : nextQuery = query := by
              simpa [transcriptInputs_append,
                transcriptInputs_length] using lookup
            simpa [equalQuery] using issued

/-- A true output of a constructed transcript-MBO game comes from an
accepted base history on which its condition is true. -/
theorem true_output_mem_historyGame_exists_query_cond_true
    (cond : List (I × O) → Bool) (system : PFunDDS.DDS I O)
    (winner : PFunDDS.Winner I O) (rounds : ℕ) (answer : O)
    (member : (some (answer, true) : Option (O × Bool)) ∈
      PFunDDS.transcriptOutputs
        (PFunDDS.transcript (PFunDDS.gameOfDDS cond system)
          (PFunDDS.winnerView winner) rounds)) :
    ∃ earlierRound : ℕ, ∃ query : I,
      PFunDDS.winnerView winner
          (PFunDDS.transcriptOutputs
            (PFunDDS.transcript (PFunDDS.gameOfDDS cond system)
              (PFunDDS.winnerView winner) earlierRound)) = some query ∧
      let queries := PFunDDS.keptPrefix (PFunDDS.gameOfDDS cond system)
          (PFunDDS.transcriptInputs
            (PFunDDS.transcript (PFunDDS.gameOfDDS cond system)
              (PFunDDS.winnerView winner) earlierRound)) ++ [query]
      ∃ accepted : queries ∈ PFunDDS.dom system,
        cond (PFunDDS.ioTranscript system queries accepted) = true := by
  induction rounds with
  | zero => simp [PFunDDS.transcriptOutputs, PFunDDS.transcript] at member
  | succ rounds inductionHypothesis =>
      by_cases stopped : PFunDDS.winnerView winner
          (PFunDDS.transcriptOutputs
            (PFunDDS.transcript (PFunDDS.gameOfDDS cond system)
              (PFunDDS.winnerView winner) rounds)) = none
      · rw [transcript_succ_stall stopped] at member
        exact inductionHypothesis member
      · rcases issued : PFunDDS.winnerView winner
          (PFunDDS.transcriptOutputs
            (PFunDDS.transcript (PFunDDS.gameOfDDS cond system)
              (PFunDDS.winnerView winner) rounds)) with _ | query
        · exact False.elim (stopped issued)
        · rw [transcript_succ_fire issued] at member
          simp only [transcriptOutputs_append, List.mem_append,
            List.mem_singleton] at member
          rcases member with previous | last
          · exact inductionHypothesis previous
          · let transcript := PFunDDS.transcript
              (PFunDDS.gameOfDDS cond system)
              (PFunDDS.winnerView winner) rounds
            let queries := PFunDDS.keptPrefix
              (PFunDDS.gameOfDDS cond system)
                (PFunDDS.transcriptInputs transcript) ++ [query]
            rw [PFunDDS.output_fullyDefined] at last
            have drop : (PFunDDS.transcriptInputs transcript ++
                  [query]).dropLast = PFunDDS.transcriptInputs transcript := by
              simp
            have getLast : (PFunDDS.transcriptInputs transcript ++
                  [query]).getLast (by simp) = query := by
              simp
            rw [drop, getLast] at last
            dsimp only [queries] at last
            split at last
            · rename_i accepted
              have baseAccepted : queries ∈ PFunDDS.dom system := accepted
              have pairOutput :
                  PFunDDS.output (PFunDDS.gameOfDDS cond system)
                    queries accepted = (answer, true) :=
                (Option.some.inj last).symm
              refine ⟨rounds, query, issued, baseAccepted, ?_⟩
              have bitTrue :
                  (PFunDDS.output (PFunDDS.gameOfDDS cond system)
                    queries accepted).2 = true := by simp [pairOutput]
              simpa [PFunDDS.outputBit_gameOfDDS cond system queries
                accepted baseAccepted] using bitTrue
            · simp at last

/-- A seed-indexed total history evaluator carrying a monotone bad bit. -/
noncomputable def seededHistoryConditionCGame
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)] :
    PFunPDS I (O × Bool) :=
  Dist.fTransform
    (fun a => PFunDDS.historyEvaluator fun history nonempty =>
      (out a history nonempty, decide (bad a history))) seed

/-- Prefix-monotonicity of the seed event makes the history-aware wrapper a
monotone-MBO game. -/
theorem seededHistoryConditionCGame_monotoneMBO
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)]
    (monotone : ∀ a, ∀ {left right : List I},
      left <+: right → bad a left → bad a right) :
    MonotoneMBO (seededHistoryConditionCGame seed out bad) := by
  exact monotoneMBO_fTransform_historyEvaluator seed out
    (fun a history => decide (bad a history))
    (fun a left right isPrefix fired => by
      simpa using monotone a isPrefix (by simpa using fired))

/-- A history evaluator is total on every nonempty query history. -/
theorem seededHistoryConditionCGame_totalOnNonempty
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)] :
    TotalOnNonempty (seededHistoryConditionCGame seed out bad) :=
  totalOnNonempty_fTransform_historyEvaluator seed
    (fun a history nonempty =>
      (out a history nonempty, decide (bad a history)))

/-- A probability seed induces a probability game. -/
theorem seededHistoryConditionCGame_isProbDist
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)]
    (seedProbability : seed.isProbDist) :
    (seededHistoryConditionCGame seed out bad).isProbDist := by
  unfold seededHistoryConditionCGame
  exact Dist.fTransform_isProbDist _ seedProbability

/-- Stripping the MBO returns the unmonitored stateful history system. -/
theorem seededHistoryConditionCGame_ignoreMBO
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)] :
    PFunPDS.ignoreMBO (seededHistoryConditionCGame seed out bad) =
      Dist.fTransform
        (fun a => PFunDDS.historyEvaluator (out a)) seed := by
  unfold seededHistoryConditionCGame PFunPDS.ignoreMBO PFunPDS.stripMBO
  simp only [dist_simp]
  rw [show
      (PFunDDS.ignoreMBO ∘ fun a : A =>
        PFunDDS.historyEvaluator fun history nonempty =>
          (out a history nonempty, decide (bad a history))) =
        (fun a : A => PFunDDS.historyEvaluator (out a)) by
      funext a
      rfl]

/-! ## Blind schedule extraction for total stateful systems -/

/-- A blind win against a filtered total history evaluator exposes a prefix
of the winner's fixed query schedule on which the transcript predicate fires. -/
theorem winsDDS_gameOfDDS_filterQueries_historyEvaluator_exists_schedule_list
    (cond : List (I × O) → Bool) (winner : PFunDDS.Winner I O) (q : ℕ)
    (blind : IsBlind winner)
    (out : (history : List I) → history ≠ [] → O)
    (win : winsDDS winner
      (PFunDDS.gameOfDDS cond
        (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out)))) :
    ∃ (queries : List I) (lengthBound : queries.length ≤ q),
      (∀ index : Fin queries.length,
        historyBlindQueryVector winner q
          ⟨index.1, lt_of_lt_of_le index.2 lengthBound⟩ =
            some (queries.get index)) ∧
      ∃ accepted : queries ∈ PFunDDS.dom
          (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out)),
        cond (PFunDDS.ioTranscript
          (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out))
          queries accepted) = true := by
  classical
  let game := PFunDDS.gameOfDDS cond
    (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out))
  obtain ⟨round, answer, member⟩ := win
  obtain ⟨earlierRound, query, issued, accepted, fired⟩ :=
    true_output_mem_historyGame_exists_query_cond_true
      cond (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out))
        winner round answer member
  let transcript := PFunDDS.transcript game
    (PFunDDS.winnerView winner) earlierRound
  let raw := PFunDDS.transcriptInputs transcript
  let queries := PFunDDS.keptPrefix game raw ++ [query]
  change queries ∈ PFunDDS.dom
    (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out)) at accepted
  change cond (PFunDDS.ioTranscript
    (PFunDDS.filterQueries q (PFunDDS.historyEvaluator out))
      queries accepted) = true at fired
  have queriesTake : queries = raw.take q ++ [query] := by
    dsimp [queries, raw, game]
    rw [PFunDDS.keptPrefix_gameOfDDS_filterQueries_eq_take_of_total]
    intro history nonempty
    exact nonempty
  have lengthBound : queries.length ≤ q := accepted.2
  have rawLength : raw.length < q := by
    have takeLength : (raw.take q).length + 1 ≤ q := by
      simpa [queriesTake] using lengthBound
    have takeShort : (raw.take q).length < q := by omega
    rw [List.length_take] at takeShort
    omega
  have queriesRaw : queries = raw ++ [query] := by
    rw [queriesTake, List.take_of_length_le rawLength.le]
  have schedule : ∀ index : Fin queries.length,
        historyBlindQueryVector winner q
        ⟨index.1, lt_of_lt_of_le index.2 lengthBound⟩ =
          some (queries.get index) := by
    intro index
    by_cases inRaw : index.1 < raw.length
    · have rawGet : raw[index.1]? = some (queries.get index) := by
        have queryGet : queries.get index =
            (raw ++ [query]).get
              ⟨index.1, by simpa [queriesRaw] using index.2⟩ :=
          List.get_of_eq queriesRaw index
        rw [List.getElem?_eq_getElem inRaw, queryGet,
          List.get_eq_getElem, List.getElem_append_left inRaw]
      have actual := history_transcript_input_get?_eq_env game
        (PFunDDS.winnerView winner) earlierRound index.1 rawGet
      have actualWinner :
          winner ((PFunDDS.transcriptOutputs
            (transcript.take index.1)).map (Option.map Prod.fst)) =
              some (queries.get index) := by
        simpa [PFunDDS.winnerView, transcript, game] using actual
      have indexLe : index.1 ≤ transcript.length := by
        have := inRaw.le
        simpa [raw, transcriptInputs_length] using this
      have sameLength :
          ((PFunDDS.transcriptOutputs
            (transcript.take index.1)).map (Option.map Prod.fst)).length =
            (List.replicate index.1 (none : Option O)).length := by
        simp [transcriptOutputs_length, List.length_take,
          Nat.min_eq_left indexLe]
      unfold historyBlindQueryVector
      change winner (List.replicate index.1 (none : Option O)) =
        some (queries.get index)
      rw [← blind
        ((PFunDDS.transcriptOutputs
          (transcript.take index.1)).map (Option.map Prod.fst))
        (List.replicate index.1 (none : Option O)) sameLength]
      exact actualWinner
    · have atEnd : index.1 = raw.length := by
        have indexLength : index.1 < raw.length + 1 := by
          simpa [queriesRaw] using index.2
        omega
      have queryGet : queries.get index = query := by
        have appendGet : queries.get index =
            (raw ++ [query]).get
              ⟨index.1, by simpa [queriesRaw] using index.2⟩ :=
          List.get_of_eq queriesRaw index
        rw [appendGet, List.get_eq_getElem,
          List.getElem_append_right (by rw [atEnd])]
        have offset : index.1 - raw.length = 0 := by omega
        simp [offset]
      have issuedWinner :
          winner ((PFunDDS.transcriptOutputs transcript).map
            (Option.map Prod.fst)) = some query := by
        simpa [PFunDDS.winnerView, transcript, game] using issued
      have sameLength :
          ((PFunDDS.transcriptOutputs transcript).map
            (Option.map Prod.fst)).length =
            (List.replicate index.1 (none : Option O)).length := by
        simp [transcriptOutputs_length, raw,
          transcriptInputs_length, atEnd]
      unfold historyBlindQueryVector
      change winner (List.replicate index.1 (none : Option O)) =
        some (queries.get index)
      rw [queryGet]
      rw [← blind
        ((PFunDDS.transcriptOutputs transcript).map (Option.map Prod.fst))
        (List.replicate index.1 (none : Option O)) sameLength]
      exact issuedWinner
  exact ⟨queries, lengthBound, schedule, accepted, fired⟩

/-- Blind winning probability of a history-aware condition-C game is bounded
by the seed mass of the bad event on every fixed blind schedule. -/
theorem blindMaxWinProb_filterQueries_historyMonitored_le
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)]
    (seedNonnegative : seed.NonNeg)
    (monotone : ∀ a, ∀ {left right : List I},
      left <+: right → bad a left → bad a right)
    (q : ℕ) (epsilon : NNReal)
    (leaf : ∀ winner : PFunDDS.Winner I O, IsBlind winner →
      seed.mass (fun a => bad a (historyBlindQueryList winner q)) ≤ epsilon) :
    Γᵇ (⌈q⌉ seededHistoryConditionCGame seed out bad) ≤ epsilon := by
  classical
  have bridge : ∀ a,
      PFunDDS.filterQueries q
          (PFunDDS.historyEvaluator fun history nonempty =>
            (out a history nonempty, decide (bad a history))) =
        PFunDDS.gameOfDDS
          (fun transcript => decide (bad a (transcript.map Prod.fst)))
          (PFunDDS.filterQueries q
            (PFunDDS.historyEvaluator (out a))) := by
    intro a
    apply Subtype.ext
    funext history
    apply Part.ext'
    · exact Iff.rfl
    · intro leftDomain rightDomain
      refine Prod.ext rfl ?_
      show decide (bad a history) =
        decide (bad a ((PFunDDS.ioTranscript
          (PFunDDS.filterQueries q (PFunDDS.historyEvaluator (out a)))
          history rightDomain).map Prod.fst))
      rw [PFunDDS.ioTranscript_map_fst]
  unfold PFunPDS.filterQueries seededHistoryConditionCGame
  rw [Dist.fTransform_comp]
  refine blindMaxWinProb_fTransform_le _ _ _ fun winner blind =>
    le_trans (CR18.mass_mono seedNonnegative fun a won => ?_)
      (leaf winner blind)
  simp only [Function.comp] at won
  rw [bridge a] at won
  obtain ⟨queries, lengthBound, schedule, accepted, fired⟩ :=
    winsDDS_gameOfDDS_filterQueries_historyEvaluator_exists_schedule_list
      _ winner q blind (out a) won
  rw [PFunDDS.ioTranscript_map_fst] at fired
  exact monotone a
    (isPrefix_historyBlindQueryList winner q queries lengthBound schedule)
    (of_decide_eq_true fired)

/-- Public history-aware condition-C endpoint. -/
theorem maxAdvantage_filterQueries_seededHistoryConditionCGame_le
    [Nonempty I]
    (seed : Dist A)
    (out : A → (history : List I) → history ≠ [] → O)
    (bad : A → List I → Prop)
    [∀ a history, Decidable (bad a history)]
    (monotone : ∀ a, ∀ {left right : List I},
      left <+: right → bad a left → bad a right)
    (q : ℕ) (target : PFunPDS I O) (epsilon : NNReal)
    (conditional : seededHistoryConditionCGame seed out bad |≡ target)
    (seedProbability : seed.isProbDist)
    (targetProbability : target.isProbDist)
    (targetTotal : TotalOnNonempty target)
    (leaf : ∀ winner : PFunDDS.Winner I O, IsBlind winner →
      seed.mass (fun a => bad a (historyBlindQueryList winner q)) ≤ epsilon) :
    Δ(⌈q⌉ PFunPDS.ignoreMBO
        (seededHistoryConditionCGame seed out bad), ⌈q⌉ target) ≤
      (epsilon : ℝ) := by
  calc
    Δ(⌈q⌉ PFunPDS.ignoreMBO
          (seededHistoryConditionCGame seed out bad), ⌈q⌉ target) ≤
        (Γᵇ (⌈q⌉ seededHistoryConditionCGame seed out bad) : ℝ) :=
      maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv q
        (seededHistoryConditionCGame seed out bad) conditional rfl
        (seededHistoryConditionCGame_monotoneMBO seed out bad monotone)
        (seededHistoryConditionCGame_isProbDist seed out bad seedProbability)
        targetProbability
        (seededHistoryConditionCGame_totalOnNonempty seed out bad)
        targetTotal
    _ ≤ (epsilon : ℝ) := by
      exact_mod_cast blindMaxWinProb_filterQueries_historyMonitored_le
        seed out bad seedProbability.nonNeg monotone q epsilon leaf

end RandomSystems.CR18
