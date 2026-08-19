/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.AEAD.RealIdeal
import RandomSystems.SpoC.Distinguishing

/-!
# A perfect full-AEAD distinguishing attack on SpoC

The two encryption answers used by `attackEnvironment` reveal the secret key
in the public-permutation model.  Its final fresh ciphertext therefore verifies
in the real system.  In the full-AEAD ideal system the same query is neither of
the two recorded encryption tuples, so it is rejected for every eager tape.
-/

namespace RandomSystems.SpoC

open RandomSystems.CR18
open RandomSystems.HCTR2Final.Bits.Facts
open scoped RandomSystems.CR18.PFunDDS
open scoped RandomSystems.HCTR2Final.Bits

noncomputable section

/-- One eager ideal tape for the concrete `q_e = 2`, `ell = 1` game. -/
abbrev FullAEADIdealTape := AEAD.IdealTape Block Block 2 1

/-- A total fixed-key SpoC representative. -/
def fullAEADRealRepresentative (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.DDS Query Response :=
  spocRepresentative permutation key

/-- A total fixed-tape full-AEAD ideal representative. -/
def fullAEADIdealRepresentative (tape : FullAEADIdealTape) :
    PFunDDS.DDS Query Response :=
  AEAD.idealRepresentative (fun plaintext : List Block => plaintext.length)
    ([] : List Block) tape

/-- Every nonempty history is in the domain of a fixed-key SpoC
representative. -/
theorem spocRepresentative_totalOnNonempty (permutation : Equiv.Perm State)
    (key : Block) (history : List Query) (hNonempty : history ≠ []) :
    history ∈ PFunDDS.dom (spocRepresentative permutation key) := by
  change history ∈
    PFunDDS.dom (PFunDDS.functionEvaluator (spocOracle permutation key))
  rw [PFunDDS.dom_functionEvaluator]
  exact hNonempty

/-- The unfiltered random-key SpoC law is total on every nonempty history. -/
theorem spocPDS_totalOnNonempty (permutation : Equiv.Perm State) :
    CondEquiv.TotalOnNonempty (spocPDS permutation).val := by
  intro representative hSupport history hNonempty
  unfold spocPDS at hSupport
  obtain ⟨key, _hKey, rfl⟩ :=
    Dist.mem_support_fTransform _ _ hSupport
  exact spocRepresentative_totalOnNonempty permutation key history hNonempty

/-- Every nonempty history is in the domain of a fixed-tape ideal
representative. -/
theorem idealBaseRepresentative_totalOnNonempty (tape : FullAEADIdealTape)
    (history : List Query) (hNonempty : history ≠ []) :
    history ∈ PFunDDS.dom
      (AEAD.idealRepresentative
        (fun plaintext : List Block => plaintext.length)
        ([] : List Block) tape) := by
  change history ∈ PFunDDS.dom
    (PFunDDS.historyEvaluator
      (AEAD.idealOracle (fun plaintext : List Block => plaintext.length)
        ([] : List Block) tape))
  rw [PFunDDS.dom_historyEvaluator]
  exact hNonempty

/-- The attack's complete query history is an admissible `q_e = 2`, `ell = 1`
AEAD history, independently of its final decryption query. -/
theorem attackQueryHistory_admissible (decryption : DecryptQuery) :
    AEAD.LegalHistory 2 1 (fun plaintext : List Block => plaintext.length)
      [Sum.inl emptyEncryptionQuery, Sum.inl oneBlockEncryptionQuery,
        Sum.inr decryption] := by
  have hNonce : tagControl ≠ (0 : Block) := by decide
  have hZeroNonce : (0 : Block) ≠ tagControl := Ne.symm hNonce
  simp [AEAD.LegalHistory, AEAD.encryptionCount, AEAD.encryptionNonces,
    AEAD.encryptionQueries,
    emptyEncryptionQuery, oneBlockEncryptionQuery]
  exact hZeroNonce

/-- On its complete interaction path, the attack makes exactly two encryption
queries (followed by one decryption query). -/
theorem attackQueryHistory_encryptionCount (decryption : DecryptQuery) :
    AEAD.encryptionCount
      [Sum.inl emptyEncryptionQuery, Sum.inl oneBlockEncryptionQuery,
        Sum.inr decryption] = 2 := by
  simp [AEAD.encryptionCount, AEAD.encryptionQueries]

/-- After three supplied answers, the concrete attack environment has stopped,
regardless of whether malformed answers made it stop earlier. -/
theorem attackEnvironment_stalls_after_three_answers
    (permutation : Equiv.Perm State) (y0 y1 y2 : Option Response) :
    attackEnvironment permutation
        (PFunDDS.transcriptOutputs
          (replay (attackEnvironment permutation) [y0, y1, y2])) = none := by
  rcases y0 with _ | (response0 | response0) <;>
    rcases y1 with _ | (response1 | response1) <;>
    simp [replay, attackEnvironment, PFunDDS.transcriptOutputs]

/-- Supplying more than three answers cannot extend the attack transcript. -/
theorem attackEnvironment_replay_eq_three_prefix
    (permutation : Equiv.Perm State) (y0 y1 y2 : Option Response)
    (tail : List (Option Response)) :
    replay (attackEnvironment permutation) (y0 :: y1 :: y2 :: tail) =
      replay (attackEnvironment permutation) [y0, y1, y2] :=
  replay_eq_of_stall
    (attackEnvironment_stalls_after_three_answers permutation y0 y1 y2)
    ⟨tail, rfl⟩

/-- Every response path of the adaptive attack makes at most two encryption
queries, never repeats an encryption nonce, and uses plaintexts of at most one
block.  These are obligations on the environment, not restrictions on either
PDS. -/
theorem attackEnvironment_replay_legal (permutation : Equiv.Perm State)
    (answers : List (Option Response)) :
    AEAD.LegalHistory 2 1
      (fun plaintext : List Block => plaintext.length)
      (PFunDDS.transcriptInputs
        (replay (attackEnvironment permutation) answers)) := by
  cases answers with
  | nil =>
      simp [replay, PFunDDS.transcriptInputs, PFunDDS.transcriptOutputs,
        AEAD.LegalHistory, AEAD.encryptionCount,
        AEAD.encryptionNonces, AEAD.encryptionQueries]
  | cons y0 answers =>
      cases answers with
      | nil =>
          simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
            PFunDDS.transcriptOutputs, AEAD.LegalHistory,
            AEAD.encryptionCount, AEAD.encryptionNonces, AEAD.encryptionQueries,
            emptyEncryptionQuery]
      | cons y1 answers =>
          cases answers with
          | nil =>
              have hZeroNonce : (0 : Block) ≠ tagControl := by decide
              rcases y0 with _ | (response0 | response0) <;>
                simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
                  PFunDDS.transcriptOutputs, AEAD.LegalHistory,
                  AEAD.encryptionCount, AEAD.encryptionNonces,
                  AEAD.encryptionQueries, emptyEncryptionQuery,
                  oneBlockEncryptionQuery]
              all_goals exact hZeroNonce
          | cons y2 tail =>
              rw [attackEnvironment_replay_eq_three_prefix]
              have hZeroNonce : (0 : Block) ≠ tagControl := by decide
              rcases y0 with _ | (response0 | response0) <;>
                rcases y1 with _ | (response1 | response1) <;>
                simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
                  PFunDDS.transcriptOutputs, AEAD.LegalHistory,
                  AEAD.encryptionCount, AEAD.encryptionNonces,
                  AEAD.encryptionQueries, emptyEncryptionQuery,
                  oneBlockEncryptionQuery] <;>
                exact hZeroNonce

/-- The attack environment emits at most three total queries on every response
path. -/
theorem attackEnvironment_replay_queryCount_le_three
    (permutation : Equiv.Perm State) (answers : List (Option Response)) :
    (PFunDDS.transcriptInputs
      (replay (attackEnvironment permutation) answers)).length ≤ 3 := by
  cases answers with
  | nil =>
      simp [replay, PFunDDS.transcriptInputs]
  | cons y0 answers =>
      cases answers with
      | nil =>
          simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
            PFunDDS.transcriptOutputs]
      | cons y1 answers =>
          cases answers with
          | nil =>
              rcases y0 with _ | (response0 | response0) <;>
                simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
                  PFunDDS.transcriptOutputs]
          | cons y2 tail =>
              rw [attackEnvironment_replay_eq_three_prefix]
              rcases y0 with _ | (response0 | response0) <;>
                rcases y1 with _ | (response1 | response1) <;>
                simp [replay, attackEnvironment, PFunDDS.transcriptInputs,
                  PFunDDS.transcriptOutputs]

/-- The concrete environment satisfies the generic full-AEAD admissibility
predicate. -/
theorem attackEnvironment_admissible (permutation : Equiv.Perm State) :
    AEAD.AdmissibleEnvironment 2 1
      (fun plaintext : List Block => plaintext.length)
      (attackEnvironment permutation) :=
  attackEnvironment_replay_legal permutation

/-- The concrete distinguisher makes at most three total oracle queries. -/
theorem attackDistinguisher_atMostThree (permutation : Equiv.Perm State) :
    ∀ answers : List (Option Response), 3 ≤ answers.length →
      ∃ verdict, (attackDistinguisher permutation).val answers =
        Sum.inr verdict := by
  intro answers hLength
  refine ⟨verificationVerdict
    (replay (attackEnvironment permutation) (answers.take 3)), ?_⟩
  simp [attackDistinguisher, PFunDDS.DDD.ofDDE, not_lt.mpr hLength]

/-- Answer equation for the total fixed-key representative. -/
theorem fullAEADRealAnswer (permutation : Equiv.Perm State) (key : Block)
    (history : List Query) (query : Query) :
    PFunDDS.output (fullAEADRealRepresentative permutation key)⊥
        (history ++ [query]) (by rw [PFunDDS.dom_fullyDefined]; simp) =
      some (spocOracle permutation key query) := by
  rw [fullAEADRealRepresentative]
  have hHistoryBase :
      history ∈ PFunDDS.dom (spocRepresentative permutation key) ∨
        history = [] := by
    by_cases hEmpty : history = []
    · exact Or.inr hEmpty
    · exact Or.inl
        (spocRepresentative_totalOnNonempty permutation key history hEmpty)
  have hNextBase : history ++ [query] ∈
      PFunDDS.dom (spocRepresentative permutation key) :=
    spocRepresentative_totalOnNonempty permutation key _ (by simp)
  rw [PFunDDS.output_fullyDefined_append_of_mem
    (spocRepresentative permutation key) history query hHistoryBase hNextBase]
  change some (PFunDDS.output
    (PFunDDS.functionEvaluator (spocOracle permutation key))
    (history ++ [query]) _) = _
  rw [PFunDDS.functionEvaluator_output]

/-- Answer equation for the total fixed-tape ideal representative. -/
theorem fullAEADIdealAnswer (tape : FullAEADIdealTape)
    (history : List Query) (query : Query) :
    PFunDDS.output (fullAEADIdealRepresentative tape)⊥
        (history ++ [query]) (by rw [PFunDDS.dom_fullyDefined]; simp) =
      some (AEAD.idealOracle
        (fun plaintext : List Block => plaintext.length) ([] : List Block)
        tape (history ++ [query]) (by simp)) := by
  rw [fullAEADIdealRepresentative]
  have hHistoryBase :
      history ∈ PFunDDS.dom
          (AEAD.idealRepresentative
            (fun plaintext : List Block => plaintext.length)
            ([] : List Block) tape) ∨
        history = [] := by
    by_cases hEmpty : history = []
    · exact Or.inr hEmpty
    · exact Or.inl
        (idealBaseRepresentative_totalOnNonempty tape history hEmpty)
  have hNextBase : history ++ [query] ∈ PFunDDS.dom
      (AEAD.idealRepresentative
        (fun plaintext : List Block => plaintext.length)
        ([] : List Block) tape) :=
    idealBaseRepresentative_totalOnNonempty tape _ (by simp)
  rw [PFunDDS.output_fullyDefined_append_of_mem
    (AEAD.idealRepresentative
      (fun plaintext : List Block => plaintext.length)
      ([] : List Block) tape) history query hHistoryBase hNextBase]
  change some (PFunDDS.output
    (PFunDDS.historyEvaluator
      (AEAD.idealOracle (fun plaintext : List Block => plaintext.length)
        ([] : List Block) tape)) (history ++ [query]) _) = _
  rw [PFunDDS.historyEvaluator_output]

/-- Every fixed real key yields the attack's accepting transcript. -/
theorem fullAEADRealTranscript (permutation : Equiv.Perm State) (key : Block) :
    let emptyResponse := encrypt permutation key 0 [] []
    let oneBlockResponse := encrypt permutation key tagControl [] [0]
    let forged := encrypt permutation key 0 [] [0]
    PFunDDS.transcript (fullAEADRealRepresentative permutation key)
      (attackEnvironment permutation) 3 =
      [(Sum.inl emptyEncryptionQuery, some (Sum.inl emptyResponse)),
       (Sum.inl oneBlockEncryptionQuery, some (Sum.inl oneBlockResponse)),
       (Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩,
        some (Sum.inr ⟨true, [0]⟩))] := by
  let emptyResponse := encrypt permutation key 0 [] []
  let oneBlockResponse := encrypt permutation key tagControl [] [0]
  let forged := encrypt permutation key 0 [] [0]
  let q0 : Query := Sum.inl emptyEncryptionQuery
  let q1 : Query := Sum.inl oneBlockEncryptionQuery
  let q2 : Query := Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩
  let r0 : Response := Sum.inl emptyResponse
  let r1 : Response := Sum.inl oneBlockResponse
  have hFire0 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADRealRepresentative permutation key)
        (attackEnvironment permutation) 0)) = some q0 := rfl
  have hTr1 : PFunDDS.transcript (fullAEADRealRepresentative permutation key)
      (attackEnvironment permutation) 1 = [(q0, some r0)] := by
    rw [show 1 = 0 + 1 by omega, transcript_succ_fire hFire0]
    simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil,
      List.nil_append]
    have hAnswer := fullAEADRealAnswer permutation key [] q0
    simp only [List.nil_append] at hAnswer
    rw [hAnswer]
    simp [q0, r0, emptyResponse, spocOracle, emptyEncryptionQuery]
  have hFire1 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADRealRepresentative permutation key)
        (attackEnvironment permutation) 1)) = some q1 := by
    rw [hTr1]
    rfl
  have hTr2 : PFunDDS.transcript (fullAEADRealRepresentative permutation key)
      (attackEnvironment permutation) 2 =
      [(q0, some r0), (q1, some r1)] := by
    rw [show 2 = 1 + 1 by omega, transcript_succ_fire hFire1, hTr1]
    simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
    rw [fullAEADRealAnswer permutation key [q0] q1]
    simp [q1, r1, oneBlockResponse, spocOracle, oneBlockEncryptionQuery]
  have hFire2 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADRealRepresentative permutation key)
        (attackEnvironment permutation) 2)) = some q2 := by
    rw [hTr2]
    simp only [PFunDDS.transcriptOutputs, List.map_cons, List.map_nil]
    change some (Sum.inr (forgedDecryptionQuery permutation
      emptyResponse oneBlockResponse)) = some q2
    dsimp only [forgedDecryptionQuery, q2, forged]
    rw [show recoveredKey permutation emptyResponse oneBlockResponse = key by
      dsimp only [emptyResponse, oneBlockResponse]
      exact recovered_key permutation key]
  rw [show 3 = 2 + 1 by omega, transcript_succ_fire hFire2, hTr2]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
  rw [fullAEADRealAnswer permutation key [q0, q1] q2]
  simp [q0, q1, q2, r0, r1, emptyResponse, oneBlockResponse, forged,
    spocOracle, emptyEncryptionQuery, oneBlockEncryptionQuery, spoc_correct]

/-- Every fixed ideal tape yields the attack's rejecting transcript. -/
theorem fullAEADIdealTranscript (permutation : Equiv.Perm State)
    (tape : FullAEADIdealTape) :
    let emptyResponse : EncryptResponse := AEAD.idealEncrypt tape 0 0
    let oneBlockResponse : EncryptResponse := AEAD.idealEncrypt tape 1 1
    let forged := encrypt permutation
      (recoveredKey permutation emptyResponse oneBlockResponse) 0 [] [0]
    PFunDDS.transcript (fullAEADIdealRepresentative tape)
      (attackEnvironment permutation) 3 =
      [(Sum.inl emptyEncryptionQuery, some (Sum.inl emptyResponse)),
       (Sum.inl oneBlockEncryptionQuery, some (Sum.inl oneBlockResponse)),
       (Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩,
        some (Sum.inr ⟨false, []⟩))] := by
  let emptyResponse : EncryptResponse := AEAD.idealEncrypt tape 0 0
  let oneBlockResponse : EncryptResponse := AEAD.idealEncrypt tape 1 1
  let forged := encrypt permutation
    (recoveredKey permutation emptyResponse oneBlockResponse) 0 [] [0]
  let q0 : Query := Sum.inl emptyEncryptionQuery
  let q1 : Query := Sum.inl oneBlockEncryptionQuery
  let q2 : Query := Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩
  let r0 : Response := Sum.inl emptyResponse
  let r1 : Response := Sum.inl oneBlockResponse
  have hFire0 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADIdealRepresentative tape) (attackEnvironment permutation) 0)) =
      some q0 := rfl
  have hTr1 : PFunDDS.transcript (fullAEADIdealRepresentative tape)
      (attackEnvironment permutation) 1 = [(q0, some r0)] := by
    rw [show 1 = 0 + 1 by omega, transcript_succ_fire hFire0]
    simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil,
      List.nil_append]
    have hAnswer := fullAEADIdealAnswer tape [] q0
    simp only [List.nil_append] at hAnswer
    rw [hAnswer]
    simp [q0, r0, emptyResponse, AEAD.idealOracle,
      AEAD.idealEncryptQuery, AEAD.encryptionCount, AEAD.encryptionQueries,
      emptyEncryptionQuery]
  have hFire1 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADIdealRepresentative tape) (attackEnvironment permutation) 1)) =
      some q1 := by
    rw [hTr1]
    rfl
  have hTr2 : PFunDDS.transcript (fullAEADIdealRepresentative tape)
      (attackEnvironment permutation) 2 =
      [(q0, some r0), (q1, some r1)] := by
    rw [show 2 = 1 + 1 by omega, transcript_succ_fire hFire1, hTr1]
    simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
    rw [fullAEADIdealAnswer tape [q0] q1]
    simp [q0, q1, r1, oneBlockResponse, AEAD.idealOracle,
      AEAD.idealEncryptQuery, oneBlockEncryptionQuery, AEAD.encryptionCount,
      AEAD.encryptionQueries]
  have hFire2 : attackEnvironment permutation
      (PFunDDS.transcriptOutputs (PFunDDS.transcript
        (fullAEADIdealRepresentative tape) (attackEnvironment permutation) 2)) =
      some q2 := by
    rw [hTr2]
    simp only [PFunDDS.transcriptOutputs, List.map_cons, List.map_nil]
    change some (Sum.inr (forgedDecryptionQuery permutation
      emptyResponse oneBlockResponse)) = some q2
    rfl
  rw [show 3 = 2 + 1 by omega, transcript_succ_fire hFire2, hTr2]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
  rw [fullAEADIdealAnswer tape [q0, q1] q2]
  have hNonce : tagControl ≠ (0 : Block) := by decide
  have hForgedLength : forged.ciphertext.length = 1 := by
    simp [forged, encrypt, cryptBlocks]
  have hEmptyNotForged : ([] : List Block) ≠ forged.ciphertext := by
    intro hEqual
    have hLengths := congrArg List.length hEqual
    simp [hForgedLength] at hLengths
  have hFresh : ∀ record ∈ AEAD.replayTable
      (fun plaintext : List Block => plaintext.length) tape [q0, q1],
      ¬ record.Matches
        (⟨0, [], forged.ciphertext, forged.tag⟩ : DecryptQuery) := by
    intro record hRecord hMatches
    simp [AEAD.replayTable, AEAD.encryptionQueries, q0, q1,
      emptyEncryptionQuery, oneBlockEncryptionQuery] at hRecord
    rcases hRecord with rfl | rfl
    · apply hEmptyNotForged
      simpa [AEAD.idealEncryptQuery, emptyEncryptionQuery,
        AEAD.idealEncrypt] using hMatches.2.2.1
    · exact hNonce hMatches.1
  have hReject := AEAD.idealDecrypt_of_forall_not_matches
    (fun plaintext : List Block => plaintext.length) ([] : List Block) tape
    [q0, q1] (⟨0, [], forged.ciphertext, forged.tag⟩ : DecryptQuery) hFresh
  change
    [(q0, some r0), (q1, some r1),
      (q2, some (Sum.inr (AEAD.idealDecrypt
        (fun plaintext : List Block => plaintext.length) ([] : List Block) tape
        [q0, q1] ⟨0, [], forged.ciphertext, forged.tag⟩)))] =
    [(q0, some r0), (q1, some r1),
      (q2, some (Sum.inr ⟨false, []⟩))]
  rw [hReject]

/-- Pointwise real acceptance of the full-AEAD attack. -/
theorem fullAEADRealVerdict (permutation : Equiv.Perm State) (key : Block) :
    PFunDDS.verdict (attackDistinguisher permutation)
      (fullAEADRealRepresentative permutation key) := by
  change PFunDDS.verdict
    (PFunDDS.DDD.ofDDE (attackEnvironment permutation) 3 verificationVerdict)
    (fullAEADRealRepresentative permutation key)
  rw [verdict_ofDDE_iff, fullAEADRealTranscript permutation key]
  simp [verificationVerdict]

/-- Pointwise ideal rejection of the full-AEAD attack. -/
theorem fullAEADIdealNoVerdict (permutation : Equiv.Perm State)
    (tape : FullAEADIdealTape) :
    ¬ PFunDDS.verdict (attackDistinguisher permutation)
      (fullAEADIdealRepresentative tape) := by
  change ¬ PFunDDS.verdict
    (PFunDDS.DDD.ofDDE (attackEnvironment permutation) 3 verificationVerdict)
    (fullAEADIdealRepresentative tape)
  rw [verdict_ofDDE_iff, fullAEADIdealTranscript permutation tape]
  simp [verificationVerdict]

/-- The normalized shared-domain full-AEAD game instantiated with SpoC. -/
def spocFullAEADGame (permutation : Equiv.Perm State) :
    AEAD.RealIdealGame Query Response :=
  AEAD.fullGame 2 1 (fun plaintext : List Block => plaintext.length)
    ([] : List Block) (spocPDS permutation)
    (spocPDS_totalOnNonempty permutation)

/-- Both laws packaged by the concrete full-AEAD game are normalized. -/
theorem spocFullAEADGame_isNormalized (permutation : Equiv.Perm State) :
    (spocFullAEADGame permutation).real.val.isProbDist ∧
      (spocFullAEADGame permutation).ideal.val.isProbDist :=
  ⟨(spocFullAEADGame permutation).real.property,
    (spocFullAEADGame permutation).ideal.property⟩

/-- The point distinguisher used by the attack is a normalized law. -/
theorem attackDistinguisherDistribution_isProbDist
    (permutation : Equiv.Perm State) :
    (attackDistinguisherDistribution permutation).isProbDist := by
  unfold attackDistinguisherDistribution
  exact Dist.isProbDist_single _

/-- Representative form of the concrete game's total real law. -/
theorem spocFullAEADGame_realLaw (permutation : Equiv.Perm State) :
    (spocFullAEADGame permutation).real.val =
      Dist.fTransform (fullAEADRealRepresentative permutation)
        (Dist.uniform Block) := by
  rfl

/-- Representative form of the concrete game's total ideal law. -/
theorem spocFullAEADGame_idealLaw (permutation : Equiv.Perm State) :
    (spocFullAEADGame permutation).ideal.val =
      Dist.fTransform fullAEADIdealRepresentative
        (Dist.uniform FullAEADIdealTape) := by
  rfl

/-- At `q_e = 2` and `ell = 1`, the existing three-query attack has exact
signed full-AEAD advantage one against SpoC. -/
theorem full_aead_advantage_one (permutation : Equiv.Perm State) :
    (spocFullAEADGame permutation).advantage
      (attackDistinguisherDistribution permutation) = 1 := by
  unfold AEAD.RealIdealGame.advantage advantage
  rw [spocFullAEADGame_idealLaw, spocFullAEADGame_realLaw]
  unfold attackDistinguisherDistribution
  rw [verdictProb_single, verdictProb_single]
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  have hReal : (Dist.uniform Block).mass
      (fun key => PFunDDS.verdict (attackDistinguisher permutation)
        (fullAEADRealRepresentative permutation key)) = 1 := by
    calc
      _ = (Dist.uniform Block).mass (fun _ => True) :=
        Dist.mass_congr _ fun key =>
          iff_of_true (fullAEADRealVerdict permutation key) trivial
      _ = (Dist.uniform Block).weight := Dist.mass_true _
      _ = 1 := Dist.uniform_isProbDist.weight_eq
  have hIdeal : (Dist.uniform FullAEADIdealTape).mass
      (fun tape => PFunDDS.verdict (attackDistinguisher permutation)
        (fullAEADIdealRepresentative tape)) = 0 := by
    exact Dist.mass_eq_zero_of_forall_not _
      (fullAEADIdealNoVerdict permutation)
  rw [hReal, hIdeal]
  norm_num

/-- Headline bounded full-AEAD break: the normalized distinguisher makes at
most three queries, satisfies the `q_e = 2`, `ell = 1`, nonce-respecting
profile, and distinguishes the total real and ideal systems with exact
advantage one. -/
theorem full_aead_break (permutation : Equiv.Perm State) :
    AEAD.AdmissibleEnvironment 2 1
        (fun plaintext : List Block => plaintext.length)
        (attackEnvironment permutation) ∧
      (∀ answers : List (Option Response),
        (PFunDDS.transcriptInputs
          (replay (attackEnvironment permutation) answers)).length ≤ 3) ∧
      (attackDistinguisherDistribution permutation).isProbDist ∧
      (spocFullAEADGame permutation).advantage
        (attackDistinguisherDistribution permutation) = 1 :=
  ⟨attackEnvironment_admissible permutation,
    attackEnvironment_replay_queryCount_le_three permutation,
    attackDistinguisherDistribution_isProbDist permutation,
    full_aead_advantage_one permutation⟩

end

end RandomSystems.SpoC
