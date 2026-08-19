/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SpoC.DDC
import RandomSystems.Distinguishing
import RandomSystems.RandomSystem

namespace RandomSystems.SpoC

open RandomSystems.CR18
open RandomSystems.HCTR2Final.Bits.Facts
open scoped RandomSystems.CR18.PFunDDS
open scoped RandomSystems.HCTR2Final.Bits

def recoveredKey (permutation : Equiv.Perm State)
    (emptyResponse oneBlockResponse : EncryptResponse) : Block :=
  capacity (permutation.symm
    (state emptyResponse.tag (oneBlockResponse.ciphertext.getD 0 0)))

def emptyEncryptionQuery : EncryptQuery := ⟨0, [], []⟩

def oneBlockEncryptionQuery : EncryptQuery := ⟨tagControl, [], [0]⟩

def forgedDecryptionQuery (permutation : Equiv.Perm State)
    (emptyResponse oneBlockResponse : EncryptResponse) : DecryptQuery :=
  let result := encrypt permutation
    (recoveredKey permutation emptyResponse oneBlockResponse) 0 [] [0]
  ⟨0, [], result.ciphertext, result.tag⟩

theorem recovered_key (permutation : Equiv.Perm State) (key : Block) :
    recoveredKey permutation
      (encrypt permutation key 0 [] [])
      (encrypt permutation key tagControl [] [0]) = key := by
  have htag : tagInput (load key 0) = load key tagControl := by
    simp [tagInput, load, state, capacity, rate, sub_cat_left, sub_cat_right]
  let z := permutation (load key tagControl)
  have hsplit : state (capacity z) (rate z) = z :=
    cat_sub_sub (a := 128) (b := 128) z
  simp only [recoveredKey, encrypt, absorbBlocks, cryptBlocks, List.getD_cons_zero,
    processData]
  rw [htag]
  simp only [Bool.false_eq_true, if_false]
  have hzero : rate (permutation (load key tagControl)) ^^^ (0 : Block) =
      rate (permutation (load key tagControl)) := BitVec.xor_zero
  rw [hzero]
  rw [show state (capacity (permutation (load key tagControl)))
      (rate (permutation (load key tagControl))) = z from hsplit]
  rw [permutation.symm_apply_apply]
  exact sub_cat_left key tagControl

def attackEnvironment (permutation : Equiv.Perm State) :
    PFunDDS.DDE Query Response
  | [] => some (Sum.inl emptyEncryptionQuery)
  | [some (Sum.inl _)] =>
      some (Sum.inl oneBlockEncryptionQuery)
  | [some (Sum.inl emptyResponse), some (Sum.inl oneBlockResponse)] =>
      some (Sum.inr (forgedDecryptionQuery permutation emptyResponse oneBlockResponse))
  | _ => none

def idealDecrypt (permutation : Equiv.Perm State) (key : Block) :
    List Query → DecryptQuery → DecryptResponse
  | [], _ => ⟨false, []⟩
  | Sum.inl encryption :: history, decryption =>
      let response := encrypt permutation key encryption.nonce
        encryption.associatedData encryption.plaintext
      if encryption.nonce = decryption.nonce ∧
          encryption.associatedData = decryption.associatedData ∧
          response.ciphertext = decryption.ciphertext ∧
          response.tag = decryption.tag then
        ⟨true, encryption.plaintext⟩
      else
        idealDecrypt permutation key history decryption
  | Sum.inr _ :: history, decryption =>
      idealDecrypt permutation key history decryption

def idealOracle (permutation : Equiv.Perm State) (key : Block)
    (history : List Query) (nonempty : history ≠ []) : Response :=
  match history.getLast nonempty with
  | Sum.inl query =>
      Sum.inl (encrypt permutation key query.nonce query.associatedData
        query.plaintext)
  | Sum.inr query =>
      Sum.inr (idealDecrypt permutation key history.dropLast query)

noncomputable def idealRepresentative
    (permutation : Equiv.Perm State) (key : Block) : PFunDDS.DDS Query Response :=
  PFunDDS.historyEvaluator (idealOracle permutation key)

noncomputable def idealSystem (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (idealRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

def verificationVerdict (transcript : List (Query × Option Response)) : Bool :=
  match transcript.getLast? with
  | some (_, some (Sum.inr response)) => response.verified
  | _ => false

noncomputable def attackDistinguisher (permutation : Equiv.Perm State) :
    PFunDDS.DDD Query Response :=
  PFunDDS.DDD.ofDDE (attackEnvironment permutation) 3 verificationVerdict

noncomputable def attackDistinguisherDistribution
    (permutation : Equiv.Perm State) : Dist (PFunDDS.DDD Query Response) :=
  Finsupp.single (attackDistinguisher permutation) 1

noncomputable def distinguishingAdvantage (permutation : Equiv.Perm State)
    (distinguisher : Dist (PFunDDS.DDD Query Response)) : ℝ :=
  advantage distinguisher
    (idealSystem permutation).val (spocPDS permutation).val

theorem attack_distinguishing_advantage (permutation : Equiv.Perm State) :
    distinguishingAdvantage permutation
      (attackDistinguisherDistribution permutation) = 1 := by
  have realAnswer (key : Block) (history : List Query) (query : Query) :
      PFunDDS.output (spocRepresentative permutation key)⊥
        (history ++ [query]) (by rw [PFunDDS.dom_fullyDefined]; simp) =
        some (spocOracle permutation key query) := by
    have hhistory :
        history ∈ PFunDDS.dom (spocRepresentative permutation key) ∨
          history = [] := by
      by_cases hempty : history = []
      · exact Or.inr hempty
      · left
        change history ∈
          PFunDDS.dom (PFunDDS.functionEvaluator (spocOracle permutation key))
        rw [PFunDDS.dom_functionEvaluator]
        exact hempty
    have hnext : history ++ [query] ∈
        PFunDDS.dom (spocRepresentative permutation key) := by
      change history ++ [query] ∈
        PFunDDS.dom (PFunDDS.functionEvaluator (spocOracle permutation key))
      rw [PFunDDS.dom_functionEvaluator]
      simp
    rw [PFunDDS.output_fullyDefined_append_of_mem
      (spocRepresentative permutation key) history query hhistory hnext]
    change some (PFunDDS.output
      (PFunDDS.functionEvaluator (spocOracle permutation key))
      (history ++ [query]) _) = _
    rw [PFunDDS.functionEvaluator_output]
  have idealAnswer (key : Block) (history : List Query) (query : Query) :
      PFunDDS.output (idealRepresentative permutation key)⊥
        (history ++ [query]) (by rw [PFunDDS.dom_fullyDefined]; simp) =
        some (idealOracle permutation key (history ++ [query]) (by simp)) := by
    have hhistory :
        history ∈ PFunDDS.dom (idealRepresentative permutation key) ∨
          history = [] := by
      by_cases hempty : history = []
      · exact Or.inr hempty
      · left
        change history ∈
          PFunDDS.dom (PFunDDS.historyEvaluator (idealOracle permutation key))
        rw [PFunDDS.dom_historyEvaluator]
        exact hempty
    have hnext : history ++ [query] ∈
        PFunDDS.dom (idealRepresentative permutation key) := by
      change history ++ [query] ∈
        PFunDDS.dom (PFunDDS.historyEvaluator (idealOracle permutation key))
      rw [PFunDDS.dom_historyEvaluator]
      simp
    rw [PFunDDS.output_fullyDefined_append_of_mem
      (idealRepresentative permutation key) history query hhistory hnext]
    change some (PFunDDS.output
      (PFunDDS.historyEvaluator (idealOracle permutation key))
      (history ++ [query]) _) = _
    rw [PFunDDS.historyEvaluator_output]
  have realTranscript (key : Block) :
      let emptyResponse := encrypt permutation key 0 [] []
      let oneBlockResponse := encrypt permutation key tagControl [] [0]
      let forged := encrypt permutation key 0 [] [0]
      PFunDDS.transcript (spocRepresentative permutation key)
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
    have hfire0 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (spocRepresentative permutation key) (attackEnvironment permutation) 0)) =
        some q0 := rfl
    have htr1 : PFunDDS.transcript (spocRepresentative permutation key)
        (attackEnvironment permutation) 1 = [(q0, some r0)] := by
      rw [show 1 = 0 + 1 by omega, transcript_succ_fire hfire0]
      simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil,
        List.nil_append]
      have hanswer := realAnswer key [] q0
      simp only [List.nil_append] at hanswer
      rw [hanswer]
      simp [q0, r0, emptyResponse, spocOracle, emptyEncryptionQuery]
    have hfire1 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (spocRepresentative permutation key) (attackEnvironment permutation) 1)) =
        some q1 := by
      rw [htr1]
      rfl
    have htr2 : PFunDDS.transcript (spocRepresentative permutation key)
        (attackEnvironment permutation) 2 =
        [(q0, some r0), (q1, some r1)] := by
      rw [show 2 = 1 + 1 by omega, transcript_succ_fire hfire1, htr1]
      simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
      rw [realAnswer key [q0] q1]
      simp [q1, r1, oneBlockResponse, spocOracle, oneBlockEncryptionQuery]
    have hfire2 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (spocRepresentative permutation key) (attackEnvironment permutation) 2)) =
        some q2 := by
      rw [htr2]
      simp only [PFunDDS.transcriptOutputs, List.map_cons, List.map_nil]
      change some (Sum.inr (forgedDecryptionQuery permutation
        emptyResponse oneBlockResponse)) = some q2
      dsimp only [forgedDecryptionQuery, q2, forged]
      rw [show recoveredKey permutation emptyResponse oneBlockResponse = key by
        dsimp only [emptyResponse, oneBlockResponse]
        exact recovered_key permutation key]
    rw [show 3 = 2 + 1 by omega, transcript_succ_fire hfire2, htr2]
    simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
    rw [realAnswer key [q0, q1] q2]
    simp [q0, q1, q2, r0, r1, emptyResponse, oneBlockResponse, forged,
      spocOracle, emptyEncryptionQuery, oneBlockEncryptionQuery, spoc_correct]
  have idealTranscript (key : Block) :
      let emptyResponse := encrypt permutation key 0 [] []
      let oneBlockResponse := encrypt permutation key tagControl [] [0]
      let forged := encrypt permutation key 0 [] [0]
      PFunDDS.transcript (idealRepresentative permutation key)
        (attackEnvironment permutation) 3 =
        [(Sum.inl emptyEncryptionQuery, some (Sum.inl emptyResponse)),
         (Sum.inl oneBlockEncryptionQuery, some (Sum.inl oneBlockResponse)),
         (Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩,
          some (Sum.inr ⟨false, []⟩))] := by
    let emptyResponse := encrypt permutation key 0 [] []
    let oneBlockResponse := encrypt permutation key tagControl [] [0]
    let forged := encrypt permutation key 0 [] [0]
    let q0 : Query := Sum.inl emptyEncryptionQuery
    let q1 : Query := Sum.inl oneBlockEncryptionQuery
    let q2 : Query := Sum.inr ⟨0, [], forged.ciphertext, forged.tag⟩
    let r0 : Response := Sum.inl emptyResponse
    let r1 : Response := Sum.inl oneBlockResponse
    have hfire0 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (idealRepresentative permutation key) (attackEnvironment permutation) 0)) =
        some q0 := rfl
    have htr1 : PFunDDS.transcript (idealRepresentative permutation key)
        (attackEnvironment permutation) 1 = [(q0, some r0)] := by
      rw [show 1 = 0 + 1 by omega, transcript_succ_fire hfire0]
      simp only [PFunDDS.transcript, PFunDDS.transcriptInputs, List.map_nil,
        List.nil_append]
      have hanswer := idealAnswer key [] q0
      simp only [List.nil_append] at hanswer
      rw [hanswer]
      simp [q0, r0, emptyResponse, idealOracle, emptyEncryptionQuery]
    have hfire1 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (idealRepresentative permutation key) (attackEnvironment permutation) 1)) =
        some q1 := by
      rw [htr1]
      rfl
    have htr2 : PFunDDS.transcript (idealRepresentative permutation key)
        (attackEnvironment permutation) 2 =
        [(q0, some r0), (q1, some r1)] := by
      rw [show 2 = 1 + 1 by omega, transcript_succ_fire hfire1, htr1]
      simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
      rw [idealAnswer key [q0] q1]
      simp [q0, q1, r1, oneBlockResponse, idealOracle,
        oneBlockEncryptionQuery]
    have hfire2 : attackEnvironment permutation
        (PFunDDS.transcriptOutputs (PFunDDS.transcript
          (idealRepresentative permutation key) (attackEnvironment permutation) 2)) =
        some q2 := by
      rw [htr2]
      simp only [PFunDDS.transcriptOutputs, List.map_cons, List.map_nil]
      change some (Sum.inr (forgedDecryptionQuery permutation
        emptyResponse oneBlockResponse)) = some q2
      dsimp only [forgedDecryptionQuery, q2, forged]
      rw [show recoveredKey permutation emptyResponse oneBlockResponse = key by
        dsimp only [emptyResponse, oneBlockResponse]
        exact recovered_key permutation key]
    rw [show 3 = 2 + 1 by omega, transcript_succ_fire hfire2, htr2]
    simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil]
    rw [idealAnswer key [q0, q1] q2]
    have hnonce : tagControl ≠ (0 : Block) := by decide
    have hcipher : emptyResponse.ciphertext ≠ forged.ciphertext := by
      simp [emptyResponse, forged, encrypt, absorbBlocks, cryptBlocks]
    simp [q0, q1, q2, r0, r1, emptyResponse, oneBlockResponse, forged,
      idealOracle, idealDecrypt, emptyEncryptionQuery, oneBlockEncryptionQuery]
    split <;> rename_i hfirst
    · exact (hcipher hfirst.1).elim
    · split <;> rename_i hsecond
      · exact (hnonce hsecond.1).elim
      · rfl
  have realVerdict (key : Block) :
      PFunDDS.verdict (attackDistinguisher permutation)
        (spocRepresentative permutation key) := by
    change PFunDDS.verdict
      (PFunDDS.DDD.ofDDE (attackEnvironment permutation) 3 verificationVerdict)
      (spocRepresentative permutation key)
    rw [verdict_ofDDE_iff, realTranscript key]
    simp [verificationVerdict]
  have idealNoVerdict (key : Block) :
      ¬ PFunDDS.verdict (attackDistinguisher permutation)
        (idealRepresentative permutation key) := by
    change ¬ PFunDDS.verdict
      (PFunDDS.DDD.ofDDE (attackEnvironment permutation) 3 verificationVerdict)
      (idealRepresentative permutation key)
    rw [verdict_ofDDE_iff, idealTranscript key]
    simp [verificationVerdict]
  unfold distinguishingAdvantage advantage attackDistinguisherDistribution
  rw [verdictProb_single, verdictProb_single]
  unfold idealSystem spocPDS
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  have hreal : (Dist.uniform Block).mass
      (fun key => PFunDDS.verdict (attackDistinguisher permutation)
        (spocRepresentative permutation key)) = 1 := by
    calc
      _ = (Dist.uniform Block).mass (fun _ => True) :=
        Dist.mass_congr _ fun key => iff_of_true (realVerdict key) trivial
      _ = (Dist.uniform Block).weight := Dist.mass_true _
      _ = 1 := Dist.uniform_isProbDist.weight_eq
  have hideal : (Dist.uniform Block).mass
      (fun key => PFunDDS.verdict (attackDistinguisher permutation)
        (idealRepresentative permutation key)) = 0 := by
    exact Dist.mass_eq_zero_of_forall_not _ idealNoVerdict
  rw [hreal, hideal]
  norm_num

end RandomSystems.SpoC
