/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.AEAD.Game
import RandomSystems.HCTR2BitStrings
import RandomSystems.ResourceView
import RandomSystems.StepConverter

/-! Block-aligned SpoC-128 over a 256-bit permutation. -/

namespace RandomSystems.SpoC

open RandomSystems.CR18
open RandomSystems.HCTR2Final.Bits
open scoped RandomSystems.CR18.PFunDDS
open scoped RandomSystems.HCTR2Final.Bits

abbrev Block := BitString 128
abbrev State := BitString 256

abbrev EncryptQuery := AEAD.EncryptQuery Block (List Block) (List Block)
abbrev DecryptQuery := AEAD.DecryptQuery Block (List Block) (List Block) Block
abbrev Query := AEAD.Query Block (List Block) (List Block) (List Block) Block
abbrev EncryptResponse := AEAD.EncryptResponse (List Block) Block
abbrev DecryptResponse := AEAD.DecryptResponse (List Block)
abbrev Response := AEAD.Response (List Block) (List Block) Block

def capacity (s : State) : Block := s[0; 128]
def rate (s : State) : Block := s[128; 128]
def state (y z : Block) : State := y ∥ z

def controlWord (tag plaintext associatedData partialBlock : Bool) : Block :=
  (if tag then 0x80 else 0) |||
  (if plaintext then 0x40 else 0) |||
  (if associatedData then 0x20 else 0) |||
  (if partialBlock then 0x10 else 0)

def fullADControl : Block := controlWord false false true false
def fullPTControl : Block := controlWord false true false false
def tagControl : Block := controlWord true false false false

def load (key nonce : Block) : State := state key nonce

def absorbAD (block : Block) (output : State) : State :=
  state (capacity output ^^^ block) (rate output ^^^ fullADControl)

def processData (decrypt : Bool) (block : Block) (output : State) : State × Block :=
  let plaintext := if decrypt then rate output ^^^ block else block
  let result := if decrypt then plaintext else rate output ^^^ block
  (state (capacity output ^^^ plaintext) (rate output ^^^ fullPTControl), result)

def afterAD (key nonce : Block) (ad : List Block) (answers : List State) : State :=
  (List.zip ad answers).foldl
    (fun _ pair => absorbAD pair.1 pair.2)
    (load key nonce)

def processBlocks (decrypt : Bool) (s : State) :
    List Block → List State → State × List Block
  | block :: blocks, output :: outputs =>
      let next := processData decrypt block output
      let rest := processBlocks decrypt next.1 blocks outputs
      (rest.1, next.2 :: rest.2)
  | _, _ => (s, [])

def afterData (key nonce : Block) (ad data : List Block) (decrypt : Bool)
    (answers : List State) : State × List Block :=
  let initial := afterAD key nonce ad (answers.take ad.length)
  processBlocks decrypt initial data (answers.drop ad.length)

def tagInput (s : State) : State :=
  state (capacity s) (rate s ^^^ tagControl)

def process (key nonce : Block) (ad data : List Block) (decrypt : Bool)
    (answers : List State) : State ⊕ (List Block × Block) :=
  if answers.length < ad.length then
    Sum.inl (afterAD key nonce ad answers)
  else
    let processed := afterData key nonce ad data decrypt answers
    if answers.length < ad.length + data.length then
      Sum.inl processed.1
    else if answers.length = ad.length + data.length then
      Sum.inl (tagInput processed.1)
    else
      Sum.inr (processed.2, capacity (answers.getD (ad.length + data.length) 0))

def absorbBlocks (permutation : State → State) : State → List Block → State
  | s, [] => s
  | s, block :: blocks =>
      absorbBlocks permutation (absorbAD block (permutation s)) blocks

def cryptBlocks (permutation : State → State) (decrypting : Bool) :
    State → List Block → State × List Block
  | s, [] => (s, [])
  | s, block :: blocks =>
      let next := processData decrypting block (permutation s)
      let rest := cryptBlocks permutation decrypting next.1 blocks
      (rest.1, next.2 :: rest.2)

def encrypt (permutation : State → State) (key nonce : Block)
    (ad plaintext : List Block) : EncryptResponse :=
  let s := absorbBlocks permutation (load key nonce) ad
  let result := cryptBlocks permutation false s plaintext
  ⟨result.2, capacity (permutation (tagInput result.1))⟩

def decrypt (permutation : State → State) (key nonce : Block)
    (ad ciphertext : List Block) (tag : Block) : DecryptResponse :=
  let s := absorbBlocks permutation (load key nonce) ad
  let result := cryptBlocks permutation true s ciphertext
  if capacity (permutation (tagInput result.1)) = tag then
    ⟨true, result.2⟩
  else
    ⟨false, []⟩

def spoc (key : Block) (query : Query) (answers : List State) : State ⊕ Response :=
  match query with
  | Sum.inl query =>
      match process key query.nonce query.associatedData query.plaintext false answers with
      | Sum.inl permutationInput => Sum.inl permutationInput
      | Sum.inr result => Sum.inr (Sum.inl ⟨result.1, result.2⟩)
  | Sum.inr query =>
      match process key query.nonce query.associatedData query.ciphertext true answers with
      | Sum.inl permutationInput => Sum.inl permutationInput
      | Sum.inr result =>
          if result.2 = query.tag then
            Sum.inr (Sum.inr ⟨true, result.1⟩)
          else
            Sum.inr (Sum.inr ⟨false, []⟩)

def spocDDC (key : Block) : PFunConverter.DDC Query Response State State :=
  PFunConverter.DDC.ofStep (spoc key)

def spocOracle (permutation : State → State) (key : Block) : Query → Response
  | Sum.inl query =>
      Sum.inl (encrypt permutation key query.nonce query.associatedData query.plaintext)
  | Sum.inr query =>
      Sum.inr (decrypt permutation key query.nonce query.associatedData
        query.ciphertext query.tag)

noncomputable def spocRepresentative
    (permutation : Equiv.Perm State) (key : Block) : PFunDDS.DDS Query Response :=
  PFunDDS.functionEvaluator (spocOracle permutation key)

noncomputable def spocPDS (permutation : Equiv.Perm State) :
    PFunPDS.Prob Query Response :=
  ⟨Dist.fTransform (spocRepresentative permutation) (Dist.uniform Block),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

theorem spoc_correct (permutation : State → State) (key nonce : Block)
    (ad plaintext : List Block) :
    let result := encrypt permutation key nonce ad plaintext
    decrypt permutation key nonce ad result.ciphertext result.tag = ⟨true, plaintext⟩ := by
  have blocksCorrect : ∀ (blocks : List Block) (s : State),
      cryptBlocks permutation true s (cryptBlocks permutation false s blocks).2 =
        ((cryptBlocks permutation false s blocks).1, blocks) := by
    intro blocks
    induction blocks with
    | nil => simp [cryptBlocks]
    | cons block blocks ih =>
        intro s
        have hxor : rate (permutation s) ^^^
            (rate (permutation s) ^^^ block) = block := by
          rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
        have hstate :
            (processData true (processData false block (permutation s)).2
              (permutation s)).1 =
              (processData false block (permutation s)).1 := by
          simp [processData, hxor]
        have hplain :
            (processData true (processData false block (permutation s)).2
              (permutation s)).2 = block := by
          simpa [processData] using hxor
        simp only [cryptBlocks]
        rw [hstate, hplain, ih]
  simp only [encrypt, decrypt]
  rw [blocksCorrect]
  simp

theorem spocPDS_correct (permutations : Dist.ProbDist (State → State))
    (key nonce : Block) (ad plaintext : List Block) :
    permutations.val.mass
      (fun permutation =>
        let result := encrypt permutation key nonce ad plaintext
        decrypt permutation key nonce ad result.ciphertext result.tag =
          ⟨true, plaintext⟩) = 1 := by
  calc
    _ = permutations.val.mass (fun _ => True) :=
      Dist.mass_congr permutations.val (fun permutation =>
        iff_of_true (spoc_correct permutation key nonce ad plaintext) trivial)
    _ = permutations.val.weight := Dist.mass_true _
    _ = 1 := permutations.property.weight_eq

open scoped RandomSystems.CR18.PFunConverter.DDC

namespace Coherence

def absorbInputs (permutation : State → State) : State → List Block → List State
  | _, [] => []
  | s, block :: blocks =>
      s :: absorbInputs permutation (absorbAD block (permutation s)) blocks

def dataInputs (permutation : State → State) (decrypting : Bool) :
    State → List Block → List State
  | _, [] => []
  | s, block :: blocks =>
      s :: dataInputs permutation decrypting
        (processData decrypting block (permutation s)).1 blocks

@[simp] theorem length_absorbInputs (permutation : State → State)
    (s : State) (blocks : List Block) :
    (absorbInputs permutation s blocks).length = blocks.length := by
  induction blocks generalizing s with
  | nil => rfl
  | cons block blocks ih => simp [absorbInputs, ih]

@[simp] theorem length_dataInputs (permutation : State → State) (decrypting : Bool)
    (s : State) (blocks : List Block) :
    (dataInputs permutation decrypting s blocks).length = blocks.length := by
  induction blocks generalizing s with
  | nil => rfl
  | cons block blocks ih => simp [dataInputs, ih]

theorem fold_absorbInputs (permutation : State → State) (s : State)
    (blocks : List Block) :
    (List.zip blocks ((absorbInputs permutation s blocks).map permutation)).foldl
      (fun _ pair => absorbAD pair.1 pair.2) s =
      absorbBlocks permutation s blocks := by
  induction blocks generalizing s with
  | nil => rfl
  | cons block blocks ih =>
      simp only [absorbInputs, List.map_cons, List.zip_cons_cons, List.foldl_cons,
        absorbBlocks]
      exact ih _

theorem processBlocks_dataInputs (permutation : State → State)
    (decrypting : Bool) (s : State) (blocks : List Block) (extra : List State) :
    processBlocks decrypting s blocks
        ((dataInputs permutation decrypting s blocks).map permutation ++ extra) =
      cryptBlocks permutation decrypting s blocks := by
  induction blocks generalizing s with
  | nil => rfl
  | cons block blocks ih =>
      simp only [dataInputs, List.map_cons, List.cons_append, processBlocks, cryptBlocks]
      rw [ih]

theorem fold_absorbInputs_take (permutation : State → State) (s : State)
    (blocks : List Block) (i : ℕ) :
    (List.zip blocks ((absorbInputs permutation s blocks).take i |>.map permutation)).foldl
        (fun _ pair => absorbAD pair.1 pair.2) s =
      absorbBlocks permutation s (blocks.take i) := by
  induction blocks generalizing s i with
  | nil => simp [absorbInputs, absorbBlocks]
  | cons block blocks ih =>
      cases i with
      | zero => simp [absorbInputs, absorbBlocks]
      | succ i =>
          simp only [absorbInputs, List.take_succ_cons, List.map_cons, List.zip_cons_cons,
            List.foldl_cons, absorbBlocks]
          exact ih _ _

theorem absorbInputs_getD (permutation : State → State) (s : State)
    (blocks : List Block) (i : ℕ) (hi : i < blocks.length) :
    (absorbInputs permutation s blocks).getD i 0 =
      absorbBlocks permutation s (blocks.take i) := by
  induction blocks generalizing s i with
  | nil => simp at hi
  | cons block blocks ih =>
      cases i with
      | zero => simp [absorbInputs, absorbBlocks]
      | succ i =>
          simp only [absorbInputs, List.getD_cons_succ, List.take_succ_cons, absorbBlocks]
          exact ih _ _ (by simp at hi; omega)

theorem processBlocks_dataInputs_take (permutation : State → State)
    (decrypting : Bool) (s : State) (blocks : List Block) (i : ℕ) :
    (processBlocks decrypting s blocks
      ((dataInputs permutation decrypting s blocks).take i |>.map permutation)).1 =
      (cryptBlocks permutation decrypting s (blocks.take i)).1 := by
  induction blocks generalizing s i with
  | nil => simp [processBlocks, cryptBlocks]
  | cons block blocks ih =>
      cases i with
      | zero => simp [dataInputs, processBlocks, cryptBlocks]
      | succ i =>
          simp only [dataInputs, List.take_succ_cons, List.map_cons, processBlocks,
            cryptBlocks]
          exact ih _ _

theorem dataInputs_getD (permutation : State → State) (decrypting : Bool)
    (s : State) (blocks : List Block) (i : ℕ) (hi : i < blocks.length) :
    (dataInputs permutation decrypting s blocks).getD i 0 =
      (cryptBlocks permutation decrypting s (blocks.take i)).1 := by
  induction blocks generalizing s i with
  | nil => simp at hi
  | cons block blocks ih =>
      cases i with
      | zero => simp [dataInputs, cryptBlocks]
      | succ i =>
          simp only [dataInputs, List.getD_cons_succ, List.take_succ_cons, cryptBlocks]
          exact ih _ _ (by simp at hi; omega)

def spocCalls (permutation : State → State) (key : Block) (query : Query) : List State :=
  match query with
  | Sum.inl query =>
      let afterAssociatedData :=
        absorbBlocks permutation (load key query.nonce) query.associatedData
      let afterPlaintext :=
        cryptBlocks permutation false afterAssociatedData query.plaintext
      absorbInputs permutation (load key query.nonce) query.associatedData ++
        dataInputs permutation false afterAssociatedData query.plaintext ++
        [tagInput afterPlaintext.1]
  | Sum.inr query =>
      let afterAssociatedData :=
        absorbBlocks permutation (load key query.nonce) query.associatedData
      let afterCiphertext :=
        cryptBlocks permutation true afterAssociatedData query.ciphertext
      absorbInputs permutation (load key query.nonce) query.associatedData ++
        dataInputs permutation true afterAssociatedData query.ciphertext ++
        [tagInput afterCiphertext.1]

theorem spoc_full_answers (permutation : State → State) (key : Block) (query : Query) :
    spoc key query ((spocCalls permutation key query).map permutation) =
      Sum.inr (spocOracle permutation key query) := by
  rcases query with encryption | decryption
  · let initial := load key encryption.nonce
    let afterAssociatedData := absorbBlocks permutation initial encryption.associatedData
    let result := cryptBlocks permutation false afterAssociatedData encryption.plaintext
    let adInputs := absorbInputs permutation initial encryption.associatedData
    let data := dataInputs permutation false afterAssociatedData encryption.plaintext
    let finalInput := tagInput result.1
    change spoc key (Sum.inl encryption) ((adInputs ++ data ++ [finalInput]).map permutation) = _
    rw [List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil, spoc, spocOracle]
    have hadLength : adInputs.length = encryption.associatedData.length := by
      simp [adInputs]
    have hdataLength : data.length = encryption.plaintext.length := by
      simp [data]
    have htake :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).take
            encryption.associatedData.length = adInputs.map permutation := by
      rw [← hadLength, ← List.length_map (as := adInputs) permutation,
        List.append_assoc, List.take_left]
    have hdrop :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).drop
            encryption.associatedData.length = data.map permutation ++ [permutation finalInput] := by
      rw [← hadLength, ← List.length_map (as := adInputs) permutation,
        List.append_assoc, List.drop_left]
    have hafter :
        afterAD key encryption.nonce encryption.associatedData (adInputs.map permutation) =
          afterAssociatedData := by
      exact fold_absorbInputs permutation initial encryption.associatedData
    have hblocks :
        processBlocks false afterAssociatedData encryption.plaintext
            (data.map permutation ++ [permutation finalInput]) = result := by
      exact processBlocks_dataInputs permutation false afterAssociatedData
        encryption.plaintext [permutation finalInput]
    have hget :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).getD
            (encryption.associatedData.length + encryption.plaintext.length) 0 =
          permutation finalInput := by
      rw [List.getD_append_right (adInputs.map permutation ++ data.map permutation)
        [permutation finalInput] 0 _ (by simp [hadLength, hdataLength])]
      simp [hadLength, hdataLength]
    unfold process
    simp only [List.length_append, List.length_map, hadLength, hdataLength,
      List.length_cons, List.length_nil]
    rw [if_neg (by omega)]
    simp only [afterData, htake, hdrop, hafter, hblocks]
    rw [if_neg (by omega), if_neg (by omega), hget]
    rfl
  · let initial := load key decryption.nonce
    let afterAssociatedData := absorbBlocks permutation initial decryption.associatedData
    let result := cryptBlocks permutation true afterAssociatedData decryption.ciphertext
    let adInputs := absorbInputs permutation initial decryption.associatedData
    let data := dataInputs permutation true afterAssociatedData decryption.ciphertext
    let finalInput := tagInput result.1
    change spoc key (Sum.inr decryption) ((adInputs ++ data ++ [finalInput]).map permutation) = _
    rw [List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil, spoc, spocOracle]
    have hadLength : adInputs.length = decryption.associatedData.length := by
      simp [adInputs]
    have hdataLength : data.length = decryption.ciphertext.length := by
      simp [data]
    have htake :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).take
            decryption.associatedData.length = adInputs.map permutation := by
      rw [← hadLength, ← List.length_map (as := adInputs) permutation,
        List.append_assoc, List.take_left]
    have hdrop :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).drop
            decryption.associatedData.length = data.map permutation ++ [permutation finalInput] := by
      rw [← hadLength, ← List.length_map (as := adInputs) permutation,
        List.append_assoc, List.drop_left]
    have hafter :
        afterAD key decryption.nonce decryption.associatedData (adInputs.map permutation) =
          afterAssociatedData := by
      exact fold_absorbInputs permutation initial decryption.associatedData
    have hblocks :
        processBlocks true afterAssociatedData decryption.ciphertext
            (data.map permutation ++ [permutation finalInput]) = result := by
      exact processBlocks_dataInputs permutation true afterAssociatedData
        decryption.ciphertext [permutation finalInput]
    have hget :
        (adInputs.map permutation ++ data.map permutation ++ [permutation finalInput]).getD
            (decryption.associatedData.length + decryption.ciphertext.length) 0 =
          permutation finalInput := by
      rw [List.getD_append_right (adInputs.map permutation ++ data.map permutation)
        [permutation finalInput] 0 _ (by simp [hadLength, hdataLength])]
      simp [hadLength, hdataLength]
    unfold process
    simp only [List.length_append, List.length_map, hadLength, hdataLength,
      List.length_cons, List.length_nil]
    rw [if_neg (by omega)]
    simp only [afterData, htake, hdrop, hafter, hblocks]
    rw [if_neg (by omega), if_neg (by omega), hget]
    by_cases htag : capacity (permutation finalInput) = decryption.tag
    · simp [decrypt, initial, afterAssociatedData, result, finalInput, htag]
    · simp [decrypt, initial, afterAssociatedData, result, finalInput, htag]

def processCalls (permutation : State → State) (key nonce : Block)
    (ad data : List Block) (decrypting : Bool) : List State :=
  let afterAssociatedData := absorbBlocks permutation (load key nonce) ad
  let result := cryptBlocks permutation decrypting afterAssociatedData data
  absorbInputs permutation (load key nonce) ad ++
    dataInputs permutation decrypting afterAssociatedData data ++
    [tagInput result.1]

theorem process_prefix_answers (permutation : State → State) (key nonce : Block)
    (ad dataBlocks : List Block) (decrypting : Bool) (i : ℕ)
    (hi : i < (processCalls permutation key nonce ad dataBlocks decrypting).length) :
    process key nonce ad dataBlocks decrypting
        (((processCalls permutation key nonce ad dataBlocks decrypting).take i).map permutation) =
      Sum.inl ((processCalls permutation key nonce ad dataBlocks decrypting).getD i 0) := by
  let initial := load key nonce
  let afterAssociatedData := absorbBlocks permutation initial ad
  let result := cryptBlocks permutation decrypting afterAssociatedData dataBlocks
  let adInputs := absorbInputs permutation initial ad
  let data := dataInputs permutation decrypting afterAssociatedData dataBlocks
  let finalInput := tagInput result.1
  change process key nonce ad dataBlocks decrypting
      (((adInputs ++ data ++ [finalInput]).take i).map permutation) =
    Sum.inl ((adInputs ++ data ++ [finalInput]).getD i 0)
  change i < (adInputs ++ data ++ [finalInput]).length at hi
  have hadLength : adInputs.length = ad.length := by simp [adInputs]
  have hdataLength : data.length = dataBlocks.length := by simp [data]
  by_cases hiAD : i < ad.length
  · have htake : (adInputs ++ data ++ [finalInput]).take i = adInputs.take i := by
      rw [List.append_assoc, List.take_append_of_le_length]
      omega
    have hget : (adInputs ++ data ++ [finalInput]).getD i 0 = adInputs.getD i 0 := by
      rw [List.append_assoc, List.getD_append]
      simpa [hadLength] using hiAD
    rw [htake, hget]
    unfold process
    rw [if_pos (by simpa [hadLength] using hiAD)]
    congr 1
    calc
      afterAD key nonce ad ((adInputs.take i).map permutation) =
          absorbBlocks permutation initial (ad.take i) :=
        fold_absorbInputs_take permutation initial ad i
      _ = adInputs.getD i 0 :=
        (absorbInputs_getD permutation initial ad i hiAD).symm
  · let j := i - ad.length
    by_cases hiData : j < dataBlocks.length
    · have hiEq : i = adInputs.length + j := by
        dsimp only [j]
        rw [hadLength]
        omega
      have htake : (adInputs ++ data ++ [finalInput]).take i =
          adInputs ++ data.take j := by
        rw [List.append_assoc, List.take_append, hiEq]
        simp only [Nat.add_sub_cancel_left]
        rw [List.take_of_length_le (by omega), List.take_append_of_le_length]
        simpa [hdataLength] using Nat.le_of_lt hiData
      have hget : (adInputs ++ data ++ [finalInput]).getD i 0 = data.getD j 0 := by
        rw [List.append_assoc, List.getD_append_right adInputs
          (data ++ [finalInput]) 0 i (by omega)]
        have hsub : i - adInputs.length = j := by simp [j, hadLength]
        rw [hsub, List.getD_append]
        simpa [hdataLength] using hiData
      have htakeAnswers :
          (adInputs.map permutation ++ (data.map permutation).take j).take ad.length =
            adInputs.map permutation := by
        rw [← hadLength, ← List.length_map (as := adInputs) permutation, List.take_left]
      have hdropAnswers :
          (adInputs.map permutation ++ (data.map permutation).take j).drop ad.length =
            (data.map permutation).take j := by
        rw [← hadLength, ← List.length_map (as := adInputs) permutation, List.drop_left]
      rw [htake, hget, List.map_append, List.map_take]
      unfold process
      simp only [List.length_append, List.length_map, hadLength, List.length_take,
        hdataLength, Nat.min_eq_left (Nat.le_of_lt hiData)]
      rw [if_neg (by omega), if_pos (by dsimp only [j] at hiData ⊢; omega)]
      simp only [afterData, htakeAnswers, hdropAnswers]
      rw [show afterAD key nonce ad (adInputs.map permutation) = afterAssociatedData by
        exact fold_absorbInputs permutation initial ad]
      congr 1
      calc
        (processBlocks decrypting afterAssociatedData dataBlocks
          ((data.map permutation).take j)).1 =
            (cryptBlocks permutation decrypting afterAssociatedData
              (dataBlocks.take j)).1 :=
          by simpa only [List.map_take] using
            processBlocks_dataInputs_take permutation decrypting afterAssociatedData dataBlocks j
        _ = data.getD j 0 :=
          (dataInputs_getD permutation decrypting afterAssociatedData
            dataBlocks j hiData).symm
    · have hjEq : j = dataBlocks.length := by
        have hcallLength : (adInputs ++ data ++ [finalInput]).length =
            ad.length + dataBlocks.length + 1 := by
          simp [hadLength, hdataLength]
          omega
        rw [hcallLength] at hi
        dsimp only [j] at hiData ⊢
        omega
      have hiEq : i = adInputs.length + data.length := by
        rw [hadLength, hdataLength, ← hjEq]
        dsimp only [j]
        omega
      have htake : (adInputs ++ data ++ [finalInput]).take i = adInputs ++ data := by
        rw [hiEq, ← List.length_append, List.take_left]
      have hget : (adInputs ++ data ++ [finalInput]).getD i 0 = finalInput := by
        have hiLength : i = (adInputs ++ data).length := by simp [hiEq]
        rw [hiLength, List.getD_append_right (adInputs ++ data) [finalInput]
          0 (adInputs ++ data).length (le_refl _)]
        simp
      have htakeAnswers :
          (adInputs.map permutation ++ data.map permutation).take ad.length =
            adInputs.map permutation := by
        rw [← hadLength, ← List.length_map (as := adInputs) permutation, List.take_left]
      have hdropAnswers :
          (adInputs.map permutation ++ data.map permutation).drop ad.length =
            data.map permutation := by
        rw [← hadLength, ← List.length_map (as := adInputs) permutation, List.drop_left]
      rw [htake, hget, List.map_append]
      have hanswerLength :
          (adInputs.map permutation ++ data.map permutation).length =
            ad.length + dataBlocks.length := by
        simp [hadLength, hdataLength]
      unfold process
      rw [if_neg (by rw [hanswerLength]; omega),
        if_neg (by rw [hanswerLength]; omega), if_pos hanswerLength]
      simp only [afterData, htakeAnswers, hdropAnswers]
      rw [show afterAD key nonce ad (adInputs.map permutation) = afterAssociatedData by
        exact fold_absorbInputs permutation initial ad]
      have hblocks :
          processBlocks decrypting afterAssociatedData dataBlocks (data.map permutation) =
            result := by
        simpa [data, result] using
          processBlocks_dataInputs permutation decrypting afterAssociatedData dataBlocks []
      rw [hblocks]

theorem spoc_prefix_answers (permutation : State → State) (key : Block)
    (query : Query) (i : ℕ) (hi : i < (spocCalls permutation key query).length) :
    spoc key query (((spocCalls permutation key query).take i).map permutation) =
      Sum.inl ((spocCalls permutation key query).getD i 0) := by
  rcases query with encryption | decryption
  · simp only [spocCalls] at hi ⊢
    have h := process_prefix_answers permutation key encryption.nonce
      encryption.associatedData encryption.plaintext false i (by simpa [processCalls] using hi)
    simp only [processCalls] at h
    rw [spoc, h]
  · simp only [spocCalls] at hi ⊢
    have h := process_prefix_answers permutation key decryption.nonce
      decryption.associatedData decryption.ciphertext true i (by simpa [processCalls] using hi)
    simp only [processCalls] at h
    rw [spoc, h]

theorem driveG_of_trace {V : Type*}
    (step : List State → State ⊕ V) (permutation : State → State)
    (calls : List State) (answer : V)
    (hprefix : ∀ i, i < calls.length →
      step ((calls.take i).map permutation) = Sum.inl (calls.getD i 0))
    (hfull : step (calls.map permutation) = Sum.inr answer) (n : ℕ) (xs : List State) :
    CausalApply.driveG step (PFunDDS.functionEvaluator permutation).1
        (n + calls.length + 1) xs [] =
      Part.some (answer, xs ++ calls) := by
  have hquery : ∀ (pre : List State) (x : State) (rest : List State),
      calls = pre ++ x :: rest → step (pre.map permutation) = Sum.inl x := by
    intro pre x rest hdecomp
    have h := hprefix pre.length (by simp [hdecomp])
    simpa [hdecomp] using h
  have aux : ∀ (rest pre : List State) (n : ℕ) (xs : List State),
      calls = pre ++ rest →
      CausalApply.driveG step (PFunDDS.functionEvaluator permutation).1
          (n + rest.length + 1) (xs ++ pre) (pre.map permutation) =
        Part.some (answer, xs ++ calls) := by
    intro rest
    induction rest with
    | nil =>
        intro pre n xs hdecomp
        simp only [List.append_nil] at hdecomp
        subst calls
        simp only [List.length_nil, Nat.add_zero]
        rw [CausalApply.driveG, hfull]
    | cons x rest ih =>
        intro pre n xs hdecomp
        have hstep := hquery pre x rest hdecomp
        have hdecomp' : calls = (pre ++ [x]) ++ rest := by
          simpa [List.append_assoc] using hdecomp
        have htail := ih (pre ++ [x]) n xs hdecomp'
        have hfuel : n + (x :: rest).length + 1 = (n + rest.length + 1) + 1 := by
          simp
          omega
        rw [hfuel]
        rw [CausalApply.driveG, hstep]
        change ((PFunDDS.functionEvaluator permutation).1 ((xs ++ pre) ++ [x])).bind
            (fun y => CausalApply.driveG step (PFunDDS.functionEvaluator permutation).1
              (n + rest.length + 1) ((xs ++ pre) ++ [x])
              (pre.map permutation ++ [y])) =
          Part.some (answer, xs ++ calls)
        rw [CausalApply.functionEvaluator_raw_append, Part.bind_some]
        simpa [List.map_append, List.append_assoc] using htail
  simpa using aux calls [] n xs (by simp)

theorem driveG_spoc (permutation : State → State) (key : Block) (query : Query)
    (n : ℕ) (xs : List State) :
    CausalApply.driveG (spoc key query) (PFunDDS.functionEvaluator permutation).1
        (n + (spocCalls permutation key query).length + 1) xs [] =
      Part.some (spocOracle permutation key query, xs ++ spocCalls permutation key query) := by
  exact driveG_of_trace (spoc key query) permutation (spocCalls permutation key query)
    (spocOracle permutation key query)
    (spoc_prefix_answers permutation key query) (spoc_full_answers permutation key query) n xs

theorem driveOuter_of_round {U V X Y : Type*}
    (step : U → List Y → X ⊕ V) (f : X → Y) (g : U → V)
    (calls : U → List X) (count : U → ℕ)
    (hround : ∀ (u : U) (n : ℕ) (xs : List X),
      CausalApply.driveG (step u) (PFunDDS.functionEvaluator f).1
          (n + count u + 1) xs [] =
        Part.some (g u, xs ++ calls u)) :
    ∀ (queries : List U) (xs : List X) (fuel : ℕ),
      (∀ u ∈ queries, count u < fuel) →
      CausalApply.driveOuter step (PFunDDS.functionEvaluator f).1 fuel xs queries =
        Part.some (queries.map g, xs ++ queries.flatMap calls) := by
  intro queries
  induction queries with
  | nil =>
      intro xs fuel _
      simp [CausalApply.driveOuter]
  | cons query queries ih =>
      intro xs fuel hfuel
      have hquery : count query < fuel := hfuel query (by simp)
      have hrest : ∀ u ∈ queries, count u < fuel := by
        intro u hu
        exact hfuel u (by simp [hu])
      let n := fuel - count query - 1
      have hfuel : n + count query + 1 = fuel := by
        dsimp only [n]
        omega
      have hfirst := hround query n xs
      rw [hfuel] at hfirst
      simp only [CausalApply.driveOuter, hfirst, Part.bind_some,
        ih _ _ hrest, Part.map_some]
      simp [List.append_assoc]

def historyCallBound (permutation : State → State) (key : Block)
    (queries : List Query) : ℕ :=
  (queries.map fun query => (spocCalls permutation key query).length).foldr max 0

theorem callCount_lt_historyCallBound_succ (permutation : State → State)
    (key : Block) (queries : List Query) (query : Query) (hquery : query ∈ queries) :
    (spocCalls permutation key query).length <
      historyCallBound permutation key queries + 1 := by
  have hmem : (spocCalls permutation key query).length ∈
      queries.map (fun q => (spocCalls permutation key q).length) :=
    List.mem_map.mpr ⟨query, hquery, rfl⟩
  have hle := List.le_max_of_le' 0 hmem (le_refl _)
  dsimp only [historyCallBound]
  omega

theorem driveOuter_spoc (permutation : State → State) (key : Block)
    (queries : List Query) (xs : List State) (fuel : ℕ)
    (hfuel : ∀ query ∈ queries, (spocCalls permutation key query).length < fuel) :
    CausalApply.driveOuter (spoc key) (PFunDDS.functionEvaluator permutation).1
        fuel xs queries =
      Part.some (queries.map (spocOracle permutation key),
        xs ++ queries.flatMap (spocCalls permutation key)) := by
  exact driveOuter_of_round (spoc key) permutation (spocOracle permutation key)
    (spocCalls permutation key) (fun query => (spocCalls permutation key query).length)
    (driveG_spoc permutation key) queries xs fuel hfuel

end Coherence

open Coherence

theorem spocDDC_apply (permutation : State → State) (key : Block) :
    (spocDDC key ·ᶜ PFunDDS.functionEvaluator permutation) =
      PFunDDS.functionEvaluator (spocOracle permutation key) := by
  unfold spocDDC
  rw [PFunConverter.DDC.apply_ofStep]
  apply Subtype.ext
  funext queries
  apply Part.ext
  intro response
  rw [show (CausalApply.applyG (spoc key)
      (PFunDDS.functionEvaluator permutation).1).1 =
      CausalApply.applyRaw (spoc key) (PFunDDS.functionEvaluator permutation).1 from rfl,
    CausalApply.mem_applyRaw, PFunConverter.DDC.mem_functionEvaluator_iff]
  constructor
  · rintro ⟨fuel, hresponse⟩
    let bound := historyCallBound permutation key queries
    have hresponse' : response ∈ CausalApply.applyRawAt (spoc key)
        (PFunDDS.functionEvaluator permutation).1 (fuel + bound + 1) queries :=
      CausalApply.applyRawAt_mono_le _ _ (by omega) hresponse
    rw [CausalApply.mem_applyRawAt_iff] at hresponse'
    obtain ⟨result, hresult, hlast⟩ := hresponse'
    have hrun := driveOuter_spoc permutation key queries [] (fuel + bound + 1)
      (fun query hquery => by
        have := callCount_lt_historyCallBound_succ permutation key queries query hquery
        dsimp only [bound]
        omega)
    rw [hrun, Part.mem_some_iff] at hresult
    subst result
    rw [List.getLast?_map] at hlast
    obtain ⟨query, hquery, hresponse⟩ := Option.map_eq_some_iff.mp hlast
    exact ⟨query, hquery, hresponse.symm⟩
  · rintro ⟨query, hquery, rfl⟩
    let fuel := historyCallBound permutation key queries + 1
    refine ⟨fuel, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(queries.map (spocOracle permutation key),
      queries.flatMap (spocCalls permutation key)), ?_, ?_⟩
    · rw [driveOuter_spoc permutation key queries [] fuel]
      · exact Part.mem_some _
      · intro q hq
        exact callCount_lt_historyCallBound_succ permutation key queries q hq
    · rw [List.getLast?_map, hquery]
      rfl

theorem spocPDS_eq_applied (permutation : Equiv.Perm State) :
    spocPDS permutation =
      ⟨Dist.fTransform
          (fun key : Block =>
            spocDDC key ·ᶜ PFunDDS.functionEvaluator (permutation : State → State))
          (Dist.uniform Block),
        Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩ := by
  have himplementation :
      (fun key : Block =>
        PFunDDS.functionEvaluator (spocOracle (permutation : State → State) key)) =
      (fun key : Block =>
        spocDDC key ·ᶜ PFunDDS.functionEvaluator (permutation : State → State)) := by
    funext key
    exact (spocDDC_apply (permutation : State → State) key).symm
  apply @Subtype.ext (PFunPDS Query Response) (fun system => system.isProbDist)
  unfold spocPDS spocRepresentative
  exact congrArg
    (fun implementation : Block → PFunDDS.DDS Query Response =>
      Dist.fTransform implementation (Dist.uniform Block))
    himplementation

end RandomSystems.SpoC
