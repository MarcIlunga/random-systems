/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.AEAD.Game
import RandomSystems.Distinguishing
import RandomSystems.RandomSystem

/-!
# A generic real/ideal AEAD game

This module gives the eager-randomness ideal system used for full AEAD
distinguishing statements.  A finite tape is sampled once, before the
interaction.  Encryption leaks only plaintext length; decryption succeeds
exactly on a previous encryption tuple and returns the recorded plaintext.

The ideal representative is total on nonempty histories.  Query bounds,
nonce-respecting encryption, and maximum encryption length are admissibility
conditions on the adversary.  They never restrict either PDS domain.
-/

namespace RandomSystems.AEAD

open RandomSystems (Dist)
open RandomSystems.CR18

noncomputable section

universe uNonce uAD uPlaintext uBlock uTag uInput uOutput

/-- The query type for a block-ciphertext real/ideal AEAD game. -/
abbrev RealIdealQuery
    (Nonce : Type uNonce) (AD : Type uAD) (Plaintext : Type uPlaintext)
    (CiphertextBlock : Type uBlock) (Tag : Type uTag) :=
  Query Nonce AD Plaintext (List CiphertextBlock) Tag

/-- The response type for a block-ciphertext real/ideal AEAD game. -/
abbrev RealIdealResponse
    (Plaintext : Type uPlaintext) (CiphertextBlock : Type uBlock) (Tag : Type uTag) :=
  Response Plaintext (List CiphertextBlock) Tag

/-- A normalized real/ideal game packages the two probability laws that a
distinguisher compares. -/
structure RealIdealGame (X : Type uInput) (Y : Type uOutput) where
  real : PFunPDS.Prob X Y
  ideal : PFunPDS.Prob X Y
  domain : Set (List X)
  real_hasFixedDomain : PFunPDS.HasFixedDomain real.val domain
  ideal_hasFixedDomain : PFunPDS.HasFixedDomain ideal.val domain

namespace RealIdealGame

/-- Signed advantage of a distinguisher against a bundled real/ideal game:
real acceptance probability minus ideal acceptance probability. -/
noncomputable def advantage {X : Type uInput} {Y : Type uOutput}
    (game : RealIdealGame X Y) (distinguisher : Dist (PFunDDS.DDD X Y)) : ℝ :=
  CR18.advantage distinguisher game.ideal.val game.real.val

end RealIdealGame

/-- The encryption queries occurring in a query history, in chronological order. -/
def encryptionQueries
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) :
    List (EncryptQuery Nonce AD Plaintext) :=
  history.filterMap Sum.getLeft?

/-- The number of encryption queries in a query history. -/
def encryptionCount
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) : Nat :=
  (encryptionQueries history).length

/-- The encryption nonces occurring in a query history. -/
def encryptionNonces
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) : List Nonce :=
  (encryptionQueries history).map EncryptQuery.nonce

/-- A full-AEAD adversary is admissible along a query history when it has made
at most `encryptionQueryBound` encryption queries, has not reused an encryption
nonce, and keeps every encryption plaintext within `maxPlaintextLength`.
Decryption queries are otherwise unrestricted.  This is an adversary-side
predicate, not a PDS domain restriction. -/
def LegalHistory
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    (plaintextLength : Plaintext → Nat)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) : Prop :=
  encryptionCount history ≤ encryptionQueryBound ∧
    (encryptionNonces history).Nodup ∧
    ∀ query ∈ encryptionQueries history,
      plaintextLength query.plaintext ≤ maxPlaintextLength

/-- An adaptive environment is admissible when every query history it can
produce, along every possible response path, satisfies the AEAD bounds.  The
predicate constrains the environment only; it does not alter the domain of a
real or ideal system. -/
def AdmissibleEnvironment
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {Response : Type uOutput}
    (encryptionQueryBound maxPlaintextLength : Nat)
    (plaintextLength : Plaintext → Nat)
    (environment : PFunDDS.DDE
      (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag) Response) : Prop :=
  ∀ answers : List (Option Response),
    LegalHistory encryptionQueryBound maxPlaintextLength plaintextLength
      (PFunDDS.transcriptInputs (replay environment answers))

/-- Legality of full-AEAD query histories is prefix-closed. -/
theorem legalHistory_prefixClosed
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    (plaintextLength : Plaintext → Nat) :
    PrefixClosed
      (LegalHistory (Nonce := Nonce) (AD := AD) (CiphertextBlock := CiphertextBlock)
        (Tag := Tag) encryptionQueryBound maxPlaintextLength plaintextLength) := by
  intro initial history hprefix hlegal
  rcases hprefix with ⟨suffix, rfl⟩
  rcases hlegal with ⟨hcount, hnonces, hlength⟩
  refine ⟨?_, ?_, ?_⟩
  · have hcount' :
        encryptionCount
            (CiphertextBlock := CiphertextBlock) (Tag := Tag) initial +
          encryptionCount
            (CiphertextBlock := CiphertextBlock) (Tag := Tag) suffix ≤
          encryptionQueryBound := by
        simpa [encryptionCount, encryptionQueries] using hcount
    exact le_trans (Nat.le_add_right _ _) hcount'
  · have hnonces' :
        (encryptionNonces
            (CiphertextBlock := CiphertextBlock) (Tag := Tag) initial ++
          encryptionNonces
            (CiphertextBlock := CiphertextBlock) (Tag := Tag) suffix).Nodup := by
        simpa [encryptionNonces, encryptionQueries] using hnonces
    exact hnonces'.of_append_left
  · intro query hquery
    apply hlength query
    simp only [encryptionQueries, List.filterMap_append, List.mem_append]
    exact Or.inl hquery

/-- If the last query is an encryption in a legal history, its zero-based
encryption ordinal is within the tape's row bound. -/
theorem legalHistory_lastEncryption_index_lt
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    {plaintextLength : Plaintext → Nat}
    {history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)}
    (nonempty : history ≠ []) (query : EncryptQuery Nonce AD Plaintext)
    (lastQuery : history.getLast nonempty = Sum.inl query)
    (legal : LegalHistory encryptionQueryBound maxPlaintextLength
      plaintextLength history) :
    encryptionCount history.dropLast < encryptionQueryBound := by
  have historyDecomposition : history.dropLast ++ [Sum.inl query] = history := by
    rw [← lastQuery]
    exact List.dropLast_append_getLast nonempty
  rw [← historyDecomposition] at legal
  have countBound := legal.1
  simp [encryptionCount, encryptionQueries] at countBound
  unfold encryptionCount encryptionQueries
  omega

/-- If the last query is an encryption in a legal history, its plaintext fits
in one ideal-tape row. -/
theorem legalHistory_lastEncryption_length_le
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    {plaintextLength : Plaintext → Nat}
    {history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)}
    (nonempty : history ≠ []) (query : EncryptQuery Nonce AD Plaintext)
    (lastQuery : history.getLast nonempty = Sum.inl query)
    (legal : LegalHistory encryptionQueryBound maxPlaintextLength
      plaintextLength history) :
    plaintextLength query.plaintext ≤ maxPlaintextLength := by
  have historyDecomposition : history.dropLast ++ [Sum.inl query] = history := by
    rw [← lastQuery]
    exact List.dropLast_append_getLast nonempty
  rw [← historyDecomposition] at legal
  exact legal.2.2 query (by simp [encryptionQueries])

/-- Eager random coins for the full-AEAD ideal system.  Row `i` contains all
ciphertext blocks available to encryption query `i`, and `tags i` is that
query's tag. -/
structure IdealTape
    (CiphertextBlock : Type uBlock) (Tag : Type uTag)
    (encryptionQueryBound maxPlaintextLength : Nat) where
  ciphertextBlocks :
    Fin encryptionQueryBound → Fin maxPlaintextLength → CiphertextBlock
  tags : Fin encryptionQueryBound → Tag
deriving Fintype, Nonempty

namespace IdealTape

/-- Read one tape row by a natural encryption index.  Totalization keeps the
history evaluator defined beyond the adversary's permitted encryption bound;
admissibility makes the fallback observationally unreachable. -/
def ciphertextRow
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock]
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex : Nat) : Fin maxPlaintextLength → CiphertextBlock :=
  if inBounds : encryptionIndex < encryptionQueryBound then
    tape.ciphertextBlocks ⟨encryptionIndex, inBounds⟩
  else
    fun _ => default

/-- Read one tag by a natural encryption index, totalized beyond the
adversary's permitted encryption bound. -/
def tagAt
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited Tag]
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex : Nat) : Tag :=
  if inBounds : encryptionIndex < encryptionQueryBound then
    tape.tags ⟨encryptionIndex, inBounds⟩
  else
    default

end IdealTape

/-- Ideal encryption at a fixed ordinal and plaintext length.  Its output is
independent of nonce, associated data, and plaintext contents. -/
def idealEncrypt
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex plaintextLength : Nat) :
    EncryptResponse (List CiphertextBlock) Tag :=
  ⟨(List.ofFn (tape.ciphertextRow encryptionIndex)).take plaintextLength,
    tape.tagAt encryptionIndex⟩

/-- The ciphertext returned by ideal encryption has the requested length
whenever that length is within the tape row. -/
@[simp] theorem idealEncrypt_ciphertext_length
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex plaintextLength : Nat)
    (hLength : plaintextLength ≤ maxPlaintextLength) :
    (idealEncrypt tape encryptionIndex plaintextLength).ciphertext.length =
      plaintextLength := by
  simp [idealEncrypt, hLength]

/-- Ideal encryption specialized to an AEAD encryption query.  The query is
observed only through `plaintextLength query.plaintext`. -/
def idealEncryptQuery
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (plaintextLength : Plaintext → Nat)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex : Nat) (query : EncryptQuery Nonce AD Plaintext) :
    EncryptResponse (List CiphertextBlock) Tag :=
  idealEncrypt tape encryptionIndex (plaintextLength query.plaintext)

/-- For a fixed tape and encryption ordinal, ideal encryption observes a
query only through its plaintext length. -/
theorem idealEncryptQuery_eq_of_plaintextLength_eq
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (plaintextLength : Plaintext → Nat)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (encryptionIndex : Nat)
    (left right : EncryptQuery Nonce AD Plaintext)
    (sameLength : plaintextLength left.plaintext =
      plaintextLength right.plaintext) :
    idealEncryptQuery plaintextLength tape encryptionIndex left =
      idealEncryptQuery plaintextLength tape encryptionIndex right := by
  simp [idealEncryptQuery, sameLength]

/-- Under the uniform eager tape, equal-length encryption queries induce the
same response law, irrespective of nonce, associated data, or plaintext
contents. -/
theorem idealEncryptQuery_uniform_law_eq_of_plaintextLength_eq
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength encryptionIndex : Nat)
    [Fintype CiphertextBlock] [Inhabited CiphertextBlock]
    [Fintype Tag] [Inhabited Tag]
    (plaintextLength : Plaintext → Nat)
    (left right : EncryptQuery Nonce AD Plaintext)
    (sameLength : plaintextLength left.plaintext =
      plaintextLength right.plaintext) :
    Dist.fTransform
        (fun tape : IdealTape CiphertextBlock Tag
            encryptionQueryBound maxPlaintextLength =>
          idealEncryptQuery plaintextLength tape encryptionIndex left)
        (Dist.uniform
          (IdealTape CiphertextBlock Tag
            encryptionQueryBound maxPlaintextLength)) =
      Dist.fTransform
        (fun tape : IdealTape CiphertextBlock Tag
            encryptionQueryBound maxPlaintextLength =>
          idealEncryptQuery plaintextLength tape encryptionIndex right)
        (Dist.uniform
          (IdealTape CiphertextBlock Tag
            encryptionQueryBound maxPlaintextLength)) := by
  apply congrArg (fun response => Dist.fTransform response
    (Dist.uniform
      (IdealTape CiphertextBlock Tag
        encryptionQueryBound maxPlaintextLength)))
  funext tape
  exact idealEncryptQuery_eq_of_plaintextLength_eq
    plaintextLength tape encryptionIndex left right sameLength

/-- One replayable encryption record reconstructed from the ideal tape and
the query history. -/
structure ReplayRecord
    (Nonce : Type uNonce) (AD : Type uAD) (Plaintext : Type uPlaintext)
    (CiphertextBlock : Type uBlock) (Tag : Type uTag) where
  nonce : Nonce
  associatedData : AD
  ciphertext : List CiphertextBlock
  tag : Tag
  plaintext : Plaintext

/-- A replay record matches a decryption query exactly on nonce, associated
data, ciphertext, and tag. -/
def ReplayRecord.Matches
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag)
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag) : Prop :=
  record.nonce = query.nonce ∧
    record.associatedData = query.associatedData ∧
    record.ciphertext = query.ciphertext ∧
    record.tag = query.tag

/-- The decryption query that exactly replays a stored encryption record. -/
def ReplayRecord.decryptionQuery
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag) :
    DecryptQuery Nonce AD (List CiphertextBlock) Tag :=
  ⟨record.nonce, record.associatedData, record.ciphertext, record.tag⟩

@[simp] theorem ReplayRecord.matches_decryptionQuery
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag) :
    record.Matches record.decryptionQuery := by
  simp [ReplayRecord.Matches, ReplayRecord.decryptionQuery]

/-- Decidable exact-match test used by ideal decryption. -/
def ReplayRecord.matches
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag)
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag) : Bool :=
  decide (record.nonce = query.nonce) &&
    decide (record.associatedData = query.associatedData) &&
    decide (record.ciphertext = query.ciphertext) &&
    decide (record.tag = query.tag)

@[simp] theorem ReplayRecord.matches_eq_true
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag)
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag) :
    record.matches query = true ↔ record.Matches query := by
  simp [ReplayRecord.matches, ReplayRecord.Matches, and_assoc]

/-- Reconstruct the ideal encryption table for a completed query history.
The list index is the encryption ordinal, not the total-query ordinal. -/
def replayTable
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (plaintextLength : Plaintext → Nat)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) :
    List (ReplayRecord Nonce AD Plaintext CiphertextBlock Tag) :=
  (encryptionQueries history).mapIdx fun encryptionIndex query =>
    let response := idealEncryptQuery plaintextLength tape encryptionIndex query
    ⟨query.nonce, query.associatedData, response.ciphertext, response.tag,
      query.plaintext⟩

/-- Reconstructed replay records preserve exactly the encryption-nonce list
of the query history. -/
theorem replayTable_map_nonce
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    (plaintextLength : Plaintext → Nat)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)) :
    (replayTable plaintextLength tape history).map ReplayRecord.nonce =
      encryptionNonces history := by
  simp only [replayTable, encryptionNonces, List.mapIdx_eq_zipIdx_map,
    List.map_map]
  change List.map (EncryptQuery.nonce ∘ Prod.fst)
      (encryptionQueries history).zipIdx =
    List.map EncryptQuery.nonce (encryptionQueries history)
  rw [← List.map_map, List.zipIdx_map_fst]

/-- Ideal decryption accepts exactly a replay of a reconstructed encryption
record and returns that record's plaintext.  A fresh tuple is rejected. -/
def idealDecrypt
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag) :
    DecryptResponse Plaintext :=
  match (replayTable plaintextLength tape history).find?
      (fun record => record.matches query) with
  | some record => ⟨true, record.plaintext⟩
  | none => ⟨false, rejectedPlaintext⟩

/-- Ideal decryption verifies exactly when its query matches a reconstructed
encryption record. -/
theorem idealDecrypt_verified_iff
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag) :
    (idealDecrypt plaintextLength rejectedPlaintext tape history query).verified = true ↔
      ∃ record ∈ replayTable plaintextLength tape history, record.Matches query := by
  unfold idealDecrypt
  generalize foundEquation :
    (replayTable plaintextLength tape history).find?
      (fun record => record.matches query) = found
  cases found with
  | none =>
      constructor
      · intro impossible
        exact (Bool.false_ne_true impossible).elim
      · intro matchingRecord
        rcases matchingRecord with ⟨record, member, matching⟩
        have foundSome :
            ((replayTable plaintextLength tape history).find?
              (fun candidate => candidate.matches query)).isSome :=
          List.find?_isSome.mpr
            ⟨record, member, (ReplayRecord.matches_eq_true record query).2 matching⟩
        rw [foundEquation] at foundSome
        simp at foundSome
  | some record =>
      constructor
      · intro _
        have selected : record.matches query = true := by
          exact List.find?_some
            (p := fun candidate :
              ReplayRecord Nonce AD Plaintext CiphertextBlock Tag =>
                candidate.matches query)
            foundEquation
        exact ⟨record, List.mem_of_find?_eq_some foundEquation,
          (ReplayRecord.matches_eq_true record query).1 selected⟩
      · intro _
        rfl

/-- A verifying ideal-decryption response returns the plaintext of the exact
replay record that caused verification. -/
theorem idealDecrypt_verified_plaintext
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag)
    (verified :
      (idealDecrypt plaintextLength rejectedPlaintext tape history query).verified =
        true) :
    ∃ record ∈ replayTable plaintextLength tape history,
      record.Matches query ∧
        idealDecrypt plaintextLength rejectedPlaintext tape history query =
          ⟨true, record.plaintext⟩ := by
  unfold idealDecrypt at verified ⊢
  generalize foundEquation :
    (replayTable plaintextLength tape history).find?
      (fun record => record.matches query) = found at verified ⊢
  cases found with
  | none =>
      exact (Bool.false_ne_true verified).elim
  | some record =>
      have selected : record.matches query = true := by
        exact List.find?_some
          (p := fun candidate :
            ReplayRecord Nonce AD Plaintext CiphertextBlock Tag =>
              candidate.matches query)
          foundEquation
      exact ⟨record, List.mem_of_find?_eq_some foundEquation,
        (ReplayRecord.matches_eq_true record query).1 selected, rfl⟩

/-- Replaying a stored record returns its stored plaintext when that record is
the unique table entry matching its decryption query. -/
theorem idealDecrypt_replay_eq_of_unique_match
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag)
    (member : record ∈ replayTable plaintextLength tape history)
    (uniqueMatch : ∀ candidate ∈ replayTable plaintextLength tape history,
      candidate.Matches record.decryptionQuery →
        candidate = record) :
    idealDecrypt plaintextLength rejectedPlaintext tape history
        record.decryptionQuery =
      ⟨true, record.plaintext⟩ := by
  unfold idealDecrypt
  generalize foundEquation :
    (replayTable plaintextLength tape history).find?
      (fun candidate => candidate.matches record.decryptionQuery) = found
  cases found with
  | none =>
      have foundSome :
          ((replayTable plaintextLength tape history).find?
            (fun candidate => candidate.matches record.decryptionQuery)).isSome :=
        List.find?_isSome.mpr
          ⟨record, member,
            (ReplayRecord.matches_eq_true record record.decryptionQuery).2
              record.matches_decryptionQuery⟩
      rw [foundEquation] at foundSome
      simp at foundSome
  | some candidate =>
      have candidateMember :
          candidate ∈ replayTable plaintextLength tape history :=
        List.mem_of_find?_eq_some foundEquation
      have candidateMatches : candidate.Matches record.decryptionQuery := by
        apply (ReplayRecord.matches_eq_true candidate record.decryptionQuery).1
        exact List.find?_some
          (p := fun stored :
            ReplayRecord Nonce AD Plaintext CiphertextBlock Tag =>
              stored.matches record.decryptionQuery)
          foundEquation
      have candidateEq := uniqueMatch candidate candidateMember candidateMatches
      subst candidate
      rfl

/-- On a legal nonce-respecting history, membership in the replay table alone
suffices for an exact replay to return its recorded plaintext. -/
theorem idealDecrypt_replay_eq_of_legalHistory
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (legal : LegalHistory encryptionQueryBound maxPlaintextLength
      plaintextLength history)
    (record : ReplayRecord Nonce AD Plaintext CiphertextBlock Tag)
    (member : record ∈ replayTable plaintextLength tape history) :
    idealDecrypt plaintextLength rejectedPlaintext tape history
        record.decryptionQuery =
      ⟨true, record.plaintext⟩ := by
  apply idealDecrypt_replay_eq_of_unique_match
    plaintextLength rejectedPlaintext tape history record member
  intro candidate candidateMember candidateMatches
  have nonceNodup :
      ((replayTable plaintextLength tape history).map
        ReplayRecord.nonce).Nodup := by
    rw [replayTable_map_nonce plaintextLength tape history]
    exact legal.2.1
  have sameNonce : candidate.nonce = record.nonce := by
    simpa [ReplayRecord.decryptionQuery] using candidateMatches.1
  exact List.inj_on_of_nodup_map nonceNodup
    candidateMember member sameNonce

/-- If no replay record matches a decryption query, ideal decryption returns
the canonical rejecting response. -/
theorem idealDecrypt_of_forall_not_matches
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (query : DecryptQuery Nonce AD (List CiphertextBlock) Tag)
    (fresh : ∀ record ∈ replayTable plaintextLength tape history,
      ¬ record.Matches query) :
    idealDecrypt plaintextLength rejectedPlaintext tape history query =
      ⟨false, rejectedPlaintext⟩ := by
  unfold idealDecrypt
  have noMatch :
      (replayTable plaintextLength tape history).find?
        (fun record => record.matches query) = none := by
    apply List.find?_eq_none.mpr
    intro record member matching
    exact fresh record member
      ((ReplayRecord.matches_eq_true record query).1 matching)
  simp [noMatch]

/-- The deterministic oracle induced by one fixed ideal tape. -/
def idealOracle
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)
    (history : List (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag))
    (nonempty : history ≠ []) :
    RealIdealResponse Plaintext CiphertextBlock Tag :=
  match history.getLast nonempty with
  | Sum.inl query =>
      Sum.inl
        (idealEncryptQuery plaintextLength tape
          (encryptionCount history.dropLast) query)
  | Sum.inr query =>
      Sum.inr
        (idealDecrypt plaintextLength rejectedPlaintext tape history.dropLast query)

/-- The deterministic ideal AEAD system represented by one fixed eager tape. -/
def idealRepresentative
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    {encryptionQueryBound maxPlaintextLength : Nat}
    [Inhabited CiphertextBlock] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (tape : IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength) :
    PFunDDS.DDS (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag) :=
  PFunDDS.historyEvaluator
    (idealOracle plaintextLength rejectedPlaintext tape)

/-- The normalized ideal AEAD probability law: sample the entire finite tape
uniformly, then interpret it as one deterministic history evaluator. -/
noncomputable def idealProb
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    [Fintype CiphertextBlock] [Inhabited CiphertextBlock]
    [Fintype Tag] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext) :
    PFunPDS.Prob (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag) :=
  ⟨Dist.fTransform
      (idealRepresentative plaintextLength rejectedPlaintext)
      (Dist.uniform
        (IdealTape CiphertextBlock Tag encryptionQueryBound maxPlaintextLength)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Every representative in the unfiltered ideal law is total on nonempty
query histories. -/
theorem idealProb_totalOnNonempty
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    [Fintype CiphertextBlock] [Inhabited CiphertextBlock]
    [Fintype Tag] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext) :
    CondEquiv.TotalOnNonempty
      (idealProb (Nonce := Nonce) (AD := AD)
        (CiphertextBlock := CiphertextBlock) (Tag := Tag)
        encryptionQueryBound maxPlaintextLength
        plaintextLength rejectedPlaintext).val := by
  unfold idealProb idealRepresentative
  exact CondEquiv.totalOnNonempty_fTransform_historyEvaluator _ _

/-- A support-total law has the common CR18 domain of all nonempty query
histories. -/
theorem hasFixedDomain_nonempty_of_totalOnNonempty
    {X : Type uInput} {Y : Type uOutput} (system : PFunPDS X Y)
    (total : CondEquiv.TotalOnNonempty system) :
    PFunPDS.HasFixedDomain system {history : List X | history ≠ []} := by
  intro representative representativeMember
  ext history
  constructor
  · intro inDomain equalNil
    exact PFunDDS.empty_not_mem representative (equalNil ▸ inDomain)
  · intro nonempty
    exact total representative representativeMember history nonempty

/-- The normalized full-AEAD real/ideal game.  Both probability laws remain
total on every nonempty history.  `encryptionQueryBound` and
`maxPlaintextLength` size the finite eager ideal tape; they are obligations on
the adversary, not filters on either system. -/
noncomputable def fullGame
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    [Fintype CiphertextBlock] [Inhabited CiphertextBlock]
    [Fintype Tag] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (real : PFunPDS.Prob
      (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag))
    (realTotal : CondEquiv.TotalOnNonempty real.val) :
    RealIdealGame (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag) :=
  { real := real
    ideal := idealProb encryptionQueryBound maxPlaintextLength
      plaintextLength rejectedPlaintext
    domain := {history | history ≠ []}
    real_hasFixedDomain :=
      hasFixedDomain_nonempty_of_totalOnNonempty real.val realTotal
    ideal_hasFixedDomain :=
      hasFixedDomain_nonempty_of_totalOnNonempty _
        (idealProb_totalOnNonempty encryptionQueryBound maxPlaintextLength
          plaintextLength rejectedPlaintext) }

/-- Signed full-AEAD distinguishing advantage: real acceptance probability
minus ideal acceptance probability. -/
noncomputable def realIdealAdvantage
    {Nonce : Type uNonce} {AD : Type uAD} {Plaintext : Type uPlaintext}
    {CiphertextBlock : Type uBlock} {Tag : Type uTag}
    (encryptionQueryBound maxPlaintextLength : Nat)
    [Fintype CiphertextBlock] [Inhabited CiphertextBlock]
    [Fintype Tag] [Inhabited Tag]
    [DecidableEq Nonce] [DecidableEq AD] [DecidableEq CiphertextBlock]
    [DecidableEq Tag]
    (plaintextLength : Plaintext → Nat) (rejectedPlaintext : Plaintext)
    (distinguisher : Dist (PFunDDS.DDD
      (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag)))
    (real : PFunPDS.Prob
      (RealIdealQuery Nonce AD Plaintext CiphertextBlock Tag)
      (RealIdealResponse Plaintext CiphertextBlock Tag))
    (realTotal : CondEquiv.TotalOnNonempty real.val) : ℝ :=
  (fullGame encryptionQueryBound maxPlaintextLength
    plaintextLength rejectedPlaintext real realTotal).advantage distinguisher

end

end RandomSystems.AEAD
