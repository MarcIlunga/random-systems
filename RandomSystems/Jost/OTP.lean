/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Surface
import RandomSystems.StrictContextAdvantage

/-!
# The one-time pad: a resource identity that is NOT a law equality

The acid test of the behavioral surface.  A single-use channel with an
eavesdropper: the real world stores the first sent message `m` and leaks
`m XOR k` under a uniform key; the ideal world leaks a uniform ciphertext
`c` independent of the message.  As laws over deterministic systems the
two are *different* — the real fibres answer message-dependently, the
ideal fibres constantly — yet they are the *same resource*
(`otp_real_eq_ideal`): no finite deterministic observation context
separates them.  This is exactly the identity the quotient surface exists
for, entering through `Resource.sampleInit_eq_of_flatten_equivalent`.

Proof layout:

1. Both machine families are (dependent) **history evaluators** in closed
   form (`realM_toDDS_eq`, `idealM_toDDS_eq`), so their flattened,
   `⊥`-completed answers at any snoc history compute
   (`SR_bot_send`, `SR_bot_leak`, `SI_bot_send`, `SI_bot_leak`).
2. **The transcript invariant** (`otp_transcript`): against every
   deterministic environment, either no message has been sent — and all
   four deterministic worlds have literally equal transcripts — or the
   first sent message `m₀` is fixed and the real world at key `k` has the
   same transcript as the ideal world at ciphertext `m₀ XOR k`.
3. Transcript-law equality (`transcriptDist_flat_eq`): the seed bijection
   `k ↦ m₀ XOR k` pushes uniform to uniform
   (`Dist.fTransform_bijection_uniform` — the library's own "OTP-style
   argument" lemma).
4. CR18 transcript equivalence → strict contextual equivalence
   (`strict_equivalent_of_equivalent`) → resource equality through the
   surface bridge.
-/

namespace RandomSystems.CC.OTP

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open scoped RandomSystems.CR18.PFunDDS

/-! ## The interface declaration and the two machine families -/

/-- Alice and Eve. -/
inductive OTPIface | A | E
  deriving DecidableEq

/-- Alice sends one bit. -/
inductive SendIn | send (m : Bool)

/-- Eve asks for the ciphertext. -/
inductive LeakIn | leak

/-- Acknowledgement. -/
inductive OkOut | ok

/-- Per-interface inputs. -/
def otpIn : OTPIface → Type
  | .A => SendIn
  | .E => LeakIn

/-- Per-interface outputs: Eve sees `⊥` (as a value) before a send. -/
def otpOut : OTPIface → Type
  | .A => OkOut
  | .E => Option Bool

/-- The one-time-pad boundary. -/
def otpInterfaces : Interfaces where
  Iface := OTPIface
  In := otpIn
  Out := otpOut

/-- Address-tagged queries of the OTP boundary. -/
abbrev Q := otpInterfaces.Query

/-- Flattened tagged answers of the OTP boundary. -/
abbrev FA := FlatAnswer otpInterfaces.sig otpInterfaces.bnd

/-- The real world at key `k`: store the FIRST sent message, leak its
XOR-encryption.  Total; single-use (later sends acknowledged, ignored). -/
def realM (k : Bool) : otpInterfaces.Realization where
  State := Option Bool
  init := none
  step state query :=
    match query with
    | ⟨.A, .send m⟩ => some (state.or (some m), .ok)
    | ⟨.E, .leak⟩ => some (state, state.map (fun m => xor m k))

/-- The ideal world at ciphertext `c`: remember only THAT a message was
sent, leak the message-independent `c`. -/
def idealM (c : Bool) : otpInterfaces.Realization where
  State := Bool
  init := false
  step state query :=
    match query with
    | ⟨.A, .send _⟩ => some (true, .ok)
    | ⟨.E, .leak⟩ => some (state, if state then some c else none)

/-- The real resource: uniform key. -/
noncomputable def real : Resource otpInterfaces :=
  Resource.sampleInit realM (Dist.uniform Bool) Dist.uniform_isProbDist

/-- The ideal resource: uniform ciphertext. -/
noncomputable def ideal : Resource otpInterfaces :=
  Resource.sampleInit idealM (Dist.uniform Bool) Dist.uniform_isProbDist

/-! ## The first sent message of a query sequence -/

/-- The message carried by a query, if it is a send. -/
def sendOf : Q → Option Bool
  | ⟨.A, .send m⟩ => some m
  | ⟨.E, .leak⟩ => none

/-- The first sent message in a query sequence. -/
def firstSend (queries : List Q) : Option Bool :=
  (queries.filterMap sendOf).head?

@[simp]
theorem firstSend_nil : firstSend [] = none := rfl

/-- One step of `firstSend` at the back: the first send wins. -/
theorem firstSend_append (queries : List Q) (query : Q) :
    firstSend (queries ++ [query]) = (firstSend queries).or (sendOf query) := by
  unfold firstSend
  rw [List.filterMap_append]
  cases h : queries.filterMap sendOf with
  | nil => cases hq : sendOf query <;> simp [hq]
  | cons a rest => simp

/-! ## Closed forms: the machines are history evaluators -/

theorem realM_runFrom (k : Bool) (state : Option Bool) (history : List Q) :
    (realM k).runFrom state history = some (state.or (firstSend history)) := by
  induction history generalizing state with
  | nil => cases state <;> rfl
  | cons query rest ih =>
      obtain ⟨iface, input⟩ := query
      match iface, input with
      | .A, .send m =>
          rw [Machine.runFrom_cons]
          show (realM k).runFrom (state.or (some m)) rest = _
          rw [ih]
          have hfs : firstSend (⟨OTPIface.A, SendIn.send m⟩ :: rest) = some m := by
            unfold firstSend
            rfl
          rw [hfs]
          cases state <;> rfl
      | .E, .leak =>
          rw [Machine.runFrom_cons]
          show (realM k).runFrom state rest = _
          rw [ih]
          have hfs : firstSend (⟨OTPIface.E, LeakIn.leak⟩ :: rest) =
              firstSend rest := by
            unfold firstSend
            rfl
          rw [hfs]

theorem idealM_runFrom (c : Bool) (sent : Bool) (history : List Q) :
    (idealM c).runFrom sent history =
      some (sent || (firstSend history).isSome) := by
  induction history generalizing sent with
  | nil => cases sent <;> rfl
  | cons query rest ih =>
      obtain ⟨iface, input⟩ := query
      match iface, input with
      | .A, .send m =>
          rw [Machine.runFrom_cons]
          show (idealM c).runFrom true rest = _
          rw [ih]
          have hfs : firstSend (⟨OTPIface.A, SendIn.send m⟩ :: rest) = some m := by
            unfold firstSend
            rfl
          rw [hfs]
          cases sent <;> rfl
      | .E, .leak =>
          rw [Machine.runFrom_cons]
          show (idealM c).runFrom sent rest = _
          rw [ih]
          have hfs : firstSend (⟨OTPIface.E, LeakIn.leak⟩ :: rest) =
              firstSend rest := by
            unfold firstSend
            rfl
          rw [hfs]

/-- The flattened real world at key `k`, on the established flat carrier. -/
noncomputable def SR (k : Bool) : PFunDDS.DDS Q FA :=
  DependentDDS.flatten ((realM k).toDDS)

/-- The flattened ideal world at ciphertext `c`. -/
noncomputable def SI (c : Bool) : PFunDDS.DDS Q FA :=
  DependentDDS.flatten ((idealM c).toDDS)

theorem realM_run (k : Bool) (history : List Q) :
    (realM k).run history = some (firstSend history) := by
  rw [Machine.run, realM_runFrom]
  cases firstSend history <;> rfl

theorem idealM_run (c : Bool) (history : List Q) :
    (idealM c).run history = some (firstSend history).isSome := by
  rw [Machine.run, idealM_runFrom]
  rfl

theorem SR_mem_dom (k : Bool) {history : List Q} (nonempty : history ≠ []) :
    history ∈ PFunDDS.dom (SR k) := by
  show history ∈ ((realM k).toDDS).domain
  rw [Machine.mem_toDDS_domain_iff, realM_run]
  exact ⟨nonempty, rfl⟩

theorem SI_mem_dom (c : Bool) {history : List Q} (nonempty : history ≠ []) :
    history ∈ PFunDDS.dom (SI c) := by
  show history ∈ ((idealM c).toDDS).domain
  rw [Machine.mem_toDDS_domain_iff, idealM_run]
  exact ⟨nonempty, rfl⟩

/-! ## Generic snoc-history computation lemmas

Two reusable facts (migration candidates for `ResourceMachine.lean` /
`PFunDDS.lean`): the flattened answer of a package at a snoc history is the
step's answer at the appended query — with no `getLast` transport in the
statement — and the `⊥`-completion of a total system is `some` of the
system's own answer. -/

section Generic

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}

/-- The flattened package answer at `init ++ [q]`, computed from the run
over `init` and one step at `q`.  The `getLast` transport happens inside
this proof, once, for every consumer. -/
theorem flatten_output_concat (m : Machine U sigma)
    (init : List (Query U sigma)) (q : Query U sigma)
    (mem : init ++ [q] ∈ PFunDDS.dom (DependentDDS.flatten m.toDDS))
    {state : m.State} (hrun : m.run init = some state)
    {next : m.State × AnswerAt q} (hstep : m.step state q = some next) :
    PFunDDS.output (DependentDDS.flatten m.toDDS) (init ++ [q]) mem =
      ⟨q.1, next.2⟩ := by
  have nonempty := DependentDDS.history_ne_nil m.toDDS mem
  have hval := DependentDDS.flatten_apply_eq_some m.toDDS (init ++ [q]) mem
  have hout : PFunDDS.output (DependentDDS.flatten m.toDDS) (init ++ [q]) mem =
      ⟨((init ++ [q]).getLast nonempty).1,
        m.toDDS.output _ nonempty mem⟩ :=
    Part.get_eq_of_mem (Part.eq_some_iff.mp hval) mem
  have hgl : (init ++ [q]).getLast nonempty = q :=
    List.getLast_append_singleton _
  have hls : m.lastStep (init ++ [q]) nonempty =
      m.step state ((init ++ [q]).getLast nonempty) := by
    rw [Machine.lastStep, List.dropLast_concat, hrun]
    rfl
  have key : ∃ pair : m.State × AnswerAt ((init ++ [q]).getLast nonempty),
      m.step state ((init ++ [q]).getLast nonempty) = some pair ∧
        (⟨((init ++ [q]).getLast nonempty).1, pair.2⟩ :
            FlatAnswer U sigma) = ⟨q.1, next.2⟩ := by
    rw [hgl]
    exact ⟨next, hstep, rfl⟩
  obtain ⟨pair, hpair, hsig⟩ := key
  rw [hout, Machine.toDDS_output m _ nonempty mem (hls.trans hpair)]
  exact hsig

end Generic

/-- The `⊥`-completion of a total flat system answers `some` of the
system's own answer at every nonempty history. -/
theorem output_fullyDefined_of_total {X : Type*} {Y : Type*}
    (S : PFunDDS.DDS X Y) (total : PFunDDS.dom S = {l : List X | l ≠ []})
    (history : List X) (nonempty : history ≠ [])
    (h : history ∈ PFunDDS.dom (S⊥)) :
    PFunDDS.output (S⊥) history h =
      some (PFunDDS.output S history (by rw [total]; exact nonempty)) := by
  have hkept : PFunDDS.keptPrefix S history.dropLast = history.dropLast := by
    rcases eq_or_ne history.dropLast [] with hnil | hne
    · rw [hnil]
      rfl
    · exact PFunDDS.keptPrefix_eq_self_of_mem S (by rw [total]; exact hne)
  simp only [PFunDDS.output_fullyDefined]
  split
  · rename_i hcand
    refine congrArg some (PFunDDS.output_congr S ?_ hcand _)
    rw [hkept, List.dropLast_append_getLast]
  · rename_i hcand
    refine absurd (show _ ∈ PFunDDS.dom S from ?_) hcand
    rw [hkept, List.dropLast_append_getLast, total]
    exact nonempty

/-! ## The four completed flattened answers at a snoc history -/

theorem SR_total (k : Bool) : PFunDDS.dom (SR k) = {l : List Q | l ≠ []} := by
  ext history
  exact ⟨fun mem => DependentDDS.history_ne_nil ((realM k).toDDS) mem,
    fun nonempty => SR_mem_dom k nonempty⟩

theorem SI_total (c : Bool) : PFunDDS.dom (SI c) = {l : List Q | l ≠ []} := by
  ext history
  exact ⟨fun mem => DependentDDS.history_ne_nil ((idealM c).toDDS) mem,
    fun nonempty => SI_mem_dom c nonempty⟩

theorem SR_bot_send (k m : Bool) (init : List Q)
    (h : init ++ [(⟨.A, .send m⟩ : Q)] ∈ PFunDDS.dom ((SR k)⊥)) :
    PFunDDS.output ((SR k)⊥) (init ++ [⟨.A, .send m⟩]) h =
      some ⟨OTPIface.A, OkOut.ok⟩ := by
  rw [output_fullyDefined_of_total (SR k) (SR_total k) _ (by simp) h]
  have hstep : (realM k).step (firstSend init) (⟨.A, .send m⟩ : Q)
      = some ((firstSend init).or (some m), OkOut.ok) := rfl
  exact congrArg some
    (flatten_output_concat (realM k) init _ _ (realM_run k init) hstep)

theorem SR_bot_leak (k : Bool) (init : List Q)
    (h : init ++ [(⟨.E, .leak⟩ : Q)] ∈ PFunDDS.dom ((SR k)⊥)) :
    PFunDDS.output ((SR k)⊥) (init ++ [⟨.E, .leak⟩]) h =
      some ⟨OTPIface.E, (firstSend init).map (fun m => xor m k)⟩ := by
  rw [output_fullyDefined_of_total (SR k) (SR_total k) _ (by simp) h]
  have hstep : (realM k).step (firstSend init) (⟨.E, .leak⟩ : Q)
      = some (firstSend init, (firstSend init).map (fun m => xor m k)) := rfl
  exact congrArg some
    (flatten_output_concat (realM k) init _ _ (realM_run k init) hstep)

theorem SI_bot_send (c m : Bool) (init : List Q)
    (h : init ++ [(⟨.A, .send m⟩ : Q)] ∈ PFunDDS.dom ((SI c)⊥)) :
    PFunDDS.output ((SI c)⊥) (init ++ [⟨.A, .send m⟩]) h =
      some ⟨OTPIface.A, OkOut.ok⟩ := by
  rw [output_fullyDefined_of_total (SI c) (SI_total c) _ (by simp) h]
  have hstep : (idealM c).step (firstSend init).isSome (⟨.A, .send m⟩ : Q)
      = some (true, OkOut.ok) := rfl
  exact congrArg some
    (flatten_output_concat (idealM c) init _ _ (idealM_run c init) hstep)

theorem SI_bot_leak (c : Bool) (init : List Q)
    (h : init ++ [(⟨.E, .leak⟩ : Q)] ∈ PFunDDS.dom ((SI c)⊥)) :
    PFunDDS.output ((SI c)⊥) (init ++ [⟨.E, .leak⟩]) h =
      some ⟨OTPIface.E,
        if (firstSend init).isSome then some c else none⟩ := by
  rw [output_fullyDefined_of_total (SI c) (SI_total c) _ (by simp) h]
  have hstep : (idealM c).step (firstSend init).isSome (⟨.E, .leak⟩ : Q)
      = some ((firstSend init).isSome,
          if (firstSend init).isSome then some c else none) := rfl
  exact congrArg some
    (flatten_output_concat (idealM c) init _ _ (idealM_run c init) hstep)

/-! ## Transcript recursion, cased on the environment's move -/

theorem transcript_succ_none {X Y : Type*} {s : PFunDDS.DDS X Y}
    {e : PFunDDS.DDE X Y} {n : ℕ}
    (hx : e (PFunDDS.transcriptOutputs (PFunDDS.transcript s e n)) = none) :
    PFunDDS.transcript s e (n + 1) = PFunDDS.transcript s e n := by
  simp only [PFunDDS.transcript, hx]

theorem transcript_succ_some {X Y : Type*} {s : PFunDDS.DDS X Y}
    {e : PFunDDS.DDE X Y} {n : ℕ} {x : X}
    (hx : e (PFunDDS.transcriptOutputs (PFunDDS.transcript s e n)) = some x) :
    PFunDDS.transcript s e (n + 1) =
      PFunDDS.transcript s e n ++
        [(x, PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs (PFunDDS.transcript s e n) ++ [x])
          (by
            rw [PFunDDS.dom_fullyDefined]
            simp))] := by
  simp only [PFunDDS.transcript, hx]

@[simp]
theorem transcriptInputs_append_entry {X Y : Type*}
    (t : List (X × Option Y)) (x : X) (y : Option Y) :
    PFunDDS.transcriptInputs (t ++ [(x, y)]) =
      PFunDDS.transcriptInputs t ++ [x] := by
  simp [PFunDDS.transcriptInputs]

/-! ## The transcript invariant -/

/-- **The one-time-pad transcript invariant.**  Against every deterministic
environment: before any send, all four deterministic worlds have literally
equal transcripts; once the first message `m₀` is sent, the real world at
key `k` and the ideal world at ciphertext `m₀ XOR k` remain
transcript-equal, and `m₀` stays the first send. -/
theorem otp_transcript (e : PFunDDS.DDE Q FA) (n : ℕ) :
    (firstSend (PFunDDS.transcriptInputs
          (PFunDDS.transcript (SR false) e n)) = none
        ∧ PFunDDS.transcript (SR true) e n = PFunDDS.transcript (SR false) e n
        ∧ ∀ c, PFunDDS.transcript (SI c) e n
            = PFunDDS.transcript (SR false) e n)
      ∨ (∃ m₀ : Bool, ∀ k : Bool,
          firstSend (PFunDDS.transcriptInputs
              (PFunDDS.transcript (SR k) e n)) = some m₀
            ∧ PFunDDS.transcript (SI (xor m₀ k)) e n
                = PFunDDS.transcript (SR k) e n) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih =>
      rcases ih with ⟨hnone, htrue, hsi⟩ | ⟨m₀, hpair⟩
      · cases hx : e (PFunDDS.transcriptOutputs
            (PFunDDS.transcript (SR false) e n)) with
        | none =>
            have h0 := transcript_succ_none (s := SR false) hx
            have h1 := transcript_succ_none (s := SR true)
              (by rw [htrue]; exact hx)
            have h2 : ∀ c, PFunDDS.transcript (SI c) e (n + 1)
                = PFunDDS.transcript (SI c) e n :=
              fun c => transcript_succ_none (by rw [hsi c]; exact hx)
            exact Or.inl ⟨by rw [h0]; exact hnone,
              by rw [h1, h0, htrue],
              fun c => by rw [h2 c, h0, hsi c]⟩
        | some x =>
            have h0 := transcript_succ_some (s := SR false) hx
            have h1 := transcript_succ_some (s := SR true)
              (by rw [htrue]; exact hx)
            have h2 : ∀ c, _ := fun c => transcript_succ_some (s := SI c)
              (by rw [hsi c]; exact hx)
            rw [htrue] at h1
            have h2' := fun c => (hsi c) ▸ (h2 c)
            obtain ⟨iface, input⟩ := x
            match iface, input with
            | .A, .send m =>
                rw [SR_bot_send] at h0 h1
                have h2'' : ∀ c, PFunDDS.transcript (SI c) e (n + 1)
                    = PFunDDS.transcript (SR false) e n ++
                      [(⟨OTPIface.A, SendIn.send m⟩,
                        some ⟨OTPIface.A, OkOut.ok⟩)] := by
                  intro c
                  rw [h2' c, SI_bot_send]
                refine Or.inr ⟨m, fun k => ?_⟩
                have hk : PFunDDS.transcript (SR k) e (n + 1)
                    = PFunDDS.transcript (SR false) e n ++
                      [(⟨OTPIface.A, SendIn.send m⟩,
                        some ⟨OTPIface.A, OkOut.ok⟩)] := by
                  cases k
                  · exact h0
                  · exact h1
                refine ⟨?_, ?_⟩
                · rw [hk, transcriptInputs_append_entry, firstSend_append,
                    hnone]
                  rfl
                · rw [hk, h2'']
            | .E, .leak =>
                rw [SR_bot_leak, hnone] at h0 h1
                have h2'' : ∀ c, PFunDDS.transcript (SI c) e (n + 1)
                    = PFunDDS.transcript (SR false) e n ++
                      [(⟨OTPIface.E, LeakIn.leak⟩,
                        some ⟨OTPIface.E, (none : Option Bool)⟩)] := by
                  intro c
                  rw [h2' c, SI_bot_leak, hnone]
                  rfl
                refine Or.inl ⟨?_, ?_, ?_⟩
                · rw [h0, transcriptInputs_append_entry, firstSend_append,
                    hnone]
                  rfl
                · rw [h0, h1]
                  rfl
                · intro c
                  rw [h2'' c, h0]
                  rfl
      · refine Or.inr ⟨m₀, fun k => ?_⟩
        obtain ⟨hfs, hpk⟩ := hpair k
        cases hx : e (PFunDDS.transcriptOutputs
            (PFunDDS.transcript (SR k) e n)) with
        | none =>
            have h0 := transcript_succ_none (s := SR k) hx
            have h1 := transcript_succ_none (s := SI (xor m₀ k))
              (by rw [hpk]; exact hx)
            exact ⟨by rw [h0]; exact hfs, by rw [h0, h1, hpk]⟩
        | some x =>
            have h0 := transcript_succ_some (s := SR k) hx
            have h1 := transcript_succ_some (s := SI (xor m₀ k))
              (by rw [hpk]; exact hx)
            rw [hpk] at h1
            obtain ⟨iface, input⟩ := x
            match iface, input with
            | .A, .send m' =>
                rw [SR_bot_send] at h0
                rw [SI_bot_send] at h1
                refine ⟨?_, ?_⟩
                · rw [h0, transcriptInputs_append_entry, firstSend_append,
                    hfs]
                  rfl
                · rw [h0, h1]
            | .E, .leak =>
                rw [SR_bot_leak, hfs] at h0
                rw [SI_bot_leak, hfs] at h1
                refine ⟨?_, ?_⟩
                · rw [h0, transcriptInputs_append_entry, firstSend_append,
                    hfs]
                  rfl
                · rw [h0, h1]
                  rfl

/-! ## Transcript-law equality and the headline -/

/-- The flattened real law is the uniform pushforward of the flattened
deterministic fibres. -/
theorem flat_real :
    DependentPDS.flatten
        (Machine.lawOf realM (Dist.uniform Bool) Dist.uniform_isProbDist).val
      = Dist.fTransform SR (Dist.uniform Bool) :=
  Dist.fTransform_comp _ _ _

/-- The flattened ideal law, likewise. -/
theorem flat_ideal :
    DependentPDS.flatten
        (Machine.lawOf idealM (Dist.uniform Bool) Dist.uniform_isProbDist).val
      = Dist.fTransform SI (Dist.uniform Bool) :=
  Dist.fTransform_comp _ _ _

/-- `XOR` with a fixed bit is an involution. -/
theorem xor_left_involutive (m₀ : Bool) :
    Function.Involutive (fun b => xor m₀ b) := fun b => by
  cases m₀ <;> cases b <;> rfl

/-- **Transcript-law equality**: in every environment, at every length, the
real and ideal transcript distributions coincide — before a send because
all worlds agree pointwise, after a send because the seed bijection
`k ↦ m₀ XOR k` pushes uniform to uniform. -/
theorem transcriptDist_flat_eq (e : PFunDDS.DDE Q FA) (n : ℕ) :
    transcriptDist (DependentPDS.flatten
        (Machine.lawOf realM (Dist.uniform Bool)
          Dist.uniform_isProbDist).val) e n
      = transcriptDist (DependentPDS.flatten
          (Machine.lawOf idealM (Dist.uniform Bool)
            Dist.uniform_isProbDist).val) e n := by
  show Dist.fTransform _ _ = Dist.fTransform _ _
  rw [flat_real, flat_ideal, Dist.fTransform_comp, Dist.fTransform_comp]
  simp only [Function.comp_def]
  rcases otp_transcript e n with ⟨_, htrue, hsi⟩ | ⟨m₀, hpair⟩
  · calc Dist.fTransform
          (fun k => PFunDDS.transcript (SR k) e n) (Dist.uniform Bool)
        = Dist.fTransform
            (fun _ => PFunDDS.transcript (SR false) e n)
            (Dist.uniform Bool) :=
          Dist.fTransform_congr _ fun k _ => by cases k <;> [rfl; exact htrue]
      _ = Dist.fTransform
            (fun c => PFunDDS.transcript (SI c) e n) (Dist.uniform Bool) :=
          (Dist.fTransform_congr _ fun c _ => hsi c).symm
  · have hcomp : (fun k => PFunDDS.transcript (SR k) e n)
        = (fun c => PFunDDS.transcript (SI c) e n) ∘ (fun k => xor m₀ k) :=
      funext fun k => ((hpair k).2).symm
    rw [hcomp, ← Dist.fTransform_comp,
      Dist.fTransform_bijection_uniform _ (xor_left_involutive m₀).bijective]

/-- **The one-time pad, on the surface**: the real and ideal worlds are the
same resource — while their laws over deterministic systems differ.  No
finite deterministic observation context separates them. -/
theorem otp_real_eq_ideal : real = ideal := by
  refine Resource.sampleInit_eq_of_flatten_equivalent
    Dist.uniform_isProbDist Dist.uniform_isProbDist ?_
  exact StrictContextAdvantage.strict_equivalent_of_equivalent _ _
    ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
      (Machine.lawOf _ _ _).property)
    ((DependentPDS.flatten_is_probability_distribution_iff _).mpr
      (Machine.lawOf _ _ _).property)
    (fun e n => transcriptDist_flat_eq e n)

end RandomSystems.CC.OTP
