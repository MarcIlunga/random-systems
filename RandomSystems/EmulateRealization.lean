/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ProtocolRealization
import RandomSystems.ComposeRealization
import RandomSystems.RandomSystem
import RandomSystems.SemanticRegistry

/-!
# Environment emulation: the distinguisher `Dα` (MauRen11 Definitions 15/16)

MauRen11 Definitions 15/16 fold a converter `α` into the environment: a
distinguisher for the assumed system is obtained by letting the environment
itself run `α`, answering the outer environment `e` from the emulated
interaction.  Function-natively:

* `emulate α e n : DDE X Y` — the **emulated environment `Dα`**: on an
  inner answer history it deterministically replays the whole layered
  interaction (`e`'s queries are recomputable from the outer answers, which
  are recomputable by walking `α` against the recorded inner answers), asks
  the next inner query of `α`, and stops after `n` outer rounds (the
  fuel-aware stop) or when `e` stalls;
* `replayTranscript α e n` — the transcript reconstruction: parse an inner
  transcript back into the outer transcript it induces (the `replay`
  pattern of `RandomSystem.lean`, one level up);
* `transcript_apply` — the **bridge**: for a productive `α` (CR18 Def 3.8's
  bounded query streaks, no silence on reachable pairs) and *every* system
  `s`, the transcript of the applied system `apply α s` (CR18 Def 3.9)
  against `e` is the replay of the transcript of `s` against `emulate α e n`;
* `transcriptDist_apply` — the bridge through the pushforward, the form the
  compatible-metric obligations consume (`CompatibleMetric.lean`);
* `applyRaw_dom` — totality of the applied system under the productivity
  hypotheses: every outer round is one bounded streak of answered inner
  queries ended by an outer answer.

The proofs run a single joint-state relation `EmuRun` (outer transcript,
current outer input, inner transcript) through the same
replay/certification pattern as `CompRun` in `ComposeRealization.lean`.
-/

namespace RandomSystems.CR18

namespace PFunConverter

open RandomSystems (Dist)
open scoped PFunDDS

universe u v w z u' w'

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The emulation state machine -/

@[simp] private theorem transcriptInputs_nil :
    PFunDDS.transcriptInputs ([] : List (X × Option Y)) = [] := rfl

@[simp] private theorem transcriptOutputs_nil :
    PFunDDS.transcriptOutputs ([] : List (X × Option Y)) = [] := rfl

open Classical in
/-- Plumbing for `emulate` (MauRen11 Def 15/16): replay the layered
interaction from the state `(k, us, vs, ysc)` — `k` outer rounds still
allowed to start after the current one, `us` outer inputs so far, `vs` the
outer answers `e` has seen, `ysc` the inner answers consumed — against the
remaining recorded inner answers `ysr`.  A pending inner query with the
record exhausted is the emulator's next query; the round budget or a stall
of `e` stops it. -/
private noncomputable def emuGo (α : ProtocolFn U V X Y) (e : PFunDDS.DDE U V) :
    ℕ → List U → List (Option V) → List (Option Y) → List (Option Y) →
      Option X
  | k, us, vs, ysc, ysr =>
    if h : (α (us, ysc)).Dom then
      match (α (us, ysc)).get h with
      | Sum.inl x =>
          match ysr with
          | [] => some x
          | y :: ysr' => emuGo α e k us vs (ysc ++ [y]) ysr'
      | Sum.inr v =>
          match k with
          | 0 => none
          | k' + 1 =>
              match e (vs ++ [some v]) with
              | none => none
              | some u => emuGo α e k' (us ++ [u]) (vs ++ [some v]) ysc ysr
    else none
  termination_by k _ _ _ ysr => (k, ysr.length)

private theorem emuGo_of_not_dom {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {us : List U} {vs : List (Option V)}
    {ysc : List (Option Y)} (h : ¬ (α (us, ysc)).Dom) (k : ℕ)
    (ysr : List (Option Y)) :
    emuGo α e k us vs ysc ysr = none := by
  rw [emuGo]
  exact dif_neg h

private theorem emuGo_inl_nil {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V}
    {us : List U} {vs : List (Option V)} {ysc : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (us, ysc)) (k : ℕ) :
    emuGo α e k us vs ysc [] = some x := by
  have hdom : (α (us, ysc)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [emuGo, dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem emuGo_inl_cons {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V}
    {us : List U} {vs : List (Option V)} {ysc : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (us, ysc)) (k : ℕ) (y : Option Y)
    (ysr : List (Option Y)) :
    emuGo α e k us vs ysc (y :: ysr) = emuGo α e k us vs (ysc ++ [y]) ysr := by
  have hdom : (α (us, ysc)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [emuGo, dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem emuGo_inr_zero {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V}
    {us : List U} {vs : List (Option V)} {ysc : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (us, ysc)) (ysr : List (Option Y)) :
    emuGo α e 0 us vs ysc ysr = none := by
  have hdom : (α (us, ysc)).Dom := Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [emuGo, dif_pos hdom, Part.get_eq_of_mem hv hdom]

private theorem emuGo_inr_succ {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V}
    {us : List U} {vs : List (Option V)} {ysc : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (us, ysc)) (k : ℕ) (ysr : List (Option Y)) :
    emuGo α e (k + 1) us vs ysc ysr
      = match e (vs ++ [some v]) with
        | none => none
        | some u => emuGo α e k (us ++ [u]) (vs ++ [some v]) ysc ysr := by
  have hdom : (α (us, ysc)).Dom := Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [emuGo, dif_pos hdom, Part.get_eq_of_mem hv hdom]

/-- **The emulated environment `Dα` (MauRen11 Definitions 15/16)**: the
converter `α` folded into the environment `e`, as a deterministic
environment for the *inner* interface.  On an inner answer history it
replays the layered interaction — `e`'s outer queries are recomputable from
the outer answers, which are recomputable by walking `α` against the
recorded inner answers — and returns `α`'s next inner query; it stops
(`none`) when `e` stalls or once `n` outer rounds are complete (the
fuel-aware stop). -/
noncomputable def emulate (α : ProtocolFn U V X Y) (e : PFunDDS.DDE U V)
    (n : ℕ) : PFunDDS.DDE X Y := fun ys =>
  match n, e [] with
  | 0, _ => none
  | _ + 1, none => none
  | m + 1, some u₀ => emuGo α e m [u₀] [] [] ys

private theorem emulate_zero (α : ProtocolFn U V X Y) (e : PFunDDS.DDE U V)
    (ys : List (Option Y)) : emulate α e 0 ys = none := rfl

private theorem emulate_of_env_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} (hu : e [] = none) (n : ℕ)
    (ys : List (Option Y)) : emulate α e n ys = none := by
  cases n with
  | zero => rfl
  | succ m => simp only [emulate, hu]

private theorem emulate_succ {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V}
    {u₀ : U} (hu : e [] = some u₀) (m : ℕ) (ys : List (Option Y)) :
    emulate α e (m + 1) ys = emuGo α e m [u₀] [] [] ys := by
  simp only [emulate, hu]

open Classical in
/-- Plumbing for `replayTranscript`: parse the remaining inner transcript
`rem` from the state `(k, acc, u, ysc)` — `acc` the completed outer rounds,
`u` the current outer input, `ysc` the inner answers consumed — emitting an
outer entry at each completed round and stopping at the round budget, a
stall of `e`, or the end of the record. -/
private noncomputable def replayGo (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) :
    ℕ → List (U × Option V) → U → List (Option Y) → List (X × Option Y) →
      List (U × Option V)
  | k, acc, u, ysc, rem =>
    if h : (α (PFunDDS.transcriptInputs acc ++ [u], ysc)).Dom then
      match (α (PFunDDS.transcriptInputs acc ++ [u], ysc)).get h with
      | Sum.inl _ =>
          match rem with
          | [] => acc
          | p :: rem' => replayGo α e k acc u (ysc ++ [p.2]) rem'
      | Sum.inr v =>
          match k with
          | 0 => acc ++ [(u, some v)]
          | k' + 1 =>
              match e (PFunDDS.transcriptOutputs acc ++ [some v]) with
              | none => acc ++ [(u, some v)]
              | some u' => replayGo α e k' (acc ++ [(u, some v)]) u' ysc rem
    else acc
  termination_by k _ _ _ rem => (k, rem.length)

private theorem replayGo_inl_cons {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {ysc : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (PFunDDS.transcriptInputs acc ++ [u], ysc)) (k : ℕ)
    (p : X × Option Y) (rem : List (X × Option Y)) :
    replayGo α e k acc u ysc (p :: rem)
      = replayGo α e k acc u (ysc ++ [p.2]) rem := by
  have hdom : (α (PFunDDS.transcriptInputs acc ++ [u], ysc)).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [replayGo, dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem replayGo_inr_zero {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {ysc : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs acc ++ [u], ysc))
    (rem : List (X × Option Y)) :
    replayGo α e 0 acc u ysc rem = acc ++ [(u, some v)] := by
  have hdom : (α (PFunDDS.transcriptInputs acc ++ [u], ysc)).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [replayGo.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hv hdom]

private theorem replayGo_inr_succ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {ysc : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs acc ++ [u], ysc)) (k : ℕ)
    (rem : List (X × Option Y)) :
    replayGo α e (k + 1) acc u ysc rem
      = match e (PFunDDS.transcriptOutputs acc ++ [some v]) with
        | none => acc ++ [(u, some v)]
        | some u' => replayGo α e k (acc ++ [(u, some v)]) u' ysc rem := by
  have hdom : (α (PFunDDS.transcriptInputs acc ++ [u], ysc)).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [replayGo.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hv hdom]

/-- **Transcript reconstruction** (the `replay` pattern of
`RandomSystem.lean`, one level up): parse an inner transcript into the
outer transcript it induces — walk `α` and `e` over the recorded inner
answers, emitting one outer entry per completed round, cut after `n` outer
rounds. -/
noncomputable def replayTranscript (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) (n : ℕ) (t : List (X × Option Y)) :
    List (U × Option V) :=
  match n, e [] with
  | 0, _ => []
  | _ + 1, none => []
  | m + 1, some u₀ => replayGo α e m [] u₀ [] t

private theorem replayTranscript_zero (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) (t : List (X × Option Y)) :
    replayTranscript α e 0 t = [] := rfl

private theorem replayTranscript_of_env_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} (hu : e [] = none) (n : ℕ)
    (t : List (X × Option Y)) : replayTranscript α e n t = [] := by
  cases n with
  | zero => rfl
  | succ m => simp only [replayTranscript, hu]

private theorem replayTranscript_succ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {u₀ : U} (hu : e [] = some u₀) (m : ℕ)
    (t : List (X × Option Y)) :
    replayTranscript α e (m + 1) t = replayGo α e m [] u₀ [] t := by
  simp only [replayTranscript, hu]

/-! ### Definition 16: absorption into the distinguisher class -/

/-- MauRen11 **Definition 16**: the distinguisher class must be "closed
under emulation of a converter" — the emulation `Dα : R ↦ D(αR)` of
Definitions 15/16, whence the name.  Instantiated at the deterministic-environment class of CR18 §3.7.2: a
converter is **absorbable** if every outer environment-and-fuel pair
factors through some inner environment, inner fuel, and transcript
post-processing map, *uniformly in the system*.  Membership in the class
`Σ` is certified per converter (`emulable_of_answersWithin_of_dom`);
non-expansion of the distinguisher metric and preservation of equivalence
are corollaries of membership alone (`maxAdvantage_apply_le`,
`equivalent_apply` in `CompatibleMetric.lean`), never per-converter
theorems. -/
@[rs_rule "rs.capability.emulable" rs_emulable random_systems]
def Emulable (α : ProtocolFn U V X Y) : Prop :=
  ∀ (e : PFunDDS.DDE U V) (n : ℕ),
    ∃ (e' : PFunDDS.DDE X Y) (m : ℕ)
      (g : List (X × Option Y) → List (U × Option V)),
      ∀ s : PFunDDS.DDS X Y,
        PFunDDS.transcript (apply α s) e n
          = g (PFunDDS.transcript s e' m)

/-- The pointwise factorization of an absorbable converter, pushed through
the distribution (thesis Def 2.12's pushforward presentation): the applied
system's transcript distribution is the post-processing pushforward of the
assumed system's. -/
theorem transcriptDist_fTransform_of_transcript_eq
    {α : ProtocolFn U V X Y} {e : PFunDDS.DDE U V} {n : ℕ}
    {e' : PFunDDS.DDE X Y} {m : ℕ}
    {g : List (X × Option Y) → List (U × Option V)}
    (hg : ∀ s, PFunDDS.transcript (apply α s) e n
      = g (PFunDDS.transcript s e' m)) (S : PFunPDS X Y) :
    transcriptDist (Dist.fTransform (fun s => apply α s) S) e n
      = Dist.fTransform g (transcriptDist S e' m) := by
  unfold transcriptDist
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun f => Dist.fTransform f S) (funext fun s => by
    simp only [Function.comp_apply]
    exact hg s)

/-! ### The joint run

`EmuRun tout u tin`: the canonical joint state of the emulation — `tout`
the completed outer rounds, `u` the current round's outer input, `tin` the
inner transcript so far.  The inner answers are the computed `s⊥`-outputs
(CR18 Def 3.9's completion), so an `EmuRun` state is simultaneously a
`drive` state of the applied system, an `emuGo` state of the emulated
environment, and a `replayGo` state of the reconstruction — the `CompRun`
pattern of `ComposeRealization.lean`. -/

section Bridge

variable (α : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE U V)

/-- The joint run of the layered interaction (MauRen11 Def 15/16). -/
inductive EmuRun :
    List (U × Option V) → U → List (X × Option Y) → Prop
  | start {u : U} (hu : e [] = some u) : EmuRun [] u []
  | query {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
      {x : X} (hr : EmuRun tout u tin)
      (hx : Sum.inl x ∈ α (PFunDDS.transcriptInputs tout ++ [u],
        PFunDDS.transcriptOutputs tin)) :
      EmuRun tout u (tin ++ [(x,
        PFunDDS.output (s⊥) (PFunDDS.transcriptInputs tin ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp))])
  | answer {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
      {v : V} {u' : U} (hr : EmuRun tout u tin)
      (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs tout ++ [u],
        PFunDDS.transcriptOutputs tin))
      (hu' : e (PFunDDS.transcriptOutputs tout ++ [some v]) = some u') :
      EmuRun (tout ++ [(u, some v)]) u' tin

variable {α s e}

theorem emuRun_env_some {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    ∃ u₀, e [] = some u₀ := by
  induction hr with
  | start hu => exact ⟨_, hu⟩
  | query hr hx ih => exact ih
  | answer hr hv hu' ih => exact ih

/-- Joint states sit on `α`'s trace tree — `EmuRun`'s constructors mirror
`Reach`'s. -/
theorem emuRun_reach {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    Reach α (PFunDDS.transcriptInputs tout ++ [u],
      PFunDDS.transcriptOutputs tin) := by
  induction hr with
  | start hu => simpa using Reach.first _
  | query hr hx ih =>
      rw [transcriptOutputs_append]
      exact Reach.answer ih hx _
  | answer hr hv hu' ih =>
      rw [transcriptInputs_append]
      exact Reach.next ih hv _

/-- **Replay, emulator side**: from the initial state, `emuGo` re-walks the
recorded inner answers of a joint state back to that state — the emulated
environment deterministically re-traces its own history. -/
theorem emuGo_replay {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    ∀ {u₀ : U}, e [] = some u₀ → ∀ {m : ℕ}, tout.length ≤ m →
      ∀ ext : List (Option Y),
      emuGo α e m [u₀] [] [] (PFunDDS.transcriptOutputs tin ++ ext)
        = emuGo α e (m - tout.length)
            (PFunDDS.transcriptInputs tout ++ [u])
            (PFunDDS.transcriptOutputs tout)
            (PFunDDS.transcriptOutputs tin) ext := by
  induction hr with
  | start hu =>
      intro u₀ hu₀ m hm ext
      rw [hu₀] at hu
      obtain rfl := Option.some.inj hu
      simp
  | query hr hx ih =>
      intro u₀ hu₀ m hm ext
      rw [transcriptOutputs_append, List.append_assoc,
        List.singleton_append, ih hu₀ hm]
      exact emuGo_inl_cons hx _ _ _
  | answer hr hv hu' ih =>
      rename_i tout u tin v u'
      intro u₀ hu₀ m hm ext
      rw [List.length_append, List.length_singleton] at hm
      rw [ih hu₀ (by omega) ext]
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [hk, emuGo_inr_succ hv _ ext, hu', transcriptInputs_append,
        transcriptOutputs_append, List.length_append,
        List.length_singleton]

/-- `emuGo_replay` through the `emulate` wrapper. -/
theorem emulate_replay {n : ℕ} {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin)
    (hn : tout.length < n) (ext : List (Option Y)) :
    emulate α e n (PFunDDS.transcriptOutputs tin ++ ext)
      = emuGo α e (n - 1 - tout.length)
          (PFunDDS.transcriptInputs tout ++ [u])
          (PFunDDS.transcriptOutputs tout)
          (PFunDDS.transcriptOutputs tin) ext := by
  obtain ⟨u₀, hu₀⟩ := emuRun_env_some hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [emulate_succ hu₀, Nat.add_sub_cancel,
    emuGo_replay hr hu₀ (by omega) ext]

/-- **Replay, reconstruction side**: from the initial state, `replayGo`
re-parses the recorded inner transcript of a joint state back to that
state. -/
theorem replayGo_replay {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    ∀ {u₀ : U}, e [] = some u₀ → ∀ {m : ℕ}, tout.length ≤ m →
      ∀ ext : List (X × Option Y),
      replayGo α e m [] u₀ [] (tin ++ ext)
        = replayGo α e (m - tout.length) tout u
            (PFunDDS.transcriptOutputs tin) ext := by
  induction hr with
  | start hu =>
      intro u₀ hu₀ m hm ext
      rw [hu₀] at hu
      obtain rfl := Option.some.inj hu
      simp
  | query hr hx ih =>
      intro u₀ hu₀ m hm ext
      rw [List.append_assoc, List.singleton_append, ih hu₀ hm,
        replayGo_inl_cons hx, transcriptOutputs_append]
  | answer hr hv hu' ih =>
      rename_i tout u tin v u'
      intro u₀ hu₀ m hm ext
      rw [List.length_append, List.length_singleton] at hm
      rw [ih hu₀ (by omega) ext]
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [hk, replayGo_inr_succ hv _ ext, hu', List.length_append,
        List.length_singleton]

/-- **Drive certification**: the completed rounds of a joint state come from
a genuine `apply α s` computation — a `driveOuter` run over the completed
outer inputs plus a round-anchor `drive` continuation for the open round
(CR18 Def 3.9 read off the state; the `compRun_middle` pattern of
`ComposeRealization.lean`). -/
theorem emuRun_driveOuter {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    ∃ (vsP : List V) (xs₀ : List X) (ys₀ : List (Option Y)),
      PFunDDS.transcriptOutputs tout = vsP.map some ∧
      (∃ fuel, (vsP, xs₀, ys₀) ∈ driveOuter α s fuel [] [] []
        (PFunDDS.transcriptInputs tout)) ∧
      ∀ {fuel : ℕ} {r : V × List X × List (Option Y)},
        r ∈ drive α s fuel (PFunDDS.transcriptInputs tout ++ [u])
          (PFunDDS.transcriptInputs tin) (PFunDDS.transcriptOutputs tin) →
        ∃ fuel', r ∈ drive α s fuel'
          (PFunDDS.transcriptInputs tout ++ [u]) xs₀ ys₀ := by
  induction hr with
  | start hu =>
      refine ⟨[], [], [], by simp, ⟨0, by simp [driveOuter]⟩, ?_⟩
      intro fuel r hm
      exact ⟨fuel, by simpa using hm⟩
  | query hr hx ih =>
      obtain ⟨vsP, xs₀, ys₀, hsome, hrun, hcont⟩ := ih
      refine ⟨vsP, xs₀, ys₀, hsome, hrun, ?_⟩
      intro fuel r hm
      simp only [transcriptInputs_append, transcriptOutputs_append] at hm
      exact hcont (drive_mem_query α s hx hm)
  | answer hr hv hu' ih =>
      rename_i tout u tin v u'
      obtain ⟨vsP, xs₀, ys₀, hsome, ⟨fuel₁, hrun⟩, hcont⟩ := ih
      have hstep : (v, PFunDDS.transcriptInputs tin,
          PFunDDS.transcriptOutputs tin) ∈ drive α s 1
          (PFunDDS.transcriptInputs tout ++ [u])
          (PFunDDS.transcriptInputs tin)
          (PFunDDS.transcriptOutputs tin) :=
        drive_mem_answer α s hv 0
      obtain ⟨fuel₂, hstep'⟩ := hcont hstep
      refine ⟨vsP ++ [v], PFunDDS.transcriptInputs tin,
        PFunDDS.transcriptOutputs tin, ?_, ?_, ?_⟩
      · simp only [transcriptOutputs_append, hsome, List.map_append,
          List.map_cons, List.map_nil]
      · refine ⟨max fuel₁ fuel₂, ?_⟩
        simp only [transcriptInputs_append]
        rw [driveOuter_append α s _ (PFunDDS.transcriptInputs tout) [u]]
        rw [Part.mem_bind_iff]
        refine ⟨(vsP, xs₀, ys₀),
          driveOuter_mono_le α s (le_max_left _ _) hrun, ?_⟩
        rw [Part.mem_map_iff]
        refine ⟨([v], PFunDDS.transcriptInputs tin,
          PFunDDS.transcriptOutputs tin), ?_, rfl⟩
        show _ ∈ (drive α s _ (PFunDDS.transcriptInputs tout ++ [u])
          xs₀ ys₀).bind _
        rw [Part.mem_bind_iff]
        refine ⟨(v, PFunDDS.transcriptInputs tin,
          PFunDDS.transcriptOutputs tin),
          drive_mono_le α s (le_max_right _ _) hstep', ?_⟩
        simp [driveOuter]
      · intro fuel r hm
        exact ⟨fuel, hm⟩

/-- The applied system answers the open round: a pending outer answer at a
joint state is a genuine `apply α s` value (the `compRun_middle_value`
pattern). -/
theorem emuRun_applyRaw_mem {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} {v : V} (hr : EmuRun α s e tout u tin)
    (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs tout ++ [u],
      PFunDDS.transcriptOutputs tin)) :
    v ∈ applyRaw α s (PFunDDS.transcriptInputs tout ++ [u]) := by
  obtain ⟨vsP, xs₀, ys₀, hsome, ⟨fuel₁, hrun⟩, hcont⟩ := emuRun_driveOuter hr
  have hstep : (v, PFunDDS.transcriptInputs tin,
      PFunDDS.transcriptOutputs tin) ∈ drive α s 1
      (PFunDDS.transcriptInputs tout ++ [u])
      (PFunDDS.transcriptInputs tin) (PFunDDS.transcriptOutputs tin) :=
    drive_mem_answer α s hv 0
  obtain ⟨fuel₂, hstep'⟩ := hcont hstep
  rw [mem_applyRaw]
  refine ⟨max fuel₁ fuel₂, ?_⟩
  rw [mem_applyRawAt_iff]
  refine ⟨(vsP ++ [v], PFunDDS.transcriptInputs tin,
    PFunDDS.transcriptOutputs tin), ?_, by simp⟩
  rw [driveOuter_append α s _ (PFunDDS.transcriptInputs tout) [u]]
  rw [Part.mem_bind_iff]
  refine ⟨(vsP, xs₀, ys₀),
    driveOuter_mono_le α s (le_max_left _ _) hrun, ?_⟩
  rw [Part.mem_map_iff]
  refine ⟨([v], PFunDDS.transcriptInputs tin,
    PFunDDS.transcriptOutputs tin), ?_, rfl⟩
  show _ ∈ (drive α s _ (PFunDDS.transcriptInputs tout ++ [u]) xs₀ ys₀).bind _
  rw [Part.mem_bind_iff]
  refine ⟨(v, PFunDDS.transcriptInputs tin, PFunDDS.transcriptOutputs tin),
    drive_mono_le α s (le_max_right _ _) hstep', ?_⟩
  simp [driveOuter]

/-- One outer round of the applied system's transcript, computed: with the
round's answer certified, the next transcript entry is `(u, some v)` — the
`⊥`-completion of a defined round answers properly. -/
private theorem transcript_apply_snoc {tout : List (U × Option V)} {u : U}
    {v : V}
    (hT : PFunDDS.transcript (apply α s) e tout.length = tout)
    (hu : e (PFunDDS.transcriptOutputs tout) = some u)
    (hvmem : v ∈ applyRaw α s (PFunDDS.transcriptInputs tout ++ [u])) :
    PFunDDS.transcript (apply α s) e (tout.length + 1)
      = tout ++ [(u, some v)] := by
  have hfire : e ((PFunDDS.transcript (apply α s) e tout.length)↓ᵧ)
      = some u := by
    rw [hT]; exact hu
  rw [transcript_succ_fire hfire, hT]
  have hdom : PFunDDS.transcriptInputs tout ++ [u]
      ∈ PFunDDS.dom (apply α s) := Part.dom_iff_mem.mpr ⟨v, hvmem⟩
  have hprev : PFunDDS.transcriptInputs tout ∈ PFunDDS.dom (apply α s) ∨
      PFunDDS.transcriptInputs tout = [] := by
    rcases eq_or_ne (PFunDDS.transcriptInputs tout) [] with h | h
    · exact Or.inr h
    · exact Or.inl (PFunDDS.prefix_closed (apply α s) ⟨[u], rfl⟩ h hdom)
  have hout : PFunDDS.output ((apply α s)⊥)
      (PFunDDS.transcriptInputs tout ++ [u])
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
    rw [PFunDDS.output_fullyDefined_append_of_mem (apply α s) _ u hprev hdom]
    exact congrArg some (Part.mem_unique (Part.get_mem hdom) hvmem)
  rw [hout]

/-- **The outer transcript of a joint state**: after the recorded rounds the
applied system's transcript against `e` is exactly the recorded outer
transcript, with `e`'s next query pending. -/
theorem emuRun_transcript_apply {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    PFunDDS.transcript (apply α s) e tout.length = tout ∧
      e (PFunDDS.transcriptOutputs tout) = some u := by
  induction hr with
  | start hu => exact ⟨rfl, hu⟩
  | query hr hx ih => exact ih
  | answer hr hv hu' ih =>
      rename_i tout u tin v u'
      obtain ⟨hT, hu⟩ := ih
      have hsnoc := transcript_apply_snoc hT hu (emuRun_applyRaw_mem hr hv)
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        exact hsnoc
      · rw [transcriptOutputs_append]
        exact hu'

/-! ### Streak bookkeeping and termination (CR18 Def 3.8's bound, cashed) -/

/-- General-append projection split (`transcriptOutputs` is a map). -/
@[simp] private theorem transcriptOutputs_append_list
    (t₁ t₂ : List (X × Option Y)) :
    PFunDDS.transcriptOutputs (t₁ ++ t₂)
      = PFunDDS.transcriptOutputs t₁ ++ PFunDDS.transcriptOutputs t₂ := by
  simp [PFunDDS.transcriptOutputs]

/-- General-append projection split (`transcriptInputs` is a map). -/
@[simp] private theorem transcriptInputs_append_list
    (t₁ t₂ : List (X × Option Y)) :
    PFunDDS.transcriptInputs (t₁ ++ t₂)
      = PFunDDS.transcriptInputs t₁ ++ PFunDDS.transcriptInputs t₂ := by
  simp [PFunDDS.transcriptInputs]

/-- A reachable pair extends along a chain of answered queries. -/
private theorem reach_append_of_streak {α : ProtocolFn U V X Y}
    {us : List U} :
    ∀ (exto : List (Option Y)) {ys₀ : List (Option Y)},
      Reach α (us, ys₀) →
      (∀ k, k < exto.length → ∃ x, Sum.inl x ∈ α (us, ys₀ ++ exto.take k)) →
      Reach α (us, ys₀ ++ exto) := by
  intro exto
  induction exto using List.reverseRecOn with
  | nil =>
      intro ys₀ h _
      simpa using h
  | append_singleton exto y ih =>
      intro ys₀ h hstreak
      have hre' : Reach α (us, ys₀ ++ exto) := by
        refine ih h ?_
        intro k hk
        have h2 := hstreak k
          (by rw [List.length_append, List.length_singleton]; omega)
        rwa [List.take_append_of_le_length (le_of_lt hk)] at h2
      obtain ⟨x, hx⟩ := hstreak exto.length
        (by rw [List.length_append, List.length_singleton]; omega)
      rw [List.take_append_of_le_length le_rfl, List.take_length] at hx
      rw [← List.append_assoc]
      exact Reach.answer hre' hx y

/-- One more query on an open streak: the extended chain is still a chain,
and its length stays under `B` (else `hB` is breached at the round
anchor). -/
private theorem streak_snoc {α : ProtocolFn U V X Y} {B : ℕ}
    (hB : AnswersWithin α B) {us : List U} {ys₀ : List (Option Y)}
    {ext : List (X × Option Y)} (hre : Reach α (us, ys₀))
    (hstreak : ∀ k, k < ext.length → ∃ x, Sum.inl x ∈ α
      (us, ys₀ ++ (PFunDDS.transcriptOutputs ext).take k))
    {x : X} (hx : Sum.inl x ∈ α (us, ys₀ ++ PFunDDS.transcriptOutputs ext))
    (p : X × Option Y) :
    (∀ k, k < (ext ++ [p]).length → ∃ x', Sum.inl x' ∈ α
      (us, ys₀ ++ (PFunDDS.transcriptOutputs (ext ++ [p])).take k)) ∧
      (ext ++ [p]).length ≤ B - 1 := by
  have hstreak' : ∀ k, k < (ext ++ [p]).length → ∃ x', Sum.inl x' ∈ α
      (us, ys₀ ++ (PFunDDS.transcriptOutputs (ext ++ [p])).take k) := by
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    rw [transcriptOutputs_append]
    rcases Nat.lt_or_ge k ext.length with hk' | hk'
    · rw [List.take_append_of_le_length
        (by simp only [transcriptOutputs_length]; omega)]
      exact hstreak k hk'
    · have hkeq : k = ext.length := by omega
      subst hkeq
      rw [List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp)]
      exact ⟨x, hx⟩
  refine ⟨hstreak', ?_⟩
  by_contra hcon
  rw [List.length_append, List.length_singleton] at hcon
  exact hB (us, ys₀) hre (PFunDDS.transcriptOutputs (ext ++ [p]))
    (by
      simp only [transcriptOutputs_length, List.length_append,
        List.length_singleton]
      omega)
    (fun k hk => hstreak' k
      (by simpa only [transcriptOutputs_length] using hk))

/-- **Streak decomposition of a joint state** (CR18 Def 3.8's finite-bound
clause on the trace tree): the inner transcript splits at the current
round's anchor; the open streak is a chain of `α`-queries of length `< B`,
and the closed rounds contribute `< B` inner entries each. -/
theorem emuRun_streak {B : ℕ} (hB : AnswersWithin α B)
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    (hr : EmuRun α s e tout u tin) :
    ∃ tin₀ ext, tin = tin₀ ++ ext ∧
      Reach α (PFunDDS.transcriptInputs tout ++ [u],
        PFunDDS.transcriptOutputs tin₀) ∧
      (∀ k, k < ext.length → ∃ x, Sum.inl x ∈ α
        (PFunDDS.transcriptInputs tout ++ [u],
          PFunDDS.transcriptOutputs tin₀
            ++ (PFunDDS.transcriptOutputs ext).take k)) ∧
      tin₀.length ≤ tout.length * (B - 1) ∧ ext.length ≤ B - 1 := by
  induction hr with
  | start hu =>
      refine ⟨[], [], rfl, by simpa using Reach.first _, ?_, by simp, by simp⟩
      intro k hk
      exact absurd hk (by simp)
  | query hr hx ih =>
      rename_i tout u tin x
      obtain ⟨tin₀, ext, rfl, hre, hstreak, hlen₀, hlenE⟩ := ih
      have hx' : Sum.inl x ∈ α (PFunDDS.transcriptInputs tout ++ [u],
          PFunDDS.transcriptOutputs tin₀
            ++ PFunDDS.transcriptOutputs ext) := by
        simpa using hx
      have hpair := streak_snoc hB hre hstreak hx'
        ((x, PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs (tin₀ ++ ext) ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp)) : X × Option Y)
      exact ⟨tin₀, ext ++ [(x, PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs (tin₀ ++ ext) ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp))],
        List.append_assoc _ _ _, hre, hpair.1, hlen₀, hpair.2⟩
  | answer hr hv hu' ih =>
      rename_i tout u tin v u'
      obtain ⟨tin₀, ext, rfl, hre, hstreak, hlen₀, hlenE⟩ := ih
      have hreach : Reach α (PFunDDS.transcriptInputs tout ++ [u],
          PFunDDS.transcriptOutputs (tin₀ ++ ext)) := by
        rw [transcriptOutputs_append_list]
        exact reach_append_of_streak _ hre
          (fun k hk => hstreak k (by simpa using hk))
      refine ⟨tin₀ ++ ext, [], (List.append_nil _).symm, ?_, ?_, ?_, by simp⟩
      · simp only [transcriptInputs_append]
        exact Reach.next hreach hv u'
      · intro k hk
        exact absurd hk (by simp)
      · rw [List.length_append, List.length_append, List.length_singleton,
          Nat.succ_mul]
        omega

/-- **Round completion**: from any joint state a bounded streak of answered
inner queries (`hB`, `hdef`) reaches an outer answer — one CR18 Def 3.9
round terminates (the `hseg` pattern of `ComposeRealization.lean`). -/
theorem emuRun_round {B : ℕ} (hB : AnswersWithin α B)
    (hdef : ∀ p, Reach α p → (α p).Dom) :
    ∀ (c : ℕ) {tout : List (U × Option V)} {u : U}
      {tin tin₀ ext : List (X × Option Y)},
      EmuRun α s e tout u tin → tin = tin₀ ++ ext →
      Reach α (PFunDDS.transcriptInputs tout ++ [u],
        PFunDDS.transcriptOutputs tin₀) →
      (∀ k, k < ext.length → ∃ x, Sum.inl x ∈ α
        (PFunDDS.transcriptInputs tout ++ [u],
          PFunDDS.transcriptOutputs tin₀
            ++ (PFunDDS.transcriptOutputs ext).take k)) →
      B ≤ ext.length + c →
      ∃ tin' v, EmuRun α s e tout u tin' ∧
        Sum.inr v ∈ α (PFunDDS.transcriptInputs tout ++ [u],
          PFunDDS.transcriptOutputs tin') := by
  intro c
  induction c with
  | zero =>
      intro tout u tin tin₀ ext hr heq hre hstreak hc
      exact absurd (fun k hk => hstreak k (by simpa using hk))
        (hB _ hre (PFunDDS.transcriptOutputs ext) (by simpa using hc))
  | succ c ih =>
      intro tout u tin tin₀ ext hr heq hre hstreak hc
      subst heq
      obtain ⟨mv, hmv⟩ := Part.dom_iff_mem.mp (hdef _ (emuRun_reach hr))
      cases mv with
      | inr v => exact ⟨tin₀ ++ ext, v, hr, hmv⟩
      | inl x =>
          have hx' : Sum.inl x ∈ α (PFunDDS.transcriptInputs tout ++ [u],
              PFunDDS.transcriptOutputs tin₀
                ++ PFunDDS.transcriptOutputs ext) := by
            simpa using hmv
          have hpair := streak_snoc hB hre hstreak hx'
            ((x, PFunDDS.output (s⊥)
              (PFunDDS.transcriptInputs (tin₀ ++ ext) ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)) : X × Option Y)
          exact ih (EmuRun.query hr hmv) (List.append_assoc _ _ _) hre
            hpair.1
            (by rw [List.length_append, List.length_singleton]; omega)

/-- **Termination of the emulation**: from any joint state within the round
budget, the interaction reaches a terminal configuration — a final outer
answer with either the budget exhausted or `e` stalled. -/
theorem emuRun_terminal {B : ℕ} (hB : AnswersWithin α B)
    (hdef : ∀ p, Reach α p → (α p).Dom) {n : ℕ} :
    ∀ (k : ℕ) {tout : List (U × Option V)} {u : U}
      {tin : List (X × Option Y)},
      EmuRun α s e tout u tin → tout.length + k + 1 = n →
      ∃ tout' u' tin' v, EmuRun α s e tout' u' tin' ∧
        Sum.inr v ∈ α (PFunDDS.transcriptInputs tout' ++ [u'],
          PFunDDS.transcriptOutputs tin') ∧
        tout'.length + 1 ≤ n ∧
        (tout'.length + 1 = n ∨
          e (PFunDDS.transcriptOutputs tout' ++ [some v]) = none) := by
  intro k
  induction k with
  | zero =>
      intro tout u tin hr hn
      obtain ⟨tin₀, ext, heq, hre, hstreak, -, hlenE⟩ := emuRun_streak hB hr
      obtain ⟨tin', v, hr', hv⟩ := emuRun_round hB hdef (B - ext.length)
        hr heq hre hstreak (by omega)
      exact ⟨tout, u, tin', v, hr', hv, by omega, Or.inl (by omega)⟩
  | succ k ih =>
      intro tout u tin hr hn
      obtain ⟨tin₀, ext, heq, hre, hstreak, -, hlenE⟩ := emuRun_streak hB hr
      obtain ⟨tin', v, hr', hv⟩ := emuRun_round hB hdef (B - ext.length)
        hr heq hre hstreak (by omega)
      rcases he : e (PFunDDS.transcriptOutputs tout ++ [some v]) with _ | u'
      · exact ⟨tout, u, tin', v, hr', hv, by omega, Or.inr he⟩
      · exact ih (EmuRun.answer hr' hv he)
          (by rw [List.length_append, List.length_singleton]; omega)

/-- At a terminal configuration the emulated environment stops: the round
budget is exhausted or `e` has stalled — the fuel-aware stop of MauRen11
Def 15/16. -/
private theorem emulate_terminal_stall {n : ℕ} {tout : List (U × Option V)}
    {u : U} {tin : List (X × Option Y)} {v : V}
    (hr : EmuRun α s e tout u tin)
    (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs tout ++ [u],
      PFunDDS.transcriptOutputs tin))
    (hn : tout.length < n)
    (hstop : tout.length + 1 = n ∨
      e (PFunDDS.transcriptOutputs tout ++ [some v]) = none) :
    emulate α e n (PFunDDS.transcriptOutputs tin) = none := by
  have h := emulate_replay hr hn []
  rw [List.append_nil] at h
  rw [h]
  rcases hk : n - 1 - tout.length with _ | k'
  · exact emuGo_inr_zero hv []
  · rw [emuGo_inr_succ hv k' []]
    rcases hstop with hstop | hstop
    · exfalso
      omega
    · rw [hstop]

/-- **The inner transcript of a joint state**: the recorded inner transcript
is exactly the transcript of `s` against the emulated environment, at its
own length. -/
theorem emuRun_transcript {n : ℕ} {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRun α s e tout u tin) :
    tout.length < n →
    PFunDDS.transcript s (emulate α e n) tin.length = tin := by
  induction hr with
  | start hu => intro _; rfl
  | query hr hx ih =>
      rename_i tout u tin x
      intro hn
      have hT := ih hn
      have hfire : emulate α e n
          ((PFunDDS.transcript s (emulate α e n) tin.length)↓ᵧ)
          = some x := by
        rw [hT]
        have h := emulate_replay hr hn []
        rw [List.append_nil] at h
        rw [h]
        exact emuGo_inl_nil hx _
      rw [List.length_append, List.length_singleton,
        transcript_succ_fire hfire, hT]
  | answer hr hv hu' ih =>
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      exact ih (by omega)

/-- At a terminal configuration the reconstruction emits the final round's
entry and stops — matching the emulator's fuel-aware stop. -/
private theorem replayGo_terminal {tout : List (U × Option V)} {u : U}
    {ysc : List (Option Y)} {v : V} {m : ℕ}
    (hv : Sum.inr v ∈ α (PFunDDS.transcriptInputs tout ++ [u], ysc))
    (hstop : tout.length + 1 = m + 1 ∨
      e (PFunDDS.transcriptOutputs tout ++ [some v]) = none)
    (rem : List (X × Option Y)) :
    replayGo α e (m - tout.length) tout u ysc rem
      = tout ++ [(u, some v)] := by
  rcases hk : m - tout.length with _ | k'
  · exact replayGo_inr_zero hv rem
  · rw [replayGo_inr_succ hv k' rem]
    rcases hstop with hstop | hstop
    · exfalso
      omega
    · rw [hstop]

end Bridge

/-! ### The bridge -/

/-- **The environment-emulation bridge** (MauRen11 Definitions 15/16; CR18
Def 3.9): for a productive converter — bounded query streaks (`hB`, CR18
Def 3.8) and no silence on reachable pairs (`hdef`) — and for **every**
system `s`, the transcript of the applied system against `e` is the
reconstruction of the transcript of `s` against the emulated environment.
The inner fuel `n * B` dominates the at most `n·(B−1)` inner rounds
actually consumed; the emulator's fuel-aware stop freezes the inner
transcript at its true length, so any sufficient fuel yields the same
value. -/
theorem transcript_apply (α : ProtocolFn U V X Y) {B : ℕ}
    (hB : AnswersWithin α B) (hdef : ∀ p, Reach α p → (α p).Dom)
    (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE U V) (n : ℕ) :
    PFunDDS.transcript (apply α s) e n
      = replayTranscript α e n
          (PFunDDS.transcript s (emulate α e n) (n * B)) := by
  rcases n with _ | m
  · rfl
  rcases hu₀ : e [] with _ | u₀
  · rw [replayTranscript_of_env_nil hu₀]
    have hstall : e ((PFunDDS.transcript (apply α s) e 0)↓ᵧ) = none := hu₀
    exact transcript_freeze hstall (Nat.zero_le _)
  · have hbase : EmuRun α s e [] u₀ [] := EmuRun.start hu₀
    obtain ⟨tout, u, tin, v, hr, hv, hle, hstop⟩ :=
      emuRun_terminal hB hdef (n := m + 1) m hbase (by simp)
    obtain ⟨hT, hu⟩ := emuRun_transcript_apply hr
    have hsnoc := transcript_apply_snoc hT hu (emuRun_applyRaw_mem hr hv)
    have hLHS : PFunDDS.transcript (apply α s) e (m + 1)
        = tout ++ [(u, some v)] := by
      rcases hstop with hstop | hstop
      · rw [← hstop]
        exact hsnoc
      · have hfreeze : e ((PFunDDS.transcript (apply α s) e
            (tout.length + 1))↓ᵧ) = none := by
          rw [hsnoc, transcriptOutputs_append]
          exact hstop
        rw [transcript_freeze hfreeze hle, hsnoc]
    have hlen : tin.length ≤ (m + 1) * B := by
      obtain ⟨tin₀, ext, rfl, -, -, hlen₀, hlenE⟩ := emuRun_streak hB hr
      have h1 : (tout.length + 1) * (B - 1) ≤ (m + 1) * B :=
        Nat.mul_le_mul hle (Nat.sub_le B 1)
      rw [List.length_append]
      rw [Nat.succ_mul] at h1
      omega
    have hstall := emulate_terminal_stall hr hv (by omega) hstop
    have hTin : PFunDDS.transcript s (emulate α e (m + 1)) ((m + 1) * B)
        = tin := by
      have h1 := emuRun_transcript hr (n := m + 1) (by omega)
      have h2 : emulate α e (m + 1)
          ((PFunDDS.transcript s (emulate α e (m + 1)) tin.length)↓ᵧ)
          = none := by
        rw [h1]
        exact hstall
      rw [transcript_freeze h2 hlen, h1]
    rw [hLHS, hTin, replayTranscript_succ hu₀]
    have h3 := replayGo_replay hr hu₀ (m := m) (by omega) []
    rw [List.append_nil] at h3
    rw [h3]
    exact (replayGo_terminal hv hstop []).symm

/-- **The bridge through the pushforward** (MauRen11 Def 15/16): the
transcript distribution of the applied random system is the
`replayTranscript`-pushforward of the assumed system's transcript
distribution under the emulated environment.  Stated on the
`Dist.fTransform` form of converter application; its `PFunPDS.apply`
packaging lives downstream in `CompatibleMetric.lean`. -/
theorem transcriptDist_apply (α : ProtocolFn U V X Y) {B : ℕ}
    (hB : AnswersWithin α B) (hdef : ∀ p, Reach α p → (α p).Dom)
    (S : PFunPDS X Y) (e : PFunDDS.DDE U V) (n : ℕ) :
    transcriptDist (Dist.fTransform (fun s => apply α s) S) e n
      = Dist.fTransform (replayTranscript α e n)
          (transcriptDist S (emulate α e n) (n * B)) := by
  unfold transcriptDist
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun f => Dist.fTransform f S) (funext fun s => by
    simp only [Function.comp_apply]
    exact transcript_apply α hB hdef s e n)

/-- **The productivity certificate** for Def 16 membership: bounded query
streaks (CR18 Def 3.8) plus no silence on reachable pairs make the
emulated environment `emulate α e n`, inner fuel `n·B`, and the
reconstruction `replayTranscript α e n` the required factorization —
`transcript_apply` is the canonical certificate.

**This is the site that consumes Def 3.8's uniform quantifier order.**
`Emulable` fixes the inner fuel `m` *before* the assumed system `s` is
quantified, so the fuel may depend on the outer round count `n` and on
nothing else — in particular not on the inner answers, which are `s`'s
output.  A merely pointwise bound (`PFunConverter.AnswersEventually`, CR18
Def 3.8's own prose) therefore cannot be turned into fuel at all:
`PFunConverter.answerGrowthFn` satisfies the prose and admits no bound as a
function of the round count.  What is genuinely needed here is uniformity in
the *answers* — `PFunConverter.AnswersWithinDepth`, which would give fuel
`∑_{i<n} F i` in place of `n * B`; uniformity in the round index on top of
that is slack (`PFunConverter.roundGrowthFn`).  Note the contrast with
`applyRaw_dom`, CR18's own undischarged Def 3.9 obligation: *that* one holds
for the prose class, one round at a time. -/
theorem emulable_of_answersWithin_of_dom (α : ProtocolFn U V X Y) {B : ℕ}
    (hB : AnswersWithin α B) (hdef : ∀ p, Reach α p → (α p).Dom) :
    Emulable α := fun e n =>
  ⟨emulate α e n, n * B, replayTranscript α e n,
    fun s => transcript_apply α hB hdef s e n⟩

/-- The DDD-surface form of absorption, derived: CR18 §3.7.2's canonical
accept-set distinguishers (`DDD.ofDDE`, the §4.10.1 normal form) absorb
the converter — the absorbed distinguisher replays the inner environment
and tests the reconstructed transcript.  (General DDDs reduce to this
class by §4.10.1 truncation on finite supports; wiring `AbsorbDPI`'s
step-level verdict engine through this surface is later-phase work.) -/
theorem Emulable.exists_ddd_verdict_iff {α : ProtocolFn U V X Y}
    (h : Emulable α) (e : PFunDDS.DDE U V) (n : ℕ)
    (A : List (U × Option V) → Bool) :
    ∃ (e' : PFunDDS.DDE X Y) (m : ℕ) (A' : List (X × Option Y) → Bool),
      ∀ s, PFunDDS.verdict (PFunDDS.DDD.ofDDE e n A) (apply α s)
        ↔ PFunDDS.verdict (PFunDDS.DDD.ofDDE e' m A') s := by
  obtain ⟨e', m, g, hg⟩ := h e n
  refine ⟨e', m, fun t => A (g t), fun s => ?_⟩
  rw [verdict_ofDDE_iff, verdict_ofDDE_iff, hg s]

/-- **Def 16 closure under serial composition**: emulations chain — the
absorbed environment of `α` is itself an environment, which `β`'s
emulation absorbs in turn; the reconstruction maps compose.  The
`AnswersInY α` hypothesis is exactly what the action law `apply_comp`
carries (the staged side must not outrun the stack past a `⊥`). -/
theorem emulable_comp {W : Type u'} {Z : Type w'}
    (α : ProtocolFn W Z U V) (β : ProtocolFn U V X Y)
    (hα : AnswersInY α) (hαE : Emulable α) (hβE : Emulable β) :
    Emulable (comp α β) := by
  intro e n
  obtain ⟨e₁, m₁, g₁, hg₁⟩ := hαE e n
  obtain ⟨e₂, m₂, g₂, hg₂⟩ := hβE e₁ m₁
  refine ⟨e₂, m₂, fun trc => g₁ (g₂ trc), fun s => ?_⟩
  rw [apply_comp α β s hα, hg₁ (apply β s), hg₂ s]

/-! ### Totality of the applied system -/

/-- **Totality of `apply` under productivity** (CR18 Def 3.9 under Def 3.8's
bound): with bounded query streaks and no silence on reachable pairs, every
outer round of the transcript equations is one answered streak ended by an
outer answer — the applied raw system is defined on every nonempty outer
history.  (Extracted against the fixed-query-list environment
`playQueries`.) -/
theorem applyRaw_dom (α : ProtocolFn U V X Y) {B : ℕ}
    (hB : AnswersWithin α B) (hdef : ∀ p, Reach α p → (α p).Dom)
    (s : PFunDDS.DDS X Y) {us : List U} (hne : us ≠ []) :
    (applyRaw α s us).Dom := by
  have hinv : ∀ {tout : List (U × Option V)} {u : U}
      {tin : List (X × Option Y)},
      EmuRun α s (playQueries (Y := V) us) tout u tin →
      PFunDDS.transcriptInputs tout ++ [u] = us.take (tout.length + 1) := by
    intro tout u tin hr
    induction hr with
    | start hu =>
        rename_i u₂
        cases us with
        | nil => simp [playQueries] at hu
        | cons a t =>
            have ha : a = u₂ := by simpa [playQueries] using hu
            simp [ha]
    | query hr hx ih => exact ih
    | answer hr hv hu' ih =>
        rename_i tout u tin v u'
        have hidx : us[tout.length + 1]? = some u' := by
          simpa [playQueries] using hu'
        rw [transcriptInputs_append, List.length_append,
          List.length_singleton, List.take_add_one, hidx, ← ih]
        rfl
  have hpos : 0 < us.length := List.length_pos_of_ne_nil hne
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, (playQueries (Y := V) us) [] = some u₁ := by
    cases us with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, by simp [playQueries]⟩
  have hbase : EmuRun α s (playQueries (Y := V) us) [] u₁ [] :=
    EmuRun.start hu₁
  obtain ⟨tout, u, tin, v, hr, hv, hle, hstop⟩ :=
    emuRun_terminal hB hdef (n := us.length) (us.length - 1) hbase
      (by simp only [List.length_nil]; omega)
  have hfull : tout.length + 1 = us.length := by
    rcases hstop with h | h
    · exact h
    · have hnone : us[tout.length + 1]? = none := by
        simpa [playQueries] using h
      have hge := List.getElem?_eq_none_iff.mp hnone
      omega
  have hus : PFunDDS.transcriptInputs tout ++ [u] = us := by
    rw [hinv hr, hfull, List.take_length]
  have hmem := emuRun_applyRaw_mem hr hv
  rw [hus] at hmem
  exact Part.dom_iff_mem.mpr ⟨v, hmem⟩



/-! ### The pollution-free certificate: anchor-confined silence

CR18 Def 3.8-class converters with **anchor-confined silence** (the
θ-discipline of CR18 §6.2.3) are absorbable without productivity: with
inner arity one (`AnswersWithin α 2`), silence past `⊥` (`AnswersInY`),
and every opened round closed (`StopsReplying`), a dead round issues
at most one `⊥`-answered inner query — which the assumed system's own
`keptPrefix` (CR18 Def 3.3) erases, so the emulation stays pollution-free.
The applied system's `⊥`-completion deletes dead outer inputs the same
way, and the bridge tracks both deletions through kept projections. -/

section KeptBridge

/-- CR18 Def 3.8 with **anchor-confined silence** (the θ-discipline, CR18
§6.2.3): every round the converter opens it also closes — after a query is
answered properly, the converter is defined.  With `AnswersWithin α 2` and
`AnswersInY α` this confines silence to pre-query round anchors and
`⊥`-pairs — the pollution-free class of `emulable_of_stopsReplying`. -/
def StopsReplying (α : ProtocolFn U V X Y) : Prop :=
  ∀ {us : List U} {ys : List (Option Y)} {x : X} (y : Y),
    Reach α (us, ys) → Sum.inl x ∈ α (us, ys) →
    (α (us, ys ++ [some y])).Dom

/-- Kept outer inputs: inputs of the live (properly answered) rounds. -/
private def keptO (t : List (U × Option V)) : List U :=
  (t.filter fun p => p.2.isSome).map Prod.fst

/-- Kept inner queries: queries with proper answers. -/
private def keptQ (t : List (X × Option Y)) : List X :=
  (t.filter fun p => p.2.isSome).map Prod.fst

/-- Kept inner answers (as completed-alphabet values, all proper). -/
private def keptY (t : List (X × Option Y)) : List (Option Y) :=
  (t.filter fun p => p.2.isSome).map Prod.snd

@[simp] private theorem keptO_nil : keptO ([] : List (U × Option V)) = [] :=
  rfl

@[simp] private theorem keptQ_nil : keptQ ([] : List (X × Option Y)) = [] :=
  rfl

@[simp] private theorem keptY_nil : keptY ([] : List (X × Option Y)) = [] :=
  rfl

@[simp] private theorem keptO_append_some (t : List (U × Option V)) (u : U)
    (v : V) : keptO (t ++ [(u, some v)]) = keptO t ++ [u] := by
  simp [keptO]

@[simp] private theorem keptO_append_none (t : List (U × Option V)) (u : U) :
    keptO (t ++ [(u, none)]) = keptO t := by
  simp [keptO]

@[simp] private theorem keptQ_append_some (t : List (X × Option Y)) (x : X)
    (y : Y) : keptQ (t ++ [(x, some y)]) = keptQ t ++ [x] := by
  simp [keptQ]

@[simp] private theorem keptQ_append_none (t : List (X × Option Y)) (x : X) :
    keptQ (t ++ [(x, none)]) = keptQ t := by
  simp [keptQ]

@[simp] private theorem keptY_append_some (t : List (X × Option Y)) (x : X)
    (y : Y) : keptY (t ++ [(x, some y)]) = keptY t ++ [some y] := by
  simp [keptY]

@[simp] private theorem keptY_append_none (t : List (X × Option Y)) (x : X) :
    keptY (t ++ [(x, none)]) = keptY t := by
  simp [keptY]

open Classical in
/-- One step of the Def 3.3 deletion scan. -/
private theorem keptPrefix_concat (S : PFunDDS.DDS X Y) (l : List X)
    (x : X) :
    PFunDDS.keptPrefix S (l ++ [x])
      = if PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S
        then PFunDDS.keptPrefix S l ++ [x] else PFunDDS.keptPrefix S l := by
  simp only [PFunDDS.keptPrefix, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

open Classical in
/-- The `⊥`-completion at a one-step extension, in kept form (CR18
Def 3.3, computed). -/
private theorem output_fullyDefined_concat (S : PFunDDS.DDS X Y)
    (l : List X) (x : X) (h : l ++ [x] ∈ PFunDDS.dom (S⊥)) :
    PFunDDS.output (S⊥) (l ++ [x]) h
      = if hc : PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S
        then some (PFunDDS.output S (PFunDDS.keptPrefix S l ++ [x]) hc)
        else none := by
  have key : ∀ (ctx : List X) (a : X), ctx = PFunDDS.keptPrefix S l →
      a = x →
      (if hc : ctx ++ [a] ∈ PFunDDS.dom S
        then some (PFunDDS.output S (ctx ++ [a]) hc) else none)
      = (if hc : PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S
        then some (PFunDDS.output S (PFunDDS.keptPrefix S l ++ [x]) hc)
        else none) := by
    rintro _ _ rfl rfl
    rfl
  exact key _ _ (congrArg (PFunDDS.keptPrefix S) (by simp))
    List.getLast_concat

private theorem keptPrefix_mem_of_output_some {S : PFunDDS.DDS X Y}
    {l : List X} {x : X} {y : Y} {h : l ++ [x] ∈ PFunDDS.dom (S⊥)}
    (hout : PFunDDS.output (S⊥) (l ++ [x]) h = some y) :
    ∃ hc : PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S,
      PFunDDS.output S (PFunDDS.keptPrefix S l ++ [x]) hc = y := by
  rw [output_fullyDefined_concat] at hout
  by_cases hc : PFunDDS.keptPrefix S l ++ [x] ∈ PFunDDS.dom S
  · rw [dif_pos hc] at hout
    exact ⟨hc, Option.some.inj hout⟩
  · rw [dif_neg hc] at hout
    simp at hout

private theorem keptPrefix_not_mem_of_output_none {S : PFunDDS.DDS X Y}
    {l : List X} {x : X} {h : l ++ [x] ∈ PFunDDS.dom (S⊥)}
    (hout : PFunDDS.output (S⊥) (l ++ [x]) h = none) :
    PFunDDS.keptPrefix S l ++ [x] ∉ PFunDDS.dom S := by
  intro hc
  rw [output_fullyDefined_concat, dif_pos hc] at hout
  simp at hout

/-- `drive` is deterministic: results agree across fuels. -/
private theorem drive_unique {α : ProtocolFn U V X Y}
    {s : PFunDDS.DDS X Y} :
    ∀ {f₁ f₂ : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
      {r₁ r₂ : V × List X × List (Option Y)},
      r₁ ∈ drive α s f₁ us xs ys → r₂ ∈ drive α s f₂ us xs ys →
      r₁ = r₂ := by
  have key : ∀ (f : ℕ) {us : List U} {xs : List X} {ys : List (Option Y)}
      {r₁ r₂ : V × List X × List (Option Y)},
      r₁ ∈ drive α s f us xs ys → r₂ ∈ drive α s f us xs ys → r₁ = r₂ := by
    intro f
    induction f with
    | zero => intro _ _ _ _ _ h _; simp [drive] at h
    | succ n ih =>
        intro us xs ys r₁ r₂ h₁ h₂
        rcases drive_succ_elim h₁ with ⟨x₁, hm₁, hr₁⟩ | ⟨v₁, hm₁, rfl⟩ <;>
          rcases drive_succ_elim h₂ with ⟨x₂, hm₂, hr₂⟩ | ⟨v₂, hm₂, he₂⟩
        · obtain rfl : x₁ = x₂ := Sum.inl.inj (Part.mem_unique hm₁ hm₂)
          exact ih hr₁ hr₂
        · exact absurd (Part.mem_unique hm₁ hm₂) (by simp)
        · exact absurd (Part.mem_unique hm₂ hm₁) (by simp)
        · rw [he₂, Sum.inr.inj (Part.mem_unique hm₁ hm₂)]
  intro f₁ f₂ us xs ys r₁ r₂ h₁ h₂
  exact key (max f₁ f₂) (drive_mono_le α s (le_max_left _ _) h₁)
    (drive_mono_le α s (le_max_right _ _) h₂)

/-- `driveOuter` is deterministic: results agree across fuels. -/
private theorem driveOuter_unique {α : ProtocolFn U V X Y}
    {s : PFunDDS.DDS X Y} :
    ∀ {rest : List U} {f₁ f₂ : ℕ} {usPre : List U} {xs : List X}
      {ys : List (Option Y)} {r₁ r₂ : List V × List X × List (Option Y)},
      r₁ ∈ driveOuter α s f₁ usPre xs ys rest →
      r₂ ∈ driveOuter α s f₂ usPre xs ys rest → r₁ = r₂ := by
  intro rest
  induction rest with
  | nil =>
      intro f₁ f₂ usPre xs ys r₁ r₂ h₁ h₂
      simp only [driveOuter, Part.mem_some_iff] at h₁ h₂
      rw [h₁, h₂]
  | cons u rest ih =>
      intro f₁ f₂ usPre xs ys r₁ r₂ h₁ h₂
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h₁ h₂
      obtain ⟨ra₁, hra₁, rb₁, hrb₁, rfl⟩ := h₁
      obtain ⟨ra₂, hra₂, rb₂, hrb₂, rfl⟩ := h₂
      obtain rfl : ra₁ = ra₂ := drive_unique hra₁ hra₂
      obtain rfl : rb₁ = rb₂ := ih hrb₁ hrb₂
      rfl

/-- A silent consultation kills the drive. -/
private theorem drive_not_mem_of_not_dom {α : ProtocolFn U V X Y}
    {s : PFunDDS.DDS X Y} {us : List U} {ys : List (Option Y)}
    (hst : ¬ (α (us, ys)).Dom) (fuel : ℕ) (xs : List X)
    {r : V × List X × List (Option Y)} :
    r ∉ drive α s fuel us xs ys := by
  intro hr
  rcases fuel with _ | fuel
  · simp [drive] at hr
  · rcases drive_succ_elim hr with ⟨x, hm, -⟩ | ⟨v, hm, -⟩
    · exact hst (Part.dom_iff_mem.mpr ⟨_, hm⟩)
    · exact hst (Part.dom_iff_mem.mpr ⟨_, hm⟩)

open Classical in
/-- Plumbing for the θ-class emulator: replay one *round* at a time from
the kept state — `kb` the kept outer inputs, `u` the current outer input,
`vs` the raw outer answers `e` has seen, `kys` the kept inner answers,
`ysr` the remaining recorded raw inner answers.  Dead rounds (anchor
silence or a `⊥`-answer to the round's single query) drop `u` from the
kept inputs and feed `e` a `⊥`. -/
private noncomputable def emuGoK (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) :
    ℕ → List U → U → List (Option V) → List (Option Y) →
      List (Option Y) → Option X
  | k, kb, u, vs, kys, ysr =>
    if h : (α (kb ++ [u], kys)).Dom then
      match (α (kb ++ [u], kys)).get h with
      | Sum.inl x =>
          match ysr with
          | [] => some x
          | some y :: ysr' =>
              if h2 : (α (kb ++ [u], kys ++ [some y])).Dom then
                match (α (kb ++ [u], kys ++ [some y])).get h2 with
                | Sum.inl _ => none
                | Sum.inr v =>
                    match k with
                    | 0 => none
                    | k' + 1 =>
                        match e (vs ++ [some v]) with
                        | none => none
                        | some u' =>
                            emuGoK α e k' (kb ++ [u]) u' (vs ++ [some v])
                              (kys ++ [some y]) ysr'
              else none
          | none :: ysr' =>
              match k with
              | 0 => none
              | k' + 1 =>
                  match e (vs ++ [none]) with
                  | none => none
                  | some u' => emuGoK α e k' kb u' (vs ++ [none]) kys ysr'
      | Sum.inr v =>
          match k with
          | 0 => none
          | k' + 1 =>
              match e (vs ++ [some v]) with
              | none => none
              | some u' =>
                  emuGoK α e k' (kb ++ [u]) u' (vs ++ [some v]) kys ysr
    else
      match k with
      | 0 => none
      | k' + 1 =>
          match e (vs ++ [none]) with
          | none => none
          | some u' => emuGoK α e k' kb u' (vs ++ [none]) kys ysr
  termination_by k _ _ _ _ _ => k

private theorem emuGoK_stallA {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {kb : List U} {u : U} {vs : List (Option V)}
    {kys : List (Option Y)} (hst : ¬ (α (kb ++ [u], kys)).Dom) (k : ℕ)
    (ysr : List (Option Y)) :
    emuGoK α e k kb u vs kys ysr
      = match k with
        | 0 => none
        | k' + 1 =>
            match e (vs ++ [none]) with
            | none => none
            | some u' => emuGoK α e k' kb u' (vs ++ [none]) kys ysr := by
  rw [emuGoK.eq_def]
  dsimp only
  rw [dif_neg hst]

private theorem emuGoK_liveNQ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {kb : List U} {u : U} {vs : List (Option V)}
    {kys : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (kb ++ [u], kys)) (k : ℕ)
    (ysr : List (Option Y)) :
    emuGoK α e k kb u vs kys ysr
      = match k with
        | 0 => none
        | k' + 1 =>
            match e (vs ++ [some v]) with
            | none => none
            | some u' =>
                emuGoK α e k' (kb ++ [u]) u' (vs ++ [some v]) kys ysr := by
  have hdom : (α (kb ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [emuGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hv hdom]

private theorem emuGoK_query_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {kb : List U} {u : U} {vs : List (Option V)}
    {kys : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (kb ++ [u], kys)) (k : ℕ) :
    emuGoK α e k kb u vs kys [] = some x := by
  have hdom : (α (kb ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [emuGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem emuGoK_query_bot {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {kb : List U} {u : U} {vs : List (Option V)}
    {kys : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (kb ++ [u], kys)) (k : ℕ)
    (ysr : List (Option Y)) :
    emuGoK α e k kb u vs kys (none :: ysr)
      = match k with
        | 0 => none
        | k' + 1 =>
            match e (vs ++ [none]) with
            | none => none
            | some u' => emuGoK α e k' kb u' (vs ++ [none]) kys ysr := by
  have hdom : (α (kb ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [emuGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem emuGoK_liveQ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {kb : List U} {u : U} {vs : List (Option V)}
    {kys : List (Option Y)} {x : X} {y : Y} {v : V}
    (hx : Sum.inl x ∈ α (kb ++ [u], kys))
    (hv : Sum.inr v ∈ α (kb ++ [u], kys ++ [some y])) (k : ℕ)
    (ysr : List (Option Y)) :
    emuGoK α e k kb u vs kys (some y :: ysr)
      = match k with
        | 0 => none
        | k' + 1 =>
            match e (vs ++ [some v]) with
            | none => none
            | some u' =>
                emuGoK α e k' (kb ++ [u]) u' (vs ++ [some v])
                  (kys ++ [some y]) ysr := by
  have hdom : (α (kb ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  have hdom2 : (α (kb ++ [u], kys ++ [some y])).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [emuGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom, dif_pos hdom2,
    Part.get_eq_of_mem hv hdom2]

/-- The θ-class emulated environment (MauRen11 Def 15/16 for the
anchor-silent class): inner fuel `n` — one recorded answer per round. -/
private noncomputable def emulateK (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) (n : ℕ) : PFunDDS.DDE X Y := fun ys =>
  match n, e [] with
  | 0, _ => none
  | _ + 1, none => none
  | m + 1, some u₀ => emuGoK α e m [] u₀ [] [] ys

private theorem emulateK_of_env_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} (hu : e [] = none) (n : ℕ)
    (ys : List (Option Y)) : emulateK α e n ys = none := by
  cases n with
  | zero => rfl
  | succ m => simp only [emulateK, hu]

private theorem emulateK_succ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {u₀ : U} (hu : e [] = some u₀) (m : ℕ)
    (ys : List (Option Y)) :
    emulateK α e (m + 1) ys = emuGoK α e m [] u₀ [] [] ys := by
  simp only [emulateK, hu]

open Classical in
/-- Plumbing for the θ-class reconstruction: parse the inner transcript
round by round from the kept state, emitting `(u, some v)` for live rounds
and `(u, none)` for dead ones. -/
private noncomputable def replayGoK (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) :
    ℕ → List (U × Option V) → U → List (Option Y) →
      List (X × Option Y) → List (U × Option V)
  | k, acc, u, kys, rem =>
    if h : (α (keptO acc ++ [u], kys)).Dom then
      match (α (keptO acc ++ [u], kys)).get h with
      | Sum.inl _ =>
          match rem with
          | [] => acc
          | (_, some y) :: rem' =>
              if h2 : (α (keptO acc ++ [u], kys ++ [some y])).Dom then
                match (α (keptO acc ++ [u], kys ++ [some y])).get h2 with
                | Sum.inl _ => acc
                | Sum.inr v =>
                    match k with
                    | 0 => acc ++ [(u, some v)]
                    | k' + 1 =>
                        match e (PFunDDS.transcriptOutputs acc
                            ++ [some v]) with
                        | none => acc ++ [(u, some v)]
                        | some u' =>
                            replayGoK α e k' (acc ++ [(u, some v)]) u'
                              (kys ++ [some y]) rem'
              else acc
          | (_, none) :: rem' =>
              match k with
              | 0 => acc ++ [(u, none)]
              | k' + 1 =>
                  match e (PFunDDS.transcriptOutputs acc ++ [none]) with
                  | none => acc ++ [(u, none)]
                  | some u' =>
                      replayGoK α e k' (acc ++ [(u, none)]) u' kys rem'
      | Sum.inr v =>
          match k with
          | 0 => acc ++ [(u, some v)]
          | k' + 1 =>
              match e (PFunDDS.transcriptOutputs acc ++ [some v]) with
              | none => acc ++ [(u, some v)]
              | some u' =>
                  replayGoK α e k' (acc ++ [(u, some v)]) u' kys rem
    else
      match k with
      | 0 => acc ++ [(u, none)]
      | k' + 1 =>
          match e (PFunDDS.transcriptOutputs acc ++ [none]) with
          | none => acc ++ [(u, none)]
          | some u' => replayGoK α e k' (acc ++ [(u, none)]) u' kys rem
  termination_by k _ _ _ _ => k

private theorem replayGoK_stallA {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {kys : List (Option Y)} (hst : ¬ (α (keptO acc ++ [u], kys)).Dom)
    (k : ℕ) (rem : List (X × Option Y)) :
    replayGoK α e k acc u kys rem
      = match k with
        | 0 => acc ++ [(u, none)]
        | k' + 1 =>
            match e (PFunDDS.transcriptOutputs acc ++ [none]) with
            | none => acc ++ [(u, none)]
            | some u' => replayGoK α e k' (acc ++ [(u, none)]) u' kys rem
      := by
  rw [replayGoK.eq_def]
  dsimp only
  rw [dif_neg hst]

private theorem replayGoK_liveNQ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {kys : List (Option Y)} {v : V}
    (hv : Sum.inr v ∈ α (keptO acc ++ [u], kys)) (k : ℕ)
    (rem : List (X × Option Y)) :
    replayGoK α e k acc u kys rem
      = match k with
        | 0 => acc ++ [(u, some v)]
        | k' + 1 =>
            match e (PFunDDS.transcriptOutputs acc ++ [some v]) with
            | none => acc ++ [(u, some v)]
            | some u' =>
                replayGoK α e k' (acc ++ [(u, some v)]) u' kys rem := by
  have hdom : (α (keptO acc ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [replayGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hv hdom]

private theorem replayGoK_query_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {kys : List (Option Y)} {x : X}
    (hx : Sum.inl x ∈ α (keptO acc ++ [u], kys)) (k : ℕ) :
    replayGoK α e k acc u kys [] = acc := by
  have hdom : (α (keptO acc ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [replayGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem replayGoK_query_bot {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {kys : List (Option Y)} {x : X} {x₀ : X}
    (hx : Sum.inl x ∈ α (keptO acc ++ [u], kys)) (k : ℕ)
    (rem : List (X × Option Y)) :
    replayGoK α e k acc u kys ((x₀, none) :: rem)
      = match k with
        | 0 => acc ++ [(u, none)]
        | k' + 1 =>
            match e (PFunDDS.transcriptOutputs acc ++ [none]) with
            | none => acc ++ [(u, none)]
            | some u' => replayGoK α e k' (acc ++ [(u, none)]) u' kys rem
      := by
  have hdom : (α (keptO acc ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  rw [replayGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom]

private theorem replayGoK_liveQ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {acc : List (U × Option V)} {u : U}
    {kys : List (Option Y)} {x : X} {x₀ : X} {y : Y} {v : V}
    (hx : Sum.inl x ∈ α (keptO acc ++ [u], kys))
    (hv : Sum.inr v ∈ α (keptO acc ++ [u], kys ++ [some y])) (k : ℕ)
    (rem : List (X × Option Y)) :
    replayGoK α e k acc u kys ((x₀, some y) :: rem)
      = match k with
        | 0 => acc ++ [(u, some v)]
        | k' + 1 =>
            match e (PFunDDS.transcriptOutputs acc ++ [some v]) with
            | none => acc ++ [(u, some v)]
            | some u' =>
                replayGoK α e k' (acc ++ [(u, some v)]) u'
                  (kys ++ [some y]) rem := by
  have hdom : (α (keptO acc ++ [u], kys)).Dom := Part.dom_iff_mem.mpr ⟨_, hx⟩
  have hdom2 : (α (keptO acc ++ [u], kys ++ [some y])).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hv⟩
  rw [replayGoK.eq_def]
  dsimp only
  rw [dif_pos hdom, Part.get_eq_of_mem hx hdom, dif_pos hdom2,
    Part.get_eq_of_mem hv hdom2]

/-- The θ-class reconstruction map. -/
private noncomputable def replayTranscriptK (α : ProtocolFn U V X Y)
    (e : PFunDDS.DDE U V) (n : ℕ) (t : List (X × Option Y)) :
    List (U × Option V) :=
  match n, e [] with
  | 0, _ => []
  | _ + 1, none => []
  | m + 1, some u₀ => replayGoK α e m [] u₀ [] t

private theorem replayTranscriptK_of_env_nil {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} (hu : e [] = none) (n : ℕ)
    (t : List (X × Option Y)) : replayTranscriptK α e n t = [] := by
  cases n with
  | zero => rfl
  | succ m => simp only [replayTranscriptK, hu]

private theorem replayTranscriptK_succ {α : ProtocolFn U V X Y}
    {e : PFunDDS.DDE U V} {u₀ : U} (hu : e [] = some u₀) (m : ℕ)
    (t : List (X × Option Y)) :
    replayTranscriptK α e (m + 1) t = replayGoK α e m [] u₀ [] t := by
  simp only [replayTranscriptK, hu]

section KeptRun

variable (α : ProtocolFn U V X Y) (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE U V)

/-- One closed round from an anchor state, in the four θ-class shapes:
live without a query, live with one properly answered query, dead at the
anchor (θ "stops replying"), dead at a `⊥`-answer. -/
private inductive RoundClose :
    List (U × Option V) → U → List (X × Option Y) →
      Option V → List (X × Option Y) → Prop
  | liveNQ {tout u tin v}
      (hv : Sum.inr v ∈ α (keptO tout ++ [u], keptY tin)) :
      RoundClose tout u tin (some v) tin
  | liveQ {tout u tin x y v}
      (hx : Sum.inl x ∈ α (keptO tout ++ [u], keptY tin))
      (hy : PFunDDS.output (s⊥) (PFunDDS.transcriptInputs tin ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y)
      (hv : Sum.inr v ∈ α (keptO tout ++ [u], keptY tin ++ [some y])) :
      RoundClose tout u tin (some v)
        (tin ++ [(x, PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs tin ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp))])
  | deadA {tout u tin}
      (hst : ¬ (α (keptO tout ++ [u], keptY tin)).Dom) :
      RoundClose tout u tin none tin
  | deadB {tout u tin x}
      (hx : Sum.inl x ∈ α (keptO tout ++ [u], keptY tin))
      (hy : PFunDDS.output (s⊥) (PFunDDS.transcriptInputs tin ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none) :
      RoundClose tout u tin none
        (tin ++ [(x, PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs tin ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp))])

/-- The round-atomic joint run of the θ-class emulation. -/
private inductive EmuRunK :
    List (U × Option V) → U → List (X × Option Y) → Prop
  | start {u} (hu : e [] = some u) : EmuRunK [] u []
  | round {tout u tin a tin' u'} (hr : EmuRunK tout u tin)
      (hc : RoundClose α s tout u tin a tin')
      (hu' : e (PFunDDS.transcriptOutputs tout ++ [a]) = some u') :
      EmuRunK (tout ++ [(u, a)]) u' tin'

variable {α s e}

/-- **The bundled invariant of a θ-class joint state** — inner kept
coherence, drive certification, outer kept coherence, the outer
transcript, the pending environment query, the length bound, and
reachability of the kept anchor. -/
private theorem emuRunK_invariant (hs : AnswersInY α)
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    (hr : EmuRunK α s e tout u tin) :
    (PFunDDS.keptPrefix s (PFunDDS.transcriptInputs tin) = keptQ tin ∧
      (keptQ tin ∈ PFunDDS.dom s ∨ keptQ tin = [])) ∧
    (∃ fuel vsP, (vsP, keptQ tin, keptY tin)
        ∈ driveOuter α s fuel [] [] [] (keptO tout)) ∧
    (PFunDDS.keptPrefix (apply α s) (PFunDDS.transcriptInputs tout)
        = keptO tout ∧
      (keptO tout ∈ PFunDDS.dom (apply α s) ∨ keptO tout = [])) ∧
    PFunDDS.transcript (apply α s) e tout.length = tout ∧
    e (PFunDDS.transcriptOutputs tout) = some u ∧
    tin.length ≤ tout.length ∧
    (∀ u₀ : U, Reach α (keptO tout ++ [u₀], keptY tin)) := by
  induction hr with
  | start hu =>
      refine ⟨⟨rfl, Or.inr rfl⟩, ⟨0, [], by simp [driveOuter]⟩,
        ⟨rfl, Or.inr rfl⟩, rfl, hu, le_rfl, fun u₀ => ?_⟩
      simpa using Reach.first u₀
  | round hr hc hu' ih =>
      obtain ⟨⟨hkc1, hkc2⟩, ⟨f₀, vsP, hdo⟩, ⟨hokc1, hokc2⟩, hL2a, hL2b,
        hlen, hreach⟩ := ih
      cases hc with
      | liveNQ hv =>
          rename_i tout u tin u' v
          have hfire : e ((PFunDDS.transcript (apply α s) e
              tout.length)↓ᵧ) = some u := by
            rw [hL2a]
            exact hL2b
          have hdo' : (vsP ++ [v], keptQ tin, keptY tin)
              ∈ driveOuter α s (max f₀ 1) [] [] []
                (keptO tout ++ [u]) := by
            rw [driveOuter_append α s _ (keptO tout) [u],
              Part.mem_bind_iff]
            refine ⟨(vsP, keptQ tin, keptY tin),
              driveOuter_mono_le α s (le_max_left _ _) hdo, ?_⟩
            rw [Part.mem_map_iff]
            refine ⟨([v], keptQ tin, keptY tin), ?_, rfl⟩
            show _ ∈ (drive α s _ (keptO tout ++ [u])
              (keptQ tin) (keptY tin)).bind _
            rw [Part.mem_bind_iff]
            refine ⟨(v, keptQ tin, keptY tin),
              drive_mono_le α s (le_max_right _ _)
                (drive_mem_answer α s hv 0), ?_⟩
            simp [driveOuter]
          have hval : v ∈ applyRaw α s (keptO tout ++ [u]) := by
            rw [mem_applyRaw]
            refine ⟨max f₀ 1, ?_⟩
            rw [mem_applyRawAt_iff]
            exact ⟨(vsP ++ [v], keptQ tin, keptY tin), hdo', by simp⟩
          have hdom' : keptO tout ++ [u] ∈ PFunDDS.dom (apply α s) :=
            Part.dom_iff_mem.mpr ⟨v, hval⟩
          have hout : PFunDDS.output ((apply α s)⊥)
              (PFunDDS.transcriptInputs tout ++ [u])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
            rw [output_fullyDefined_concat, hokc1, dif_pos hdom']
            exact congrArg some (Part.get_eq_of_mem hval hdom')
          refine ⟨⟨hkc1, hkc2⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · exact ⟨max f₀ 1, vsP ++ [v],
              by rw [keptO_append_some]; exact hdo'⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hokc1,
              if_pos hdom', keptO_append_some]
          · exact Or.inl (by rw [keptO_append_some]; exact hdom')
          · rw [List.length_append, List.length_singleton,
              transcript_succ_fire hfire, hL2a, hout]
          · rw [transcriptOutputs_append]
            exact hu'
          · rw [List.length_append, List.length_singleton]
            omega
          · intro u₀
            rw [keptO_append_some]
            exact Reach.next (hreach u) hv u₀
      | liveQ hx hy hv =>
          rename_i tout u tin u' x y v
          have hfire : e ((PFunDDS.transcript (apply α s) e
              tout.length)↓ᵧ) = some u := by
            rw [hL2a]
            exact hL2b
          rw [hy]
          have hyk : ∃ hc : keptQ tin ++ [x] ∈ PFunDDS.dom s,
              PFunDDS.output s (keptQ tin ++ [x]) hc = y := by
            have h0 := keptPrefix_mem_of_output_some hy
            rw [hkc1] at h0
            exact h0
          obtain ⟨hqdom, hqval⟩ := hyk
          have houtk : PFunDDS.output (s⊥) (keptQ tin ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            rw [output_fullyDefined_concat,
              PFunDDS.keptPrefix_eq_self_of_mem_or_empty s hkc2,
              dif_pos hqdom]
            exact congrArg some hqval
          have hdrive : (v, keptQ tin ++ [x], keptY tin ++ [some y])
              ∈ drive α s 2 (keptO tout ++ [u]) (keptQ tin)
                (keptY tin) := by
            refine drive_mem_query α s hx ?_
            rw [houtk]
            exact drive_mem_answer α s hv 0
          have hdo' : (vsP ++ [v], keptQ tin ++ [x],
              keptY tin ++ [some y]) ∈ driveOuter α s (max f₀ 2) [] [] []
                (keptO tout ++ [u]) := by
            rw [driveOuter_append α s _ (keptO tout) [u],
              Part.mem_bind_iff]
            refine ⟨(vsP, keptQ tin, keptY tin),
              driveOuter_mono_le α s (le_max_left _ _) hdo, ?_⟩
            rw [Part.mem_map_iff]
            refine ⟨([v], keptQ tin ++ [x], keptY tin ++ [some y]),
              ?_, rfl⟩
            show _ ∈ (drive α s _ (keptO tout ++ [u])
              (keptQ tin) (keptY tin)).bind _
            rw [Part.mem_bind_iff]
            refine ⟨(v, keptQ tin ++ [x], keptY tin ++ [some y]),
              drive_mono_le α s (le_max_right _ _) hdrive, ?_⟩
            simp [driveOuter]
          have hval : v ∈ applyRaw α s (keptO tout ++ [u]) := by
            rw [mem_applyRaw]
            refine ⟨max f₀ 2, ?_⟩
            rw [mem_applyRawAt_iff]
            exact ⟨(vsP ++ [v], keptQ tin ++ [x], keptY tin ++ [some y]),
              hdo', by simp⟩
          have hdom' : keptO tout ++ [u] ∈ PFunDDS.dom (apply α s) :=
            Part.dom_iff_mem.mpr ⟨v, hval⟩
          have hout : PFunDDS.output ((apply α s)⊥)
              (PFunDDS.transcriptInputs tout ++ [u])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
            rw [output_fullyDefined_concat, hokc1, dif_pos hdom']
            exact congrArg some (Part.get_eq_of_mem hval hdom')
          refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hkc1,
              if_pos hqdom, keptQ_append_some]
          · exact Or.inl (by rw [keptQ_append_some]; exact hqdom)
          · exact ⟨max f₀ 2, vsP ++ [v], by
              rw [keptO_append_some, keptQ_append_some,
                keptY_append_some]
              exact hdo'⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hokc1,
              if_pos hdom', keptO_append_some]
          · exact Or.inl (by rw [keptO_append_some]; exact hdom')
          · rw [List.length_append, List.length_singleton,
              transcript_succ_fire hfire, hL2a, hout]
          · rw [transcriptOutputs_append]
            exact hu'
          · rw [List.length_append, List.length_append,
              List.length_singleton, List.length_singleton]
            omega
          · intro u₀
            rw [keptO_append_some, keptY_append_some]
            exact Reach.next (Reach.answer (hreach u) hx (some y)) hv u₀
      | deadA hst =>
          rename_i tout u tin u'
          have hfire : e ((PFunDDS.transcript (apply α s) e
              tout.length)↓ᵧ) = some u := by
            rw [hL2a]
            exact hL2b
          have hnd : keptO tout ++ [u] ∉ PFunDDS.dom (apply α s) := by
            intro hdom'
            obtain ⟨w, hw₀⟩ := Part.dom_iff_mem.mp hdom'
            have hw : w ∈ applyRaw α s (keptO tout ++ [u]) := hw₀
            rw [mem_applyRaw] at hw
            obtain ⟨f, hw⟩ := hw
            rw [mem_applyRawAt_iff] at hw
            obtain ⟨r, hrr, -⟩ := hw
            rw [driveOuter_append α s _ (keptO tout) [u],
              Part.mem_bind_iff] at hrr
            obtain ⟨ra, hra, hrb⟩ := hrr
            obtain rfl : ra = (vsP, keptQ tin, keptY tin) :=
              driveOuter_unique hra hdo
            rw [Part.mem_map_iff] at hrb
            obtain ⟨rb, hrb, -⟩ := hrb
            simp only [driveOuter, Part.mem_bind_iff,
              Part.mem_map_iff] at hrb
            obtain ⟨r₁, hr₁, -⟩ := hrb
            exact drive_not_mem_of_not_dom hst f _ hr₁
          have hout : PFunDDS.output ((apply α s)⊥)
              (PFunDDS.transcriptInputs tout ++ [u])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_concat, hokc1, dif_neg hnd]
          refine ⟨⟨hkc1, hkc2⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · exact ⟨f₀, vsP, by rw [keptO_append_none]; exact hdo⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hokc1,
              if_neg hnd, keptO_append_none]
          · rw [keptO_append_none]
            exact hokc2
          · rw [List.length_append, List.length_singleton,
              transcript_succ_fire hfire, hL2a, hout]
          · rw [transcriptOutputs_append]
            exact hu'
          · rw [List.length_append, List.length_singleton]
            omega
          · intro u₀
            rw [keptO_append_none]
            exact hreach u₀
      | deadB hx hy =>
          rename_i tout u tin u' x
          have hfire : e ((PFunDDS.transcript (apply α s) e
              tout.length)↓ᵧ) = some u := by
            rw [hL2a]
            exact hL2b
          rw [hy]
          have hnd_q : keptQ tin ++ [x] ∉ PFunDDS.dom s := by
            have h0 := keptPrefix_not_mem_of_output_none hy
            rw [hkc1] at h0
            exact h0
          have houtk : PFunDDS.output (s⊥) (keptQ tin ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_concat,
              PFunDDS.keptPrefix_eq_self_of_mem_or_empty s hkc2,
              dif_neg hnd_q]
          have hbotpair : ¬ (α (keptO tout ++ [u],
              keptY tin ++ [none])).Dom :=
            hs _ (Reach.answer (hreach u) hx none) (by simp)
          have hnd : keptO tout ++ [u] ∉ PFunDDS.dom (apply α s) := by
            intro hdom'
            obtain ⟨w, hw₀⟩ := Part.dom_iff_mem.mp hdom'
            have hw : w ∈ applyRaw α s (keptO tout ++ [u]) := hw₀
            rw [mem_applyRaw] at hw
            obtain ⟨f, hw⟩ := hw
            rw [mem_applyRawAt_iff] at hw
            obtain ⟨r, hrr, -⟩ := hw
            rw [driveOuter_append α s _ (keptO tout) [u],
              Part.mem_bind_iff] at hrr
            obtain ⟨ra, hra, hrb⟩ := hrr
            obtain rfl : ra = (vsP, keptQ tin, keptY tin) :=
              driveOuter_unique hra hdo
            rw [Part.mem_map_iff] at hrb
            obtain ⟨rb, hrb, -⟩ := hrb
            simp only [driveOuter, Part.mem_bind_iff,
              Part.mem_map_iff] at hrb
            obtain ⟨r₁, hr₁, -⟩ := hrb
            rcases f with _ | f
            · simp [drive] at hr₁
            · rcases drive_succ_elim hr₁ with ⟨x', hm, hrec⟩ |
                ⟨v', hm, -⟩
              · obtain rfl : x' = x :=
                  Sum.inl.inj (Part.mem_unique hm hx)
                rw [houtk] at hrec
                exact drive_not_mem_of_not_dom hbotpair f _ hrec
              · exact absurd (Part.mem_unique hm hx) (by simp)
          have hout : PFunDDS.output ((apply α s)⊥)
              (PFunDDS.transcriptInputs tout ++ [u])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
            rw [output_fullyDefined_concat, hokc1, dif_neg hnd]
          refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hkc1,
              if_neg hnd_q, keptQ_append_none]
          · rw [keptQ_append_none]
            exact hkc2
          · exact ⟨f₀, vsP, by
              rw [keptO_append_none, keptQ_append_none,
                keptY_append_none]
              exact hdo⟩
          · rw [transcriptInputs_append, keptPrefix_concat, hokc1,
              if_neg hnd, keptO_append_none]
          · rw [keptO_append_none]
            exact hokc2
          · rw [List.length_append, List.length_singleton,
              transcript_succ_fire hfire, hL2a, hout]
          · rw [transcriptOutputs_append]
            exact hu'
          · rw [List.length_append, List.length_append,
              List.length_singleton, List.length_singleton]
            omega
          · intro u₀
            rw [keptO_append_none, keptY_append_none]
            exact hreach u₀

private theorem emuRunK_env_some {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRunK α s e tout u tin) :
    ∃ u₀, e [] = some u₀ := by
  induction hr with
  | start hu => exact ⟨_, hu⟩
  | round hr hc hu' ih => exact ih

/-- Replay, emulator side: `emuGoK` re-traces a joint state's recorded
answers back to that state. -/
private theorem emuGoK_replay {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRunK α s e tout u tin) :
    ∀ {u₀ : U}, e [] = some u₀ → ∀ {m : ℕ}, tout.length ≤ m →
      ∀ ext : List (Option Y),
      emuGoK α e m [] u₀ [] [] (PFunDDS.transcriptOutputs tin ++ ext)
        = emuGoK α e (m - tout.length) (keptO tout) u
            (PFunDDS.transcriptOutputs tout) (keptY tin) ext := by
  induction hr with
  | start hu =>
      intro u₀ hu₀ m hm ext
      rw [hu₀] at hu
      obtain rfl := Option.some.inj hu
      simp
  | round hr hc hu' ih =>
      intro u₀ hu₀ m hm ext
      rw [List.length_append, List.length_singleton] at hm
      cases hc with
      | liveNQ hv =>
          rename_i tout u tin u' v
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            ih hu₀ (by omega) ext, hk, emuGoK_liveNQ hv, hu',
            keptO_append_some, transcriptOutputs_append]
      | liveQ hx hy hv =>
          rename_i tout u tin u' x y v
          rw [hy]
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            transcriptOutputs_append, List.append_assoc,
            List.singleton_append, ih hu₀ (by omega), hk,
            emuGoK_liveQ hx hv, hu', keptO_append_some,
            keptY_append_some, transcriptOutputs_append]
      | deadA hst =>
          rename_i tout u tin u'
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            ih hu₀ (by omega) ext, hk, emuGoK_stallA hst, hu',
            keptO_append_none, transcriptOutputs_append]
      | deadB hx hy =>
          rename_i tout u tin u' x
          rw [hy]
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            transcriptOutputs_append, List.append_assoc,
            List.singleton_append, ih hu₀ (by omega), hk,
            emuGoK_query_bot hx, hu', keptO_append_none,
            keptY_append_none, transcriptOutputs_append]

/-- Replay, reconstruction side: `replayGoK` re-parses a joint state's
recorded inner transcript back to that state. -/
private theorem replayGoK_replay {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} (hr : EmuRunK α s e tout u tin) :
    ∀ {u₀ : U}, e [] = some u₀ → ∀ {m : ℕ}, tout.length ≤ m →
      ∀ ext : List (X × Option Y),
      replayGoK α e m [] u₀ [] (tin ++ ext)
        = replayGoK α e (m - tout.length) tout u (keptY tin) ext := by
  induction hr with
  | start hu =>
      intro u₀ hu₀ m hm ext
      rw [hu₀] at hu
      obtain rfl := Option.some.inj hu
      simp
  | round hr hc hu' ih =>
      intro u₀ hu₀ m hm ext
      rw [List.length_append, List.length_singleton] at hm
      cases hc with
      | liveNQ hv =>
          rename_i tout u tin u' v
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            ih hu₀ (by omega) ext, hk, replayGoK_liveNQ hv, hu']
      | liveQ hx hy hv =>
          rename_i tout u tin u' x y v
          rw [hy]
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            List.append_assoc, List.singleton_append,
            ih hu₀ (by omega), hk, replayGoK_liveQ hx hv, hu',
            keptY_append_some]
      | deadA hst =>
          rename_i tout u tin u'
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            ih hu₀ (by omega) ext, hk, replayGoK_stallA hst, hu']
      | deadB hx hy =>
          rename_i tout u tin u' x
          rw [hy]
          have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by
            omega
          rw [List.length_append, List.length_singleton,
            List.append_assoc, List.singleton_append,
            ih hu₀ (by omega), hk, replayGoK_query_bot hx, hu',
            keptY_append_none]

/-- The applied system's transcript, one closed round appended: live
rounds answer properly, dead rounds answer `⊥` (their outer input is
`keptPrefix`-deleted). -/
private theorem roundClose_snoc (hs : AnswersInY α)
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    {a : Option V} {tin' : List (X × Option Y)}
    (hr : EmuRunK α s e tout u tin)
    (hc : RoundClose α s tout u tin a tin') :
    PFunDDS.transcript (apply α s) e (tout.length + 1)
      = tout ++ [(u, a)] := by
  obtain ⟨⟨hkc1, hkc2⟩, ⟨f₀, vsP, hdo⟩, ⟨hokc1, hokc2⟩, hL2a, hL2b,
    hlen, hreach⟩ := emuRunK_invariant hs hr
  have hfire : e ((PFunDDS.transcript (apply α s) e tout.length)↓ᵧ)
      = some u := by
    rw [hL2a]
    exact hL2b
  rw [transcript_succ_fire hfire, hL2a]
  cases hc with
  | liveNQ hv =>
      rename_i v
      have hdo' : (vsP ++ [v], keptQ tin, keptY tin)
          ∈ driveOuter α s (max f₀ 1) [] [] [] (keptO tout ++ [u]) := by
        rw [driveOuter_append α s _ (keptO tout) [u], Part.mem_bind_iff]
        refine ⟨(vsP, keptQ tin, keptY tin),
          driveOuter_mono_le α s (le_max_left _ _) hdo, ?_⟩
        rw [Part.mem_map_iff]
        refine ⟨([v], keptQ tin, keptY tin), ?_, rfl⟩
        show _ ∈ (drive α s _ (keptO tout ++ [u])
          (keptQ tin) (keptY tin)).bind _
        rw [Part.mem_bind_iff]
        refine ⟨(v, keptQ tin, keptY tin),
          drive_mono_le α s (le_max_right _ _)
            (drive_mem_answer α s hv 0), ?_⟩
        simp [driveOuter]
      have hval : v ∈ applyRaw α s (keptO tout ++ [u]) := by
        rw [mem_applyRaw]
        refine ⟨max f₀ 1, ?_⟩
        rw [mem_applyRawAt_iff]
        exact ⟨(vsP ++ [v], keptQ tin, keptY tin), hdo', by simp⟩
      have hdom' : keptO tout ++ [u] ∈ PFunDDS.dom (apply α s) :=
        Part.dom_iff_mem.mpr ⟨v, hval⟩
      have hout : PFunDDS.output ((apply α s)⊥)
          (PFunDDS.transcriptInputs tout ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
        rw [output_fullyDefined_concat, hokc1, dif_pos hdom']
        exact congrArg some (Part.get_eq_of_mem hval hdom')
      rw [hout]
  | liveQ hx hy hv =>
      rename_i x y v
      have hyk : ∃ hc : keptQ tin ++ [x] ∈ PFunDDS.dom s,
          PFunDDS.output s (keptQ tin ++ [x]) hc = y := by
        have h0 := keptPrefix_mem_of_output_some hy
        rw [hkc1] at h0
        exact h0
      obtain ⟨hqdom, hqval⟩ := hyk
      have houtk : PFunDDS.output (s⊥) (keptQ tin ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
        rw [output_fullyDefined_concat,
          PFunDDS.keptPrefix_eq_self_of_mem_or_empty s hkc2,
          dif_pos hqdom]
        exact congrArg some hqval
      have hdrive : (v, keptQ tin ++ [x], keptY tin ++ [some y])
          ∈ drive α s 2 (keptO tout ++ [u]) (keptQ tin) (keptY tin) := by
        refine drive_mem_query α s hx ?_
        rw [houtk]
        exact drive_mem_answer α s hv 0
      have hdo' : (vsP ++ [v], keptQ tin ++ [x], keptY tin ++ [some y])
          ∈ driveOuter α s (max f₀ 2) [] [] [] (keptO tout ++ [u]) := by
        rw [driveOuter_append α s _ (keptO tout) [u], Part.mem_bind_iff]
        refine ⟨(vsP, keptQ tin, keptY tin),
          driveOuter_mono_le α s (le_max_left _ _) hdo, ?_⟩
        rw [Part.mem_map_iff]
        refine ⟨([v], keptQ tin ++ [x], keptY tin ++ [some y]), ?_, rfl⟩
        show _ ∈ (drive α s _ (keptO tout ++ [u])
          (keptQ tin) (keptY tin)).bind _
        rw [Part.mem_bind_iff]
        refine ⟨(v, keptQ tin ++ [x], keptY tin ++ [some y]),
          drive_mono_le α s (le_max_right _ _) hdrive, ?_⟩
        simp [driveOuter]
      have hval : v ∈ applyRaw α s (keptO tout ++ [u]) := by
        rw [mem_applyRaw]
        refine ⟨max f₀ 2, ?_⟩
        rw [mem_applyRawAt_iff]
        exact ⟨(vsP ++ [v], keptQ tin ++ [x], keptY tin ++ [some y]),
          hdo', by simp⟩
      have hdom' : keptO tout ++ [u] ∈ PFunDDS.dom (apply α s) :=
        Part.dom_iff_mem.mpr ⟨v, hval⟩
      have hout : PFunDDS.output ((apply α s)⊥)
          (PFunDDS.transcriptInputs tout ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some v := by
        rw [output_fullyDefined_concat, hokc1, dif_pos hdom']
        exact congrArg some (Part.get_eq_of_mem hval hdom')
      rw [hout]
  | deadA hst =>
      have hnd : keptO tout ++ [u] ∉ PFunDDS.dom (apply α s) := by
        intro hdom'
        obtain ⟨w, hw₀⟩ := Part.dom_iff_mem.mp hdom'
        have hw : w ∈ applyRaw α s (keptO tout ++ [u]) := hw₀
        rw [mem_applyRaw] at hw
        obtain ⟨f, hw⟩ := hw
        rw [mem_applyRawAt_iff] at hw
        obtain ⟨r, hrr, -⟩ := hw
        rw [driveOuter_append α s _ (keptO tout) [u],
          Part.mem_bind_iff] at hrr
        obtain ⟨ra, hra, hrb⟩ := hrr
        obtain rfl : ra = (vsP, keptQ tin, keptY tin) :=
          driveOuter_unique hra hdo
        rw [Part.mem_map_iff] at hrb
        obtain ⟨rb, hrb, -⟩ := hrb
        simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hrb
        obtain ⟨r₁, hr₁, -⟩ := hrb
        exact drive_not_mem_of_not_dom hst f _ hr₁
      have hout : PFunDDS.output ((apply α s)⊥)
          (PFunDDS.transcriptInputs tout ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
        rw [output_fullyDefined_concat, hokc1, dif_neg hnd]
      rw [hout]
  | deadB hx hy =>
      rename_i x
      have hnd_q : keptQ tin ++ [x] ∉ PFunDDS.dom s := by
        have h0 := keptPrefix_not_mem_of_output_none hy
        rw [hkc1] at h0
        exact h0
      have houtk : PFunDDS.output (s⊥) (keptQ tin ++ [x])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
        rw [output_fullyDefined_concat,
          PFunDDS.keptPrefix_eq_self_of_mem_or_empty s hkc2,
          dif_neg hnd_q]
      have hbotpair : ¬ (α (keptO tout ++ [u], keptY tin ++ [none])).Dom :=
        hs _ (Reach.answer (hreach u) hx none) (by simp)
      have hnd : keptO tout ++ [u] ∉ PFunDDS.dom (apply α s) := by
        intro hdom'
        obtain ⟨w, hw₀⟩ := Part.dom_iff_mem.mp hdom'
        have hw : w ∈ applyRaw α s (keptO tout ++ [u]) := hw₀
        rw [mem_applyRaw] at hw
        obtain ⟨f, hw⟩ := hw
        rw [mem_applyRawAt_iff] at hw
        obtain ⟨r, hrr, -⟩ := hw
        rw [driveOuter_append α s _ (keptO tout) [u],
          Part.mem_bind_iff] at hrr
        obtain ⟨ra, hra, hrb⟩ := hrr
        obtain rfl : ra = (vsP, keptQ tin, keptY tin) :=
          driveOuter_unique hra hdo
        rw [Part.mem_map_iff] at hrb
        obtain ⟨rb, hrb, -⟩ := hrb
        simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hrb
        obtain ⟨r₁, hr₁, -⟩ := hrb
        rcases f with _ | f
        · simp [drive] at hr₁
        · rcases drive_succ_elim hr₁ with ⟨x', hm, hrec⟩ | ⟨v', hm, -⟩
          · obtain rfl : x' = x := Sum.inl.inj (Part.mem_unique hm hx)
            rw [houtk] at hrec
            exact drive_not_mem_of_not_dom hbotpair f _ hrec
          · exact absurd (Part.mem_unique hm hx) (by simp)
      have hout : PFunDDS.output ((apply α s)⊥)
          (PFunDDS.transcriptInputs tout ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
        rw [output_fullyDefined_concat, hokc1, dif_neg hnd]
      rw [hout]

/-- The inner transcript of a joint state, at its own length. -/
private theorem emuRunK_transcript {n : ℕ} {tout : List (U × Option V)}
    {u : U} {tin : List (X × Option Y)} (hr : EmuRunK α s e tout u tin) :
    tout.length < n →
    PFunDDS.transcript s (emulateK α e n) tin.length = tin := by
  induction hr with
  | start hu => intro _; rfl
  | round hr hc hu' ih =>
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      obtain ⟨u₀, hu₀⟩ := emuRunK_env_some hr
      cases hc with
      | liveNQ hv => exact ih (by omega)
      | deadA hst => exact ih (by omega)
      | liveQ hx hy hv =>
          rename_i tout u tin u' x y v
          have hfireK : emulateK α e n
              ((PFunDDS.transcript s (emulateK α e n) tin.length)↓ᵧ)
              = some x := by
            rw [ih (by omega)]
            obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
            rw [emulateK_succ hu₀]
            have h := emuGoK_replay hr hu₀ (m := m') (by omega) []
            rw [List.append_nil] at h
            rw [h]
            exact emuGoK_query_nil hx _
          rw [List.length_append, List.length_singleton,
            transcript_succ_fire hfireK, ih (by omega)]
      | deadB hx hy =>
          rename_i tout u tin u' x
          have hfireK : emulateK α e n
              ((PFunDDS.transcript s (emulateK α e n) tin.length)↓ᵧ)
              = some x := by
            rw [ih (by omega)]
            obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
            rw [emulateK_succ hu₀]
            have h := emuGoK_replay hr hu₀ (m := m') (by omega) []
            rw [List.append_nil] at h
            rw [h]
            exact emuGoK_query_nil hx _
          rw [List.length_append, List.length_singleton,
            transcript_succ_fire hfireK, ih (by omega)]

/-- The inner transcript of a closed round, at its own length. -/
private theorem roundClose_transcript {n : ℕ} {tout : List (U × Option V)}
    {u : U} {tin : List (X × Option Y)} {a : Option V}
    {tin' : List (X × Option Y)} (hr : EmuRunK α s e tout u tin)
    (hc : RoundClose α s tout u tin a tin') (hn : tout.length < n) :
    PFunDDS.transcript s (emulateK α e n) tin'.length = tin' := by
  obtain ⟨u₀, hu₀⟩ := emuRunK_env_some hr
  cases hc with
  | liveNQ hv => exact emuRunK_transcript hr hn
  | deadA hst => exact emuRunK_transcript hr hn
  | liveQ hx hy hv =>
      rename_i x y v
      have hfireK : emulateK α e n
          ((PFunDDS.transcript s (emulateK α e n) tin.length)↓ᵧ)
          = some x := by
        rw [emuRunK_transcript hr hn]
        obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
        rw [emulateK_succ hu₀]
        have h := emuGoK_replay hr hu₀ (m := m') (by omega) []
        rw [List.append_nil] at h
        rw [h]
        exact emuGoK_query_nil hx _
      rw [List.length_append, List.length_singleton,
        transcript_succ_fire hfireK, emuRunK_transcript hr hn]
  | deadB hx hy =>
      rename_i x
      have hfireK : emulateK α e n
          ((PFunDDS.transcript s (emulateK α e n) tin.length)↓ᵧ)
          = some x := by
        rw [emuRunK_transcript hr hn]
        obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
        rw [emulateK_succ hu₀]
        have h := emuGoK_replay hr hu₀ (m := m') (by omega) []
        rw [List.append_nil] at h
        rw [h]
        exact emuGoK_query_nil hx _
      rw [List.length_append, List.length_singleton,
        transcript_succ_fire hfireK, emuRunK_transcript hr hn]

/-- At a terminal configuration the θ-class emulator stops. -/
private theorem emulateK_terminal_stall {n : ℕ}
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    {a : Option V} {tin' : List (X × Option Y)}
    (hr : EmuRunK α s e tout u tin)
    (hc : RoundClose α s tout u tin a tin') (hn : tout.length < n)
    (hstop : tout.length + 1 = n ∨
      e (PFunDDS.transcriptOutputs tout ++ [a]) = none) :
    emulateK α e n (PFunDDS.transcriptOutputs tin') = none := by
  obtain ⟨u₀, hu₀⟩ := emuRunK_env_some hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [emulateK_succ hu₀]
  cases hc with
  | liveNQ hv =>
      have h := emuGoK_replay hr hu₀ (m := m) (by omega) []
      rw [List.append_nil] at h
      rw [h, emuGoK_liveNQ hv]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | liveQ hx hy hv =>
      rename_i x y v
      rw [hy, transcriptOutputs_append]
      have h := emuGoK_replay hr hu₀ (m := m) (by omega) [some y]
      rw [h, emuGoK_liveQ hx hv]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | deadA hst =>
      have h := emuGoK_replay hr hu₀ (m := m) (by omega) []
      rw [List.append_nil] at h
      rw [h, emuGoK_stallA hst]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | deadB hx hy =>
      rename_i x
      rw [hy, transcriptOutputs_append]
      have h := emuGoK_replay hr hu₀ (m := m) (by omega) [none]
      rw [h, emuGoK_query_bot hx]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]

/-- At a terminal configuration the reconstruction emits the last round
and stops. -/
private theorem replayGoK_terminal {m : ℕ} {u₀ : U}
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    {a : Option V} {tin' : List (X × Option Y)}
    (hr : EmuRunK α s e tout u tin)
    (hc : RoundClose α s tout u tin a tin')
    (hu₀ : e [] = some u₀) (hle : tout.length ≤ m)
    (hstop : tout.length + 1 = m + 1 ∨
      e (PFunDDS.transcriptOutputs tout ++ [a]) = none) :
    replayGoK α e m [] u₀ [] tin' = tout ++ [(u, a)] := by
  cases hc with
  | liveNQ hv =>
      have h := replayGoK_replay hr hu₀ hle []
      rw [List.append_nil] at h
      rw [h, replayGoK_liveNQ hv]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | liveQ hx hy hv =>
      rename_i x y v
      rw [hy]
      have h := replayGoK_replay hr hu₀ hle [(x, some y)]
      rw [h, replayGoK_liveQ hx hv]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | deadA hst =>
      have h := replayGoK_replay hr hu₀ hle []
      rw [List.append_nil] at h
      rw [h, replayGoK_stallA hst]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]
  | deadB hx hy =>
      rename_i x
      rw [hy]
      have h := replayGoK_replay hr hu₀ hle [(x, none)]
      rw [h, replayGoK_query_bot hx]
      rcases hstop with hstop | hstop
      · rw [show m - tout.length = 0 from by omega]
      · rcases hk : m - tout.length with _ | k'
        · rfl
        · rw [hstop]

private theorem roundClose_length {tout : List (U × Option V)} {u : U}
    {tin : List (X × Option Y)} {a : Option V} {tin' : List (X × Option Y)}
    (hc : RoundClose α s tout u tin a tin') :
    tin'.length ≤ tin.length + 1 := by
  cases hc <;> simp

/-- **Round closure** (`hB`+`hs`+`ha` make the four shapes exhaustive):
every anchor state closes its round. -/
private theorem emuRunK_close (hB : AnswersWithin α 2)
    (hs : AnswersInY α) (ha : StopsReplying α)
    {tout : List (U × Option V)} {u : U} {tin : List (X × Option Y)}
    (hr : EmuRunK α s e tout u tin) :
    ∃ a tin', RoundClose α s tout u tin a tin' := by
  obtain ⟨-, -, -, -, -, -, hreach⟩ := emuRunK_invariant hs hr
  by_cases hdom : (α (keptO tout ++ [u], keptY tin)).Dom
  · obtain ⟨mv, hmv⟩ := Part.dom_iff_mem.mp hdom
    cases mv with
    | inr v => exact ⟨some v, tin, RoundClose.liveNQ hmv⟩
    | inl x =>
        rcases hy : PFunDDS.output (s⊥)
            (PFunDDS.transcriptInputs tin ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exact ⟨none, _, RoundClose.deadB hmv hy⟩
        · have hdom2 : (α (keptO tout ++ [u],
              keptY tin ++ [some y])).Dom := ha y (hreach u) hmv
          obtain ⟨mv2, hmv2⟩ := Part.dom_iff_mem.mp hdom2
          cases mv2 with
          | inr v => exact ⟨some v, _, RoundClose.liveQ hmv hy hmv2⟩
          | inl x₂ =>
              exfalso
              refine hB (keptO tout ++ [u], keptY tin) (hreach u)
                [some y, none] (by simp) ?_
              intro j hj
              match j, hj with
              | 0, _ => exact ⟨x, by simpa using hmv⟩
              | 1, _ => exact ⟨x₂, by simpa using hmv2⟩
  · exact ⟨none, tin, RoundClose.deadA hdom⟩

/-- **Termination**: from any joint state within the round budget, the
interaction reaches a terminal configuration. -/
private theorem emuRunK_terminal (hB : AnswersWithin α 2)
    (hs : AnswersInY α) (ha : StopsReplying α) {n : ℕ} :
    ∀ (k : ℕ) {tout : List (U × Option V)} {u : U}
      {tin : List (X × Option Y)},
      EmuRunK α s e tout u tin → tout.length + k + 1 = n →
      ∃ tout' u' tinP a tinC, EmuRunK α s e tout' u' tinP ∧
        RoundClose α s tout' u' tinP a tinC ∧
        tout'.length + 1 ≤ n ∧
        (tout'.length + 1 = n ∨
          e (PFunDDS.transcriptOutputs tout' ++ [a]) = none) := by
  intro k
  induction k with
  | zero =>
      intro tout u tin hr hn
      obtain ⟨a, tin', hc⟩ := emuRunK_close hB hs ha hr
      exact ⟨tout, u, tin, a, tin', hr, hc, by omega, Or.inl (by omega)⟩
  | succ k ih =>
      intro tout u tin hr hn
      obtain ⟨a, tin', hc⟩ := emuRunK_close hB hs ha hr
      rcases he : e (PFunDDS.transcriptOutputs tout ++ [a]) with _ | u'
      · exact ⟨tout, u, tin, a, tin', hr, hc, by omega, Or.inr he⟩
      · exact ih (EmuRunK.round hr hc he)
          (by rw [List.length_append, List.length_singleton]; omega)

end KeptRun

/-- **The θ-class bridge**: for a Def 3.8 converter with anchor-confined
silence, the applied system's transcript against `e` is the kept
reconstruction of the assumed system's transcript against the θ-class
emulator, with inner fuel `n` (one recorded answer per round). -/
private theorem transcript_apply_kept (α : ProtocolFn U V X Y)
    (hB : AnswersWithin α 2) (hs : AnswersInY α) (ha : StopsReplying α)
    (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE U V) (n : ℕ) :
    PFunDDS.transcript (apply α s) e n
      = replayTranscriptK α e n
          (PFunDDS.transcript s (emulateK α e n) n) := by
  rcases n with _ | m
  · rfl
  rcases hu₀ : e [] with _ | u₀
  · rw [replayTranscriptK_of_env_nil hu₀]
    have hstall : e ((PFunDDS.transcript (apply α s) e 0)↓ᵧ) = none := hu₀
    exact transcript_freeze hstall (Nat.zero_le _)
  · have hbase : EmuRunK α s e [] u₀ [] := EmuRunK.start hu₀
    obtain ⟨tout, u, tinP, a, tinC, hr, hc, hle, hstop⟩ :=
      emuRunK_terminal hB hs ha (n := m + 1) m hbase (by simp)
    obtain ⟨-, -, -, -, -, hlen, -⟩ := emuRunK_invariant hs hr
    have hsnoc := roundClose_snoc hs hr hc
    have hLHS : PFunDDS.transcript (apply α s) e (m + 1)
        = tout ++ [(u, a)] := by
      rcases hstop with hstop | hstop
      · rw [← hstop]
        exact hsnoc
      · have hfreeze : e ((PFunDDS.transcript (apply α s) e
            (tout.length + 1))↓ᵧ) = none := by
          rw [hsnoc, transcriptOutputs_append]
          exact hstop
        rw [transcript_freeze hfreeze hle, hsnoc]
    have hlenC : tinC.length ≤ m + 1 := by
      have := roundClose_length hc
      omega
    have hTin : PFunDDS.transcript s (emulateK α e (m + 1)) (m + 1)
        = tinC := by
      have h1 := roundClose_transcript (n := m + 1) hr hc (by omega)
      have h2 : emulateK α e (m + 1)
          ((PFunDDS.transcript s (emulateK α e (m + 1))
            tinC.length)↓ᵧ) = none := by
        rw [h1]
        exact emulateK_terminal_stall (n := m + 1) hr hc (by omega) hstop
      rw [transcript_freeze h2 hlenC, h1]
    rw [hLHS, hTin, replayTranscriptK_succ hu₀]
    exact (replayGoK_terminal hr hc hu₀ (by omega) hstop).symm

/-- **The θ-class certificate for Def 16 membership** (CR18 §6.2.3):
a converter with inner arity one (`AnswersWithin α 2`), silence past `⊥`
(`AnswersInY`), and every opened round closed (`StopsReplying`) is
emulable — its dead rounds issue at most one `⊥`-answered query, which
both the assumed system's and the applied system's `keptPrefix` erase. -/
theorem emulable_of_stopsReplying (α : ProtocolFn U V X Y)
    (hB : AnswersWithin α 2) (hs : AnswersInY α) (ha : StopsReplying α) :
    Emulable α := fun e n =>
  ⟨emulateK α e n, n, replayTranscriptK α e n,
    fun s => transcript_apply_kept α hB hs ha s e n⟩

/-! ### Class membership: the simple-converter shape and its budget cuts -/

private theorem reach_mono_of_le {α β : ProtocolFn U V X Y}
    (hle : ∀ p mv, mv ∈ α p → mv ∈ β p) {p : List U × List (Option Y)}
    (h : Reach α p) : Reach β p := by
  induction h with
  | first u => exact Reach.first u
  | answer hr hx y ih => exact Reach.answer ih (hle _ _ hx) y
  | next hr hv u ih => exact Reach.next ih (hle _ _ hv) u

/-- Any value-subfunction of a simple converter has inner arity one. -/
theorem answersWithin_of_le_simpleFn {α : ProtocolFn U V X Y}
    {c : U → X} {d : Y → V}
    (hle : ∀ p mv, mv ∈ α p → mv ∈ simpleFn c d p) :
    AnswersWithin α 2 := by
  intro p _ ext hlen hchain
  obtain ⟨x₀, h₀⟩ := hchain 0 (by omega)
  obtain ⟨x₁, h₁⟩ := hchain 1 (by omega)
  have e₀ := simpleFn_inl_inv (hle _ _ h₀)
  have e₁ := simpleFn_inl_inv (hle _ _ h₁)
  simp only [List.length_append, List.length_take] at e₀ e₁
  omega

/-- Any value-subfunction of a simple converter answers in `Y`. -/
theorem answersInY_of_le_simpleFn {α : ProtocolFn U V X Y}
    {c : U → X} {d : Y → V}
    (hle : ∀ p mv, mv ∈ α p → mv ∈ simpleFn c d p) :
    AnswersInY α := by
  intro p hre hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  have hre' := reach_mono_of_le hle hre
  rw [reach_simpleFn_iff] at hre'
  have hm' := hle _ _ hm
  rcases hre' with ⟨hlen, hsome⟩ | ⟨hlen, hpos, hsome⟩
  · have := hsome none hnone
    simp at this
  · cases mv with
    | inl x =>
        have h1 := simpleFn_inl_inv hm'
        omega
    | inr v =>
        obtain ⟨h1, h0, y, hy, -⟩ := simpleFn_inr_inv hm'
        rw [← List.dropLast_append_getLast
          (List.ne_nil_of_length_pos h0)] at hnone
        rcases List.mem_append.mp hnone with hmem | hmem
        · have := hsome none hmem
          simp at this
        · rw [List.mem_singleton] at hmem
          have hcontra := hmem.trans hy
          simp at hcontra

/-- The simple converter closes every round it opens. -/
theorem stopsReplying_simpleFn (c : U → X) (d : Y → V) :
    StopsReplying (simpleFn c d) := by
  intro us ys x y hre hx
  have hlen := simpleFn_inl_inv hx
  refine Part.dom_iff_mem.mpr ⟨_, simpleFn_inr_mem c d ?_ ?_ (y := y) ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · simp
  · exact List.getLast_concat

/-- MauRen11 Def 16 membership of the simple converter (DESIGN §10.5's
worked example, hence of `idFn` — MauRen11 fn. 22). -/
@[rs_rule "rs.emulable.simple" rs_emulable random_systems]
theorem emulable_simpleFn (c : U → X) (d : Y → V) :
    Emulable (simpleFn c d) :=
  emulable_of_stopsReplying _
    (answersWithin_of_le_simpleFn (fun _ _ h => h))
    (answersInY_of_le_simpleFn (fun _ _ h => h))
    (stopsReplying_simpleFn c d)

private theorem queryLimitFn_le (q : ℕ) (p : List X × List (Option Y))
    (mv : X ⊕ Y) (h : mv ∈ queryLimitFn q p) :
    mv ∈ simpleFn (id : X → X) (id : Y → Y) p := by
  obtain ⟨us, ys⟩ := p
  cases mv with
  | inl x =>
      obtain ⟨hne, rfl, hlen, -⟩ := queryLimitFn_inl_elim h
      exact simpleFn_inl_mem id id hlen
  | inr v =>
      obtain ⟨h0, hy, hlen, -⟩ := queryLimitFn_inr_elim h
      exact simpleFn_inr_mem id id hlen h0 hy

/-- The `[q]` filter closes every round it opens — its budget silence is
anchor-confined (CR18 Def 3.10's "undefined as of the `(q+1)`-st query"
arrives *before* the round's query). -/
theorem stopsReplying_queryLimitFn (q : ℕ) :
    StopsReplying (queryLimitFn q : ProtocolFn X Y X Y) := by
  intro us ys x y hre hx
  obtain ⟨hlen, hq⟩ := queryLimitFn_inl_inv hx
  refine Part.dom_iff_mem.mpr
    ⟨_, queryLimitFn_inr_mem q ?_ ?_ ?_ (y := y) ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · simp
  · omega
  · exact List.getLast_concat

/-- MauRen11 Def 16 membership of the `[q]` query filter (CR18
Def 3.10). -/
@[rs_rule "rs.emulable.query_limit" rs_emulable random_systems]
theorem emulable_queryLimitFn (q : ℕ) :
    Emulable (queryLimitFn q : ProtocolFn X Y X Y) :=
  emulable_of_stopsReplying _
    (answersWithin_of_le_simpleFn (queryLimitFn_le q))
    (answersInY_of_le_simpleFn (queryLimitFn_le q))
    (stopsReplying_queryLimitFn q)

end KeptBridge

/-! ### The boundary of the class: a Def 3.8 converter that is not absorbable

MauRen11's Σ is a *chosen* set of converters; membership is certified, not
automatic.  `probeFn` witnesses that CR18 Def 3.8's two clauses (bounded
streaks, silence past `⊥`) do **not** imply absorbability: it makes one
properly-answered inner query and then stalls, so the applied system's
`⊥`-completion erases the probe (`keptPrefix` deletes the dead outer
input) while any inner interrogation that discovers the stall must have
made it — the outer transcript then encodes a correlation across
incompatible inner interrogations that no single inner environment
obtains. -/

section Boundary

/-- The stall-after-probe converter: the identity relay (`simpleFn id id`)
made silent at the single reachable all-proper pair `([true], [some
false])` — it probes, learns, and refuses to answer. -/
def probeFn : ProtocolFn Bool Bool Bool Bool := fun p =>
  if h : p.1.length = p.2.length + 1 then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2) with
    | some y =>
        if p.1 = [true] ∧ y = false then Part.none
        else Part.some (Sum.inr y)
    | none => Part.none
  else Part.none

private theorem probeFn_le {p : List Bool × List (Option Bool)}
    {mv : Bool ⊕ Bool} (h : mv ∈ probeFn p) :
    mv ∈ simpleFn (id : Bool → Bool) (id : Bool → Bool) p := by
  simp only [probeFn, simpleFn] at h ⊢
  split_ifs at h ⊢ with h1 h2
  · exact h
  · split at h
    · rename_i y hy
      rw [hy]
      split_ifs at h with h3
      · simp at h
      · simpa using h
    · simp at h
  · exact h

private theorem reach_probeFn_imp {p : List Bool × List (Option Bool)}
    (h : Reach probeFn p) :
    Reach (simpleFn (id : Bool → Bool) (id : Bool → Bool)) p := by
  induction h with
  | first u => exact Reach.first u
  | answer hr hx y ih => exact Reach.answer ih (probeFn_le hx) y
  | next hr hv u ih => exact Reach.next ih (probeFn_le hv) u

/-- `probeFn` satisfies CR18 Def 3.8's finite-bound clause. -/
theorem answersWithin_probeFn : AnswersWithin probeFn 2 := by
  intro p _ ext hlen hchain
  obtain ⟨x₀, h₀⟩ := hchain 0 (by omega)
  obtain ⟨x₁, h₁⟩ := hchain 1 (by omega)
  have e₀ := simpleFn_inl_inv (probeFn_le h₀)
  have e₁ := simpleFn_inl_inv (probeFn_le h₁)
  simp only [List.length_append, List.length_take] at e₀ e₁
  omega

/-- `probeFn` satisfies CR18 Def 3.8's input-alphabet clause. -/
theorem answersInY_probeFn : AnswersInY probeFn := by
  intro p hre hnone hdom
  obtain ⟨mv, hm⟩ := Part.dom_iff_mem.mp hdom
  have hre' := reach_probeFn_imp hre
  rw [reach_simpleFn_iff] at hre'
  have hm' := probeFn_le hm
  rcases hre' with ⟨hlen, hsome⟩ | ⟨hlen, hpos, hsome⟩
  · have := hsome none hnone
    simp at this
  · cases mv with
    | inl x =>
        have h1 := simpleFn_inl_inv hm'
        omega
    | inr v =>
        obtain ⟨h1, h0, y, hy, -⟩ := simpleFn_inr_inv hm'
        rw [← List.dropLast_append_getLast
          (List.ne_nil_of_length_pos h0)] at hnone
        rcases List.mem_append.mp hnone with hmem | hmem
        · have := hsome none hmem
          simp at this
        · rw [List.mem_singleton] at hmem
          have hcontra := hmem.trans hy
          simp at hcontra

/-- The two-parameter probe target: answer `b` to interrogations opening
with query `true`, answer `c` otherwise — total, so `⊥` never arises. -/
def probeSys (b c : Bool) : PFunDDS.DDS Bool Bool :=
  PFunDDS.historyEvaluator (fun l hne => if l.head hne then b else c)

private theorem output_fullyDefined_historyEvaluator
    {g : (l : List X) → l ≠ [] → Y} {l : List X} (hne : l ≠ [])
    (h : l ∈ PFunDDS.dom ((PFunDDS.historyEvaluator g)⊥)) :
    PFunDDS.output ((PFunDDS.historyEvaluator g)⊥) l h
      = some (g l hne) := by
  obtain ⟨l', x, rfl⟩ : ∃ l' x, l = l' ++ [x] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hl' : l' ∈ PFunDDS.dom (PFunDDS.historyEvaluator g) ∨ l' = [] := by
    rcases eq_or_ne l' [] with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (by rw [PFunDDS.dom_historyEvaluator]; exact h0)
  have hnext : l' ++ [x] ∈ PFunDDS.dom (PFunDDS.historyEvaluator g) := by
    rw [PFunDDS.dom_historyEvaluator]
    simp
  rw [PFunDDS.output_fullyDefined_append_of_mem _ l' x hl' hnext,
    PFunDDS.historyEvaluator_output]

private theorem probeSys_out (b c : Bool) {l : List Bool} (hne : l ≠ [])
    (h : l ∈ PFunDDS.dom ((probeSys b c)⊥)) :
    PFunDDS.output ((probeSys b c)⊥) l h
      = some (if l.head hne then b else c) :=
  output_fullyDefined_historyEvaluator hne h

private theorem probeFn_val_q :
    probeFn ([true], []) = Part.some (Sum.inl true) := by
  simp [probeFn]

private theorem probeFn_val_qF :
    probeFn ([false], []) = Part.some (Sum.inl false) := by
  simp [probeFn]

private theorem probeFn_val_stall :
    probeFn ([true], [some false]) = Part.none := by
  simp [probeFn]

private theorem probeFn_val_aT :
    probeFn ([true], [some true]) = Part.some (Sum.inr true) := by
  simp [probeFn]

private theorem probeFn_val_aF (c : Bool) :
    probeFn ([false], [some c]) = Part.some (Sum.inr c) := by
  simp [probeFn]

private theorem probeFn_val_q2 :
    probeFn ([true, false], [some true]) = Part.some (Sum.inl false) := by
  simp [probeFn]

private theorem probeFn_val_a2 :
    probeFn ([true, false], [some true, some true])
      = Part.some (Sum.inr true) := by
  simp [probeFn]

private def probeEnv : PFunDDS.DDE Bool Bool :=
  playQueries [true, false]

private theorem drive_probe_dead (c : Bool) :
    ∀ (fuel : ℕ) (r : Bool × List Bool × List (Option Bool)),
      r ∉ drive probeFn (probeSys false c) fuel [true] [] [] := by
  intro fuel r hr
  rcases fuel with _ | fuel
  · simp [drive] at hr
  · rcases drive_succ_elim hr with ⟨x, hx, hrec⟩ | ⟨v, hv, -⟩
    · rw [probeFn_val_q] at hx
      obtain rfl : x = true := by simpa using hx
      have hout : PFunDDS.output ((probeSys false c)⊥) ([] ++ [true])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some false := by
        rw [probeSys_out false c (by simp)]
        simp
      rw [hout] at hrec
      simp only [List.nil_append] at hrec
      rcases fuel with _ | fuel
      · simp [drive] at hrec
      · rcases drive_succ_elim hrec with ⟨x₂, hx₂, -⟩ | ⟨v₂, hv₂, -⟩
        · rw [probeFn_val_stall] at hx₂
          simp at hx₂
        · rw [probeFn_val_stall] at hv₂
          simp at hv₂
    · rw [probeFn_val_q] at hv
      simp at hv

private theorem probe_dead_not_dom (c : Bool) :
    ¬ (applyRaw probeFn (probeSys false c) [true]).Dom := by
  intro hdom
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
  rw [mem_applyRaw] at hv
  obtain ⟨fuel, hv⟩ := hv
  rw [mem_applyRawAt_iff] at hv
  obtain ⟨r, hr, -⟩ := hv
  simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
  obtain ⟨r₁, hr₁, -⟩ := hr
  exact drive_probe_dead c fuel r₁ (by simpa using hr₁)

private theorem probe_alive_mem (c : Bool) :
    true ∈ applyRaw probeFn (probeSys true c) [true] := by
  rw [mem_applyRaw]
  refine ⟨2, ?_⟩
  rw [mem_applyRawAt_iff]
  refine ⟨([true], [true], [some true]), ?_, by simp⟩
  show _ ∈ (drive probeFn (probeSys true c) 2 ([] ++ [true]) [] []).bind _
  rw [Part.mem_bind_iff]
  refine ⟨(true, [true], [some true]), ?_, ?_⟩
  · simp only [List.nil_append]
    have hout : PFunDDS.output ((probeSys true c)⊥) ([] ++ [true])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some true := by
      rw [probeSys_out true c (by simp)]
      simp
    have hm : Sum.inl true ∈ probeFn ([true], []) := by
      rw [probeFn_val_q]
      exact Part.mem_some _
    have hm2 : Sum.inr true ∈ probeFn ([true], [some true]) := by
      rw [probeFn_val_aT]
      exact Part.mem_some _
    refine drive_mem_query probeFn (probeSys true c) hm ?_
    rw [hout]
    simp only [List.nil_append]
    exact drive_mem_answer probeFn (probeSys true c) hm2 0
  · rw [Part.mem_map_iff]
    exact ⟨([], [true], [some true]), by simp [driveOuter], rfl⟩

private theorem probe_deadF_mem (c : Bool) :
    c ∈ applyRaw probeFn (probeSys false c) [false] := by
  rw [mem_applyRaw]
  refine ⟨2, ?_⟩
  rw [mem_applyRawAt_iff]
  refine ⟨([c], [false], [some c]), ?_, by simp⟩
  show _ ∈ (drive probeFn (probeSys false c) 2 ([] ++ [false]) [] []).bind _
  rw [Part.mem_bind_iff]
  refine ⟨(c, [false], [some c]), ?_, ?_⟩
  · simp only [List.nil_append]
    have hout : PFunDDS.output ((probeSys false c)⊥) ([] ++ [false])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some c := by
      rw [probeSys_out false c (by simp)]
      simp
    have hm : Sum.inl false ∈ probeFn ([false], []) := by
      rw [probeFn_val_qF]
      exact Part.mem_some _
    have hm2 : Sum.inr c ∈ probeFn ([false], [some c]) := by
      rw [probeFn_val_aF]
      exact Part.mem_some _
    refine drive_mem_query probeFn (probeSys false c) hm ?_
    rw [hout]
    simp only [List.nil_append]
    exact drive_mem_answer probeFn (probeSys false c) hm2 0
  · rw [Part.mem_map_iff]
    exact ⟨([], [false], [some c]), by simp [driveOuter], rfl⟩

private theorem probe_aliveTF_mem (c : Bool) :
    true ∈ applyRaw probeFn (probeSys true c) [true, false] := by
  rw [mem_applyRaw]
  refine ⟨2, ?_⟩
  rw [mem_applyRawAt_iff]
  refine ⟨([true, true], [true, false], [some true, some true]), ?_, by simp⟩
  show _ ∈ (drive probeFn (probeSys true c) 2 ([] ++ [true]) [] []).bind _
  rw [Part.mem_bind_iff]
  refine ⟨(true, [true], [some true]), ?_, ?_⟩
  · simp only [List.nil_append]
    have hout : PFunDDS.output ((probeSys true c)⊥) ([] ++ [true])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some true := by
      rw [probeSys_out true c (by simp)]
      simp
    have hm : Sum.inl true ∈ probeFn ([true], []) := by
      rw [probeFn_val_q]
      exact Part.mem_some _
    have hm2 : Sum.inr true ∈ probeFn ([true], [some true]) := by
      rw [probeFn_val_aT]
      exact Part.mem_some _
    refine drive_mem_query probeFn (probeSys true c) hm ?_
    rw [hout]
    simp only [List.nil_append]
    exact drive_mem_answer probeFn (probeSys true c) hm2 0
  · rw [Part.mem_map_iff]
    refine ⟨([true], [true, false], [some true, some true]), ?_, rfl⟩
    show _ ∈ (drive probeFn (probeSys true c) 2
      (([] ++ [true]) ++ [false]) [true] [some true]).bind _
    rw [Part.mem_bind_iff]
    refine ⟨(true, [true, false], [some true, some true]), ?_, ?_⟩
    · have hout2 : PFunDDS.output ((probeSys true c)⊥) ([true] ++ [false])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some true := by
        rw [probeSys_out true c (by simp)]
        simp
      have hq : (true, [true, false], [some true, some true]) ∈
          drive probeFn (probeSys true c) 2 [true, false] [true]
            [some true] := by
        have hm : Sum.inl false ∈ probeFn ([true, false], [some true]) := by
          rw [probeFn_val_q2]
          exact Part.mem_some _
        have hm2 : Sum.inr true ∈
            probeFn ([true, false], [some true, some true]) := by
          rw [probeFn_val_a2]
          exact Part.mem_some _
        refine drive_mem_query probeFn (probeSys true c) hm ?_
        rw [hout2]
        show _ ∈ drive probeFn (probeSys true c) 1 [true, false]
          [true, false] [some true, some true]
        exact drive_mem_answer probeFn (probeSys true c) hm2 0
      exact hq
    · rw [Part.mem_map_iff]
      exact ⟨([], [true, false], [some true, some true]),
        by simp [driveOuter], rfl⟩

open Classical in
private theorem probe_out_dead1 (c : Bool) :
    PFunDDS.output ((apply probeFn (probeSys false c))⊥) [true]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  have key : ∀ (ctx : List Bool), ctx = [] →
      (if hcand : ctx ++ [true]
          ∈ PFunDDS.dom (apply probeFn (probeSys false c))
        then some (PFunDDS.output (apply probeFn (probeSys false c))
          (ctx ++ [true]) hcand)
        else none) = none := by
    rintro _ rfl
    rw [dif_neg (show ¬ ([] ++ [true]
      ∈ PFunDDS.dom (apply probeFn (probeSys false c))) from probe_dead_not_dom c)]
  exact key _ rfl

private theorem probe_out_alive1 (c : Bool) :
    PFunDDS.output ((apply probeFn (probeSys true c))⊥) [true]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some true := by
  have h := PFunDDS.output_fullyDefined_append_of_mem
    (apply probeFn (probeSys true c)) [] true (Or.inr rfl)
    (show [] ++ [true] ∈ PFunDDS.dom (apply probeFn (probeSys true c)) from Part.dom_iff_mem.mpr ⟨true, probe_alive_mem c⟩)
  exact h.trans (congrArg some (Part.get_eq_of_mem (probe_alive_mem c) _))

open Classical in
private theorem probe_out_dead2 (c : Bool) :
    PFunDDS.output ((apply probeFn (probeSys false c))⊥) [true, false]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some c := by
  have hkp : PFunDDS.keptPrefix (apply probeFn (probeSys false c)) [true]
      = [] := by
    show (if [] ++ [true] ∈ PFunDDS.dom (apply probeFn (probeSys false c))
      then [] ++ [true] else []) = []
    rw [if_neg (show ¬ ([] ++ [true]
      ∈ PFunDDS.dom (apply probeFn (probeSys false c))) from probe_dead_not_dom c)]
  have key : ∀ (ctx : List Bool), ctx = [] →
      (if hcand : ctx ++ [false]
          ∈ PFunDDS.dom (apply probeFn (probeSys false c))
        then some (PFunDDS.output (apply probeFn (probeSys false c))
          (ctx ++ [false]) hcand)
        else none) = some c := by
    rintro _ rfl
    rw [dif_pos (show [] ++ [false]
      ∈ PFunDDS.dom (apply probeFn (probeSys false c)) from Part.dom_iff_mem.mpr ⟨c, probe_deadF_mem c⟩)]
    exact congrArg some (Part.get_eq_of_mem (probe_deadF_mem c) _)
  exact key _ hkp

private theorem probe_out_alive2 (c : Bool) :
    PFunDDS.output ((apply probeFn (probeSys true c))⊥) [true, false]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = some true := by
  have h := PFunDDS.output_fullyDefined_append_of_mem
    (apply probeFn (probeSys true c)) [true] false
    (Or.inl (Part.dom_iff_mem.mpr ⟨true, probe_alive_mem c⟩))
    (show [true] ++ [false]
        ∈ PFunDDS.dom (apply probeFn (probeSys true c)) from Part.dom_iff_mem.mpr ⟨true, probe_aliveTF_mem c⟩)
  exact h.trans (congrArg some (Part.get_eq_of_mem (probe_aliveTF_mem c) _))

private theorem probe_outer_dead (c : Bool) :
    PFunDDS.transcript (apply probeFn (probeSys false c)) probeEnv 2
      = [(true, none), (false, some c)] := by
  have hf1 : probeEnv ((PFunDDS.transcript
      (apply probeFn (probeSys false c)) probeEnv 0)↓ᵧ) = some true := rfl
  have h1 : PFunDDS.transcript (apply probeFn (probeSys false c)) probeEnv 1
      = [(true, none)] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, transcript_succ_fire hf1]
    simp only [transcript_zero, transcriptInputs_nil, List.nil_append]
    rw [probe_out_dead1]
  have hf2 : probeEnv ((PFunDDS.transcript
      (apply probeFn (probeSys false c)) probeEnv 1)↓ᵧ) = some false := by
    rw [h1]
    rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, transcript_succ_fire hf2, h1]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [probe_out_dead2]

private theorem probe_outer_alive (c : Bool) :
    PFunDDS.transcript (apply probeFn (probeSys true c)) probeEnv 2
      = [(true, some true), (false, some true)] := by
  have hf1 : probeEnv ((PFunDDS.transcript
      (apply probeFn (probeSys true c)) probeEnv 0)↓ᵧ) = some true := rfl
  have h1 : PFunDDS.transcript (apply probeFn (probeSys true c)) probeEnv 1
      = [(true, some true)] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, transcript_succ_fire hf1]
    simp only [transcript_zero, transcriptInputs_nil, List.nil_append]
    rw [probe_out_alive1]
  have hf2 : probeEnv ((PFunDDS.transcript
      (apply probeFn (probeSys true c)) probeEnv 1)↓ᵧ) = some false := by
    rw [h1]
    rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, transcript_succ_fire hf2, h1]
  simp only [PFunDDS.transcriptInputs, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  rw [probe_out_alive2]

/-- Interrogations of `probeSys` reveal only the bit selected by the first
query: systems agreeing on that bit are transcript-indistinguishable under
any environment opening with it. -/
private theorem probe_inner_congr {e' : PFunDDS.DDE Bool Bool} {x₁ : Bool}
    (he : e' [] = some x₁) {b c b' c' : Bool}
    (hagree : (if x₁ then b else c) = (if x₁ then b' else c')) (m : ℕ) :
    PFunDDS.transcript (probeSys b c) e' m
      = PFunDDS.transcript (probeSys b' c') e' m := by
  have key : ∀ m, PFunDDS.transcript (probeSys b c) e' m
      = PFunDDS.transcript (probeSys b' c') e' m ∧
      (PFunDDS.transcript (probeSys b c) e' m = [] ∨
        ((PFunDDS.transcript (probeSys b c) e' m)↓ₓ).head? = some x₁) := by
    intro m
    induction m with
    | zero => exact ⟨rfl, Or.inl rfl⟩
    | succ m ih =>
        obtain ⟨heq, hinv⟩ := ih
        rcases hstep : e' ((PFunDDS.transcript (probeSys b c) e' m)↓ᵧ)
          with _ | x
        · rw [transcript_succ_stall hstep,
            transcript_succ_stall (by rw [← heq]; exact hstep)]
          exact ⟨heq, hinv⟩
        · have hstep' : e' ((PFunDDS.transcript (probeSys b' c') e' m)↓ᵧ)
              = some x := by
            rw [← heq]
            exact hstep
          rw [transcript_succ_fire hstep, transcript_succ_fire hstep']
          have hne : (PFunDDS.transcript (probeSys b c) e' m)↓ₓ ++ [x]
              ≠ [] := by simp
          have hhead? : ((PFunDDS.transcript (probeSys b c) e' m)↓ₓ
              ++ [x]).head? = some x₁ := by
            rcases hinv with hnil | hh
            · have hx : x = x₁ := by
                rw [hnil] at hstep
                rw [show ((([] : List (Bool × Option Bool)))↓ᵧ) = []
                  from rfl, he] at hstep
                exact (Option.some.inj hstep).symm
              rw [hnil]
              simp [hx]
            · cases hT : (PFunDDS.transcript (probeSys b c) e' m)↓ₓ with
              | nil => rw [hT] at hh; simp at hh
              | cons a l =>
                  rw [hT] at hh
                  simp only [List.head?_cons, Option.some.injEq] at hh
                  simp [hh]
          have hhead : ((PFunDDS.transcript (probeSys b c) e' m)↓ₓ
              ++ [x]).head hne = x₁ := by
            rw [List.head?_eq_some_head hne] at hhead?
            exact Option.some.inj hhead?
          have hout : PFunDDS.output ((probeSys b c)⊥)
              ((PFunDDS.transcript (probeSys b c) e' m)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              = PFunDDS.output ((probeSys b' c')⊥)
              ((PFunDDS.transcript (probeSys b' c') e' m)↓ₓ ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) := by
            rw [probeSys_out b c hne, ← heq,
              probeSys_out b' c' hne, hhead, hagree]
          refine ⟨?_, Or.inr ?_⟩
          · rw [hout, heq]
          · rw [transcriptInputs_append]
            exact hhead?
  exact (key m).1

/-- **The boundary of Σ** (MauRen11 Def 16 membership is a genuine choice):
`probeFn` satisfies both CR18 Def 3.8 clauses (`answersWithin_probeFn`,
`answersInY_probeFn`) yet is **not absorbable** — its dead round makes a
properly-answered probe that the applied system's `⊥`-completion erases
while any inner interrogation discovering the stall must have made it. -/
theorem not_emulable_probeFn : ¬ Emulable probeFn := by
  intro h
  obtain ⟨e', m, g, hg⟩ := h probeEnv 2
  rcases he : e' [] with _ | x₁
  · have hstall : ∀ s : PFunDDS.DDS Bool Bool,
        PFunDDS.transcript s e' m = [] := by
      intro s
      have h0 : e' ((PFunDDS.transcript s e' 0)↓ᵧ) = none := he
      exact transcript_freeze h0 (Nat.zero_le m)
    have h1 := hg (probeSys false false)
    have h2 := hg (probeSys true false)
    rw [probe_outer_dead, hstall] at h1
    rw [probe_outer_alive, hstall] at h2
    have hcontra := h1.trans h2.symm
    simp at hcontra
  · cases x₁ with
    | true =>
        have hcongr := probe_inner_congr he
          (b := false) (c := false) (b' := false) (c' := true)
          (by simp) m
        have h1 := hg (probeSys false false)
        have h2 := hg (probeSys false true)
        rw [probe_outer_dead] at h1 h2
        rw [hcongr] at h1
        have hcontra := h1.trans h2.symm
        simp at hcontra
    | false =>
        have hcongr := probe_inner_congr he
          (b := false) (c := false) (b' := true) (c' := false)
          (by simp) m
        have h1 := hg (probeSys false false)
        have h2 := hg (probeSys true false)
        rw [probe_outer_dead] at h1
        rw [probe_outer_alive] at h2
        rw [hcongr] at h1
        have hcontra := h1.trans h2.symm
        simp at hcontra

end Boundary

section ParConverter

variable {U' : Type*} {V' : Type*} {X' : Type*} {Y' : Type*}

/-- MauRen11 §6.2: the parallel composition `α‖β` of converters —
queries are routed by their tag, and the mover's move is re-tagged.
Fn. 23: `(α‖β)ⁱT` need not be determined if `T` is not of the form
`R‖S`; accordingly, off `‖`-shaped histories the values are junk in the
sense of the trace-tree discipline (DESIGN §10.5).  ⊥-attribution
pending: an untagged `⊥` answer cannot be routed by `filterMap`; values
beyond the all-`some` fragment are junk in the trace-tree sense until
the attribution fold lands. -/
def par (α : ProtocolFn U V X Y) (β : ProtocolFn U' V' X' Y') :
    ProtocolFn (U ⊕ U') (V ⊕ V') (X ⊕ X') (Y ⊕ Y') := fun p =>
  match p.1.getLast? with
  | some (Sum.inl _) =>
      (α (p.1.filterMap Sum.getLeft?,
          p.2.filterMap fun oy => (oy.bind Sum.getLeft?).map some)).map
        (Sum.map Sum.inl Sum.inl)
  | some (Sum.inr _) =>
      (β (p.1.filterMap Sum.getRight?,
          p.2.filterMap fun oy => (oy.bind Sum.getRight?).map some)).map
        (Sum.map Sum.inr Sum.inr)
  | none => Part.none


end ParConverter

end PFunConverter

namespace PFunDDS

variable {X Y X' Y' : Type*}

/-- CR18 Definition 3.4, binary form (fn. 20: the two interfaces
"merged into a single interface, by some addressing mechanism" — the
tagged sum): each query is routed to the component owning its tag,
which answers on the sub-history of its own inputs. -/
noncomputable def par (s : DDS X Y) (t : DDS X' Y') :
    DDS (X ⊕ X') (Y ⊕ Y') :=
  ⟨fun l =>
    Part.assert ((l.filterMap Sum.getLeft? ≠ []) →
        (s.1 (l.filterMap Sum.getLeft?)).Dom) fun _ =>
      Part.assert ((l.filterMap Sum.getRight? ≠ []) →
          (t.1 (l.filterMap Sum.getRight?)).Dom) fun _ =>
        match l.getLast? with
        | some (Sum.inl _) => (s.1 (l.filterMap Sum.getLeft?)).map Sum.inl
        | some (Sum.inr _) => (t.1 (l.filterMap Sum.getRight?)).map Sum.inr
        | none => Part.none, by
    constructor
    · rintro ⟨hp, hq, h⟩
      exact h
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨hL₂, hR₂, -⟩ := hdom
      obtain ⟨u, rfl⟩ := hpre
      have hL₁ : l₁.filterMap Sum.getLeft? ≠ [] →
          (s.1 (l₁.filterMap Sum.getLeft?)).Dom := by
        intro hne'
        have hpre' : l₁.filterMap Sum.getLeft? <+:
            (l₁ ++ u).filterMap Sum.getLeft? :=
          ⟨u.filterMap Sum.getLeft?, (List.filterMap_append).symm⟩
        by_cases hu : (l₁ ++ u).filterMap Sum.getLeft? = []
        · rw [hu] at hpre'
          exact absurd (List.prefix_nil.mp hpre') hne'
        · exact prefix_closed s hpre' hne' (hL₂ hu)
      have hR₁ : l₁.filterMap Sum.getRight? ≠ [] →
          (t.1 (l₁.filterMap Sum.getRight?)).Dom := by
        intro hne'
        have hpre' : l₁.filterMap Sum.getRight? <+:
            (l₁ ++ u).filterMap Sum.getRight? :=
          ⟨u.filterMap Sum.getRight?, (List.filterMap_append).symm⟩
        by_cases hu : (l₁ ++ u).filterMap Sum.getRight? = []
        · rw [hu] at hpre'
          exact absurd (List.prefix_nil.mp hpre') hne'
        · exact prefix_closed t hpre' hne' (hR₂ hu)
      refine ⟨hL₁, hR₁, ?_⟩
      cases hl : l₁.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
      | some e =>
        have hlast : l₁.getLast hne = e := by
          rw [List.getLast?_eq_some_getLast hne] at hl
          exact Option.some.inj hl
        cases e with
        | inl x =>
          have hxmem : Sum.inl x ∈ l₁ := hlast ▸ List.getLast_mem hne
          have hnel : l₁.filterMap Sum.getLeft? ≠ [] :=
            List.ne_nil_of_mem
              (List.mem_filterMap.mpr ⟨Sum.inl x, hxmem, rfl⟩)
          exact hL₁ hnel
        | inr x =>
          have hxmem : Sum.inr x ∈ l₁ := hlast ▸ List.getLast_mem hne
          have hner : l₁.filterMap Sum.getRight? ≠ [] :=
            List.ne_nil_of_mem
              (List.mem_filterMap.mpr ⟨Sum.inr x, hxmem, rfl⟩)
          exact hR₁ hner⟩

/-! ### Resource-emulation core (MauRen11 Def 16, second closure clause)

"Closed under emulation of a **resource**": for a fixed deterministic atom
of one component, the environment can simulate that side internally.  The
kept-scan lemmas below are the semantic core: CR18 Def 3.3's deletion scan
of a parallel composition projects to the components' scans, so the
`⊥`-completion of `s ∥ t` factors side by side. -/

private theorem mem_par_iff (s : DDS X Y) (t : DDS X' Y')
    (l : List (X ⊕ X')) (o : Y ⊕ Y') :
    o ∈ (par s t).1 l ↔
      ((l.filterMap Sum.getLeft? ≠ []) →
        (s.1 (l.filterMap Sum.getLeft?)).Dom) ∧
      ((l.filterMap Sum.getRight? ≠ []) →
        (t.1 (l.filterMap Sum.getRight?)).Dom) ∧
      o ∈ (match l.getLast? with
        | some (Sum.inl _) => (s.1 (l.filterMap Sum.getLeft?)).map Sum.inl
        | some (Sum.inr _) => (t.1 (l.filterMap Sum.getRight?)).map Sum.inr
        | none => Part.none) := by
  show o ∈ Part.assert _ _ ↔ _
  rw [Part.mem_assert_iff]
  constructor
  · rintro ⟨hA, h⟩
    rw [Part.mem_assert_iff] at h
    obtain ⟨hB, h⟩ := h
    exact ⟨hA, hB, h⟩
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, Part.mem_assert_iff.mpr ⟨hB, h⟩⟩

private theorem par_dom_concat_inl {s : DDS X Y} {t : DDS X' Y'}
    {l : List (X ⊕ X')} (hl : l ∈ dom (par s t) ∨ l = []) (x : X) :
    l ++ [Sum.inl x] ∈ dom (par s t)
      ↔ l.filterMap Sum.getLeft? ++ [x] ∈ dom s := by
  have hfl : (l ++ [Sum.inl x]).filterMap Sum.getLeft?
      = l.filterMap Sum.getLeft? ++ [x] := by simp
  constructor
  · intro hdom
    obtain ⟨o, ho⟩ := Part.dom_iff_mem.mp hdom
    rw [mem_par_iff] at ho
    have := ho.1 (by rw [hfl]; simp)
    rw [hfl] at this
    exact this
  · intro hs'
    refine Part.dom_iff_mem.mpr
      ⟨Sum.inl ((s.1 (l.filterMap Sum.getLeft? ++ [x])).get hs'), ?_⟩
    rw [mem_par_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro _
      rw [hfl]
      exact hs'
    · have hfr : (l ++ [Sum.inl x]).filterMap Sum.getRight?
          = l.filterMap Sum.getRight? := by simp
      rcases hl with hmem | rfl
      · obtain ⟨o₀, ho₀⟩ := Part.dom_iff_mem.mp hmem
        rw [mem_par_iff] at ho₀
        rw [hfr]
        exact ho₀.2.1
      · intro hcon
        simp at hcon
    · rw [List.getLast?_concat]
      dsimp only
      rw [Part.mem_map_iff]
      refine ⟨(s.1 (l.filterMap Sum.getLeft? ++ [x])).get hs', ?_, rfl⟩
      rw [hfl]
      exact Part.get_mem hs'

private theorem par_dom_concat_inr {s : DDS X Y} {t : DDS X' Y'}
    {l : List (X ⊕ X')} (hl : l ∈ dom (par s t) ∨ l = []) (x' : X') :
    l ++ [Sum.inr x'] ∈ dom (par s t)
      ↔ l.filterMap Sum.getRight? ++ [x'] ∈ dom t := by
  have hfr : (l ++ [Sum.inr x']).filterMap Sum.getRight?
      = l.filterMap Sum.getRight? ++ [x'] := by simp
  constructor
  · intro hdom
    obtain ⟨o, ho⟩ := Part.dom_iff_mem.mp hdom
    rw [mem_par_iff] at ho
    have := ho.2.1 (by rw [hfr]; simp)
    rw [hfr] at this
    exact this
  · intro ht'
    refine Part.dom_iff_mem.mpr
      ⟨Sum.inr ((t.1 (l.filterMap Sum.getRight? ++ [x'])).get ht'), ?_⟩
    rw [mem_par_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hfl : (l ++ [Sum.inr x']).filterMap Sum.getLeft?
          = l.filterMap Sum.getLeft? := by simp
      rcases hl with hmem | rfl
      · obtain ⟨o₀, ho₀⟩ := Part.dom_iff_mem.mp hmem
        rw [mem_par_iff] at ho₀
        rw [hfl]
        exact ho₀.1
      · intro hcon
        simp at hcon
    · intro _
      rw [hfr]
      exact ht'
    · rw [List.getLast?_concat]
      dsimp only
      rw [Part.mem_map_iff]
      refine ⟨(t.1 (l.filterMap Sum.getRight? ++ [x'])).get ht', ?_, rfl⟩
      rw [hfr]
      exact Part.get_mem ht'

/-- **The kept scans project** (the resource-emulation core): the Def 3.3
deletion scan of `s ∥ t` is, on each side, the component's own scan — a
dead query on one side is invisible to the other. -/
private theorem keptPrefix_par_proj (s : DDS X Y) (t : DDS X' Y')
    (l : List (X ⊕ X')) :
    (keptPrefix (par s t) l).filterMap Sum.getLeft?
        = keptPrefix s (l.filterMap Sum.getLeft?) ∧
      (keptPrefix (par s t) l).filterMap Sum.getRight?
        = keptPrefix t (l.filterMap Sum.getRight?) ∧
      (keptPrefix (par s t) l ∈ dom (par s t) ∨
        keptPrefix (par s t) l = []) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, Or.inr rfl⟩
  | append_singleton l q ih =>
      obtain ⟨ihL, ihR, ihD⟩ := ih
      cases q with
      | inl x =>
          have hfl : (l ++ [Sum.inl x]).filterMap Sum.getLeft?
              = l.filterMap Sum.getLeft? ++ [x] := by simp
          have hfr : (l ++ [Sum.inl x]).filterMap Sum.getRight?
              = l.filterMap Sum.getRight? := by simp
          rw [PFunConverter.keptPrefix_concat]
          by_cases hd : keptPrefix (par s t) l ++ [Sum.inl x]
              ∈ dom (par s t)
          · have hds : keptPrefix s (l.filterMap Sum.getLeft?) ++ [x]
                ∈ dom s := by
              rw [← ihL]
              exact (par_dom_concat_inl ihD x).mp hd
            rw [if_pos hd]
            refine ⟨?_, ?_, Or.inl hd⟩
            · rw [hfl, PFunConverter.keptPrefix_concat, if_pos hds]
              simp [ihL]
            · rw [hfr]
              simpa using ihR
          · have hds : keptPrefix s (l.filterMap Sum.getLeft?) ++ [x]
                ∉ dom s := by
              rw [← ihL]
              exact fun hc => hd ((par_dom_concat_inl ihD x).mpr hc)
            rw [if_neg hd]
            refine ⟨?_, ?_, ihD⟩
            · rw [hfl, PFunConverter.keptPrefix_concat, if_neg hds]
              exact ihL
            · rw [hfr]
              exact ihR
      | inr x' =>
          have hfl : (l ++ [Sum.inr x']).filterMap Sum.getLeft?
              = l.filterMap Sum.getLeft? := by simp
          have hfr : (l ++ [Sum.inr x']).filterMap Sum.getRight?
              = l.filterMap Sum.getRight? ++ [x'] := by simp
          rw [PFunConverter.keptPrefix_concat]
          by_cases hd : keptPrefix (par s t) l ++ [Sum.inr x']
              ∈ dom (par s t)
          · have hdt : keptPrefix t (l.filterMap Sum.getRight?) ++ [x']
                ∈ dom t := by
              rw [← ihR]
              exact (par_dom_concat_inr ihD x').mp hd
            rw [if_pos hd]
            refine ⟨?_, ?_, Or.inl hd⟩
            · rw [hfl]
              simpa using ihL
            · rw [hfr, PFunConverter.keptPrefix_concat, if_pos hdt]
              simp [ihR]
          · have hdt : keptPrefix t (l.filterMap Sum.getRight?) ++ [x']
                ∉ dom t := by
              rw [← ihR]
              exact fun hc => hd ((par_dom_concat_inr ihD x').mpr hc)
            rw [if_neg hd]
            refine ⟨?_, ?_, ihD⟩
            · rw [hfl]
              exact ihL
            · rw [hfr, PFunConverter.keptPrefix_concat, if_neg hdt]
              exact ihR

private theorem par_output_concat_inl {s : DDS X Y} {t : DDS X' Y'}
    {l : List (X ⊕ X')} (x : X)
    (hd : l ++ [Sum.inl x] ∈ dom (par s t))
    (hs' : l.filterMap Sum.getLeft? ++ [x] ∈ dom s) :
    output (par s t) (l ++ [Sum.inl x]) hd
      = Sum.inl (output s (l.filterMap Sum.getLeft? ++ [x]) hs') := by
  have hfl : (l ++ [Sum.inl x]).filterMap Sum.getLeft?
      = l.filterMap Sum.getLeft? ++ [x] := by simp
  have hmem : Sum.inl (output s (l.filterMap Sum.getLeft? ++ [x]) hs')
      ∈ (par s t).1 (l ++ [Sum.inl x]) := by
    rw [mem_par_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro _
      rw [hfl]
      exact hs'
    · obtain ⟨o₀, ho₀⟩ := Part.dom_iff_mem.mp hd
      rw [mem_par_iff] at ho₀
      exact ho₀.2.1
    · rw [List.getLast?_concat]
      dsimp only
      rw [Part.mem_map_iff]
      refine ⟨output s (l.filterMap Sum.getLeft? ++ [x]) hs', ?_, rfl⟩
      rw [hfl]
      exact Part.get_mem hs'
  exact Part.get_eq_of_mem hmem hd

private theorem par_output_concat_inr {s : DDS X Y} {t : DDS X' Y'}
    {l : List (X ⊕ X')} (x' : X')
    (hd : l ++ [Sum.inr x'] ∈ dom (par s t))
    (ht' : l.filterMap Sum.getRight? ++ [x'] ∈ dom t) :
    output (par s t) (l ++ [Sum.inr x']) hd
      = Sum.inr (output t (l.filterMap Sum.getRight? ++ [x']) ht') := by
  have hfr : (l ++ [Sum.inr x']).filterMap Sum.getRight?
      = l.filterMap Sum.getRight? ++ [x'] := by simp
  have hmem : Sum.inr (output t (l.filterMap Sum.getRight? ++ [x']) ht')
      ∈ (par s t).1 (l ++ [Sum.inr x']) := by
    rw [mem_par_iff]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨o₀, ho₀⟩ := Part.dom_iff_mem.mp hd
      rw [mem_par_iff] at ho₀
      exact ho₀.1
    · intro _
      rw [hfr]
      exact ht'
    · rw [List.getLast?_concat]
      dsimp only
      rw [Part.mem_map_iff]
      refine ⟨output t (l.filterMap Sum.getRight? ++ [x']) ht', ?_, rfl⟩
      rw [hfr]
      exact Part.get_mem ht'
  exact Part.get_eq_of_mem hmem hd

/-- **The `⊥`-completion of `s ∥ t` factors, left side**: an `inl`-query's
completed answer is the `inl`-relabeling of `s⊥`'s answer on the projected
history — dead queries on either side included. -/
theorem output_fully_defined_par_inl (s : DDS X Y) (t : DDS X' Y')
    {l : List (X ⊕ X')} (x : X)
    (h : l ++ [Sum.inl x] ∈ dom ((par s t)⊥))
    (h' : l.filterMap Sum.getLeft? ++ [x] ∈ dom (s⊥)) :
    output ((par s t)⊥) (l ++ [Sum.inl x]) h
      = Option.map Sum.inl
          (output (s⊥) (l.filterMap Sum.getLeft? ++ [x]) h') := by
  obtain ⟨ihL, ihR, ihD⟩ := keptPrefix_par_proj s t l
  rw [PFunConverter.output_fullyDefined_concat,
    PFunConverter.output_fullyDefined_concat]
  by_cases hds : keptPrefix s (l.filterMap Sum.getLeft?) ++ [x] ∈ dom s
  · have hd' : keptPrefix (par s t) l ++ [Sum.inl x] ∈ dom (par s t) := by
      rw [par_dom_concat_inl ihD, ihL]
      exact hds
    rw [dif_pos hd', dif_pos hds]
    have hval := par_output_concat_inl (l := keptPrefix (par s t) l) x hd'
      (by rw [ihL]; exact hds)
    rw [hval]
    simp only [Option.map_some]
    refine congrArg (some ∘ Sum.inl) ?_
    exact output_congr s (by rw [ihL]) _ hds
  · rw [dif_neg hds, dif_neg (by rw [par_dom_concat_inl ihD, ihL]; exact hds)]
    rfl

/-- **The `⊥`-completion of `s ∥ t` factors, right side**. -/
theorem output_fully_defined_par_inr (s : DDS X Y) (t : DDS X' Y')
    {l : List (X ⊕ X')} (x' : X')
    (h : l ++ [Sum.inr x'] ∈ dom ((par s t)⊥))
    (h' : l.filterMap Sum.getRight? ++ [x'] ∈ dom (t⊥)) :
    output ((par s t)⊥) (l ++ [Sum.inr x']) h
      = Option.map Sum.inr
          (output (t⊥) (l.filterMap Sum.getRight? ++ [x']) h') := by
  obtain ⟨ihL, ihR, ihD⟩ := keptPrefix_par_proj s t l
  rw [PFunConverter.output_fullyDefined_concat,
    PFunConverter.output_fullyDefined_concat]
  by_cases hdt : keptPrefix t (l.filterMap Sum.getRight?) ++ [x'] ∈ dom t
  · have hd' : keptPrefix (par s t) l ++ [Sum.inr x'] ∈ dom (par s t) := by
      rw [par_dom_concat_inr ihD, ihR]
      exact hdt
    rw [dif_pos hd', dif_pos hdt]
    have hval := par_output_concat_inr (l := keptPrefix (par s t) l) x' hd'
      (by rw [ihR]; exact hdt)
    rw [hval]
    simp only [Option.map_some]
    refine congrArg (some ∘ Sum.inr) ?_
    exact output_congr t (by rw [ihR]) _ hdt
  · rw [dif_neg hdt, dif_neg (by rw [par_dom_concat_inr ihD, ihR]; exact hdt)]
    rfl

/-! ### The fixed-atom emulated environment (MauRen11 Defs 15/16, resource
side): for a fixed deterministic atom `t` of the right component, an
environment `e` against `s ∥ t` induces an environment against `s` alone —
`t`'s side is simulated inside the environment, deterministically. -/

/-- Plumbing for `emulateRes`: replay `e` step by step — `vs` the joint
answers so far, `rq` the right-side queries so far (their answers are
recomputed from `t⊥`), `ysr` the remaining recorded left answers.  Returns
`e`'s next left query with the record exhausted; stops on `e`-stall or
budget. -/
private noncomputable def emuGoR (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) :
    ℕ → List (Option (Y ⊕ Y')) → List X' → List (Option Y) → Option X
  | 0, _, _, _ => none
  | k + 1, vs, rq, ysr =>
      match e vs with
      | none => none
      | some (Sum.inl x) =>
          match ysr with
          | [] => some x
          | y :: ysr' => emuGoR t e k (vs ++ [Option.map Sum.inl y]) rq ysr'
      | some (Sum.inr x') =>
          emuGoR t e k
            (vs ++ [Option.map Sum.inr (output (t⊥) (rq ++ [x'])
              (by rw [dom_fullyDefined]; simp))])
            (rq ++ [x']) ysr

/-- **The fixed-atom emulated environment** (Def 16, "closed under
emulation of a resource", at a deterministic atom of the right
component). -/
private noncomputable def emulateRes (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) : DDE X Y := fun ys =>
  emuGoR t e n [] [] ys

/-- Plumbing for `replayRes`: rebuild the joint transcript from the
recorded left transcript, recomputing the `t`-side. -/
private noncomputable def replayGoR (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) :
    ℕ → List ((X ⊕ X') × Option (Y ⊕ Y')) → List X' →
      List (X × Option Y) → List ((X ⊕ X') × Option (Y ⊕ Y'))
  | 0, acc, _, _ => acc
  | k + 1, acc, rq, rem =>
      match e (transcriptOutputs acc) with
      | none => acc
      | some (Sum.inl x) =>
          match rem with
          | [] => acc
          | p :: rem' =>
              replayGoR t e k
                (acc ++ [(Sum.inl x, Option.map Sum.inl p.2)]) rq rem'
      | some (Sum.inr x') =>
          replayGoR t e k
            (acc ++ [(Sum.inr x', Option.map Sum.inr (output (t⊥)
              (rq ++ [x']) (by rw [dom_fullyDefined]; simp)))])
            (rq ++ [x']) rem

/-- **The transcript reconstruction** for the fixed-atom emulation. -/
private noncomputable def replayRes (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ)
    (trc : List (X × Option Y)) : List ((X ⊕ X') × Option (Y ⊕ Y')) :=
  replayGoR t e n [] [] trc

section ResRun

variable (s : DDS X Y) (t : DDS X' Y') (e : DDE (X ⊕ X') (Y ⊕ Y'))

/-- The joint state of the fixed-atom emulation: joint transcript and
left-component transcript. -/
private inductive EmuRunR :
    List ((X ⊕ X') × Option (Y ⊕ Y')) → List (X × Option Y) → Prop
  | start : EmuRunR [] []
  | stepL {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X × Option Y)} {x : X} (hr : EmuRunR tout tin)
      (hq : e (transcriptOutputs tout) = some (Sum.inl x)) :
      EmuRunR
        (tout ++ [(Sum.inl x, Option.map Sum.inl
          (output (s⊥) (transcriptInputs tin ++ [x])
            (by rw [dom_fullyDefined]; simp)))])
        (tin ++ [(x, output (s⊥) (transcriptInputs tin ++ [x])
          (by rw [dom_fullyDefined]; simp))])
  | stepR {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X × Option Y)} {x' : X'} (hr : EmuRunR tout tin)
      (hq : e (transcriptOutputs tout) = some (Sum.inr x')) :
      EmuRunR
        (tout ++ [(Sum.inr x', Option.map Sum.inr
          (output (t⊥) ((transcriptInputs tout).filterMap Sum.getRight?
              ++ [x'])
            (by rw [dom_fullyDefined]; simp)))])
        tin

variable {s t e}

/-- The bundled invariant: query projection, the joint transcript, and the
length bound. -/
private theorem emuRunR_invariant
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) :
    transcriptInputs tin
        = (transcriptInputs tout).filterMap Sum.getLeft? ∧
      transcript (par s t) e tout.length = tout ∧
      tin.length ≤ tout.length := by
  induction hr with
  | start => exact ⟨rfl, rfl, le_rfl⟩
  | stepL hr hq ih =>
      rename_i tout tin x
      obtain ⟨hproj, hT, hlen⟩ := ih
      have hfire : e ((transcript (par s t) e tout.length)↓ᵧ)
          = some (Sum.inl x) := by
        rw [hT]
        exact hq
      have hout : output ((par s t)⊥)
          (transcriptInputs tout ++ [Sum.inl x])
          (by rw [dom_fullyDefined]; simp)
          = Option.map Sum.inl (output (s⊥)
            (transcriptInputs tin ++ [x])
            (by rw [dom_fullyDefined]; simp)) := by
        rw [output_fully_defined_par_inl s t x _
          (by rw [dom_fullyDefined]; simp)]
        exact congrArg (Option.map Sum.inl)
          (output_congr (s⊥) (by rw [hproj]) _ _)
      refine ⟨?_, ?_, ?_⟩
      · rw [transcriptInputs_append, transcriptInputs_append, hproj]
        simp
      · rw [List.length_append, List.length_singleton,
          transcript_succ_fire hfire, hT, hout]
      · rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton]
        omega
  | stepR hr hq ih =>
      rename_i tout tin x'
      obtain ⟨hproj, hT, hlen⟩ := ih
      have hfire : e ((transcript (par s t) e tout.length)↓ᵧ)
          = some (Sum.inr x') := by
        rw [hT]
        exact hq
      have hout : output ((par s t)⊥)
          (transcriptInputs tout ++ [Sum.inr x'])
          (by rw [dom_fullyDefined]; simp)
          = Option.map Sum.inr (output (t⊥)
            ((transcriptInputs tout).filterMap Sum.getRight? ++ [x'])
            (by rw [dom_fullyDefined]; simp)) :=
        output_fully_defined_par_inr s t x' _
          (by rw [dom_fullyDefined]; simp)
      refine ⟨?_, ?_, ?_⟩
      · rw [transcriptInputs_append, hproj]
        simp
      · rw [List.length_append, List.length_singleton,
          transcript_succ_fire hfire, hT, hout]
      · rw [List.length_append, List.length_singleton]
        omega

end ResRun

section ResRun2

variable {s : DDS X Y} {t : DDS X' Y'} {e : DDE (X ⊕ X') (Y ⊕ Y')}

private theorem emuGoR_replay
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) :
    ∀ {m : ℕ}, tout.length ≤ m → ∀ ext : List (Option Y),
      emuGoR t e m [] [] (transcriptOutputs tin ++ ext)
        = emuGoR t e (m - tout.length) (transcriptOutputs tout)
            ((transcriptInputs tout).filterMap Sum.getRight?) ext := by
  induction hr with
  | start =>
      intro m hm ext
      simp
  | stepL hr hq ih =>
      rename_i tout tin x
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton,
        transcriptOutputs_append, List.append_assoc,
        List.singleton_append, ih (by omega), hk]
      simp only [emuGoR]
      rw [hq, transcriptOutputs_append, transcriptInputs_append]
      simp
  | stepR hr hq ih =>
      rename_i tout tin x'
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, ih (by omega), hk]
      simp only [emuGoR]
      rw [hq, transcriptOutputs_append, transcriptInputs_append]
      simp

private theorem replayGoR_replay
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) :
    ∀ {m : ℕ}, tout.length ≤ m → ∀ ext : List (X × Option Y),
      replayGoR t e m [] [] (tin ++ ext)
        = replayGoR t e (m - tout.length) tout
            ((transcriptInputs tout).filterMap Sum.getRight?) ext := by
  induction hr with
  | start =>
      intro m hm ext
      simp
  | stepL hr hq ih =>
      rename_i tout tin x
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, ih (by omega), hk]
      simp only [replayGoR]
      rw [hq, transcriptInputs_append]
      simp
  | stepR hr hq ih =>
      rename_i tout tin x'
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, ih (by omega), hk]
      simp only [replayGoR]
      rw [hq, transcriptInputs_append]
      simp

private theorem emuRunR_transcript {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) : tout.length ≤ n →
    transcript s (emulateRes t e n) tin.length = tin := by
  induction hr with
  | start => intro _; rfl
  | stepL hr hq ih =>
      rename_i tout tin x
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      have hfire : emulateRes t e n
          ((transcript s (emulateRes t e n) tin.length)↓ᵧ) = some x := by
        rw [ih (by omega)]
        show emuGoR t e n [] [] (transcriptOutputs tin) = some x
        have h := emuGoR_replay hr (m := n) (by omega) []
        rw [List.append_nil] at h
        rw [h]
        obtain ⟨k, hk⟩ : ∃ k, n - tout.length = k + 1 :=
          ⟨n - tout.length - 1, by omega⟩
        rw [hk]
        simp only [emuGoR]
        rw [hq]
      rw [List.length_append, List.length_singleton,
        transcript_succ_fire hfire, ih (by omega)]
  | stepR hr hq ih =>
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      exact ih (by omega)

private theorem emulateRes_terminal_stall {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) (hle : tout.length ≤ n)
    (hterm : tout.length = n ∨ e (transcriptOutputs tout) = none) :
    emulateRes t e n (transcriptOutputs tin) = none := by
  show emuGoR t e n [] [] (transcriptOutputs tin) = none
  have h := emuGoR_replay hr (m := n) hle []
  rw [List.append_nil] at h
  rw [h]
  rcases hterm with hterm | hterm
  · rw [show n - tout.length = 0 from by omega]
    rfl
  · rcases hk : n - tout.length with _ | k'
    · rfl
    · simp only [emuGoR]
      rw [hterm]

private theorem replayGoR_terminal {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X × Option Y)}
    (hr : EmuRunR s t e tout tin) (hle : tout.length ≤ n)
    (hterm : tout.length = n ∨ e (transcriptOutputs tout) = none) :
    replayGoR t e n [] [] tin = tout := by
  have h := replayGoR_replay hr (m := n) hle []
  rw [List.append_nil] at h
  rw [h]
  rcases hterm with hterm | hterm
  · rw [show n - tout.length = 0 from by omega]
    rfl
  · rcases hk : n - tout.length with _ | k'
    · rfl
    · simp only [replayGoR]
      rw [hterm]

private theorem emuRunR_terminal {n : ℕ} :
    ∀ (k : ℕ) {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X × Option Y)},
      EmuRunR s t e tout tin → tout.length + k = n →
      ∃ tout' tin', EmuRunR s t e tout' tin' ∧ tout'.length ≤ n ∧
        (tout'.length = n ∨ e (transcriptOutputs tout') = none) := by
  intro k
  induction k with
  | zero =>
      intro tout tin hr hn
      exact ⟨tout, tin, hr, by omega, Or.inl (by omega)⟩
  | succ k ih =>
      intro tout tin hr hn
      rcases hq : e (transcriptOutputs tout) with _ | q
      · exact ⟨tout, tin, hr, by omega, Or.inr hq⟩
      · cases q with
        | inl x =>
            exact ih (EmuRunR.stepL hr hq)
              (by rw [List.length_append, List.length_singleton]; omega)
        | inr x' =>
            exact ih (EmuRunR.stepR hr hq)
              (by rw [List.length_append, List.length_singleton]; omega)

/-- **The fixed-atom bridge, right atom** (MauRen11 Def 16, resource
side): pointwise in the left system, the transcript of `s ∥ t` is the
reconstruction of `s`'s transcript against the emulated environment. -/
private theorem transcript_par_fixed_right (s : DDS X Y) (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) :
    transcript (par s t) e n
      = replayRes t e n (transcript s (emulateRes t e n) n) := by
  obtain ⟨tout, tin, hr, hle, hterm⟩ :=
    emuRunR_terminal (n := n) n
      (EmuRunR.start (s := s) (t := t) (e := e)) (by simp)
  obtain ⟨hproj, hT, hlen⟩ := emuRunR_invariant hr
  have hLHS : transcript (par s t) e n = tout := by
    rcases hterm with hterm | hterm
    · rw [← hterm]
      exact hT
    · have hfreeze : e ((transcript (par s t) e tout.length)↓ᵧ)
          = none := by
        rw [hT]
        exact hterm
      rw [transcript_freeze hfreeze hle]
      exact hT
  have hTin : transcript s (emulateRes t e n) n = tin := by
    have h1 := emuRunR_transcript hr hle
    have h2 : emulateRes t e n
        ((transcript s (emulateRes t e n) tin.length)↓ᵧ) = none := by
      rw [h1]
      exact emulateRes_terminal_stall hr hle hterm
    rw [transcript_freeze h2 (by omega), h1]
  rw [hLHS, hTin]
  exact (replayGoR_terminal hr hle hterm).symm

end ResRun2

/-! ### The mirror: fixed left atom, emulated right component. -/

private noncomputable def emuGoL (s : DDS X Y)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) :
    ℕ → List (Option (Y ⊕ Y')) → List X → List (Option Y') → Option X'
  | 0, _, _, _ => none
  | k + 1, vs, lq, ysr =>
      match e vs with
      | none => none
      | some (Sum.inr x') =>
          match ysr with
          | [] => some x'
          | y :: ysr' => emuGoL s e k (vs ++ [Option.map Sum.inr y]) lq ysr'
      | some (Sum.inl x) =>
          emuGoL s e k
            (vs ++ [Option.map Sum.inl (output (s⊥) (lq ++ [x])
              (by rw [dom_fullyDefined]; simp))])
            (lq ++ [x]) ysr

private noncomputable def emulateResL (s : DDS X Y)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) : DDE X' Y' := fun ys =>
  emuGoL s e n [] [] ys

private noncomputable def replayGoL (s : DDS X Y)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) :
    ℕ → List ((X ⊕ X') × Option (Y ⊕ Y')) → List X →
      List (X' × Option Y') → List ((X ⊕ X') × Option (Y ⊕ Y'))
  | 0, acc, _, _ => acc
  | k + 1, acc, lq, rem =>
      match e (transcriptOutputs acc) with
      | none => acc
      | some (Sum.inr x') =>
          match rem with
          | [] => acc
          | p :: rem' =>
              replayGoL s e k
                (acc ++ [(Sum.inr x', Option.map Sum.inr p.2)]) lq rem'
      | some (Sum.inl x) =>
          replayGoL s e k
            (acc ++ [(Sum.inl x, Option.map Sum.inl (output (s⊥)
              (lq ++ [x]) (by rw [dom_fullyDefined]; simp)))])
            (lq ++ [x]) rem

private noncomputable def replayResL (s : DDS X Y)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ)
    (trc : List (X' × Option Y')) : List ((X ⊕ X') × Option (Y ⊕ Y')) :=
  replayGoL s e n [] [] trc

section ResRunL

variable (s : DDS X Y) (t : DDS X' Y') (e : DDE (X ⊕ X') (Y ⊕ Y'))

private inductive EmuRunL :
    List ((X ⊕ X') × Option (Y ⊕ Y')) → List (X' × Option Y') → Prop
  | start : EmuRunL [] []
  | stepR {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X' × Option Y')} {x' : X'} (hr : EmuRunL tout tin)
      (hq : e (transcriptOutputs tout) = some (Sum.inr x')) :
      EmuRunL
        (tout ++ [(Sum.inr x', Option.map Sum.inr
          (output (t⊥) (transcriptInputs tin ++ [x'])
            (by rw [dom_fullyDefined]; simp)))])
        (tin ++ [(x', output (t⊥) (transcriptInputs tin ++ [x'])
          (by rw [dom_fullyDefined]; simp))])
  | stepL {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X' × Option Y')} {x : X} (hr : EmuRunL tout tin)
      (hq : e (transcriptOutputs tout) = some (Sum.inl x)) :
      EmuRunL
        (tout ++ [(Sum.inl x, Option.map Sum.inl
          (output (s⊥) ((transcriptInputs tout).filterMap Sum.getLeft?
              ++ [x])
            (by rw [dom_fullyDefined]; simp)))])
        tin

variable {s t e}

private theorem emuRunL_invariant
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) :
    transcriptInputs tin
        = (transcriptInputs tout).filterMap Sum.getRight? ∧
      transcript (par s t) e tout.length = tout ∧
      tin.length ≤ tout.length := by
  induction hr with
  | start => exact ⟨rfl, rfl, le_rfl⟩
  | stepR hr hq ih =>
      rename_i tout tin x'
      obtain ⟨hproj, hT, hlen⟩ := ih
      have hfire : e ((transcript (par s t) e tout.length)↓ᵧ)
          = some (Sum.inr x') := by
        rw [hT]
        exact hq
      have hout : output ((par s t)⊥)
          (transcriptInputs tout ++ [Sum.inr x'])
          (by rw [dom_fullyDefined]; simp)
          = Option.map Sum.inr (output (t⊥)
            (transcriptInputs tin ++ [x'])
            (by rw [dom_fullyDefined]; simp)) := by
        rw [output_fully_defined_par_inr s t x' _
          (by rw [dom_fullyDefined]; simp)]
        exact congrArg (Option.map Sum.inr)
          (output_congr (t⊥) (by rw [hproj]) _ _)
      refine ⟨?_, ?_, ?_⟩
      · rw [transcriptInputs_append, transcriptInputs_append, hproj]
        simp
      · rw [List.length_append, List.length_singleton,
          transcript_succ_fire hfire, hT, hout]
      · rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton]
        omega
  | stepL hr hq ih =>
      rename_i tout tin x
      obtain ⟨hproj, hT, hlen⟩ := ih
      have hfire : e ((transcript (par s t) e tout.length)↓ᵧ)
          = some (Sum.inl x) := by
        rw [hT]
        exact hq
      have hout : output ((par s t)⊥)
          (transcriptInputs tout ++ [Sum.inl x])
          (by rw [dom_fullyDefined]; simp)
          = Option.map Sum.inl (output (s⊥)
            ((transcriptInputs tout).filterMap Sum.getLeft? ++ [x])
            (by rw [dom_fullyDefined]; simp)) :=
        output_fully_defined_par_inl s t x _
          (by rw [dom_fullyDefined]; simp)
      refine ⟨?_, ?_, ?_⟩
      · rw [transcriptInputs_append, hproj]
        simp
      · rw [List.length_append, List.length_singleton,
          transcript_succ_fire hfire, hT, hout]
      · rw [List.length_append, List.length_singleton]
        omega

private theorem emuGoL_replay
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) :
    ∀ {m : ℕ}, tout.length ≤ m → ∀ ext : List (Option Y'),
      emuGoL s e m [] [] (transcriptOutputs tin ++ ext)
        = emuGoL s e (m - tout.length) (transcriptOutputs tout)
            ((transcriptInputs tout).filterMap Sum.getLeft?) ext := by
  induction hr with
  | start =>
      intro m hm ext
      simp
  | stepR hr hq ih =>
      rename_i tout tin x'
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton,
        transcriptOutputs_append, List.append_assoc,
        List.singleton_append, ih (by omega), hk]
      simp only [emuGoL]
      rw [hq, transcriptOutputs_append, transcriptInputs_append]
      simp
  | stepL hr hq ih =>
      rename_i tout tin x
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, ih (by omega), hk]
      simp only [emuGoL]
      rw [hq, transcriptOutputs_append, transcriptInputs_append]
      simp

private theorem replayGoL_replay
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) :
    ∀ {m : ℕ}, tout.length ≤ m → ∀ ext : List (X' × Option Y'),
      replayGoL s e m [] [] (tin ++ ext)
        = replayGoL s e (m - tout.length) tout
            ((transcriptInputs tout).filterMap Sum.getLeft?) ext := by
  induction hr with
  | start =>
      intro m hm ext
      simp
  | stepR hr hq ih =>
      rename_i tout tin x'
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, ih (by omega), hk]
      simp only [replayGoL]
      rw [hq, transcriptInputs_append]
      simp
  | stepL hr hq ih =>
      rename_i tout tin x
      intro m hm ext
      rw [List.length_append, List.length_singleton] at hm
      have hk : m - tout.length = (m - (tout.length + 1)) + 1 := by omega
      rw [List.length_append, List.length_singleton, ih (by omega), hk]
      simp only [replayGoL]
      rw [hq, transcriptInputs_append]
      simp

private theorem emuRunL_transcript {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) : tout.length ≤ n →
    transcript t (emulateResL s e n) tin.length = tin := by
  induction hr with
  | start => intro _; rfl
  | stepR hr hq ih =>
      rename_i tout tin x'
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      have hfire : emulateResL s e n
          ((transcript t (emulateResL s e n) tin.length)↓ᵧ)
          = some x' := by
        rw [ih (by omega)]
        show emuGoL s e n [] [] (transcriptOutputs tin) = some x'
        have h := emuGoL_replay hr (m := n) (by omega) []
        rw [List.append_nil] at h
        rw [h]
        obtain ⟨k, hk⟩ : ∃ k, n - tout.length = k + 1 :=
          ⟨n - tout.length - 1, by omega⟩
        rw [hk]
        simp only [emuGoL]
        rw [hq]
      rw [List.length_append, List.length_singleton,
        transcript_succ_fire hfire, ih (by omega)]
  | stepL hr hq ih =>
      intro hn
      rw [List.length_append, List.length_singleton] at hn
      exact ih (by omega)

private theorem emulateResL_terminal_stall {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) (hle : tout.length ≤ n)
    (hterm : tout.length = n ∨ e (transcriptOutputs tout) = none) :
    emulateResL s e n (transcriptOutputs tin) = none := by
  show emuGoL s e n [] [] (transcriptOutputs tin) = none
  have h := emuGoL_replay hr (m := n) hle []
  rw [List.append_nil] at h
  rw [h]
  rcases hterm with hterm | hterm
  · rw [show n - tout.length = 0 from by omega]
    rfl
  · rcases hk : n - tout.length with _ | k'
    · rfl
    · simp only [emuGoL]
      rw [hterm]

private theorem replayGoL_terminal {n : ℕ}
    {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))} {tin : List (X' × Option Y')}
    (hr : EmuRunL s t e tout tin) (hle : tout.length ≤ n)
    (hterm : tout.length = n ∨ e (transcriptOutputs tout) = none) :
    replayGoL s e n [] [] tin = tout := by
  have h := replayGoL_replay hr (m := n) hle []
  rw [List.append_nil] at h
  rw [h]
  rcases hterm with hterm | hterm
  · rw [show n - tout.length = 0 from by omega]
    rfl
  · rcases hk : n - tout.length with _ | k'
    · rfl
    · simp only [replayGoL]
      rw [hterm]

private theorem emuRunL_terminal {n : ℕ} :
    ∀ (k : ℕ) {tout : List ((X ⊕ X') × Option (Y ⊕ Y'))}
      {tin : List (X' × Option Y')},
      EmuRunL s t e tout tin → tout.length + k = n →
      ∃ tout' tin', EmuRunL s t e tout' tin' ∧ tout'.length ≤ n ∧
        (tout'.length = n ∨ e (transcriptOutputs tout') = none) := by
  intro k
  induction k with
  | zero =>
      intro tout tin hr hn
      exact ⟨tout, tin, hr, by omega, Or.inl (by omega)⟩
  | succ k ih =>
      intro tout tin hr hn
      rcases hq : e (transcriptOutputs tout) with _ | q
      · exact ⟨tout, tin, hr, by omega, Or.inr hq⟩
      · cases q with
        | inr x' =>
            exact ih (EmuRunL.stepR hr hq)
              (by rw [List.length_append, List.length_singleton]; omega)
        | inl x =>
            exact ih (EmuRunL.stepL hr hq)
              (by rw [List.length_append, List.length_singleton]; omega)

/-- **The fixed-atom bridge, left atom**. -/
private theorem transcript_par_fixed_left (s : DDS X Y) (t : DDS X' Y')
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) :
    transcript (par s t) e n
      = replayResL s e n (transcript t (emulateResL s e n) n) := by
  obtain ⟨tout, tin, hr, hle, hterm⟩ :=
    emuRunL_terminal (n := n) n
      (EmuRunL.start (s := s) (t := t) (e := e)) (by simp)
  obtain ⟨hproj, hT, hlen⟩ := emuRunL_invariant hr
  have hLHS : transcript (par s t) e n = tout := by
    rcases hterm with hterm | hterm
    · rw [← hterm]
      exact hT
    · have hfreeze : e ((transcript (par s t) e tout.length)↓ᵧ)
          = none := by
        rw [hT]
        exact hterm
      rw [transcript_freeze hfreeze hle]
      exact hT
  have hTin : transcript t (emulateResL s e n) n = tin := by
    have h1 := emuRunL_transcript hr hle
    have h2 : emulateResL s e n
        ((transcript t (emulateResL s e n) tin.length)↓ᵧ) = none := by
      rw [h1]
      exact emulateResL_terminal_stall hr hle hterm
    rw [transcript_freeze h2 (by omega), h1]
  rw [hLHS, hTin]
  exact (replayGoL_terminal hr hle hterm).symm

end ResRunL

/-! ### The mixture decomposition and the parallel congruence hops -/

open RandomSystems (Dist)

/-- **The mixture decomposition, right atom fixed** (MauRen11 Def 16,
resource side, through the pushforward): the transcript distribution of
`S ∥ T` is the `T`-mixture of the reconstruction pushforwards of `S`'s
transcript distributions under the per-atom emulated environments. -/
theorem transcriptDist_par_mixture_right (S : PFunPDS X Y)
    (T : PFunPDS X' Y') (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ)
    (τ : List ((X ⊕ X') × Option (Y ⊕ Y'))) :
    transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S T)) e n τ
      = T.sum fun t wt =>
          wt * (transcriptDist S (emulateRes t e n) n).mass
            (fun trc => replayRes t e n trc = τ) := by
  rw [transcriptDist, Dist.fTransform_apply_eq_mass, Dist.mass_fTransform,
    Dist.mass_prod_eq_double_sum, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [transcriptDist, Dist.mass_fTransform]
  unfold Dist.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun s _ => ?_
  rw [transcript_par_fixed_right s t e n]
  split_ifs with hcond
  · rw [mul_comm]
  · rw [mul_zero]

/-- **The mixture decomposition, left atom fixed**. -/
theorem transcriptDist_par_mixture_left (S : PFunPDS X Y)
    (T : PFunPDS X' Y') (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ)
    (τ : List ((X ⊕ X') × Option (Y ⊕ Y'))) :
    transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S T)) e n τ
      = S.sum fun s ws =>
          ws * (transcriptDist T (emulateResL s e n) n).mass
            (fun trc => replayResL s e n trc = τ) := by
  rw [transcriptDist, Dist.fTransform_apply_eq_mass, Dist.mass_fTransform,
    Dist.mass_prod_eq_double_sum]
  refine Finsupp.sum_congr fun s _ => ?_
  rw [transcriptDist, Dist.mass_fTransform]
  unfold Dist.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [transcript_par_fixed_left s t e n]
  split_ifs with hcond
  · rw [mul_comm]
  · rw [mul_zero]

/-- Left-component congruence of the parallel composition, at one
environment (fn. 20, one hop). -/
theorem transcriptDist_par_congr_left {S S' : PFunPDS X Y}
    (T : PFunPDS X' Y')
    (h : ∀ (e' : DDE X Y) (m : ℕ),
      transcriptDist S e' m = transcriptDist S' e' m)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) :
    transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S T)) e n
      = transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S' T)) e n := by
  refine Finsupp.ext fun τ => ?_
  rw [transcriptDist_par_mixture_right S T e n τ,
    transcriptDist_par_mixture_right S' T e n τ]
  apply Finsupp.sum_congr
  intro t ht
  rw [h (emulateRes t e n) n]

/-- Right-component congruence of the parallel composition, at one
environment (fn. 20, one hop). -/
theorem transcriptDist_par_congr_right (S : PFunPDS X Y)
    {T T' : PFunPDS X' Y'}
    (h : ∀ (e' : DDE X' Y') (m : ℕ),
      transcriptDist T e' m = transcriptDist T' e' m)
    (e : DDE (X ⊕ X') (Y ⊕ Y')) (n : ℕ) :
    transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S T)) e n
      = transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S T')) e n := by
  refine Finsupp.ext fun τ => ?_
  rw [transcriptDist_par_mixture_left S T e n τ,
    transcriptDist_par_mixture_left S T' e n τ]
  apply Finsupp.sum_congr
  intro s₀ hs₀
  rw [h (emulateResL s₀ e n) n]

/-! ### The fixed-component hops of eq. (3) -/

/-- `δ` is subadditive over common mixtures (thesis Def 2.4 with LanMau20
Lemma 3's convexity): if `μ` and `ν` are the same `W`-mixture of the
families `μf`, `νf`, the one-sided excess is at most the mixture of the
excesses. -/
private theorem δ_mixture_le {A : Type*} {B : Type*} {W : Dist B}
    (hW : W.NonNeg)
    (μ ν : Dist A) {μf νf : B → Dist A}
    (hνf : ∀ b ∈ W.support, (νf b).NonNeg)
    (hμ : ∀ τ, μ τ = W.sum fun b w => w * μf b τ)
    (hν : ∀ τ, ν τ = W.sum fun b w => w * νf b τ) :
    δ μ ν ≤ W.sum fun b w => w * δ (μf b) (νf b) := by
  classical
  unfold δ
  rw [Finsupp.sum, Finsupp.sum]
  have hpt : ∀ τ : A, max (μ τ - ν τ) 0
      ≤ ∑ b ∈ W.support, W b * max (μf b τ - νf b τ) 0 := by
    intro τ
    refine max_le ?_ (Finset.sum_nonneg fun b _ =>
      mul_nonneg (hW b) (le_max_right _ _))
    rw [hμ τ, hν τ, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hW b)
  calc ∑ τ ∈ μ.support, max (μ τ - ν τ) 0
      ≤ ∑ τ ∈ μ.support, ∑ b ∈ W.support, W b * max (μf b τ - νf b τ) 0 :=
        Finset.sum_le_sum fun τ _ => hpt τ
    _ = ∑ b ∈ W.support, ∑ τ ∈ μ.support, W b * max (μf b τ - νf b τ) 0 :=
        Finset.sum_comm
    _ ≤ ∑ b ∈ W.support, W b * ((μf b).sum fun τ m => max (m - νf b τ) 0) := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hW b)
        rw [Finsupp.sum]
        calc ∑ τ ∈ μ.support, max (μf b τ - νf b τ) 0
            ≤ ∑ τ ∈ μ.support ∪ (μf b).support, max (μf b τ - νf b τ) 0 :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
                (fun τ _ _ => le_max_right _ _)
          _ = ∑ τ ∈ (μf b).support, max (μf b τ - νf b τ) 0 := by
              refine (Finset.sum_subset Finset.subset_union_right ?_).symm
              intro τ _ hτ
              rw [Finsupp.notMem_support_iff.mp hτ]
              exact max_eq_right (sub_nonpos.mpr (hνf b hb τ))

/-- **Eq. (3), right-fixed hop**: replacing the left component cannot cost
more than its own distance, when the fixed right component is a
probability system (its weight absorbs the mixture). -/
theorem maxAdvantage_par_fixed_right_le {S T : PFunPDS X Y}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (R : PFunPDS X' Y') (hR : R.isProbDist) :
    Δ(Dist.fTransform (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S R),
      Dist.fTransform (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod T R)) ≤ Δ(S, T) := by
  rw [← adv_eq_maxAdvantage_swap
      ((hTnn.prod hR.nonNeg).fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2))
      ((hSnn.prod hR.nonNeg).fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)),
    ← adv_eq_maxAdvantage_swap hTnn hSnn]
  refine csSup_le ⟨_, ⟨(fun _ => none), 0, rfl⟩⟩ ?_
  rintro x ⟨e, n, rfl⟩
  have hkey : δ
      (transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod T R)) e n)
      (transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod S R)) e n)
      ≤ R.sum fun t wt => wt * δ
          (Dist.fTransform (replayRes t e n)
            (transcriptDist T (emulateRes t e n) n))
          (Dist.fTransform (replayRes t e n)
            (transcriptDist S (emulateRes t e n) n)) := by
    refine δ_mixture_le hR.nonNeg _ _
      (fun t _ => ((hSnn.fTransform _).fTransform _)) ?_ ?_
    · intro τ
      rw [transcriptDist_par_mixture_right T R e n τ]
      refine Finsupp.sum_congr fun t _ => ?_
      rw [Dist.fTransform_apply_eq_mass]
    · intro τ
      rw [transcriptDist_par_mixture_right S R e n τ]
      refine Finsupp.sum_congr fun t _ => ?_
      rw [Dist.fTransform_apply_eq_mass]
  have hterm : ∀ t ∈ R.support,
      (δ (Dist.fTransform (replayRes t e n)
          (transcriptDist T (emulateRes t e n) n))
        (Dist.fTransform (replayRes t e n)
          (transcriptDist S (emulateRes t e n) n)) : ℝ)
        ≤ Adv T S := by
    intro t _
    refine le_trans ?_ (le_csSup (bddAbove_adv_set hTnn hSnn)
      ⟨emulateRes t e n, n, rfl⟩)
    exact δ_fTransform_le (replayRes t e n) _
      (transcriptDist_nonNeg hSnn _ n)
  calc (δ _ _ : ℝ)
      ≤ (R.sum fun t wt => wt * δ
          (Dist.fTransform (replayRes t e n)
            (transcriptDist T (emulateRes t e n) n))
          (Dist.fTransform (replayRes t e n)
            (transcriptDist S (emulateRes t e n) n)) : ℝ) := hkey
    _ = ∑ t ∈ R.support, (R t : ℝ)
        * (δ (Dist.fTransform (replayRes t e n)
            (transcriptDist T (emulateRes t e n) n))
          (Dist.fTransform (replayRes t e n)
            (transcriptDist S (emulateRes t e n) n)) : ℝ) := by
        rw [Finsupp.sum]
    _ ≤ ∑ t ∈ R.support, (R t : ℝ) * Adv T S :=
        Finset.sum_le_sum fun t ht =>
          mul_le_mul_of_nonneg_left (hterm t ht) (hR.nonNeg t)
    _ = (R.weight : ℝ) * Adv T S := by
        rw [← Finset.sum_mul, Dist.weight_eq_finsupp_sum, Finsupp.sum]
    _ = Adv T S := by
        rw [hR.weight_eq]
        simp

/-- **Eq. (3), left-fixed hop**. -/
theorem maxAdvantage_par_fixed_left_le (R : PFunPDS X Y)
    (hR : R.isProbDist) {S T : PFunPDS X' Y'}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) :
    Δ(Dist.fTransform (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod R S),
      Dist.fTransform (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod R T)) ≤ Δ(S, T) := by
  rw [← adv_eq_maxAdvantage_swap
      ((hR.nonNeg.prod hTnn).fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2))
      ((hR.nonNeg.prod hSnn).fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)),
    ← adv_eq_maxAdvantage_swap hTnn hSnn]
  refine csSup_le ⟨_, ⟨(fun _ => none), 0, rfl⟩⟩ ?_
  rintro x ⟨e, n, rfl⟩
  have hkey : δ
      (transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod R T)) e n)
      (transcriptDist (Dist.fTransform
        (fun p : DDS X Y × DDS X' Y' => par p.1 p.2)
        (Dist.prod R S)) e n)
      ≤ R.sum fun s₀ ws => ws * δ
          (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist T (emulateResL s₀ e n) n))
          (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist S (emulateResL s₀ e n) n)) := by
    refine δ_mixture_le hR.nonNeg _ _
      (fun s₀ _ => ((hSnn.fTransform _).fTransform _)) ?_ ?_
    · intro τ
      rw [transcriptDist_par_mixture_left R T e n τ]
      refine Finsupp.sum_congr fun s₀ _ => ?_
      rw [Dist.fTransform_apply_eq_mass]
    · intro τ
      rw [transcriptDist_par_mixture_left R S e n τ]
      refine Finsupp.sum_congr fun s₀ _ => ?_
      rw [Dist.fTransform_apply_eq_mass]
  have hterm : ∀ s₀ ∈ R.support,
      (δ (Dist.fTransform (replayResL s₀ e n)
          (transcriptDist T (emulateResL s₀ e n) n))
        (Dist.fTransform (replayResL s₀ e n)
          (transcriptDist S (emulateResL s₀ e n) n)) : ℝ)
        ≤ Adv T S := by
    intro s₀ _
    refine le_trans ?_ (le_csSup (bddAbove_adv_set hTnn hSnn)
      ⟨emulateResL s₀ e n, n, rfl⟩)
    exact δ_fTransform_le (replayResL s₀ e n) _
      (transcriptDist_nonNeg hSnn _ n)
  calc (δ _ _ : ℝ)
      ≤ (R.sum fun s₀ ws => ws * δ
          (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist T (emulateResL s₀ e n) n))
          (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist S (emulateResL s₀ e n) n)) : ℝ) := hkey
    _ = ∑ s₀ ∈ R.support, (R s₀ : ℝ)
        * (δ (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist T (emulateResL s₀ e n) n))
          (Dist.fTransform (replayResL s₀ e n)
            (transcriptDist S (emulateResL s₀ e n) n)) : ℝ) := by
        rw [Finsupp.sum]
    _ ≤ ∑ s₀ ∈ R.support, (R s₀ : ℝ) * Adv T S :=
        Finset.sum_le_sum fun s₀ hs₀ =>
          mul_le_mul_of_nonneg_left (hterm s₀ hs₀) (hR.nonNeg s₀)
    _ = (R.weight : ℝ) * Adv T S := by
        rw [← Finset.sum_mul, Dist.weight_eq_finsupp_sum, Finsupp.sum]
    _ = Adv T S := by
        rw [hR.weight_eq]
        simp

end PFunDDS

/-! ### The attribution fold (MauRen11 §6.2, `(α‖β)(R‖S) = αR ‖ βS`) -/

namespace PFunConverter

section ParFold

open scoped PFunDDS

variable {U V X Y U' V' X' Y' : Type*}

/-- Left attribution of a joint answer history: the `inl`-valued answers,
as proper answers.  (Untagged `⊥`s cannot be attributed — the reason
`apply_parallel_eq_parallel_apply` carries the `AnswersInY` hypotheses.) -/
def attribute_left_answers (jys : List (Option (Y ⊕ Y'))) : List (Option Y) :=
  jys.filterMap fun oy => (oy.bind Sum.getLeft?).map some

/-- Right attribution of a joint answer history. -/
def attribute_right_answers (jys : List (Option (Y ⊕ Y'))) : List (Option Y') :=
  jys.filterMap fun oy => (oy.bind Sum.getRight?).map some

@[simp] theorem attribute_left_answers_nil :
    attribute_left_answers ([] : List (Option (Y ⊕ Y'))) = [] := rfl

@[simp] theorem attribute_right_answers_nil :
    attribute_right_answers ([] : List (Option (Y ⊕ Y'))) = [] := rfl

@[simp] theorem attribute_left_answers_append_inl
    (jys : List (Option (Y ⊕ Y'))) (y : Y) :
    attribute_left_answers (jys ++ [some (Sum.inl y)]) =
      attribute_left_answers jys ++ [some y] := by
  simp [attribute_left_answers]

@[simp] theorem attribute_left_answers_append_inr
    (jys : List (Option (Y ⊕ Y'))) (y' : Y') :
    attribute_left_answers (jys ++ [some (Sum.inr y')]) =
      attribute_left_answers jys := by
  simp [attribute_left_answers]

@[simp] theorem attribute_left_answers_append_none
    (jys : List (Option (Y ⊕ Y'))) :
    attribute_left_answers (jys ++ [none]) = attribute_left_answers jys := by
  simp [attribute_left_answers]

@[simp] theorem attribute_right_answers_append_inr
    (jys : List (Option (Y ⊕ Y'))) (y' : Y') :
    attribute_right_answers (jys ++ [some (Sum.inr y')]) =
      attribute_right_answers jys ++ [some y'] := by
  simp [attribute_right_answers]

@[simp] theorem attribute_right_answers_append_inl
    (jys : List (Option (Y ⊕ Y'))) (y : Y) :
    attribute_right_answers (jys ++ [some (Sum.inl y)]) =
      attribute_right_answers jys := by
  simp [attribute_right_answers]

@[simp] theorem attribute_right_answers_append_none
    (jys : List (Option (Y ⊕ Y'))) :
    attribute_right_answers (jys ++ [none]) = attribute_right_answers jys := by
  simp [attribute_right_answers]

/-- The composite's move at an `inl`-ended outer history is `α`'s move at
the attributed pair, re-tagged. -/
private theorem mem_par_move_inl {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {ws : List (U ⊕ U')} {u : U}
    (hgl : ws.getLast? = some (Sum.inl u)) (jys : List (Option (Y ⊕ Y')))
    (m : (X ⊕ X') ⊕ (V ⊕ V')) :
    m ∈ par α β (ws, jys) ↔
      ∃ mα ∈ α (ws.filterMap Sum.getLeft?, attribute_left_answers jys),
        Sum.map Sum.inl Sum.inl mα = m := by
  unfold par attribute_left_answers
  rw [hgl]
  dsimp only
  exact Part.mem_map_iff _

/-- The composite's move at an `inr`-ended outer history. -/
private theorem mem_par_move_inr {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {ws : List (U ⊕ U')} {u' : U'}
    (hgl : ws.getLast? = some (Sum.inr u')) (jys : List (Option (Y ⊕ Y')))
    (m : (X ⊕ X') ⊕ (V ⊕ V')) :
    m ∈ par α β (ws, jys) ↔
      ∃ mβ ∈ β (ws.filterMap Sum.getRight?, attribute_right_answers jys),
        Sum.map Sum.inr Sum.inr mβ = m := by
  unfold par attribute_right_answers
  rw [hgl]
  dsimp only
  exact Part.mem_map_iff _

/-- Under `AnswersInY`, a successful `drive` round from a reachable
all-proper anchor consumes only proper answers, ends at a reachable
all-proper pair, and its answer is an `inr`-member. -/
private theorem drive_proper_of_answersInY {α : ProtocolFn U V X Y}
    {s : PFunDDS.DDS X Y} (hα : AnswersInY α) :
    ∀ {fuel : ℕ} {us : List U} {xs : List X} {ys : List (Option Y)}
      {r : V × List X × List (Option Y)},
      Reach α (us, ys) → (∀ oy ∈ ys, oy.isSome) →
      r ∈ drive α s fuel us xs ys →
      Sum.inr r.1 ∈ α (us, r.2.2) ∧ Reach α (us, r.2.2) ∧
        (∀ oy ∈ r.2.2, oy.isSome) := by
  intro fuel
  induction fuel with
  | zero =>
      intro us xs ys r _ _ h
      simp [drive] at h
  | succ n ih =>
      intro us xs ys r hre hprop h
      rcases drive_succ_elim h with ⟨x, hx, hrec⟩ | ⟨v, hv, rfl⟩
      · rcases hout : PFunDDS.output (s⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exfalso
          rw [hout] at hrec
          exact drive_not_mem_of_not_dom
            (hα _ (Reach.answer hre hx none) (by simp)) n _ hrec
        · rw [hout] at hrec
          refine ih (Reach.answer hre hx (some y)) ?_ hrec
          intro oy hmem
          rcases List.mem_append.mp hmem with hm | hm
          · exact hprop oy hm
          · rw [List.mem_singleton.mp hm]
            rfl
      · exact ⟨hv, hre, hprop⟩

/-- **Forward round fold, left side**: a composite round at an `inl`-ended
outer history projects to an `α`-round against `s` — dead inner queries
are absorbed by the kept-scan correspondence, the `β`-side is untouched. -/
theorem drive_parallel_left_projects {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {s : PFunDDS.DDS X Y}
    {t : PFunDDS.DDS X' Y'} :
    ∀ {fuel : ℕ} {ws : List (U ⊕ U')} {u : U} {jxs : List (X ⊕ X')}
      {jys : List (Option (Y ⊕ Y'))} {xs : List X} {ys : List (Option Y)}
      {r : (V ⊕ V') × List (X ⊕ X') × List (Option (Y ⊕ Y'))},
      ws.getLast? = some (Sum.inl u) →
      PFunDDS.keptPrefix s (jxs.filterMap Sum.getLeft?)
        = PFunDDS.keptPrefix s xs →
      attribute_left_answers jys = ys →
      r ∈ drive (par α β) (PFunDDS.par s t) fuel ws jxs jys →
      ∃ (v : V) (fuel' : ℕ) (xs' : List X) (ys' : List (Option Y)),
        r.1 = Sum.inl v ∧
        (v, xs', ys') ∈ drive α s fuel' (ws.filterMap Sum.getLeft?) xs ys ∧
        PFunDDS.keptPrefix s (r.2.1.filterMap Sum.getLeft?)
          = PFunDDS.keptPrefix s xs' ∧
        attribute_left_answers r.2.2 = ys' ∧
        r.2.1.filterMap Sum.getRight? = jxs.filterMap Sum.getRight? ∧
        attribute_right_answers r.2.2 = attribute_right_answers jys := by
  intro fuel
  induction fuel with
  | zero =>
      intro ws u jxs jys xs ys r _ _ _ hmem
      simp [drive] at hmem
  | succ n ih =>
      intro ws u jxs jys xs ys r hgl hC1 hview hmem
      rcases drive_succ_elim hmem with ⟨jq, hjq, hrec⟩ | ⟨jv, hjv, rfl⟩
      · rw [mem_par_move_inl hgl] at hjq
        obtain ⟨mα, hmα, hmap⟩ := hjq
        cases mα with
        | inr v =>
            exact absurd (show Sum.inr (Sum.inl v) = Sum.inl jq from hmap)
              (by simp)
        | inl x =>
            obtain rfl : jq = Sum.inl x :=
              (Sum.inl.inj
                (show Sum.inl (Sum.inl x) = Sum.inl jq from hmap)).symm
            rw [hview] at hmα
            have hproj : (jxs ++ [Sum.inl x]).filterMap Sum.getLeft?
                = jxs.filterMap Sum.getLeft? ++ [x] := by simp
            have hfac := PFunDDS.output_fully_defined_par_inl s t
              (l := jxs) x (by rw [PFunDDS.dom_fullyDefined]; simp)
              (by rw [PFunDDS.dom_fullyDefined]; simp)
            rcases hout : PFunDDS.output (s⊥)
                (jxs.filterMap Sum.getLeft? ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
            · rw [hout] at hfac
              rw [hfac] at hrec
              simp only [Option.map_none] at hrec
              have hC1' : PFunDDS.keptPrefix s
                  ((jxs ++ [Sum.inl x]).filterMap Sum.getLeft?)
                  = PFunDDS.keptPrefix s xs := by
                rw [hproj, keptPrefix_concat,
                  if_neg (keptPrefix_not_mem_of_output_none hout)]
                exact hC1
              have hview' : attribute_left_answers (jys ++ [none]) = ys := by
                rw [attribute_left_answers_append_none]
                exact hview
              obtain ⟨v, f', xs', ys', h1, h2, h3, h4, h5, h6⟩ :=
                ih hgl hC1' hview' hrec
              refine ⟨v, f', xs', ys', h1, h2, h3, h4, ?_, ?_⟩
              · rw [h5]
                simp
              · rw [h6, attribute_right_answers_append_none]
            · rw [hout] at hfac
              rw [hfac] at hrec
              simp only [Option.map_some] at hrec
              obtain ⟨hqdom, -⟩ := keptPrefix_mem_of_output_some hout
              rw [hC1] at hqdom
              have hC1' : PFunDDS.keptPrefix s
                  ((jxs ++ [Sum.inl x]).filterMap Sum.getLeft?)
                  = PFunDDS.keptPrefix s (xs ++ [x]) := by
                rw [hproj, keptPrefix_concat, keptPrefix_concat, hC1,
                  if_pos hqdom]
              have hstd : PFunDDS.output (s⊥) (xs ++ [x])
                  (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
                rw [output_fullyDefined_concat]
                rw [output_fullyDefined_concat] at hout
                rw [← hC1]
                exact hout
              have hview' : attribute_left_answers (jys ++ [some (Sum.inl y)])
                  = ys ++ [some y] := by
                rw [attribute_left_answers_append_inl, hview]
              obtain ⟨v, f', xs', ys', h1, h2, h3, h4, h5, h6⟩ :=
                ih hgl hC1' hview' hrec
              refine ⟨v, f' + 1, xs', ys', h1, ?_, h3, h4, ?_, ?_⟩
              · refine drive_mem_query α s hmα ?_
                rw [hstd]
                exact h2
              · rw [h5]
                simp
              · rw [h6, attribute_right_answers_append_inl]
      · rw [mem_par_move_inl hgl] at hjv
        obtain ⟨mα, hmα, hmap⟩ := hjv
        cases mα with
        | inl x =>
            exact absurd (show Sum.inl (Sum.inl x) = Sum.inr jv from hmap)
              (by simp)
        | inr v =>
            obtain rfl : jv = Sum.inl v :=
              (Sum.inr.inj
                (show Sum.inr (Sum.inl v) = Sum.inr jv from hmap)).symm
            rw [hview] at hmα
            exact ⟨v, 1, xs, ys, rfl, drive_mem_answer α s hmα 0, hC1,
              hview, rfl, rfl⟩

/-- **Forward round fold, right side**. -/
theorem drive_parallel_right_projects {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {s : PFunDDS.DDS X Y}
    {t : PFunDDS.DDS X' Y'} :
    ∀ {fuel : ℕ} {ws : List (U ⊕ U')} {u' : U'} {jxs : List (X ⊕ X')}
      {jys : List (Option (Y ⊕ Y'))} {xs : List X'} {ys : List (Option Y')}
      {r : (V ⊕ V') × List (X ⊕ X') × List (Option (Y ⊕ Y'))},
      ws.getLast? = some (Sum.inr u') →
      PFunDDS.keptPrefix t (jxs.filterMap Sum.getRight?)
        = PFunDDS.keptPrefix t xs →
      attribute_right_answers jys = ys →
      r ∈ drive (par α β) (PFunDDS.par s t) fuel ws jxs jys →
      ∃ (v : V') (fuel' : ℕ) (xs' : List X') (ys' : List (Option Y')),
        r.1 = Sum.inr v ∧
        (v, xs', ys') ∈ drive β t fuel' (ws.filterMap Sum.getRight?) xs ys ∧
        PFunDDS.keptPrefix t (r.2.1.filterMap Sum.getRight?)
          = PFunDDS.keptPrefix t xs' ∧
        attribute_right_answers r.2.2 = ys' ∧
        r.2.1.filterMap Sum.getLeft? = jxs.filterMap Sum.getLeft? ∧
        attribute_left_answers r.2.2 = attribute_left_answers jys := by
  intro fuel
  induction fuel with
  | zero =>
      intro ws u' jxs jys xs ys r _ _ _ hmem
      simp [drive] at hmem
  | succ n ih =>
      intro ws u' jxs jys xs ys r hgl hC1 hview hmem
      rcases drive_succ_elim hmem with ⟨jq, hjq, hrec⟩ | ⟨jv, hjv, rfl⟩
      · rw [mem_par_move_inr hgl] at hjq
        obtain ⟨mβ, hmβ, hmap⟩ := hjq
        cases mβ with
        | inr v =>
            exact absurd (show Sum.inr (Sum.inr v) = Sum.inl jq from hmap)
              (by simp)
        | inl x =>
            obtain rfl : jq = Sum.inr x :=
              (Sum.inl.inj
                (show Sum.inl (Sum.inr x) = Sum.inl jq from hmap)).symm
            rw [hview] at hmβ
            have hproj : (jxs ++ [Sum.inr x]).filterMap Sum.getRight?
                = jxs.filterMap Sum.getRight? ++ [x] := by simp
            have hfac := PFunDDS.output_fully_defined_par_inr s t
              (l := jxs) x (by rw [PFunDDS.dom_fullyDefined]; simp)
              (by rw [PFunDDS.dom_fullyDefined]; simp)
            rcases hout : PFunDDS.output (t⊥)
                (jxs.filterMap Sum.getRight? ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
            · rw [hout] at hfac
              rw [hfac] at hrec
              simp only [Option.map_none] at hrec
              have hC1' : PFunDDS.keptPrefix t
                  ((jxs ++ [Sum.inr x]).filterMap Sum.getRight?)
                  = PFunDDS.keptPrefix t xs := by
                rw [hproj, keptPrefix_concat,
                  if_neg (keptPrefix_not_mem_of_output_none hout)]
                exact hC1
              have hview' : attribute_right_answers (jys ++ [none]) = ys := by
                rw [attribute_right_answers_append_none]
                exact hview
              obtain ⟨v, f', xs', ys', h1, h2, h3, h4, h5, h6⟩ :=
                ih hgl hC1' hview' hrec
              refine ⟨v, f', xs', ys', h1, h2, h3, h4, ?_, ?_⟩
              · rw [h5]
                simp
              · rw [h6, attribute_left_answers_append_none]
            · rw [hout] at hfac
              rw [hfac] at hrec
              simp only [Option.map_some] at hrec
              obtain ⟨hqdom, -⟩ := keptPrefix_mem_of_output_some hout
              rw [hC1] at hqdom
              have hC1' : PFunDDS.keptPrefix t
                  ((jxs ++ [Sum.inr x]).filterMap Sum.getRight?)
                  = PFunDDS.keptPrefix t (xs ++ [x]) := by
                rw [hproj, keptPrefix_concat, keptPrefix_concat, hC1,
                  if_pos hqdom]
              have hstd : PFunDDS.output (t⊥) (xs ++ [x])
                  (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
                rw [output_fullyDefined_concat]
                rw [output_fullyDefined_concat] at hout
                rw [← hC1]
                exact hout
              have hview' : attribute_right_answers (jys ++ [some (Sum.inr y)])
                  = ys ++ [some y] := by
                rw [attribute_right_answers_append_inr, hview]
              obtain ⟨v, f', xs', ys', h1, h2, h3, h4, h5, h6⟩ :=
                ih hgl hC1' hview' hrec
              refine ⟨v, f' + 1, xs', ys', h1, ?_, h3, h4, ?_, ?_⟩
              · refine drive_mem_query β t hmβ ?_
                rw [hstd]
                exact h2
              · rw [h5]
                simp
              · rw [h6, attribute_left_answers_append_inr]
      · rw [mem_par_move_inr hgl] at hjv
        obtain ⟨mβ, hmβ, hmap⟩ := hjv
        cases mβ with
        | inl x =>
            exact absurd (show Sum.inl (Sum.inr x) = Sum.inr jv from hmap)
              (by simp)
        | inr v =>
            obtain rfl : jv = Sum.inr v :=
              (Sum.inr.inj
                (show Sum.inr (Sum.inr v) = Sum.inr jv from hmap)).symm
            rw [hview] at hmβ
            exact ⟨v, 1, xs, ys, rfl, drive_mem_answer β t hmβ 0, hC1,
              hview, rfl, rfl⟩

/-- **Backward round fold, left side**: an `α`-round against `s` from a
reachable all-proper anchor lifts to a composite round — `AnswersInY α`
rules out motion past a `⊥` (the ⊥-attribution counterexample). -/
theorem drive_left_lifts_to_parallel {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {s : PFunDDS.DDS X Y}
    {t : PFunDDS.DDS X' Y'} (hα : AnswersInY α) :
    ∀ {fuel : ℕ} {ws : List (U ⊕ U')} {u : U} {jxs : List (X ⊕ X')}
      {jys : List (Option (Y ⊕ Y'))} {xs xs' : List X}
      {ys ys' : List (Option Y)} {v : V},
      ws.getLast? = some (Sum.inl u) →
      Reach α (ws.filterMap Sum.getLeft?, ys) →
      (∀ oy ∈ ys, oy.isSome) →
      PFunDDS.keptPrefix s (jxs.filterMap Sum.getLeft?)
        = PFunDDS.keptPrefix s xs →
      attribute_left_answers jys = ys →
      (v, xs', ys') ∈ drive α s fuel (ws.filterMap Sum.getLeft?) xs ys →
      ∃ (fuel' : ℕ) (jxs' : List (X ⊕ X')) (jys' : List (Option (Y ⊕ Y'))),
        (Sum.inl v, jxs', jys')
            ∈ drive (par α β) (PFunDDS.par s t) fuel' ws jxs jys ∧
        PFunDDS.keptPrefix s (jxs'.filterMap Sum.getLeft?)
          = PFunDDS.keptPrefix s xs' ∧
        attribute_left_answers jys' = ys' ∧
        jxs'.filterMap Sum.getRight? = jxs.filterMap Sum.getRight? ∧
        attribute_right_answers jys' = attribute_right_answers jys := by
  intro fuel
  induction fuel with
  | zero =>
      intro ws u jxs jys xs xs' ys ys' v _ _ _ _ _ hmem
      simp [drive] at hmem
  | succ n ih =>
      intro ws u jxs jys xs xs' ys ys' v hgl hre hprop hC1 hview hmem
      rcases drive_succ_elim hmem with ⟨x, hx, hrec⟩ | ⟨v₀, hv, heq⟩
      · rcases hstd : PFunDDS.output (s⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exfalso
          rw [hstd] at hrec
          exact drive_not_mem_of_not_dom
            (hα _ (Reach.answer hre hx none) (by simp)) n _ hrec
        · rw [hstd] at hrec
          have hx' : Sum.inl x
              ∈ α (ws.filterMap Sum.getLeft?, attribute_left_answers jys) := by
            rw [hview]
            exact hx
          have hmove : (Sum.inl (Sum.inl x) : (X ⊕ X') ⊕ (V ⊕ V'))
              ∈ par α β (ws, jys) :=
            (mem_par_move_inl hgl jys _).mpr ⟨Sum.inl x, hx', rfl⟩
          obtain ⟨hqdom, -⟩ := keptPrefix_mem_of_output_some hstd
          have hjoint : PFunDDS.output (s⊥)
              (jxs.filterMap Sum.getLeft? ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            rw [output_fullyDefined_concat, hC1]
            rw [output_fullyDefined_concat] at hstd
            exact hstd
          have hcout : PFunDDS.output ((PFunDDS.par s t)⊥)
              (jxs ++ [Sum.inl x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              = some (Sum.inl y) := by
            rw [PFunDDS.output_fully_defined_par_inl s t x
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              (by rw [PFunDDS.dom_fullyDefined]; simp), hjoint]
            rfl
          have hproj : (jxs ++ [Sum.inl x]).filterMap Sum.getLeft?
              = jxs.filterMap Sum.getLeft? ++ [x] := by simp
          have hC1' : PFunDDS.keptPrefix s
              ((jxs ++ [Sum.inl x]).filterMap Sum.getLeft?)
              = PFunDDS.keptPrefix s (xs ++ [x]) := by
            rw [hproj, keptPrefix_concat, keptPrefix_concat, hC1,
              if_pos hqdom]
          have hview' : attribute_left_answers (jys ++ [some (Sum.inl y)])
              = ys ++ [some y] := by
            rw [attribute_left_answers_append_inl, hview]
          obtain ⟨f', jxs', jys', h1, h2, h3, h4, h5⟩ :=
            ih hgl (Reach.answer hre hx (some y))
              (by
                intro oy hmem'
                rcases List.mem_append.mp hmem' with hm | hm
                · exact hprop oy hm
                · rw [List.mem_singleton.mp hm]
                  rfl)
              hC1' hview' hrec
          refine ⟨f' + 1, jxs', jys', ?_, h2, h3, ?_, ?_⟩
          · refine drive_mem_query (par α β) (PFunDDS.par s t) hmove ?_
            rw [hcout]
            exact h1
          · rw [h4]
            simp
          · rw [h5, attribute_right_answers_append_inl]
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        have hv' : Sum.inr v
            ∈ α (ws.filterMap Sum.getLeft?, attribute_left_answers jys) := by
          rw [hview]
          exact hv
        have hmove : (Sum.inr (Sum.inl v) : (X ⊕ X') ⊕ (V ⊕ V'))
            ∈ par α β (ws, jys) :=
          (mem_par_move_inl hgl jys _).mpr ⟨Sum.inr v, hv', rfl⟩
        exact ⟨1, jxs, jys,
          drive_mem_answer (par α β) (PFunDDS.par s t) hmove 0,
          hC1, hview, rfl, rfl⟩

/-- **Backward round fold, right side**: a `β`-round against `t` from a
reachable all-proper anchor lifts to a composite round.  `AnswersInY β`
rules out motion past an untagged `⊥`, symmetrically to the left fold. -/
theorem drive_right_lifts_to_parallel {α : ProtocolFn U V X Y}
    {β : ProtocolFn U' V' X' Y'} {s : PFunDDS.DDS X Y}
    {t : PFunDDS.DDS X' Y'} (hβ : AnswersInY β) :
    ∀ {fuel : ℕ} {ws : List (U ⊕ U')} {u' : U'} {jxs : List (X ⊕ X')}
      {jys : List (Option (Y ⊕ Y'))} {xs xs' : List X'}
      {ys ys' : List (Option Y')} {v : V'},
      ws.getLast? = some (Sum.inr u') →
      Reach β (ws.filterMap Sum.getRight?, ys) →
      (∀ oy ∈ ys, oy.isSome) →
      PFunDDS.keptPrefix t (jxs.filterMap Sum.getRight?)
        = PFunDDS.keptPrefix t xs →
      attribute_right_answers jys = ys →
      (v, xs', ys') ∈ drive β t fuel (ws.filterMap Sum.getRight?) xs ys →
      ∃ (fuel' : ℕ) (jxs' : List (X ⊕ X')) (jys' : List (Option (Y ⊕ Y'))),
        (Sum.inr v, jxs', jys')
            ∈ drive (par α β) (PFunDDS.par s t) fuel' ws jxs jys ∧
        PFunDDS.keptPrefix t (jxs'.filterMap Sum.getRight?)
          = PFunDDS.keptPrefix t xs' ∧
        attribute_right_answers jys' = ys' ∧
        jxs'.filterMap Sum.getLeft? = jxs.filterMap Sum.getLeft? ∧
        attribute_left_answers jys' = attribute_left_answers jys := by
  intro fuel
  induction fuel with
  | zero =>
      intro ws u' jxs jys xs xs' ys ys' v _ _ _ _ _ hmem
      simp [drive] at hmem
  | succ n ih =>
      intro ws u' jxs jys xs xs' ys ys' v hgl hre hprop hC1 hview hmem
      rcases drive_succ_elim hmem with ⟨x, hx, hrec⟩ | ⟨v₀, hv, heq⟩
      · rcases hstd : PFunDDS.output (t⊥) (xs ++ [x])
            (by rw [PFunDDS.dom_fullyDefined]; simp) with _ | y
        · exfalso
          rw [hstd] at hrec
          exact drive_not_mem_of_not_dom
            (hβ _ (Reach.answer hre hx none) (by simp)) n _ hrec
        · rw [hstd] at hrec
          have hx' : Sum.inl x
              ∈ β (ws.filterMap Sum.getRight?, attribute_right_answers jys) := by
            rw [hview]
            exact hx
          have hmove : (Sum.inl (Sum.inr x) : (X ⊕ X') ⊕ (V ⊕ V'))
              ∈ par α β (ws, jys) :=
            (mem_par_move_inr hgl jys _).mpr ⟨Sum.inl x, hx', rfl⟩
          obtain ⟨hqdom, -⟩ := keptPrefix_mem_of_output_some hstd
          have hjoint : PFunDDS.output (t⊥)
              (jxs.filterMap Sum.getRight? ++ [x])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            rw [output_fullyDefined_concat, hC1]
            rw [output_fullyDefined_concat] at hstd
            exact hstd
          have hcout : PFunDDS.output ((PFunDDS.par s t)⊥)
              (jxs ++ [Sum.inr x])
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              = some (Sum.inr y) := by
            rw [PFunDDS.output_fully_defined_par_inr s t x
              (by rw [PFunDDS.dom_fullyDefined]; simp)
              (by rw [PFunDDS.dom_fullyDefined]; simp), hjoint]
            rfl
          have hproj : (jxs ++ [Sum.inr x]).filterMap Sum.getRight?
              = jxs.filterMap Sum.getRight? ++ [x] := by simp
          have hC1' : PFunDDS.keptPrefix t
              ((jxs ++ [Sum.inr x]).filterMap Sum.getRight?)
              = PFunDDS.keptPrefix t (xs ++ [x]) := by
            rw [hproj, keptPrefix_concat, keptPrefix_concat, hC1,
              if_pos hqdom]
          have hview' : attribute_right_answers (jys ++ [some (Sum.inr y)])
              = ys ++ [some y] := by
            rw [attribute_right_answers_append_inr, hview]
          obtain ⟨f', jxs', jys', h1, h2, h3, h4, h5⟩ :=
            ih hgl (Reach.answer hre hx (some y))
              (by
                intro oy hmem'
                rcases List.mem_append.mp hmem' with hm | hm
                · exact hprop oy hm
                · rw [List.mem_singleton.mp hm]
                  rfl)
              hC1' hview' hrec
          refine ⟨f' + 1, jxs', jys', ?_, h2, h3, ?_, ?_⟩
          · refine drive_mem_query (par α β) (PFunDDS.par s t) hmove ?_
            rw [hcout]
            exact h1
          · rw [h4]
            simp
          · rw [h5, attribute_left_answers_append_inr]
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        have hv' : Sum.inr v
            ∈ β (ws.filterMap Sum.getRight?, attribute_right_answers jys) := by
          rw [hview]
          exact hv
        have hmove : (Sum.inr (Sum.inr v) : (X ⊕ X') ⊕ (V ⊕ V'))
            ∈ par α β (ws, jys) :=
          (mem_par_move_inr hgl jys _).mpr ⟨Sum.inr v, hv', rfl⟩
        exact ⟨1, jxs, jys,
          drive_mem_answer (par α β) (PFunDDS.par s t) hmove 0,
          hC1, hview, rfl, rfl⟩

end ParFold

end PFunConverter

end RandomSystems.CR18
