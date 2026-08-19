/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distinguishing
import RandomSystems.StepConverter
import RandomSystems.ResourceView
import RandomSystems.GameOf

/-!
# Converter DPI via absorption (DESIGN §10.7)

`Δ(αS, αT) ≤ Δ(S, T)`: applying a converter cannot increase distinguishing
advantage — converters are 1-Lipschitz, the categorical content of
"converters are morphisms".

The engine is **absorption**: from a distinguisher `d` of the applied
systems and the converter's protocol `step`, build the distinguisher
`absorb d step` of the base systems that runs `d` and the converter
internally, replaying the base system's answer history.  The deterministic
core is the **verdict correspondence**

`verdict (absorb d step) s ↔ verdict d (applyG step s.1)`

proven under two paper-faithful hypotheses:

* the system is **total on nonempty histories** (the resource view — CR18
  treats systems as "defined on the histories under discussion"; without
  it, the `keptPrefix` pruning of the *composite* and of the *base* system
  genuinely diverge and the naive correspondence is false);
* the converter has **bounded rounds** (CR18 Def 3.8's "finite upper bound
  on the number of consecutive `(in, x)` outputs", as a hypothesis).

The replay itself needs *no* hypotheses: it is the fuel-monotone driver
`absorbGo`, with the move extracted classically (`absorbFun`); an
interaction in which `d` never stops and never needs another answer
defaults to verdict `0` on both sides, so `StopFinal` holds unconditionally.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v w z

attribute [local instance] Classical.propDecidable

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ### The replay driver -/

/-- One replay machine for "`d` with the converter `step` fused in", driven
by the *base-system answer history* `h`: in distinguisher mode (`none`)
consult `d`; in round mode (`some (u, ys)`) consult `step`; an inner query
consumes the next answer from `h`, or is emitted as the absorbed
distinguisher's next move when `h` is exhausted.  `fuel` is the
unrolling counter (hidden by `absorbFun`). -/
def absorbGo (d : PFunDDS.DDD U V) (step : U → List Y → X ⊕ V) :
    ℕ → List (Option V) → Option (U × List Y) → List (Option Y) →
      Option (X ⊕ Bool)
  | 0, _, _, _ => none
  | fuel + 1, vs, none, h =>
      match d.val vs with
      | Sum.inr b => some (Sum.inr b)
      | Sum.inl u => absorbGo d step fuel vs (some (u, [])) h
  | fuel + 1, vs, some (u, ys), h =>
      match step u ys with
      | Sum.inr v => absorbGo d step fuel (vs ++ [some v]) none h
      | Sum.inl x =>
          match h with
          | [] => some (Sum.inl x)
          | some y :: h' => absorbGo d step fuel vs (some (u, ys ++ [y])) h'
          | none :: h' => absorbGo d step fuel (vs ++ [none]) none h'

theorem absorbGo_mono (d : PFunDDS.DDD U V) (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {vs : List (Option V)} {mode : Option (U × List Y)}
      {h : List (Option Y)} {m : X ⊕ Bool},
      absorbGo d step fuel vs mode h = some m →
      absorbGo d step (fuel + 1) vs mode h = some m := by
  intro fuel
  induction fuel with
  | zero => intro vs mode h m hm; simp [absorbGo] at hm
  | succ n ih =>
      intro vs mode h m hm
      cases mode with
      | none =>
          rw [absorbGo] at hm ⊢
          cases hd : d.val vs with
          | inr b => rw [hd] at hm; exact hm
          | inl u => rw [hd] at hm; exact ih hm
      | some p =>
          obtain ⟨u, ys⟩ := p
          rw [absorbGo] at hm ⊢
          cases hs : step u ys with
          | inr v => rw [hs] at hm; exact ih hm
          | inl x =>
              rw [hs] at hm
              cases h with
              | nil => exact hm
              | cons oy h' =>
                  cases oy with
                  | some y => exact ih hm
                  | none => exact ih hm

theorem absorbGo_mono_le (d : PFunDDS.DDD U V) (step : U → List Y → X ⊕ V)
    {fuel fuel' : ℕ} {vs : List (Option V)} {mode : Option (U × List Y)}
    {h : List (Option Y)} {m : X ⊕ Bool} (hle : fuel ≤ fuel')
    (hm : absorbGo d step fuel vs mode h = some m) :
    absorbGo d step fuel' vs mode h = some m := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using hm
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]
      exact absorbGo_mono d step ih

/-- A replay that returns a *verdict* never needed more answers: extending the
answer history does not change it. -/
theorem absorbGo_append_of_inr (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {vs : List (Option V)} {mode : Option (U × List Y)}
      {h ext : List (Option Y)} {b : Bool},
      absorbGo d step fuel vs mode h = some (Sum.inr b) →
      absorbGo d step fuel vs mode (h ++ ext) = some (Sum.inr b) := by
  intro fuel
  induction fuel with
  | zero => intro vs mode h ext b hm; simp [absorbGo] at hm
  | succ n ih =>
      intro vs mode h ext b hm
      cases mode with
      | none =>
          rw [absorbGo] at hm ⊢
          cases hd : d.val vs with
          | inr b' => rw [hd] at hm; exact hm
          | inl u => rw [hd] at hm; exact ih hm
      | some p =>
          obtain ⟨u, ys⟩ := p
          rw [absorbGo] at hm ⊢
          cases hs : step u ys with
          | inr v => rw [hs] at hm; exact ih hm
          | inl x =>
              rw [hs] at hm
              cases h with
              | nil => simp at hm
              | cons oy h' =>
                  cases oy with
                  | some y => exact ih hm
                  | none => exact ih hm

/-- A replay that answers on an extended history answers (possibly with the
pending query) on the original one. -/
theorem absorbGo_isSome_of_append (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {vs : List (Option V)} {mode : Option (U × List Y)}
      {h ext : List (Option Y)},
      (absorbGo d step fuel vs mode (h ++ ext)).isSome →
      ∃ fuel', (absorbGo d step fuel' vs mode h).isSome := by
  intro fuel
  induction fuel with
  | zero => intro vs mode h ext hm; simp [absorbGo] at hm
  | succ n ih =>
      intro vs mode h ext hm
      cases mode with
      | none =>
          rw [absorbGo] at hm
          cases hd : d.val vs with
          | inr b =>
              exact ⟨1, by rw [absorbGo, hd]; rfl⟩
          | inl u =>
              rw [hd] at hm
              obtain ⟨fuel', hf⟩ := ih hm
              exact ⟨fuel' + 1, by rw [absorbGo, hd]; exact hf⟩
      | some p =>
          obtain ⟨u, ys⟩ := p
          rw [absorbGo] at hm
          cases hs : step u ys with
          | inr v =>
              rw [hs] at hm
              obtain ⟨fuel', hf⟩ := ih hm
              exact ⟨fuel' + 1, by rw [absorbGo, hs]; exact hf⟩
          | inl x =>
              rw [hs] at hm
              cases h with
              | nil =>
                  exact ⟨1, by rw [absorbGo, hs]; rfl⟩
              | cons oy h' =>
                  cases oy with
                  | some y =>
                      obtain ⟨fuel', hf⟩ := ih hm
                      exact ⟨fuel' + 1, by rw [absorbGo, hs]; exact hf⟩
                  | none =>
                      obtain ⟨fuel', hf⟩ := ih hm
                      exact ⟨fuel' + 1, by rw [absorbGo, hs]; exact hf⟩

/-! ### The absorbed distinguisher -/

/-- The absorbed distinguisher's move at a base-answer history: the eventual
value of the replay (fuel-independent by monotonicity), defaulting to
verdict `0` when the internal interaction never produces a move. -/
noncomputable def absorbFun (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) (h : List (Option Y)) : X ⊕ Bool :=
  if hex : ∃ fuel, (absorbGo d step fuel [] none h).isSome then
    (absorbGo d step hex.choose [] none h).get hex.choose_spec
  else Sum.inr false

theorem absorbFun_eq_of_go {d : PFunDDS.DDD U V}
    {step : U → List Y → X ⊕ V} {h : List (Option Y)} {fuel : ℕ}
    {m : X ⊕ Bool} (hm : absorbGo d step fuel [] none h = some m) :
    absorbFun d step h = m := by
  have hex : ∃ fuel, (absorbGo d step fuel [] none h).isSome :=
    ⟨fuel, by rw [hm]; rfl⟩
  unfold absorbFun
  rw [dif_pos hex]
  have h₁ : absorbGo d step (max hex.choose fuel) [] none h
      = some ((absorbGo d step hex.choose [] none h).get hex.choose_spec) := by
    refine absorbGo_mono_le d step (le_max_left _ _) ?_
    rw [Option.some_get]
  have h₂ : absorbGo d step (max hex.choose fuel) [] none h = some m :=
    absorbGo_mono_le d step (le_max_right _ _) hm
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- The absorbed distinguisher: verdicts are final. -/
theorem stopFinal_absorbFun (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) :
    PFunDDS.StopFinal (absorbFun d step) := by
  intro h h' hpre b hb
  obtain ⟨ext, rfl⟩ := hpre
  by_cases hex : ∃ fuel, (absorbGo d step fuel [] none h).isSome
  · have hval : absorbGo d step hex.choose [] none h = some (Sum.inr b) := by
      unfold absorbFun at hb
      rw [dif_pos hex] at hb
      rw [← Option.some_get hex.choose_spec, hb]
    exact absorbFun_eq_of_go (absorbGo_append_of_inr d step hval)
  · have hb' : b = false := by
      unfold absorbFun at hb
      rw [dif_neg hex] at hb
      exact (Sum.inr.inj hb).symm
    subst hb'
    unfold absorbFun
    rw [dif_neg ?_]
    rintro ⟨fuel, hs⟩
    exact hex (absorbGo_isSome_of_append d step hs)

/-- **The absorbed distinguisher** (DESIGN §10.7 step 1): `d` with the
converter protocol fused in, as a distinguisher of the base systems. -/
noncomputable def absorb (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) : PFunDDS.DDD X Y :=
  ⟨absorbFun d step, stopFinal_absorbFun d step⟩

@[simp] theorem absorb_val (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) :
    (absorb d step).val = absorbFun d step := rfl

/-! ### The joint run

`AbsRun t T mode`: the deterministic joint evolution of `d`, the converter,
and the base system `s` — `t` is the base-side (Def 3.7) transcript so far,
`T` the composite-side transcript so far, `mode` the converter's round state.
The composite-side answers recorded in `T` are *claimed* by `roundEnd` and
certified against `applyG` by `absRun_driveOuter`. -/

section Correspondence

open PFunConverter
open scoped PFunDDS

variable (d : PFunDDS.DDD U V) (step : U → List Y → X ⊕ V)
  (s : PFunDDS.DDS X Y)

inductive AbsRun :
    List (X × Option Y) → List (U × Option V) → Option (U × List Y) → Prop
  | init : AbsRun [] [] none
  | dquery {t T u} (hr : AbsRun t T none)
      (hd : d.val (PFunDDS.transcriptOutputs T) = Sum.inl u) :
      AbsRun t T (some (u, []))
  | roundEnd {t T u ys v} (hr : AbsRun t T (some (u, ys)))
      (hstep : step u ys = Sum.inr v) :
      AbsRun t (T ++ [(u, some v)]) none
  | consume {t T u ys x y} (hr : AbsRun t T (some (u, ys)))
      (hstep : step u ys = Sum.inl x)
      (hy : PFunDDS.output (s⊥) (PFunDDS.transcriptInputs t ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some y) :
      AbsRun (t ++ [(x, some y)]) T (some (u, ys ++ [y]))

variable {d step s}

/-- Mode invariant: an open round was opened by a `d`-query. -/
theorem absRun_mode_dval :
    ∀ {t T mode}, AbsRun d step s t T mode →
      ∀ {u : U} {ys : List Y}, mode = some (u, ys) →
      d.val (PFunDDS.transcriptOutputs T) = Sum.inl u := by
  intro t T mode h
  induction h with
  | init => intro u ys hm; exact absurd hm (by simp)
  | dquery hr hd ih =>
      intro u' ys' hm
      have h1 : _ = u' := congrArg Prod.fst (Option.some.inj hm)
      rw [← h1]
      exact hd
  | roundEnd hr hstep ih => intro u ys hm; exact absurd hm (by simp)
  | consume hr hstep hy ih =>
      intro u' ys' hm
      have h1 : _ = u' := congrArg Prod.fst (Option.some.inj hm)
      rw [← h1]
      exact ih rfl

/-- **Replay composition**: a `go`-run from a reachable joint state embeds
into a `go`-run from the initial state over the recorded base answers. -/
theorem absorbGo_replay :
    ∀ {t T mode}, AbsRun d step s t T mode →
      ∀ {fuel : ℕ} {h' : List (Option Y)} {m : X ⊕ Bool},
      absorbGo d step fuel (PFunDDS.transcriptOutputs T) mode h' = some m →
      ∃ fuel', absorbGo d step fuel' [] none
        (PFunDDS.transcriptOutputs t ++ h') = some m := by
  intro t T mode h
  induction h with
  | init =>
      intro fuel h' m hm
      exact ⟨fuel, hm⟩
  | dquery hr hd ih =>
      intro fuel h' m hm
      refine ih (fuel := fuel + 1) ?_
      rw [absorbGo, hd]
      exact hm
  | roundEnd hr hstep ih =>
      rename_i t' T' u ys v
      intro fuel h' m hm
      have hout : PFunDDS.transcriptOutputs (T' ++ [(u, some v)])
          = PFunDDS.transcriptOutputs T' ++ [some v] := by
        simp [PFunDDS.transcriptOutputs]
      rw [hout] at hm
      refine ih (fuel := fuel + 1) ?_
      rw [absorbGo, hstep]
      exact hm
  | consume hr hstep hy ih =>
      rename_i t' T' u ys x y
      intro fuel h' m hm
      have hpre : absorbGo d step (fuel + 1) (PFunDDS.transcriptOutputs T')
          (some (u, ys)) (some y :: h') = some m := by
        rw [absorbGo, hstep]
        exact hm
      obtain ⟨fuel', hf⟩ := ih hpre
      refine ⟨fuel', ?_⟩
      have hout : PFunDDS.transcriptOutputs (t' ++ [(x, some y)])
          = PFunDDS.transcriptOutputs t' ++ [some y] := by
        simp [PFunDDS.transcriptOutputs]
      rw [hout, List.append_assoc]
      exact hf

/-- The absorbed distinguisher's move at a recorded history is the machine's
move from the corresponding joint state. -/
theorem absorb_val_of_run {t T mode} (hr : AbsRun d step s t T mode)
    {fuel : ℕ} {m : X ⊕ Bool}
    (hrun : absorbGo d step fuel (PFunDDS.transcriptOutputs T) mode [] = some m) :
    absorbFun d step (PFunDDS.transcriptOutputs t) = m := by
  obtain ⟨fuel', hf⟩ := absorbGo_replay hr hrun
  rw [List.append_nil] at hf
  exact absorbFun_eq_of_go hf

/-- **Extraction**: a `go`-run from a reachable state that produces a move
lands, after internal steps, at either a pending query or a `d`-verdict. -/
theorem absorbGo_run_extract :
    ∀ {fuel : ℕ} {t T mode} {m : X ⊕ Bool},
      AbsRun d step s t T mode →
      absorbGo d step fuel (PFunDDS.transcriptOutputs T) mode [] = some m →
      (∃ T' u ys x, AbsRun d step s t T' (some (u, ys)) ∧
        step u ys = Sum.inl x ∧ m = Sum.inl x) ∨
      (∃ T' b, AbsRun d step s t T' none ∧
        d.val (PFunDDS.transcriptOutputs T') = Sum.inr b ∧ m = Sum.inr b) := by
  intro fuel
  induction fuel with
  | zero => intro t T mode m _ hm; simp [absorbGo] at hm
  | succ n ih =>
      intro t T mode m hr hm
      cases mode with
      | none =>
          rw [absorbGo] at hm
          cases hd : d.val (PFunDDS.transcriptOutputs T) with
          | inr b =>
              rw [hd] at hm
              refine Or.inr ⟨T, b, hr, hd, ?_⟩
              simpa using (Option.some.inj hm).symm
          | inl u =>
              rw [hd] at hm
              exact ih (AbsRun.dquery hr hd) hm
      | some p =>
          obtain ⟨u, ys⟩ := p
          rw [absorbGo] at hm
          cases hs : step u ys with
          | inr v =>
              rw [hs] at hm
              have hr' := AbsRun.roundEnd hr hs
              have hm' : absorbGo d step n
                  (PFunDDS.transcriptOutputs (T ++ [(u, some v)])) none []
                    = some m := by
                simpa [PFunDDS.transcriptOutputs] using hm
              exact ih hr' hm'
          | inl x =>
              rw [hs] at hm
              refine Or.inl ⟨T, u, ys, x, hr, hs, ?_⟩
              simpa using (Option.some.inj hm).symm

/-- Base-side alignment: the recorded base transcript is a genuine Def 3.7
transcript prefix of `s` against the absorbed distinguisher. -/
theorem absRun_transcript_base :
    ∀ {t T mode}, AbsRun d step s t T mode →
      PFunDDS.Transcript s (PFunDDS.ddToDDE (absorb d step)) t := by
  intro t T mode h
  induction h with
  | init => exact PFunDDS.Transcript.nil
  | dquery hr hd ih => exact ih
  | roundEnd hr hstep ih => exact ih
  | consume hr hstep hy ih =>
      rename_i t T u ys x y
      have hmove : absorbFun d step (PFunDDS.transcriptOutputs t)
          = Sum.inl x := by
        refine absorb_val_of_run hr (fuel := 1) ?_
        rw [absorbGo, hstep]
      have he : PFunDDS.ddToDDE (absorb d step)
          (PFunDDS.transcriptOutputs t) = some x := by
        show (match (absorb d step).val (PFunDDS.transcriptOutputs t) with
          | Sum.inl x => some x
          | Sum.inr _ => none) = some x
        rw [absorb_val, hmove]
      have := PFunDDS.Transcript.snoc (S := s)
        (e := PFunDDS.ddToDDE (absorb d step)) ih he
      rw [show (PFunDDS.output (s⊥)
          (PFunDDS.transcriptInputs t ++ [x]) (by
            rw [PFunDDS.dom_fullyDefined]; simp)) = some y from hy] at this
      exact this

/-- **Reverse replay**: an initial-state run over the recorded answers (plus a
remainder) factors through the reachable joint state — the machine
deterministically re-traces its own history. -/
theorem absorbGo_replay_rev :
    ∀ {t T mode}, AbsRun d step s t T mode →
      ∀ {fuel : ℕ} {h' : List (Option Y)} {m : X ⊕ Bool},
      absorbGo d step fuel [] none
        (PFunDDS.transcriptOutputs t ++ h') = some m →
      ∃ fuel', absorbGo d step fuel' (PFunDDS.transcriptOutputs T) mode h'
        = some m := by
  intro t T mode h
  induction h with
  | init =>
      intro fuel h' m hm
      exact ⟨fuel, hm⟩
  | dquery hr hd ih =>
      intro fuel h' m hm
      obtain ⟨fuel', hf⟩ := ih hm
      rcases fuel' with _ | k
      · simp [absorbGo] at hf
      · rw [absorbGo, hd] at hf
        exact ⟨k, hf⟩
  | roundEnd hr hstep ih =>
      rename_i t' T' u ys v
      intro fuel h' m hm
      obtain ⟨fuel', hf⟩ := ih hm
      rcases fuel' with _ | k
      · simp [absorbGo] at hf
      · rw [absorbGo, hstep] at hf
        refine ⟨k, ?_⟩
        have hout : PFunDDS.transcriptOutputs (T' ++ [(u, some v)])
            = PFunDDS.transcriptOutputs T' ++ [some v] := by
          simp [PFunDDS.transcriptOutputs]
        rw [hout]
        exact hf
  | consume hr hstep hy ih =>
      rename_i t' T' u ys x y
      intro fuel h' m hm
      have hm' : absorbGo d step fuel [] none
          (PFunDDS.transcriptOutputs t' ++ (some y :: h')) = some m := by
        have hout : PFunDDS.transcriptOutputs (t' ++ [(x, some y)])
            = PFunDDS.transcriptOutputs t' ++ [some y] := by
          simp [PFunDDS.transcriptOutputs]
        rw [hout, List.append_assoc] at hm
        exact hm
      obtain ⟨fuel', hf⟩ := ih hm'
      rcases fuel' with _ | k
      · simp [absorbGo] at hf
      · rw [absorbGo, hstep] at hf
        exact ⟨k, hf⟩

/-- A non-default value of the absorbed distinguisher comes from a genuine
replay run. -/
theorem absorbFun_go_of_ne_default {h : List (Option Y)} {m : X ⊕ Bool}
    (hv : absorbFun d step h = m) (hne : m ≠ Sum.inr false) :
    ∃ fuel, absorbGo d step fuel [] none h = some m := by
  by_cases hex : ∃ fuel, (absorbGo d step fuel [] none h).isSome
  · refine ⟨hex.choose, ?_⟩
    unfold absorbFun at hv
    rw [dif_pos hex] at hv
    rw [← Option.some_get hex.choose_spec, hv]
  · exfalso
    unfold absorbFun at hv
    rw [dif_neg hex] at hv
    exact hne hv.symm

/-- The `driveOuter` certification of the joint run: the composite-side
answers recorded in `T` come from a genuine `applyG` computation, and an open
round is a genuine `driveG` continuation. -/
theorem absRun_driveOuter (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s) :
    ∀ {t T mode}, AbsRun d step s t T mode →
      ∃ (ws : List V) (xs₀ : List X),
        PFunDDS.transcriptOutputs T = ws.map some ∧
        (∃ fuel, (ws, xs₀) ∈ CausalApply.driveOuter step s.1 fuel []
          (PFunDDS.transcriptInputs T)) ∧
        (mode = none → xs₀ = PFunDDS.transcriptInputs t) ∧
        (∀ (u : U) (ys : List Y), mode = some (u, ys) →
          ∀ {fuel : ℕ} {m : V × List X},
            m ∈ CausalApply.driveG (step u) s.1 fuel
              (PFunDDS.transcriptInputs t) ys →
            ∃ fuel', m ∈ CausalApply.driveG (step u) s.1 fuel' xs₀ []) := by
  intro t T mode h
  induction h with
  | init =>
      refine ⟨[], [], by simp [PFunDDS.transcriptOutputs], ⟨0, ?_⟩,
        fun _ => rfl, fun u ys hm => absurd hm (by simp)⟩
      show ([], []) ∈ CausalApply.driveOuter step s.1 0 [] []
      simp [CausalApply.driveOuter]
  | dquery hr hd ih =>
      obtain ⟨ws, xs₀, h1, h2, h3, h4⟩ := ih
      refine ⟨ws, xs₀, h1, h2, fun hm => absurd hm (by simp), ?_⟩
      intro u' ys' hm fuel m hmem
      have hu : _ = u' := congrArg Prod.fst (Option.some.inj hm)
      have hys : ([] : List Y) = ys' := congrArg Prod.snd (Option.some.inj hm)
      subst hu
      subst hys
      rw [h3 rfl]
      exact ⟨fuel, hmem⟩
  | roundEnd hr hstep ih =>
      rename_i t' T' u ys v
      obtain ⟨ws, xs₀, h1, h2, h3, h4⟩ := ih
      obtain ⟨fuel₁, hrun₁⟩ := h2
      have hround : (v, PFunDDS.transcriptInputs t') ∈
          CausalApply.driveG (step u) s.1 1
            (PFunDDS.transcriptInputs t') ys := by
        simp only [CausalApply.driveG, hstep]
        exact Part.mem_some _
      obtain ⟨fuel₂, hround'⟩ := h4 u ys rfl hround
      refine ⟨ws ++ [v], PFunDDS.transcriptInputs t', ?_, ?_, fun _ => rfl,
        fun u' ys' hm => absurd hm (by simp)⟩
      · simp only [PFunDDS.transcriptOutputs, List.map_append] at h1 ⊢
        rw [h1]
        simp
      · refine ⟨max fuel₁ fuel₂, ?_⟩
        have hTx : PFunDDS.transcriptInputs (T' ++ [(u, some v)])
            = PFunDDS.transcriptInputs T' ++ [u] := by
          simp [PFunDDS.transcriptInputs]
        rw [hTx, CausalApply.driveOuter_append]
        rw [Part.mem_bind_iff]
        refine ⟨(ws, xs₀),
          CausalApply.driveOuter_mono_le step s.1 (le_max_left _ _) hrun₁, ?_⟩
        rw [Part.mem_map_iff]
        refine ⟨([v], PFunDDS.transcriptInputs t'), ?_, rfl⟩
        show _ ∈ (CausalApply.driveG (step u) s.1 (max fuel₁ fuel₂) xs₀ []).bind _
        rw [Part.mem_bind_iff]
        refine ⟨(v, PFunDDS.transcriptInputs t'),
          CausalApply.driveG_mono_le (step u) s.1 (le_max_right _ _) hround', ?_⟩
        simp [CausalApply.driveOuter]
  | consume hr hstep hy ih =>
      rename_i t' T' u ys x y
      obtain ⟨ws, xs₀, h1, h2, h3, h4⟩ := ih
      refine ⟨ws, xs₀, h1, ?_, fun hm => absurd hm (by simp), ?_⟩
      · have hTx : PFunDDS.transcriptInputs T' = PFunDDS.transcriptInputs T' :=
          rfl
        exact h2
      · intro u' ys' hm fuel m hmem
        have hu : u = u' := congrArg Prod.fst (Option.some.inj hm)
        have hys : ys ++ [y] = ys' := congrArg Prod.snd (Option.some.inj hm)
        subst hu
        subst hys
        -- prepend the consume step
        have hliv : PFunDDS.transcriptInputs t' ∈ PFunDDS.dom s ∨
            PFunDDS.transcriptInputs t' = [] := by
          rcases List.eq_nil_or_concat (PFunDDS.transcriptInputs t')
            with hnil | ⟨l', a', hcat⟩
          · exact Or.inr hnil
          · exact Or.inl (hs _ (by rw [hcat]; simp))
        obtain ⟨hdomx, houtS⟩ :=
          PFunDDS.mem_of_output_fullyDefined_append_eq_some s
            (PFunDDS.transcriptInputs t') x hliv hy
        have hymem : y ∈ s.1 (PFunDDS.transcriptInputs t' ++ [x]) := by
          rw [← houtS]
          exact Part.get_mem _
        have hpre : m ∈ CausalApply.driveG (step u) s.1 (fuel + 1)
            (PFunDDS.transcriptInputs t') ys := by
          simp only [CausalApply.driveG, hstep]
          rw [Part.mem_bind_iff]
          refine ⟨y, hymem, ?_⟩
          have hin : PFunDDS.transcriptInputs (t' ++ [(x, some y)])
              = PFunDDS.transcriptInputs t' ++ [x] := by
            simp [PFunDDS.transcriptInputs]
          rw [← hin]
          exact hmem
        exact h4 u ys rfl hpre

/-- The composite system's answer at a completed round is the recorded one. -/
theorem absRun_comp_output (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s)
    {t : List (X × Option Y)} {T : List (U × Option V)} {u : U} {v : V}
    (hr : AbsRun d step s t (T ++ [(u, some v)]) none) :
    PFunDDS.output ((CausalApply.applyG step s.1)⊥)
        (PFunDDS.transcriptInputs T ++ [u])
        (by rw [PFunDDS.dom_fullyDefined]; simp)
      = some v := by
  obtain ⟨ws, xs₀, h1, h2, h3, h4⟩ := absRun_driveOuter hs hr
  have h1' : PFunDDS.transcriptOutputs T ++ [some v] = ws.map some := by
    simpa [PFunDDS.transcriptOutputs] using h1
  have hwsne : ws ≠ [] := by
    intro hnil
    rw [hnil] at h1'
    simp at h1'
  obtain ⟨ws', w, rfl⟩ := (List.eq_nil_or_concat ws).resolve_left hwsne
  have hw : v = w := by
    have h2' := congrArg List.getLast? h1'
    rw [List.getLast?_concat] at h2'
    rw [show (ws'.concat w).map some = ws'.map some ++ [some w] from by
      simp] at h2'
    rw [List.getLast?_concat] at h2'
    exact Option.some.inj (Option.some.inj h2')
  subst hw
  obtain ⟨fuel, hrun⟩ := h2
  have hTx : PFunDDS.transcriptInputs (T ++ [(u, some v)])
      = PFunDDS.transcriptInputs T ++ [u] := by
    simp [PFunDDS.transcriptInputs]
  rw [hTx] at hrun
  have hvmem : v ∈ CausalApply.applyRawAt step s.1 fuel
      (PFunDDS.transcriptInputs T ++ [u]) := by
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(ws'.concat v, xs₀), hrun, ?_⟩
    rw [List.concat_eq_append, List.getLast?_concat]
  have hvraw : v ∈ CausalApply.applyRaw step s.1
      (PFunDDS.transcriptInputs T ++ [u]) := by
    rw [CausalApply.mem_applyRaw]
    exact ⟨fuel, hvmem⟩
  have hdom : PFunDDS.transcriptInputs T ++ [u]
      ∈ PFunDDS.dom (CausalApply.applyG step s.1) := by
    rw [PFunDDS.dom_def, PFun.mem_dom]
    exact ⟨v, hvraw⟩
  have hliv : PFunDDS.transcriptInputs T
        ∈ PFunDDS.dom (CausalApply.applyG step s.1) ∨
      PFunDDS.transcriptInputs T = [] := by
    rcases List.eq_nil_or_concat (PFunDDS.transcriptInputs T)
      with hnil | ⟨l', a', hcat⟩
    · exact Or.inr hnil
    · exact Or.inl (PFunDDS.prefix_closed _ (List.prefix_append _ _)
        (by rw [hcat]; simp) hdom)
  rw [PFunDDS.output_fullyDefined_append_of_mem
    (CausalApply.applyG step s.1) _ u hliv hdom]
  exact congrArg some (Part.mem_unique (Part.get_mem _) hvraw)

/-- Composite-side alignment: the recorded composite transcript is a genuine
Def 3.7 transcript prefix of the applied system against `d`. -/
theorem absRun_transcript_comp
    (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s) :
    ∀ {t T mode}, AbsRun d step s t T mode →
      PFunDDS.Transcript (CausalApply.applyG step s.1)
        (PFunDDS.ddToDDE d) T := by
  intro t T mode h
  induction h with
  | init => exact PFunDDS.Transcript.nil
  | dquery hr hd ih => exact ih
  | consume hr hstep hy ih => exact ih
  | roundEnd hr hstep ih =>
      rename_i t' T' u ys v
      have hd := absRun_mode_dval hr rfl
      have he : PFunDDS.ddToDDE d (PFunDDS.transcriptOutputs T') = some u := by
        show (match d.val (PFunDDS.transcriptOutputs T') with
          | Sum.inl x => some x
          | Sum.inr _ => none) = some u
        rw [hd]
      have hsnoc := PFunDDS.Transcript.snoc
        (S := CausalApply.applyG step s.1) (e := PFunDDS.ddToDDE d) ih he
      have hout := absRun_comp_output hs (AbsRun.roundEnd hr hstep)
      rw [show PFunDDS.output ((CausalApply.applyG step s.1)⊥)
          (PFunDDS.transcriptInputs T' ++ [u])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some v from hout]
        at hsnoc
      exact hsnoc

/-- Round completion under the Def 3.8 bound and totality. -/
theorem absRun_round_completes {B : ℕ}
    (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s)
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length →
      ∃ v, step u ys = Sum.inr v) :
    ∀ (k : ℕ) {t : List (X × Option Y)} {T : List (U × Option V)}
      {u : U} {ys : List Y},
      AbsRun d step s t T (some (u, ys)) → B ≤ ys.length + k →
      ∃ t' v, AbsRun d step s t' (T ++ [(u, some v)]) none := by
  intro k
  induction k with
  | zero =>
      intro t T u ys hr hk
      obtain ⟨v, hv⟩ := hB u ys (by omega)
      exact ⟨t, v, AbsRun.roundEnd hr hv⟩
  | succ n ih =>
      intro t T u ys hr hk
      cases hst : step u ys with
      | inr v => exact ⟨t, v, AbsRun.roundEnd hr hst⟩
      | inl x =>
          have hliv : PFunDDS.transcriptInputs t ∈ PFunDDS.dom s ∨
              PFunDDS.transcriptInputs t = [] := by
            rcases List.eq_nil_or_concat (PFunDDS.transcriptInputs t)
              with hnil | ⟨l', a', hcat⟩
            · exact Or.inr hnil
            · exact Or.inl (hs _ (by rw [hcat]; simp))
          have hdom : PFunDDS.transcriptInputs t ++ [x] ∈ PFunDDS.dom s :=
            hs _ (by simp)
          have hy := PFunDDS.output_fullyDefined_append_of_mem s _ x hliv hdom
          have hr' := AbsRun.consume hr hst hy
          refine ih hr' ?_
          simp only [List.length_append, List.length_singleton]
          omega

/-- Every composite-side transcript prefix is a joint-run state. -/
theorem transcript_comp_reachable {B : ℕ}
    (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s)
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length →
      ∃ v, step u ys = Sum.inr v) :
    ∀ m : ℕ, ∃ t T, AbsRun d step s t T none ∧
      PFunDDS.transcript (CausalApply.applyG step s.1)
        (PFunDDS.ddToDDE d) m = T := by
  intro m
  induction m with
  | zero => exact ⟨[], [], AbsRun.init, rfl⟩
  | succ n ih =>
      obtain ⟨t, T, hr, heq⟩ := ih
      subst heq
      simp only [PFunDDS.transcript]
      cases hd : d.val (PFunDDS.transcriptOutputs
          (PFunDDS.transcript (CausalApply.applyG step s.1)
            (PFunDDS.ddToDDE d) n)) with
      | inr b =>
          have he : PFunDDS.ddToDDE d (PFunDDS.transcriptOutputs
              (PFunDDS.transcript (CausalApply.applyG step s.1)
                (PFunDDS.ddToDDE d) n)) = none := by
            show (match d.val _ with
              | Sum.inl x => some x
              | Sum.inr _ => none) = none
            rw [hd]
          rw [he]
          exact ⟨t, _, hr, rfl⟩
      | inl u =>
          have he : PFunDDS.ddToDDE d (PFunDDS.transcriptOutputs
              (PFunDDS.transcript (CausalApply.applyG step s.1)
                (PFunDDS.ddToDDE d) n)) = some u := by
            show (match d.val _ with
              | Sum.inl x => some x
              | Sum.inr _ => none) = some u
            rw [hd]
          rw [he]
          have hr₁ := AbsRun.dquery hr hd
          obtain ⟨t', v, hr'⟩ := absRun_round_completes hs hB B hr₁ (by simp)
          have hout := absRun_comp_output hs hr'
          refine ⟨t', _, hr', ?_⟩
          show PFunDDS.transcript (CausalApply.applyG step s.1)
              (PFunDDS.ddToDDE d) n ++
              [(u, PFunDDS.output ((CausalApply.applyG step s.1)⊥)
                (PFunDDS.transcriptInputs
                  (PFunDDS.transcript (CausalApply.applyG step s.1)
                    (PFunDDS.ddToDDE d) n) ++ [u])
                (by rw [PFunDDS.dom_fullyDefined]; simp))]
            = _
          rw [show PFunDDS.output ((CausalApply.applyG step s.1)⊥)
              (PFunDDS.transcriptInputs
                (PFunDDS.transcript (CausalApply.applyG step s.1)
                  (PFunDDS.ddToDDE d) n) ++ [u])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = some v from hout]

/-- Every base-side transcript prefix is a joint-run state. -/
theorem transcript_base_reachable
    (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s) :
    ∀ n : ℕ, ∃ t T mode, AbsRun d step s t T mode ∧
      PFunDDS.transcript s (PFunDDS.ddToDDE (absorb d step)) n = t := by
  intro n
  induction n with
  | zero => exact ⟨[], [], none, AbsRun.init, rfl⟩
  | succ n ih =>
      obtain ⟨t, T, mode, hr, heq⟩ := ih
      subst heq
      simp only [PFunDDS.transcript]
      cases hA : absorbFun d step (PFunDDS.transcriptOutputs
          (PFunDDS.transcript s
            (PFunDDS.ddToDDE (absorb d step)) n)) with
      | inr b =>
          have he : PFunDDS.ddToDDE (absorb d step)
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE (absorb d step)) n)) = none := by
            show (match (absorb d step).val _ with
              | Sum.inl x => some x
              | Sum.inr _ => none) = none
            rw [absorb_val, hA]
          rw [he]
          exact ⟨_, T, mode, hr, rfl⟩
      | inl x =>
          have he : PFunDDS.ddToDDE (absorb d step)
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE (absorb d step)) n)) = some x := by
            show (match (absorb d step).val _ with
              | Sum.inl x => some x
              | Sum.inr _ => none) = some x
            rw [absorb_val, hA]
          rw [he]
          obtain ⟨fuel, hgo⟩ := absorbFun_go_of_ne_default hA (by simp)
          have hgo' : absorbGo d step fuel [] none
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE (absorb d step)) n) ++ [])
              = some (Sum.inl x) := by
            rw [List.append_nil]
            exact hgo
          obtain ⟨fuel', hstate⟩ := absorbGo_replay_rev hr hgo'
          rcases absorbGo_run_extract hr hstate with
            ⟨T', u, ys, x', hr', hstep', hx'⟩ | ⟨T', b, hr', hd', hbad⟩
          · have hx'' : x' = x := (Sum.inl.inj hx').symm
            subst hx''
            have hliv : PFunDDS.transcriptInputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE (absorb d step)) n) ∈ PFunDDS.dom s ∨
                PFunDDS.transcriptInputs
                  (PFunDDS.transcript s
                    (PFunDDS.ddToDDE (absorb d step)) n) = [] := by
              rcases List.eq_nil_or_concat (PFunDDS.transcriptInputs
                  (PFunDDS.transcript s
                    (PFunDDS.ddToDDE (absorb d step)) n))
                with hnil | ⟨l', a', hcat⟩
              · exact Or.inr hnil
              · exact Or.inl (hs _ (by rw [hcat]; simp))
            have hdom : PFunDDS.transcriptInputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE (absorb d step)) n) ++ [x']
                  ∈ PFunDDS.dom s :=
              hs _ (by simp)
            have hy := PFunDDS.output_fullyDefined_append_of_mem s _ x'
              hliv hdom
            refine ⟨_, T',
              some (u, ys ++ [PFunDDS.output s
                (PFunDDS.transcriptInputs
                  (PFunDDS.transcript s
                    (PFunDDS.ddToDDE (absorb d step)) n) ++ [x']) hdom]),
              AbsRun.consume hr' hstep' hy, ?_⟩
            show PFunDDS.transcript s (PFunDDS.ddToDDE (absorb d step)) n ++
                [(x', PFunDDS.output (s⊥)
                  (PFunDDS.transcriptInputs
                    (PFunDDS.transcript s
                      (PFunDDS.ddToDDE (absorb d step)) n) ++ [x'])
                  (by rw [PFunDDS.dom_fullyDefined]; simp))]
              = _
            rw [show PFunDDS.output (s⊥)
                (PFunDDS.transcriptInputs
                  (PFunDDS.transcript s
                    (PFunDDS.ddToDDE (absorb d step)) n) ++ [x'])
                (by rw [PFunDDS.dom_fullyDefined]; simp)
              = some (PFunDDS.output s
                (PFunDDS.transcriptInputs
                  (PFunDDS.transcript s
                    (PFunDDS.ddToDDE (absorb d step)) n) ++ [x']) hdom)
              from hy]
          · exact absurd hbad (by simp)

/-- **The verdict correspondence** (DESIGN §10.7 step 2): the absorbed
distinguisher accepts the base system exactly when `d` accepts the applied
system. -/
theorem verdict_absorb_iff {B : ℕ}
    (hs : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom s)
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length →
      ∃ v, step u ys = Sum.inr v) :
    PFunDDS.verdict (absorb d step) s ↔
      PFunDDS.verdict d (CausalApply.applyG step s.1) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨t, T, mode, hr, heq⟩ := transcript_base_reachable hs n
    rw [heq] at hn
    rw [show (absorb d step).val = absorbFun d step from rfl] at hn
    obtain ⟨fuel, hgo⟩ := absorbFun_go_of_ne_default hn (by simp)
    have hgo' : absorbGo d step fuel [] none
        (PFunDDS.transcriptOutputs t ++ []) = some (Sum.inr true) := by
      rw [List.append_nil]
      exact hgo
    obtain ⟨fuel', hstate⟩ := absorbGo_replay_rev hr hgo'
    rcases absorbGo_run_extract hr hstate with
      ⟨T', u, ys, x, hr', hstep', hbad⟩ | ⟨T', b, hr', hd', hb⟩
    · exact absurd hbad (by simp)
    · have hb' : b = true := (Sum.inr.inj hb).symm
      subst hb'
      have htr := absRun_transcript_comp hs hr'
      obtain ⟨m, hm⟩ := (PFunDDS.transcript_mem_iff _ _ _).mp htr
      exact ⟨m, by rw [hm]; exact hd'⟩
  · rintro ⟨m, hm⟩
    obtain ⟨t, T, hr, heq⟩ := transcript_comp_reachable hs hB m
    rw [heq] at hm
    have hAval : absorbFun d step (PFunDDS.transcriptOutputs t)
        = Sum.inr true := by
      refine absorb_val_of_run hr (fuel := 1) ?_
      rw [absorbGo, hm]
    have htr := absRun_transcript_base hr
    obtain ⟨n, hn⟩ := (PFunDDS.transcript_mem_iff _ _ _).mp htr
    exact ⟨n, by rw [hn]; exact hAval⟩

end Correspondence

/-! ### The law-level lift and the DPI endpoint (DESIGN §10.7 steps 3–4) -/

section Lift

open PFunConverter

/-- Pushforward transport of `winProb` on the winner side. -/
theorem winProb_fTransform_left {Winner Winner' Game : Type*}
    (win : Winner' → Game → Prop) (f : Winner → Winner')
    (W : Dist Winner) (G : Dist Game) :
    GamePerf.winProb win (Dist.fTransform f W) G
      = GamePerf.winProb (fun w g => win (f w) g) W G := by
  unfold GamePerf.winProb
  show Finsupp.sum (Finsupp.mapDomain f W) _ = _
  rw [Finsupp.sum_mapDomain_index]
  · intro b
    simp
  · intro b m₁ m₂
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun g _ => ?_
    ring

/-- Pushforward transport of `winProb` on the game side. -/
theorem winProb_fTransform_right {Winner Game Game' : Type*}
    (win : Winner → Game' → Prop) (f : Game → Game')
    (W : Dist Winner) (G : Dist Game) :
    GamePerf.winProb win W (Dist.fTransform f G)
      = GamePerf.winProb (fun w g => win w (f g)) W G := by
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun w _ => ?_
  show Finsupp.sum (Finsupp.mapDomain f G) _ = _
  rw [Finsupp.sum_mapDomain_index]
  · intro b
    simp
  · intro b m₁ m₂
    ring

/-- `winProb` respects support-pointwise equivalent winning predicates. -/
theorem winProb_congr_support {Winner Game : Type*}
    {win win' : Winner → Game → Prop} (W : Dist Winner) (G : Dist Game)
    (h : ∀ g ∈ G.support, ∀ w, win w g ↔ win' w g) :
    GamePerf.winProb win W G = GamePerf.winProb win' W G := by
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun w _ => ?_
  refine Finsupp.sum_congr fun g hg => ?_
  by_cases hwin : win w g
  · rw [if_pos hwin, if_pos ((h g hg w).mp hwin)]
  · rw [if_neg hwin, if_neg (fun hw' => hwin ((h g hg w).mpr hw'))]

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- **The law-level lift** (DESIGN §10.7 step 3): the absorbed distinguisher
distribution achieves against the base law exactly what `D` achieves against
the applied law. -/
theorem verdictProb_absorb (step : U → List Y → X ⊕ V) {B : ℕ}
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length → ∃ v, step u ys = Sum.inr v)
    (D : Dist (PFunDDS.DDD U V)) (S : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) :
    verdictProb (Dist.fTransform (fun dd => absorb dd step) D) S
      = verdictProb D (PFunPDS.applyDDC (DDC.ofStep step) S) := by
  unfold verdictProb PFunPDS.applyDDC
  rw [winProb_fTransform_left, winProb_fTransform_right]
  refine winProb_congr_support D S ?_
  intro g hg dd
  have hs' : ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom g :=
    fun xs hne => hS g hg xs hne
  rw [show DDC.apply (DDC.ofStep step) g = CausalApply.applyG step g.1 from
    DDC.apply_ofStep step g]
  exact verdict_absorb_iff hs' hB

/-- Absorption preserves the achieved advantage exactly. -/
theorem advantage_absorb (step : U → List Y → X ⊕ V) {B : ℕ}
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length → ∃ v, step u ys = Sum.inr v)
    (D : Dist (PFunDDS.DDD U V)) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T) :
    advantage D (PFunPDS.applyDDC (DDC.ofStep step) S)
        (PFunPDS.applyDDC (DDC.ofStep step) T)
      = advantage (Dist.fTransform (fun dd => absorb dd step) D) S T := by
  unfold advantage
  rw [verdictProb_absorb step hB D S hS, verdictProb_absorb step hB D T hT]

/-- **Converter DPI** (DESIGN §10.7 step 4): applying a converter cannot
increase the maximal distinguishing advantage — converters are 1-Lipschitz.
Hypotheses: the Def 3.8 round bound on the converter, and the resource-view
totality of both laws (CR18's "defined on the histories under discussion"). -/
theorem maxAdvantage_applyDDC_le (step : U → List Y → X ⊕ V) {B : ℕ}
    (hB : ∀ (u : U) (ys : List Y), B ≤ ys.length → ∃ v, step u ys = Sum.inr v)
    (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T) :
    maxAdvantage (PFunPDS.applyDDC (DDC.ofStep step) S)
        (PFunPDS.applyDDC (DDC.ofStep step) T)
      ≤ maxAdvantage S T := by
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  rw [advantage_absorb step hB D S T hS hT]
  refine le_csSup (bddAbove_advantage_image S T) ?_
  exact ⟨Dist.fTransform (fun dd => absorb dd step) D,
    Dist.fTransform_isProbDist _ hD, rfl⟩

end Lift


/-! ## The filtered (query-budgeted) surface

Generic `maxAdvantage` lemmas over the `[q]` filter — the triangle, filter
monotonicity, the exactly-`q` padding bridge, the de-duplicating cache
converter (`PFunDDS.Cache`), and the absorbed distinguisher's query bound.
Relocated verbatim from `HTechnique/HCTR2Computational.lean`'s generic CR18
section (2026-07-10); protocol-independent, consumed by the HCTR2
computational leg and the CBC-MAC URP corollary alike. -/


open scoped PFunDDS

/-! ## Generic `maxAdvantage` lemmas -/

section MaxAdvantageLemmas

-- (universe levels inherited from the file header)

variable {X : Type u} {Y : Type v}

/-- **Triangle inequality for the maximal distinguishing advantage.**  The
signed advantage is exactly additive per distinguisher
(`∆^D(S,U) = ∆^D(S,T) + ∆^D(T,U)`), so the supremum is subadditive. -/
theorem maxAdvantage_triangle (S T U : PFunPDS X Y) :
    Δ(S, U) ≤ Δ(S, T) + Δ(T, U) := by
  have h : ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
      advantage D S U ≤ Δ(S, T) + Δ(T, U) := by
    intro D hD
    have h3 : advantage D S U = advantage D S T + advantage D T U := by
      unfold advantage; ring
    rw [h3]
    exact add_le_add (advantage_le_maxAdvantage D S T hD)
      (advantage_le_maxAdvantage D T U hD)
  exact maxAdvantage_le_of_forall_advantage_le h

/-- Against a total system, the `[q]` filter is invisible to the first `q`
rounds of the CR18 Def 3.7 interaction: the transcripts agree up to round
`q`. -/
theorem PFunDDS.transcript_filterQueries_eq_of_le
    (S : PFunDDS.DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom S) (e : PFunDDS.DDE X Y) :
    ∀ {n : ℕ}, n ≤ q →
      PFunDDS.transcript (PFunDDS.filterQueries q S) e n
        = PFunDDS.transcript S e n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hEq := ih (Nat.le_of_succ_le hn)
      rcases hfire : e (PFunDDS.transcript S e n)↓ᵧ with _ | x
      · rw [transcript_succ_stall (by rw [hEq]; exact hfire),
          transcript_succ_stall hfire, hEq]
      · rw [transcript_succ_fire (by rw [hEq]; exact hfire),
          transcript_succ_fire hfire, hEq]
        have hlen : (PFunDDS.transcript S e n)↓ₓ.length < q := by
          rw [transcriptInputs_length]
          exact lt_of_le_of_lt (transcript_length_le n) (Nat.lt_of_succ_le hn)
        have hxs : (PFunDDS.transcript S e n)↓ₓ ∈ PFunDDS.dom S ∨
            (PFunDDS.transcript S e n)↓ₓ = [] := by
          rcases eq_or_ne ((PFunDDS.transcript S e n)↓ₓ) [] with hnil | hne
          · exact Or.inr hnil
          · exact Or.inl (hS _ hne)
        have hdom : (PFunDDS.transcript S e n)↓ₓ ++ [x] ∈ PFunDDS.dom S :=
          hS _ (by simp)
        rw [PFunDDS.output_fullyDefined_filterQueries_of_total_lt S q hS _ x hlen,
          PFunDDS.output_fullyDefined_append_of_mem S _ x hxs hdom]

/-- For an exact-`q` distinguisher against a total system, the `[q]` filter is
invisible to the verdict. -/
theorem PFunDDS.verdict_filterQueries_iff_of_queriesExactly
    (d : PFunDDS.DDD X Y) (s : PFunDDS.DDS X Y) (q : ℕ)
    (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q) :
    PFunDDS.verdict d (PFunDDS.filterQueries q s) ↔ PFunDDS.verdict d s := by
  rw [PFunDDS.verdict_iff_at_exact d _ q hQ, PFunDDS.verdict_iff_at_exact d s q hQ,
    PFunDDS.transcript_filterQueries_eq_of_le s q hs (PFunDDS.ddToDDE d) le_rfl]

/-- For a distribution of exact-`q` distinguishers, the verdict probability
against `⌈q⌉S` equals the one against the total `S`. -/
theorem verdictProb_filterQueries_eq_of_queriesExactly (q : ℕ)
    (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q) :
    verdictProb D (⌈q⌉ S) = verdictProb D S := by
  unfold verdictProb PFunPDS.filterQueries
  rw [winProb_fTransform_right]
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun d hd => Finsupp.sum_congr fun s hs => ?_
  have hiff := PFunDDS.verdict_filterQueries_iff_of_queriesExactly d s q
    (hS s hs) (hQ d hd)
  by_cases hv : PFunDDS.verdict d s
  · simp [hv, hiff.mpr hv]
  · have hv' : ¬ PFunDDS.verdict d (PFunDDS.filterQueries q s) :=
      fun h => hv (hiff.mp h)
    simp [hv, hv']

/-- **`[q]`-filter monotonicity of the maximal distinguishing advantage**
(CR18 §4.10.1): `Δ(⌈q⌉S, ⌈q⌉T) ≤ Δ(S,T)` for total `S, T`.  Any distinguisher
of the filtered systems is dominated by its padded exact-`q` normal form
(`padDDDDist`), to which the filter is invisible. -/
theorem maxAdvantage_filterQueries_le (dummy : X) (q : ℕ)
    (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T) :
    Δ(⌈q⌉ S, ⌈q⌉ T) ≤ Δ(S, T) := by
  classical
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  have hQ := PFunDDS.padDDDDist_queriesExactly_support dummy q D
  calc advantage D (⌈q⌉ S) (⌈q⌉ T)
      = advantage (PFunDDS.padDDDDist dummy q D) (⌈q⌉ S) (⌈q⌉ T) :=
        (advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty
          dummy q D S T hS hT).symm
    _ = advantage (PFunDDS.padDDDDist dummy q D) S T := by
        unfold advantage
        rw [verdictProb_filterQueries_eq_of_queriesExactly q _ S hS hQ,
          verdictProb_filterQueries_eq_of_queriesExactly q _ T hT hQ]
    _ ≤ Δ(S, T) := advantage_le_maxAdvantage _ S T
        (PFunDDS.padDDDDist_isProbDist dummy q D hD)

end MaxAdvantageLemmas

/-! ## Distinguisher-side de-duplication cache (D1)

Against a *function-backed* system every query answer depends only on the
current query, so re-asking a query is free: the answer is already determined
by the transcript.  `cacheDDD` is the distinguisher-side mirror of the
derivation's `SelfAnswerFilter` (Derivation.lean §SelfAnswer): it replays a
distinguisher `d`, answering `d`'s *repeated* queries from its own recorded
history (`lookupAns`) and forwarding only *first occurrences* to the system.

The construction uses the advance/consume structural recursion of the
derivation (well-founded on the remaining query budget `N`, structural on the
answer supply — **no** fuel-with-absorbing-states), specialised to the concrete
filter `ptl h x := "x already appears in h"`, `det := lookupAns`.

UPSTREAM-CANDIDATE: this whole `Cache` block is generic CR18 machinery
(distinguisher-side dual of `SelfAnswerFilter`); it lives here only to keep the
migration surface frozen this phase. -/

namespace PFunDDS.Cache

open RandomSystems.CR18.PFunDDS

-- Several structural lemmas below live under the shared `[DecidableEq X]`
-- variable (needed by `lookupAns`) without using it; silence the linter.
set_option linter.unusedSectionVars false

-- (universe levels inherited from the file header)
variable {X : Type u} {Y : Type v} [DecidableEq X]

/-- The recorded answer of `x` in a pair-history `h` (first occurrence), or
`none` if `x` was never asked. -/
def lookupAns (h : List (X × Y)) (x : X) : Option Y :=
  (h.find? (fun p => decide (p.1 = x))).map Prod.snd

/-- Run `d` from the reconstructed pair-history `h` through self-answered
(already-asked) queries until it emits a *fresh* query (`some (Sum.inl x)`, not
yet appended), stops with a verdict (`some (Sum.inr b)`), or the history reaches
the budget `N` (`none`).  Well-founded on `N − h.length`; no fuel, no absorbing
terminal state. -/
def advance (N : ℕ) (d : DDD X Y) (h : List (X × Y)) :
    List (X × Y) × Option (X ⊕ Bool) :=
  match d.val (h.map fun p => some p.2) with
  | Sum.inr b => (h, some (Sum.inr b))
  | Sum.inl x =>
    match lookupAns h x with
    | some y => if _hlen : h.length < N then advance N d (h ++ [(x, y)]) else (h, none)
    | none => (h, some (Sum.inl x))
termination_by N - h.length
decreasing_by simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- Feed the real-answer supply to the advancing run: each supplied answer
resolves one forwarded (fresh) query.  Structural on the supply. -/
def consume (N : ℕ) (d : DDD X Y) (h : List (X × Y)) :
    List Y → List (X × Y) × Option (X ⊕ Bool)
  | [] => advance N d h
  | y :: ys =>
    match advance N d h with
    | (h', some (Sum.inl x)) => consume N d (h' ++ [(x, y)]) ys
    | (h', r) => (h', r)

@[simp] theorem consume_nil (N : ℕ) (d : DDD X Y) (h : List (X × Y)) :
    consume N d h [] = advance N d h := rfl

theorem consume_cons (N : ℕ) (d : DDD X Y) (h : List (X × Y)) (y : Y)
    (ys : List Y) :
    consume N d h (y :: ys) =
      match advance N d h with
      | (h', some (Sum.inl x)) => consume N d (h' ++ [(x, y)]) ys
      | (h', r) => (h', r) := rfl

/-- **`advance` master spec**: the result extends the input history, is
*absorbing* (re-running from the result reproduces the result), and a forwarded
query is *fresh* against the result history (`lookupAns h' x = none`) — the
source of `nodup`. -/
theorem advance_spec (N : ℕ) (d : DDD X Y) :
    ∀ (h h' : List (X × Y)) (r : Option (X ⊕ Bool)), advance N d h = (h', r) →
      h <+: h' ∧ advance N d h' = (h', r) ∧
        ∀ x, r = some (Sum.inl x) → lookupAns h' x = none := by
  suffices H : ∀ (fuel : ℕ) (h : List (X × Y)), N - h.length ≤ fuel →
      ∀ (h' : List (X × Y)) (r : Option (X ⊕ Bool)), advance N d h = (h', r) →
        h <+: h' ∧ advance N d h' = (h', r) ∧
          ∀ x, r = some (Sum.inl x) → lookupAns h' x = none from
    fun h h' r => H (N - h.length) h le_rfl h' r
  intro fuel
  induction fuel with
  | zero =>
    intro h hf h' r hadv
    have hnl : ¬ h.length < N := by omega
    rw [advance] at hadv
    rcases hd : d.val (h.map fun p => some p.2) with x | b
    · rw [hd] at hadv; dsimp only at hadv
      rcases hl : lookupAns h x with _ | y
      · rw [hl] at hadv; dsimp only at hadv
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
        refine ⟨List.prefix_rfl, ?_, ?_⟩
        · rw [advance, hd]; dsimp only; rw [hl]
        · rintro x' hx'; obtain rfl := Sum.inl.inj (Option.some.inj hx'); exact hl
      · rw [hl] at hadv; dsimp only at hadv
        rw [dif_neg hnl] at hadv
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
        exact ⟨List.prefix_rfl,
          by rw [advance, hd]; dsimp only; simp only [hl]; rw [dif_neg hnl],
          fun x hx => by simp at hx⟩
    · rw [hd] at hadv; dsimp only at hadv
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
      exact ⟨List.prefix_rfl, by rw [advance, hd], fun x hx => by simp at hx⟩
  | succ fuel ih =>
    intro h hf h' r hadv
    rw [advance] at hadv
    rcases hd : d.val (h.map fun p => some p.2) with x | b
    · rw [hd] at hadv; dsimp only at hadv
      rcases hl : lookupAns h x with _ | y
      · rw [hl] at hadv; dsimp only at hadv
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
        refine ⟨List.prefix_rfl, ?_, ?_⟩
        · rw [advance, hd]; dsimp only; rw [hl]
        · rintro x' hx'; obtain rfl := Sum.inl.inj (Option.some.inj hx'); exact hl
      · rw [hl] at hadv; dsimp only at hadv
        by_cases hlen : h.length < N
        · rw [dif_pos hlen] at hadv
          obtain ⟨hpre, hab, hnp⟩ := ih (h ++ [(x, y)])
            (by simp only [List.length_append, List.length_cons,
              List.length_nil]; omega) h' r hadv
          exact ⟨(List.prefix_append _ _).trans hpre, hab, hnp⟩
        · rw [dif_neg hlen] at hadv
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
          exact ⟨List.prefix_rfl,
            by rw [advance, hd]; dsimp only; simp only [hl]; rw [dif_neg hlen],
            fun x hx => by simp at hx⟩
    · rw [hd] at hadv; dsimp only at hadv
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hadv
      exact ⟨List.prefix_rfl, by rw [advance, hd], fun x hx => by simp at hx⟩

/-- A run ending with a pending forwarded query has that outcome re-derivable
from its final history. -/
theorem consume_some_advance (N : ℕ) (d : DDD X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (x : X),
      consume N d h ys = (h', some (Sum.inl x)) →
      advance N d h' = (h', some (Sum.inl x)) := by
  intro ys
  induction ys with
  | nil =>
    intro h h' x hc
    rw [consume_nil] at hc
    exact (advance_spec N d h h' _ hc).2.1
  | cons y ys ih =>
    intro h h' x hc
    rw [consume_cons] at hc
    rcases hadv : advance N d h with ⟨h₁, _ | r₁⟩
    · rw [hadv] at hc; dsimp only at hc
      exact absurd hc (by simp)
    · rw [hadv] at hc
      rcases r₁ with x₁ | b₁ <;> dsimp only at hc
      · exact ih _ h' x hc
      · exact absurd hc (by simp)

/-- **Supply extension, live side**: a run ending with a pending forwarded
query continues from its final history. -/
theorem consume_append_some (N : ℕ) (d : DDD X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (x : X) (zs : List Y),
      consume N d h ys = (h', some (Sum.inl x)) →
      consume N d h (ys ++ zs) = consume N d h' zs := by
  intro ys
  induction ys with
  | nil =>
    intro h h' x zs hc
    rw [consume_nil] at hc
    have hab := (advance_spec N d h h' _ hc).2.1
    cases zs with
    | nil => rw [List.nil_append, consume_nil, consume_nil, hc, hab]
    | cons z zs' => rw [List.nil_append, consume_cons, consume_cons, hc, hab]
  | cons y ys ih =>
    intro h h' x zs hc
    rw [consume_cons] at hc
    rw [List.cons_append, consume_cons]
    rcases hadv : advance N d h with ⟨h₁, _ | r₁⟩
    · rw [hadv] at hc; dsimp only at hc ⊢
      exact absurd hc (by simp)
    · rw [hadv] at hc
      rcases r₁ with x₁ | b₁ <;> dsimp only at hc ⊢
      · exact ih _ h' x zs hc
      · exact absurd hc (by simp)

/-- **Supply extension, halted side**: a run whose distinguisher gave a verdict
(or filled the budget) ignores additional answers. -/
theorem consume_append_none (N : ℕ) (d : DDD X Y) :
    ∀ (ys : List Y) (h h' : List (X × Y)) (r : Option (X ⊕ Bool)) (zs : List Y),
      consume N d h ys = (h', r) → (∀ x, r ≠ some (Sum.inl x)) →
      consume N d h (ys ++ zs) = (h', r) := by
  intro ys
  induction ys with
  | nil =>
    intro h h' r zs hc hr
    rw [consume_nil] at hc
    cases zs with
    | nil => rw [List.nil_append, consume_nil, hc]
    | cons z zs' =>
      rw [List.nil_append, consume_cons, hc]
      rcases r with _ | r₁
      · rfl
      · rcases r₁ with x₁ | b₁
        · exact absurd rfl (hr x₁)
        · rfl
  | cons y ys ih =>
    intro h h' r zs hc hr
    rw [consume_cons] at hc
    rw [List.cons_append, consume_cons]
    rcases hadv : advance N d h with ⟨h₁, _ | r₁⟩
    · rw [hadv] at hc; dsimp only at hc ⊢
      exact hc
    · rw [hadv] at hc
      rcases r₁ with x₁ | b₁ <;> dsimp only at hc ⊢
      · exact ih _ h' r zs hc hr
      · exact hc

/-- One-step supply extension: consuming one more answer resolves the pending
query and advances. -/
theorem consume_concat_some {N : ℕ} {d : DDD X Y}
    {h h' : List (X × Y)} {x : X} {ys : List Y}
    (hc : consume N d h ys = (h', some (Sum.inl x))) (y : Y) :
    consume N d h (ys ++ [y]) = advance N d (h' ++ [(x, y)]) := by
  rw [consume_append_some N d ys h h' x [y] hc, consume_cons,
    consume_some_advance N d ys h h' x hc]
  rfl

/-! ### The cache distinguisher -/

/-- The cache's move after seeing the fresh-answer supply `rs`: forward the
pending fresh query, emit the verdict, or (budget exhausted — unreachable under
the query bound) default to verdict `0`. -/
def cacheOut (N : ℕ) (d : DDD X Y) (rs : List Y) : X ⊕ Bool :=
  match (consume N d [] rs).2 with
  | some (Sum.inl x) => Sum.inl x
  | some (Sum.inr b) => Sum.inr b
  | none => Sum.inr false

/-- Once the cache emits a verdict, extending the answer supply keeps it. -/
theorem cacheOut_stop (N : ℕ) (d : DDD X Y) (rs ts : List Y) (b : Bool)
    (h : cacheOut N d rs = Sum.inr b) :
    cacheOut N d (rs ++ ts) = Sum.inr b := by
  unfold cacheOut at h ⊢
  rcases hcons : consume N d [] rs with ⟨h₁, o⟩
  rw [hcons] at h
  rcases o with _ | r₁
  · dsimp only at h
    rw [consume_append_none N d rs [] h₁ none ts hcons (by simp)]
    dsimp only; exact h
  · rcases r₁ with x₁ | b₁
    · dsimp only at h; exact absurd h (by simp)
    · dsimp only at h
      rw [consume_append_none N d rs [] h₁ (some (Sum.inr b₁)) ts hcons (by simp)]
      dsimp only; exact h

/-- The cache distinguisher's move function: reconstruct the fresh-answer supply
by dropping stalls, then run the de-dup simulation. -/
def cacheFun (N : ℕ) (d : DDD X Y) : List (Option Y) → X ⊕ Bool :=
  fun oys => cacheOut N d (oys.filterMap id)

/-- **The distinguisher-side de-duplication cache** (D1): replays `d`, answering
`d`'s already-asked queries from its own recorded history and forwarding only
first occurrences to the system.  The budget `N` bounds the total simulated
queries (well-definedness); it is met by any `QueriesAtMostN`-bounded `d`.

**On `N` and the scheme (protocol note).**  This is *not* the prohibited
fuel-with-absorbing-states scheme.  `advance` consults `d.val` *first* (verdicts
and fresh queries are always emitted); `N` bounds only the *well-founded
self-answer recursion* (`termination_by N - h.length`), exactly as the
derivation's `SelfAnswerFilter.advance` is well-founded on `q - h.length`.
`consume` is plain structural recursion on the answer supply.  There is no
absorbing terminal state and no fuel-monotonicity tax: `StopFinal` is discharged
by `cacheOut_stop`, whose engine is `consume_append_none` (the derivation's own
"halted side ignores more answers" absorption lemma), *not* a `simTrace_extend`-
style inr-monotonicity-across-fuel lemma.  `N` is a genuine query-budget: a DDD's
interaction is intrinsically round-bounded, and the consumers instantiate `N`
at the converter's per-run cipher-call bound, on which `d` provably halts
(`QueriesAtMostN`), so the pathological `none` branch never fires. -/
def cacheDDD (N : ℕ) (d : DDD X Y) : DDD X Y :=
  ⟨cacheFun N d, by
    intro h h' hpre b hb
    obtain ⟨ts, rfl⟩ := hpre
    unfold cacheFun at hb ⊢
    rw [List.filterMap_append]
    exact cacheOut_stop N d _ _ b hb⟩

@[simp] theorem cacheDDD_val (N : ℕ) (d : DDD X Y) :
    (cacheDDD N d).val = cacheFun N d := rfl

/-! ### The pure run of a distinguisher against a function oracle

Against `functionEvaluator f` the interaction is deterministic; `dRun d f n` is
its pair-history after `n` rounds, and `verdict` reads `d.val` off its
`some`-wrapped output projection. -/

/-- The pure `n`-round pair-history of `d` answered by `f`. -/
def dRun (d : DDD X Y) (f : X → Y) : ℕ → List (X × Y)
  | 0 => []
  | n + 1 =>
    match d.val ((dRun d f n).map fun p => some p.2) with
    | Sum.inl x => dRun d f n ++ [(x, f x)]
    | Sum.inr _ => dRun d f n

/-- The fully-defined completion of a function evaluator answers `some (f x)` on
the last query. -/
theorem output_fullyDefined_functionEvaluator (f : X → Y) (l : List X) (x : X)
    (h : l ++ [x] ∈ dom (functionEvaluator f)⊥) :
    output (functionEvaluator f)⊥ (l ++ [x]) h = some (f x) := by
  have hin : l ∈ dom (functionEvaluator f) ∨ l = [] := by
    rcases eq_or_ne l [] with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (by rw [dom_functionEvaluator]; exact h0)
  have hnext : l ++ [x] ∈ dom (functionEvaluator f) := by
    rw [dom_functionEvaluator]; simp
  rw [output_fullyDefined_append_of_mem (functionEvaluator f) l x hin hnext,
    functionEvaluator_output]

/-- The transcript against `functionEvaluator f` is exactly `dRun`, with outputs
wrapped in `some`. -/
theorem transcript_functionEvaluator_eq (d : DDD X Y) (f : X → Y) (n : ℕ) :
    transcript (functionEvaluator f) (ddToDDE d) n
      = (dRun d f n).map (fun p => (p.1, some p.2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hview : (transcript (functionEvaluator f) (ddToDDE d) n)↓ᵧ
        = (dRun d f n).map (fun p => some p.2) := by
      rw [transcriptOutputs, ih, List.map_map]; rfl
    rcases hd : d.val ((dRun d f n).map fun p => some p.2) with x | b
    · have hfire : ddToDDE d (transcript (functionEvaluator f) (ddToDDE d) n)↓ᵧ
          = some x := by rw [hview]; unfold ddToDDE; rw [hd]
      have hrun : dRun d f (n + 1) = dRun d f n ++ [(x, f x)] := by rw [dRun, hd]
      rw [transcript_succ_fire hfire, ih, hrun,
        output_fullyDefined_functionEvaluator]
      simp
    · have hstall : ddToDDE d (transcript (functionEvaluator f) (ddToDDE d) n)↓ᵧ
          = none := by rw [hview]; unfold ddToDDE; rw [hd]
      rw [transcript_succ_stall hstall, ih, dRun, hd]

/-- The output projection against `functionEvaluator f` is the `some`-wrapped
`dRun` view. -/
theorem transcriptOutputs_functionEvaluator_eq (d : DDD X Y) (f : X → Y) (n : ℕ) :
    (transcript (functionEvaluator f) (ddToDDE d) n)↓ᵧ
      = (dRun d f n).map (fun p => some p.2) := by
  rw [transcriptOutputs, transcript_functionEvaluator_eq, List.map_map]; rfl

/-- **Verdict against a function oracle**, purely in terms of `dRun`. -/
theorem verdict_functionEvaluator_iff (d : DDD X Y) (f : X → Y) :
    verdict d (functionEvaluator f) ↔
      ∃ n, d.val ((dRun d f n).map fun p => some p.2) = Sum.inr true := by
  unfold verdict
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rwa [transcriptOutputs_functionEvaluator_eq] at hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rwa [transcriptOutputs_functionEvaluator_eq]⟩

/-! ### Concrete-filter correctness -/

/-- On a history consistent with `f`, an already-asked query recalls `f x`. -/
theorem lookupAns_of_consistent (h : List (X × Y)) (x : X) (f : X → Y)
    (hcons : ∀ p ∈ h, p.2 = f p.1) (hmem : x ∈ h.map Prod.fst) :
    lookupAns h x = some (f x) := by
  unfold lookupAns
  have hex : ∃ p, p ∈ h ∧ decide (p.1 = x) = true := by
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hmem
    exact ⟨p, hp, by simp [hpx]⟩
  obtain ⟨p₀, hfind⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr hex)
  rw [hfind]
  have hp₀ : p₀ ∈ h := List.mem_of_find?_eq_some hfind
  have hp₀x : p₀.1 = x := by simpa using List.find?_some hfind
  rw [Option.map_some, hcons p₀ hp₀, hp₀x]

/-- A never-asked query recalls nothing. -/
theorem lookupAns_eq_none_iff (h : List (X × Y)) (x : X) :
    lookupAns h x = none ↔ x ∉ h.map Prod.fst := by
  unfold lookupAns
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro hh hmem
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hmem
    exact hh p hp (by simp [hpx])
  · intro hh p hp hdec
    exact hh (List.mem_map.mpr ⟨p, hp, by simpa using hdec⟩)

/-- `dRun` is consistent with `f`: every recorded answer is `f` of its query. -/
theorem dRun_consistent (d : DDD X Y) (f : X → Y) (n : ℕ) :
    ∀ p ∈ dRun d f n, p.2 = f p.1 := by
  induction n with
  | zero => intro p hp; simp [dRun] at hp
  | succ n ih =>
    rcases hd : d.val ((dRun d f n).map fun p => some p.2) with x | b
    · have hrun : dRun d f (n + 1) = dRun d f n ++ [(x, f x)] := by rw [dRun, hd]
      intro p hp
      rw [hrun, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ih p hp
      · rw [List.mem_singleton] at hp; subst hp; rfl
    · have hrun : dRun d f (n + 1) = dRun d f n := by rw [dRun, hd]
      intro p hp; rw [hrun] at hp; exact ih p hp

/-! ### Simulation correctness against a function oracle -/

/-- **`advance` along the true run**: starting from the `n`-round pair-prefix of
`dRun`, `advance` self-answers repeated queries (correctly, by consistency) and
stops at the first *fresh* query, at `d`'s verdict, or — pathologically, only if
`d` never halts within budget `N` — with `none`. -/
theorem advance_run_spec (N : ℕ) (d : DDD X Y) (f : X → Y) :
    ∀ (fuel n : ℕ), N - (dRun d f n).length ≤ fuel →
      (∃ m x, n ≤ m ∧
          d.val ((dRun d f m).map fun p => some p.2) = Sum.inl x ∧
          x ∉ (dRun d f m).map Prod.fst ∧
          advance N d (dRun d f n) = (dRun d f m, some (Sum.inl x)))
      ∨ (∃ m b, n ≤ m ∧
          d.val ((dRun d f m).map fun p => some p.2) = Sum.inr b ∧
          advance N d (dRun d f n) = (dRun d f m, some (Sum.inr b)))
      ∨ (∃ m x, n ≤ m ∧
          d.val ((dRun d f m).map fun p => some p.2) = Sum.inl x ∧
          N ≤ (dRun d f m).length ∧
          advance N d (dRun d f n) = (dRun d f m, none)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hf
    rcases hd : d.val ((dRun d f n).map fun p => some p.2) with x | b
    · rcases hl : lookupAns (dRun d f n) x with _ | y
      · have hadv : advance N d (dRun d f n) = (dRun d f n, some (Sum.inl x)) := by
          rw [advance, hd]; dsimp only; rw [hl]
        exact Or.inl ⟨n, x, le_rfl, hd, (lookupAns_eq_none_iff _ _).mp hl, hadv⟩
      · have hadv : advance N d (dRun d f n) = (dRun d f n, none) := by
          rw [advance, hd]; dsimp only; simp only [hl]; rw [dif_neg (by omega)]
        exact Or.inr (Or.inr ⟨n, x, le_rfl, hd, by omega, hadv⟩)
    · have hadv : advance N d (dRun d f n) = (dRun d f n, some (Sum.inr b)) := by
        rw [advance, hd]
      exact Or.inr (Or.inl ⟨n, b, le_rfl, hd, hadv⟩)
  | succ fuel ih =>
    intro n hf
    rcases hd : d.val ((dRun d f n).map fun p => some p.2) with x | b
    · rcases hl : lookupAns (dRun d f n) x with _ | y
      · have hadv : advance N d (dRun d f n) = (dRun d f n, some (Sum.inl x)) := by
          rw [advance, hd]; dsimp only; rw [hl]
        exact Or.inl ⟨n, x, le_rfl, hd, (lookupAns_eq_none_iff _ _).mp hl, hadv⟩
      · have hmem : x ∈ (dRun d f n).map Prod.fst := by
          by_contra hc
          rw [(lookupAns_eq_none_iff _ _).mpr hc] at hl; exact absurd hl (by simp)
        have hyfx : y = f x := by
          have hc := lookupAns_of_consistent (dRun d f n) x f
            (dRun_consistent d f n) hmem
          rw [hl] at hc; exact Option.some.inj hc
        have hrun : dRun d f (n + 1) = dRun d f n ++ [(x, y)] := by
          rw [dRun, hd, hyfx]
        by_cases hlen : (dRun d f n).length < N
        · have hadv_eq : advance N d (dRun d f n) = advance N d (dRun d f (n + 1)) := by
            rw [advance, hd]; dsimp only; simp only [hl]; rw [dif_pos hlen, hrun]
          have hf' : N - (dRun d f (n + 1)).length ≤ fuel := by
            rw [hrun, List.length_append, List.length_singleton]; omega
          rcases ih (n + 1) hf' with h1 | h2 | h3
          · obtain ⟨m, x', hm, hdm, hfr, hadv⟩ := h1
            exact Or.inl ⟨m, x', by omega, hdm, hfr, by rw [hadv_eq, hadv]⟩
          · obtain ⟨m, b', hm, hdm, hadv⟩ := h2
            exact Or.inr (Or.inl ⟨m, b', by omega, hdm, by rw [hadv_eq, hadv]⟩)
          · obtain ⟨m, x', hm, hdm, hlenm, hadv⟩ := h3
            exact Or.inr (Or.inr ⟨m, x', by omega, hdm, hlenm, by rw [hadv_eq, hadv]⟩)
        · have hadv : advance N d (dRun d f n) = (dRun d f n, none) := by
            rw [advance, hd]; dsimp only; simp only [hl]; rw [dif_neg hlen]
          exact Or.inr (Or.inr ⟨n, x, le_rfl, hd, not_lt.mp hlen, hadv⟩)
    · have hadv : advance N d (dRun d f n) = (dRun d f n, some (Sum.inr b)) := by
        rw [advance, hd]
      exact Or.inr (Or.inl ⟨n, b, le_rfl, hd, hadv⟩)

/-- `d` makes at most `N` queries: once `N` answers are seen it has a verdict. -/
def QueriesAtMostN (d : DDD X Y) (N : ℕ) : Prop :=
  ∀ h : List (Option Y), N ≤ h.length → ∃ b, d.val h = Sum.inr b

/-- Under the query bound the pathological budget-exhaustion case cannot occur:
`advance` from a `dRun`-prefix stops at a fresh query or a verdict. -/
theorem advance_run_spec2 (N : ℕ) (d : DDD X Y) (f : X → Y)
    (hQ : QueriesAtMostN d N) (n : ℕ) :
    (∃ m x, n ≤ m ∧
        d.val ((dRun d f m).map fun p => some p.2) = Sum.inl x ∧
        x ∉ (dRun d f m).map Prod.fst ∧
        advance N d (dRun d f n) = (dRun d f m, some (Sum.inl x)))
    ∨ (∃ m b, n ≤ m ∧
        d.val ((dRun d f m).map fun p => some p.2) = Sum.inr b ∧
        advance N d (dRun d f n) = (dRun d f m, some (Sum.inr b))) := by
  rcases advance_run_spec N d f (N - (dRun d f n).length) n le_rfl with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · obtain ⟨m, x, hm, hdm, hlenm, _⟩ := h3
    obtain ⟨b, hb⟩ := hQ ((dRun d f m).map fun p => some p.2)
      (by rw [List.length_map]; exact hlenm)
    rw [hb] at hdm; exact absurd hdm (by simp)

/-- The cache's pending forwarded query after seeing supply `rs` (else a junk
default). -/
def cacheQuery (N : ℕ) (d : DDD X Y) (dflt : X) (rs : List Y) : X :=
  match (consume N d [] rs).2 with
  | some (Sum.inl x) => x
  | _ => dflt

/-- **`consume` along the true run**: replaying a supply whose every answer is
`f` of the cache's pending query lands on a `dRun`-prefix, having reconstructed
`d`'s run; the verdict/next-fresh-query is `d`'s. -/
theorem consume_run_spec (N : ℕ) (d : DDD X Y) (f : X → Y)
    (hQ : QueriesAtMostN d N) (dflt : X) :
    ∀ (rs : List Y),
      (∀ k (hk : k < rs.length), rs[k] = f (cacheQuery N d dflt (rs.take k))) →
      (∃ m x, rs.length ≤ m ∧
          d.val ((dRun d f m).map fun p => some p.2) = Sum.inl x ∧
          x ∉ (dRun d f m).map Prod.fst ∧
          consume N d [] rs = (dRun d f m, some (Sum.inl x)))
      ∨ (∃ m b,
          d.val ((dRun d f m).map fun p => some p.2) = Sum.inr b ∧
          consume N d [] rs = (dRun d f m, some (Sum.inr b))) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro _
    rcases advance_run_spec2 N d f hQ 0 with h1 | h2
    · obtain ⟨m, x, _, hdm, hfr, hadv⟩ := h1
      exact Or.inl ⟨m, x, Nat.zero_le _, hdm, hfr, by rw [consume_nil]; exact hadv⟩
    · obtain ⟨m, b, _, hdm, hadv⟩ := h2
      exact Or.inr ⟨m, b, hdm, by rw [consume_nil]; exact hadv⟩
  | append_singleton rs y ih =>
    intro hrs
    have hrs' : ∀ k (hk : k < rs.length),
        rs[k] = f (cacheQuery N d dflt (rs.take k)) := by
      intro k hk
      have h := hrs k (by rw [List.length_append, List.length_singleton]; omega)
      rwa [List.getElem_append_left hk,
        List.take_append_of_le_length (le_of_lt hk)] at h
    rcases ih hrs' with ⟨m, x, hlen, hdm, hfr, hcons⟩ | ⟨m, b, hdm, hcons⟩
    · have hxq : cacheQuery N d dflt rs = x := by unfold cacheQuery; rw [hcons]
      have hy : y = f x := by
        have h := hrs rs.length
          (by rw [List.length_append, List.length_singleton]; omega)
        rw [List.getElem_concat_length rfl
            (by rw [List.length_append, List.length_singleton]; omega),
          List.take_append_of_le_length le_rfl, List.take_length, hxq] at h
        exact h
      have hrun : dRun d f (m + 1) = dRun d f m ++ [(x, y)] := by rw [dRun, hdm, hy]
      have hcc : consume N d [] (rs ++ [y]) = advance N d (dRun d f (m + 1)) := by
        rw [consume_concat_some hcons y, hrun]
      rcases advance_run_spec2 N d f hQ (m + 1) with h1 | h2
      · obtain ⟨m', x', hm', hdm', hfr', hadv'⟩ := h1
        exact Or.inl ⟨m', x', by rw [List.length_append, List.length_singleton]; omega,
          hdm', hfr', by rw [hcc, hadv']⟩
      · obtain ⟨m', b', hm', hdm', hadv'⟩ := h2
        exact Or.inr ⟨m', b', hdm', by rw [hcc, hadv']⟩
    · exact Or.inr ⟨m, b, hdm,
        consume_append_none N d rs [] (dRun d f m) (some (Sum.inr b)) [y] hcons (by simp)⟩

/-! ### Assembling the verdict equivalence -/

/-- The cache move on the `some`-wrapped view equals `cacheOut` on the raw
answers. -/
theorem cacheFun_view_eq (N : ℕ) (d : DDD X Y) (l : List (X × Y)) :
    cacheFun N d (l.map fun p => some p.2) = cacheOut N d (l.map Prod.snd) := by
  unfold cacheFun
  congr 1
  induction l with
  | nil => rfl
  | cons a t ih => simp

/-- `dRun` grows by at most one pair per step. -/
theorem dRun_succ_prefix (c : DDD X Y) (f : X → Y) (n : ℕ) :
    dRun c f n <+: dRun c f (n + 1) := by
  rcases hc : c.val ((dRun c f n).map fun p => some p.2) with x | b
  · have h : dRun c f (n + 1) = dRun c f n ++ [(x, f x)] := by rw [dRun, hc]
    rw [h]; exact List.prefix_append _ _
  · have h : dRun c f (n + 1) = dRun c f n := by rw [dRun, hc]
    rw [h]

/-- `dRun` is prefix-monotone. -/
theorem dRun_mono (c : DDD X Y) (f : X → Y) {k n : ℕ} (h : k ≤ n) :
    dRun c f k <+: dRun c f n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ n hkn ih => exact ih.trans (dRun_succ_prefix c f n)

/-- A distinguisher's verdict against a function oracle is unique (`StopFinal`):
if it is `true` at some round, every reached verdict is `true`. -/
theorem dRun_view_verdict_unique (d : DDD X Y) (f : X → Y) {M m : ℕ} {b : Bool}
    (hM : d.val ((dRun d f M).map fun p => some p.2) = Sum.inr true)
    (hm : d.val ((dRun d f m).map fun p => some p.2) = Sum.inr b) : b = true := by
  rcases le_total M m with h | h
  · have h1 := d.property ((dRun_mono d f h).map fun p => some p.2) true hM
    rw [hm] at h1; exact Sum.inr.inj h1
  · have h1 := d.property ((dRun_mono d f h).map fun p => some p.2) b hm
    rw [hM] at h1; exact (Sum.inr.inj h1).symm

/-- If the cache forwards `x` after supply `rs`, then `x` is the cache's query. -/
theorem cacheQuery_of_cacheOut_inl (N : ℕ) (d : DDD X Y) (dflt : X)
    (rs : List Y) (x : X) (h : cacheOut N d rs = Sum.inl x) :
    cacheQuery N d dflt rs = x := by
  unfold cacheOut at h; unfold cacheQuery
  set o := (consume N d [] rs).2 with ho
  clear_value o
  rcases o with _ | (x' | b') <;> dsimp only at h ⊢
  · exact absurd h (by simp)
  · exact Sum.inl.inj h
  · exact absurd h (by simp)

/-- **The cache's own answer-run is a valid supply** (part A): every answer the
cache receives is `f` of its pending query. -/
theorem cacheSupply_valid (N : ℕ) (d : DDD X Y) (f : X → Y) (dflt : X) :
    ∀ (n k : ℕ) (hk : k < ((dRun (cacheDDD N d) f n).map Prod.snd).length),
      ((dRun (cacheDDD N d) f n).map Prod.snd)[k]
        = f (cacheQuery N d dflt (((dRun (cacheDDD N d) f n).map Prod.snd).take k)) := by
  intro n
  induction n with
  | zero => intro k hk; simp [dRun] at hk
  | succ n ih =>
    rcases hc : (cacheDDD N d).val ((dRun (cacheDDD N d) f n).map fun p => some p.2)
      with x | b
    · have hpair : dRun (cacheDDD N d) f (n + 1)
          = dRun (cacheDDD N d) f n ++ [(x, f x)] := by rw [dRun, hc]
      have hxq : cacheQuery N d dflt ((dRun (cacheDDD N d) f n).map Prod.snd) = x :=
        cacheQuery_of_cacheOut_inl N d dflt _ x (by rw [← cacheFun_view_eq]; exact hc)
      have hmap : (dRun (cacheDDD N d) f (n + 1)).map Prod.snd
          = (dRun (cacheDDD N d) f n).map Prod.snd ++ [f x] := by
        rw [hpair, List.map_append]; rfl
      intro k hk
      simp only [hmap] at hk ⊢
      rcases Nat.lt_or_ge k ((dRun (cacheDDD N d) f n).map Prod.snd).length
        with hklt | hkge
      · rw [List.getElem_append_left hklt,
          List.take_append_of_le_length (le_of_lt hklt)]
        exact ih k hklt
      · have hkeq : k = ((dRun (cacheDDD N d) f n).map Prod.snd).length := by
          rw [List.length_append, List.length_singleton] at hk; omega
        subst hkeq
        rw [List.getElem_concat_length rfl
            (by rw [List.length_append, List.length_singleton]; omega),
          List.take_append_of_le_length le_rfl, List.take_length, hxq]
    · have hpair : dRun (cacheDDD N d) f (n + 1) = dRun (cacheDDD N d) f n := by
        rw [dRun, hc]
      intro k hk; simp only [hpair] at hk ⊢; exact ih k hk

/-- **Progress**: assuming `d`'s verdict is `true` at round `M`, at every cache
step either the cache has already forwarded `n` distinct queries or it has
already produced a `true` verdict. -/
theorem cache_progress (N : ℕ) (d : DDD X Y) (hQ : QueriesAtMostN d N)
    (f : X → Y) (dflt : X) {M : ℕ}
    (hM : d.val ((dRun d f M).map fun p => some p.2) = Sum.inr true) :
    ∀ n, n ≤ (dRun (cacheDDD N d) f n).length
      ∨ ∃ k, cacheOut N d ((dRun (cacheDDD N d) f k).map Prod.snd) = Sum.inr true := by
  intro n
  induction n with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ n ih =>
    rcases ih with hlen | hex
    · rcases consume_run_spec N d f hQ dflt _ (cacheSupply_valid N d f dflt n)
        with ⟨m, x, _, hdm, _, hcons⟩ | ⟨m, b, hdm, hcons⟩
      · have hco : cacheOut N d ((dRun (cacheDDD N d) f n).map Prod.snd) = Sum.inl x := by
          unfold cacheOut; rw [hcons]
        have hcf : (cacheDDD N d).val ((dRun (cacheDDD N d) f n).map fun p => some p.2)
            = Sum.inl x := by rw [cacheDDD_val, cacheFun_view_eq]; exact hco
        have hpair : dRun (cacheDDD N d) f (n + 1)
            = dRun (cacheDDD N d) f n ++ [(x, f x)] := by rw [dRun, hcf]
        exact Or.inl (by rw [hpair, List.length_append, List.length_singleton]; omega)
      · have hbt : b = true := dRun_view_verdict_unique d f hM hdm
        subst hbt
        exact Or.inr ⟨n, by unfold cacheOut; rw [hcons]⟩
    · exact Or.inr hex

/-- **D1(a) — repeats are free against a function oracle.**  The de-dup cache is
verdict-transparent: it accepts `functionEvaluator f` iff `d` does. -/
theorem verdict_cacheDDD_iff (N : ℕ) (d : DDD X Y) (hQ : QueriesAtMostN d N)
    (f : X → Y) (dflt : X) :
    verdict (cacheDDD N d) (functionEvaluator f) ↔ verdict d (functionEvaluator f) := by
  rw [verdict_functionEvaluator_iff, verdict_functionEvaluator_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [cacheDDD_val, cacheFun_view_eq] at hn
    rcases consume_run_spec N d f hQ dflt _ (cacheSupply_valid N d f dflt n)
      with ⟨m, x, _, hdm, _, hcons⟩ | ⟨m, b, hdm, hcons⟩
    · exfalso; unfold cacheOut at hn; rw [hcons] at hn; simp at hn
    · refine ⟨m, ?_⟩
      have hbt : b = true := by unfold cacheOut at hn; rw [hcons] at hn; exact Sum.inr.inj hn
      rw [hdm, hbt]
  · rintro ⟨M, hM⟩
    obtain ⟨n, hco⟩ : ∃ n,
        cacheOut N d ((dRun (cacheDDD N d) f n).map Prod.snd) = Sum.inr true := by
      rcases cache_progress N d hQ f dflt hM (M + 1) with hlen | hex
      · rcases consume_run_spec N d f hQ dflt _ (cacheSupply_valid N d f dflt (M + 1))
          with ⟨m, x, hmlen, hdm, _, hcons⟩ | ⟨m, b, hdm, hcons⟩
        · exfalso
          have hmM : M ≤ m := by simp only [List.length_map] at hmlen; omega
          have hcontra := d.property ((dRun_mono d f hmM).map fun p => some p.2) true hM
          rw [hdm] at hcontra; simp at hcontra
        · have hbt : b = true := dRun_view_verdict_unique d f hM hdm
          subst hbt
          exact ⟨M + 1, by unfold cacheOut; rw [hcons]⟩
      · exact hex
    exact ⟨n, by rw [cacheDDD_val, cacheFun_view_eq]; exact hco⟩

/-- **D1(b) — the forwarded queries are distinct.**  The cache forwards only
first occurrences, so its query list (against `functionEvaluator f`) has no
duplicates; jointly, every forwarded query lies in the reconstructed `d`-run. -/
theorem cacheDDD_run_nodup (N : ℕ) (d : DDD X Y) (hQ : QueriesAtMostN d N)
    (f : X → Y) (dflt : X) (n : ℕ) :
    ((dRun (cacheDDD N d) f n).map Prod.fst).Nodup ∧
      (∀ x ∈ (dRun (cacheDDD N d) f n).map Prod.fst,
        x ∈ (consume N d [] ((dRun (cacheDDD N d) f n).map Prod.snd)).1.map Prod.fst) := by
  induction n with
  | zero => exact ⟨by simp [dRun], by simp [dRun]⟩
  | succ n ih =>
    obtain ⟨ihnodup, ihsub⟩ := ih
    rcases consume_run_spec N d f hQ dflt _ (cacheSupply_valid N d f dflt n)
      with ⟨m, x, _, hdm, hfr, hcons⟩ | ⟨m, b, hdm, hcons⟩
    · have hco : cacheOut N d ((dRun (cacheDDD N d) f n).map Prod.snd) = Sum.inl x := by
        unfold cacheOut; rw [hcons]
      have hcf : (cacheDDD N d).val ((dRun (cacheDDD N d) f n).map fun p => some p.2)
          = Sum.inl x := by rw [cacheDDD_val, cacheFun_view_eq]; exact hco
      have hpair : dRun (cacheDDD N d) f (n + 1)
          = dRun (cacheDDD N d) f n ++ [(x, f x)] := by rw [dRun, hcf]
      have hRn : (consume N d [] ((dRun (cacheDDD N d) f n).map Prod.snd)).1
          = dRun d f m := by rw [hcons]
      have hxnotin : x ∉ (dRun (cacheDDD N d) f n).map Prod.fst := by
        intro hxin; have := ihsub x hxin; rw [hRn] at this; exact hfr this
      have hmap : (dRun (cacheDDD N d) f (n + 1)).map Prod.snd
          = (dRun (cacheDDD N d) f n).map Prod.snd ++ [f x] := by
        rw [hpair, List.map_append]; rfl
      have hrun_d : dRun d f (m + 1) = dRun d f m ++ [(x, f x)] := by rw [dRun, hdm]
      have hcc : consume N d [] ((dRun (cacheDDD N d) f (n + 1)).map Prod.snd)
          = advance N d (dRun d f (m + 1)) := by
        rw [hmap, consume_concat_some hcons (f x), hrun_d]
      have hprefix : dRun d f (m + 1)
          <+: (consume N d [] ((dRun (cacheDDD N d) f (n + 1)).map Prod.snd)).1 := by
        rw [hcc]
        rcases hav : advance N d (dRun d f (m + 1)) with ⟨h', r⟩
        exact (advance_spec N d _ h' r hav).1
      have hsubfst : (dRun d f (m + 1)).map Prod.fst
          ⊆ (consume N d [] ((dRun (cacheDDD N d) f (n + 1)).map Prod.snd)).1.map Prod.fst :=
        (hprefix.map Prod.fst).subset
      refine ⟨?_, ?_⟩
      · rw [hpair, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
        refine ⟨ihnodup, List.nodup_singleton x, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        exact fun h => hxnotin (h ▸ ha)
      · intro y hy
        rw [hpair, List.map_append, List.map_cons, List.map_nil, List.mem_append] at hy
        rcases hy with hy1 | hy2
        · have h1 := ihsub y hy1; rw [hRn] at h1
          exact hsubfst (((dRun_mono d f (Nat.le_succ m)).map Prod.fst).subset h1)
        · rw [List.mem_singleton] at hy2; subst hy2
          exact hsubfst (by rw [hrun_d, List.map_append]; simp)
    · have hco : cacheOut N d ((dRun (cacheDDD N d) f n).map Prod.snd) = Sum.inr b := by
        unfold cacheOut; rw [hcons]
      have hcf : (cacheDDD N d).val ((dRun (cacheDDD N d) f n).map fun p => some p.2)
          = Sum.inr b := by rw [cacheDDD_val, cacheFun_view_eq]; exact hco
      have hpair : dRun (cacheDDD N d) f (n + 1) = dRun (cacheDDD N d) f n := by
        rw [dRun, hcf]
      rw [hpair]; exact ⟨ihnodup, ihsub⟩

/-- **D2 (cache run-vocabulary) — the forwarded-query count is at most any
covering finset.**  Because the cache forwards only first occurrences
(`cacheDDD_run_nodup`: the forwarded list is `Nodup`, i.e. forwarded = distinct),
its length is the cardinality of its underlying set, hence bounded by the card of
any finset `G` covering the forwarded queries.  Instantiated with
`G := (us.flatMap (hctrCalls be Hf π)).toFinset` and the `B := 2 + q·(L+1)` cap
(`hctrCalls_flatMap_toFinset_card_le_cap`), this is the paper's `σ + 2` cipher-
query budget in the exact vocabulary the padding step consumes. -/
theorem cacheDDD_forwarded_card_le (N : ℕ) (d : DDD X Y) (hQ : QueriesAtMostN d N)
    (f : X → Y) (dflt : X) (G : Finset X) (n : ℕ)
    (hsub : ∀ x ∈ (dRun (cacheDDD N d) f n).map Prod.fst, x ∈ G) :
    ((dRun (cacheDDD N d) f n).map Prod.fst).length ≤ G.card := by
  rw [← List.toFinset_card_of_nodup (cacheDDD_run_nodup N d hQ f dflt n).1]
  exact Finset.card_le_card fun x hx => hsub x (List.mem_toFinset.mp hx)

/-- **D3(a) — the distribution-level lift of `verdict_cacheDDD_iff`.**  Against a
function-backed law `S` (every system in its support is `functionEvaluator f`),
de-duplicating the winner distribution is verdict-transparent: the cache
distribution `fTransform (cacheDDD N) D` achieves exactly what `D` achieves.
Mirrors `verdictProb_filterQueries_eq_of_queriesExactly`'s `Finsupp.sum_congr`
structure and `verdictProb_absorb`'s `fTransform` (winner-side) handling. -/
theorem verdictProb_cacheDDD_eq [Inhabited X] (N : ℕ)
    (D : Dist (DDD X Y)) (S : PFunPDS X Y)
    (hbacked : ∀ s ∈ S.support, ∃ f : X → Y, s = functionEvaluator f)
    (hQ : ∀ d ∈ D.support, QueriesAtMostN d N) :
    verdictProb (Dist.fTransform (cacheDDD N) D) S = verdictProb D S := by
  unfold verdictProb
  rw [winProb_fTransform_left]
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun d hd => Finsupp.sum_congr fun s hs => ?_
  obtain ⟨f, rfl⟩ := hbacked s hs
  have hiff := verdict_cacheDDD_iff N d (hQ d hd) f default
  by_cases hv : verdict d (functionEvaluator f)
  · rw [if_pos (hiff.mpr hv), if_pos hv]
  · rw [if_neg (fun h => hv (hiff.mp h)), if_neg hv]

/-! ### D3(b) generic input — filter invisibility against a function oracle

If the pure run of `d` against `functionEvaluator f` never forwards more than `B`
distinct queries (`(dRun d f n).length ≤ B` for all `n`), the `[B]` filter is
invisible to `d`'s verdict.  This is the at-most-`B` companion of
`PFunDDS.verdict_filterQueries_iff_of_queriesExactly` (which needs exactly-`B`),
proved directly off the transcript-prefix agreement + freeze rather than through
a padding normal form.  UPSTREAM-CANDIDATE (generic distinguisher machinery). -/

/-- If `d` forwards a query at every round `< m`, its run has grown by `m`. -/
theorem dRun_length_eq_of_all_forward (d : DDD X Y) (f : X → Y) :
    ∀ (m : ℕ),
      (∀ k, k < m → ∃ x, d.val ((dRun d f k).map fun p => some p.2) = Sum.inl x) →
      (dRun d f m).length = m := by
  intro m
  induction m with
  | zero => intro _; simp [dRun]
  | succ m ih =>
      intro h
      obtain ⟨x, hx⟩ := h m (Nat.lt_succ_self m)
      have hrun : dRun d f (m + 1) = dRun d f m ++ [(x, f x)] := by rw [dRun, hx]
      rw [hrun, List.length_append, List.length_singleton,
        ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- Once `d` returns a verdict at round `k`, its run freezes: `dRun d f m = dRun d f k`
for all `m ≥ k`. -/
theorem dRun_eq_of_verdict (d : DDD X Y) (f : X → Y) {k : ℕ} {b : Bool}
    (hk : d.val ((dRun d f k).map fun p => some p.2) = Sum.inr b) :
    ∀ {m : ℕ}, k ≤ m → dRun d f m = dRun d f k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
      have hview : d.val ((dRun d f m).map fun p => some p.2) = Sum.inr b := by
        rw [ih]; exact hk
      rw [dRun, hview]; exact ih

/-- A run whose length never exceeds `B` must reach a verdict by round `B`. -/
theorem dRun_verdict_at_of_length_le (d : DDD X Y) (f : X → Y) (B : ℕ)
    (hlen : ∀ n, (dRun d f n).length ≤ B) :
    ∃ b, d.val ((dRun d f B).map fun p => some p.2) = Sum.inr b := by
  by_cases hex : ∃ k, k ≤ B ∧
      ∃ b, d.val ((dRun d f k).map fun p => some p.2) = Sum.inr b
  · obtain ⟨k, hkB, b, hkb⟩ := hex
    refine ⟨b, ?_⟩
    rw [show (dRun d f B).map (fun p => some p.2)
          = (dRun d f k).map (fun p => some p.2)
        from by rw [dRun_eq_of_verdict d f hkb hkB]]
    exact hkb
  · exfalso
    have hall : ∀ k, k < B + 1 →
        ∃ x, d.val ((dRun d f k).map fun p => some p.2) = Sum.inl x := by
      intro k hk
      rcases hd : d.val ((dRun d f k).map fun p => some p.2) with x | b
      · exact ⟨x, hd⟩
      · exact absurd ⟨k, Nat.lt_succ_iff.mp hk, b, hd⟩ hex
    have h1 := dRun_length_eq_of_all_forward d f (B + 1) hall
    have h2 := hlen (B + 1)
    omega

/-- A `QueriesAtMostN`-bounded distinguisher's pure run never exceeds `N` in
length: once it has forwarded `N` queries it is answered by a verdict. -/
theorem dRun_length_le_of_QueriesAtMostN (d : DDD X Y) (f : X → Y) (N : ℕ)
    (hQ : QueriesAtMostN d N) : ∀ m, (dRun d f m).length ≤ N := by
  intro m
  induction m with
  | zero => simp [dRun]
  | succ m ih =>
      rcases hd : d.val ((dRun d f m).map fun p => some p.2) with x | b
      · have hrun : dRun d f (m + 1) = dRun d f m ++ [(x, f x)] := by rw [dRun, hd]
        have hlt : (dRun d f m).length < N := by
          by_contra hge
          push_neg at hge
          obtain ⟨b, hb⟩ := hQ ((dRun d f m).map fun p => some p.2)
            (by rw [List.length_map]; exact hge)
          rw [hd] at hb; exact absurd hb (by simp)
        rw [hrun, List.length_append, List.length_singleton]; omega
      · have hrun : dRun d f (m + 1) = dRun d f m := by rw [dRun, hd]
        rw [hrun]; exact ih

/-- **Verdict at a stalled round.**  If `d` has stopped by round `B` against `s`
(the environment stalls: `ddToDDE d` returns `none`), its verdict is exactly the
stopping symbol read at round `B`. -/
theorem verdict_iff_at_stall (d : DDD X Y) (s : DDS X Y) (B : ℕ)
    (hstop : ddToDDE d (transcriptOutputs (transcript s (ddToDDE d) B)) = none) :
    verdict d s ↔
      d.val (transcriptOutputs (transcript s (ddToDDE d) B)) = Sum.inr true := by
  constructor
  · rintro ⟨n, hn⟩
    rcases le_total n B with hnB | hBn
    · have hstopn :
          ddToDDE d (transcriptOutputs (transcript s (ddToDDE d) n)) = none := by
        show (match d.val (transcriptOutputs (transcript s (ddToDDE d) n)) with
          | Sum.inl x => some x | Sum.inr _ => none) = none
        rw [hn]
      rw [transcript_freeze hstopn hnB]; exact hn
    · rw [transcript_freeze hstop hBn] at hn; exact hn
  · intro h; exact ⟨B, h⟩

/-- **D3(b) — filter invisibility against a function oracle.**  A distinguisher
whose pure run forwards at most `B` distinct queries cannot tell the `[B]`-filtered
function oracle from the total one. -/
theorem verdict_filterQueries_functionEvaluator_iff (d : DDD X Y) (f : X → Y)
    (B : ℕ) (hlen : ∀ n, (dRun d f n).length ≤ B) :
    verdict d (filterQueries B (functionEvaluator f))
      ↔ verdict d (functionEvaluator f) := by
  obtain ⟨b, hb⟩ := dRun_verdict_at_of_length_le d f B hlen
  have hview : transcriptOutputs (transcript (functionEvaluator f) (ddToDDE d) B)
      = (dRun d f B).map (fun p => some p.2) :=
    transcriptOutputs_functionEvaluator_eq d f B
  have hstopS :
      ddToDDE d (transcriptOutputs (transcript (functionEvaluator f) (ddToDDE d) B))
        = none := by
    rw [hview]
    show (match d.val ((dRun d f B).map fun p => some p.2) with
      | Sum.inl x => some x | Sum.inr _ => none) = none
    rw [hb]
  have htotal : ∀ l : List X, l ≠ [] → l ∈ dom (functionEvaluator f) := by
    intro l hl; rw [dom_functionEvaluator]; exact hl
  have hagreeB :
      transcript (filterQueries B (functionEvaluator f)) (ddToDDE d) B
        = transcript (functionEvaluator f) (ddToDDE d) B :=
    transcript_filterQueries_eq_of_le (functionEvaluator f) B htotal (ddToDDE d)
      (le_refl B)
  have hstopF :
      ddToDDE d (transcriptOutputs
          (transcript (filterQueries B (functionEvaluator f)) (ddToDDE d) B)) = none := by
    rw [hagreeB]; exact hstopS
  rw [verdict_iff_at_stall d (filterQueries B (functionEvaluator f)) B hstopF,
    verdict_iff_at_stall d (functionEvaluator f) B hstopS, hagreeB]

/-- `functionEvaluator` is injective: the underlying function is recovered by
evaluating on singleton histories. -/
theorem functionEvaluator_inj {f g : X → Y}
    (h : functionEvaluator f = functionEvaluator g) : f = g := by
  funext x
  have hfe : (functionEvaluator f).1 [x] = (functionEvaluator g).1 [x] := by rw [h]
  have hf : (functionEvaluator f).1 [x] = Part.some (f x) := by
    simpa using CausalApply.functionEvaluator_raw_append f [] x
  have hg : (functionEvaluator g).1 [x] = Part.some (g x) := by
    simpa using CausalApply.functionEvaluator_raw_append g [] x
  rw [hf, hg] at hfe
  exact Part.some_inj.mp hfe

/-- **D3(b) mixture form — the `[B]` filter is invisible against a function-backed
law** to a distribution of distinguishers whose runs forward at most `B` queries.
Mirrors `verdictProb_filterQueries_eq_of_queriesExactly` with the per-point iff
supplied by `verdict_filterQueries_functionEvaluator_iff`. -/
theorem verdictProb_filterQueries_eq_of_dRunBounded (B : ℕ)
    (D : Dist (DDD X Y)) (S : PFunPDS X Y)
    (hbacked : ∀ s ∈ S.support, ∃ f : X → Y, s = functionEvaluator f)
    (hbound : ∀ d ∈ D.support, ∀ f : X → Y, functionEvaluator f ∈ S.support →
      ∀ n, (dRun d f n).length ≤ B) :
    verdictProb D (⌈B⌉ S) = verdictProb D S := by
  unfold verdictProb PFunPDS.filterQueries
  rw [winProb_fTransform_right]
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun d hd => Finsupp.sum_congr fun s hs => ?_
  obtain ⟨f, rfl⟩ := hbacked s hs
  have hiff := verdict_filterQueries_functionEvaluator_iff d f B (hbound d hd f hs)
  by_cases hv : verdict d (functionEvaluator f)
  · rw [if_pos (hiff.mpr hv), if_pos hv]
  · rw [if_neg (fun h => hv (hiff.mp h)), if_neg hv]

end PFunDDS.Cache

/-! ## D3(b) input — the absorbed distinguisher's query bound (B2)

The absorbed distinguisher of a `q`-outer-query distinguisher makes at most
`q·R` base-system queries, where `R` is the converter's Def-3.8 round bound: each
outer round completes within `R` inner calls (`absorbGo_round_reduce`), and there
are at most `q` rounds (`QueriesExactly`), composed by `absorbGo_none_reaches_verdict`.
This furnishes the `QueriesAtMostN` hypothesis the `Cache` de-dup lemmas consume. -/

section AbsorbQueryBound

open PFunDDS

universe u' v' w' z'
variable {U : Type u'} {V : Type w'} {X : Type z'} {Y : Type v'}

/-- An exactly-`q` environment produces transcripts of length at most `q`. -/
theorem transcript_length_le_of_queriesExactly (s : DDS X Y) (e : DDE X Y) (q : ℕ)
    (hQ : QueriesExactly e q) :
    ∀ n, (transcript s e n).length ≤ q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rcases hfire : e (transcriptOutputs (transcript s e n)) with _ | x
      · rw [transcript_succ_stall hfire]; exact ih
      · rw [transcript_succ_fire hfire, List.length_append, List.length_singleton]
        have hlt : (transcript s e n).length < q := by
          by_contra hge
          push_neg at hge
          have hst := hQ.2 (transcriptOutputs (transcript s e n))
            (by rw [transcriptOutputs_length]; exact hge)
          rw [hst] at hfire; exact absurd hfire (by simp)
        omega

/-- **One round completes within `R − |ys|` base answers.**  From round state
`(u, ys)` with `|ys| + k = R`, the replay consumes at most `k` answers and lands
at a fresh distinguisher-mode state `(vs ++ [ov], none, h')`; any verdict of the
continuation lifts back through the round. -/
theorem absorbGo_round_reduce (d : DDD U V) (step : U → List Y → X ⊕ V) (R : ℕ)
    (hR : ∀ (u : U) (ys : List Y), R ≤ ys.length → ∃ v, step u ys = Sum.inr v) :
    ∀ (k : ℕ) (u : U) (ys : List Y) (vs : List (Option V)) (h : List (Option Y)),
      ys.length + k = R → k ≤ h.length →
      ∃ (ov : Option V) (h' : List (Option Y)),
        h.length ≤ h'.length + k ∧
        ∀ (m : X ⊕ Bool),
          (∃ fuel, absorbGo d step fuel (vs ++ [ov]) none h' = some m) →
          (∃ fuel, absorbGo d step fuel vs (some (u, ys)) h = some m) := by
  intro k
  induction k with
  | zero =>
      intro u ys vs h hlen _
      obtain ⟨v, hv⟩ := hR u ys (by omega)
      refine ⟨some v, h, by omega, ?_⟩
      rintro m ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by rw [absorbGo, hv]; exact hfuel⟩
  | succ k ih =>
      intro u ys vs h hlen hk
      cases hstep : step u ys with
      | inr v =>
          refine ⟨some v, h, by omega, ?_⟩
          rintro m ⟨fuel, hfuel⟩
          exact ⟨fuel + 1, by rw [absorbGo, hstep]; exact hfuel⟩
      | inl x =>
          cases h with
          | nil => simp at hk
          | cons oy h' =>
              cases oy with
              | some y =>
                  have hlen' : (ys ++ [y]).length + k = R := by
                    simp only [List.length_append, List.length_singleton]; omega
                  have hk' : k ≤ h'.length := by
                    simp only [List.length_cons] at hk; omega
                  obtain ⟨ov, h'', hbound, hchain⟩ := ih u (ys ++ [y]) vs h' hlen' hk'
                  refine ⟨ov, h'', by simp only [List.length_cons] at *; omega, ?_⟩
                  rintro m hm
                  obtain ⟨fuel, hfuel⟩ := hchain m hm
                  exact ⟨fuel + 1, by rw [absorbGo, hstep]; exact hfuel⟩
              | none =>
                  refine ⟨none, h', by simp only [List.length_cons]; omega, ?_⟩
                  rintro m ⟨fuel, hfuel⟩
                  exact ⟨fuel + 1, by rw [absorbGo, hstep]; exact hfuel⟩

/-- **The absorbed distinguisher verdicts within `n·R` base answers**, where `n`
is the number of outer queries still to be made.  Composes `absorbGo_round_reduce`
over the (at most `q`) rounds. -/
theorem absorbGo_none_reaches_verdict (d : DDD U V) (step : U → List Y → X ⊕ V)
    (q R : ℕ) (hQ : QueriesExactly (ddToDDE d) q)
    (hR : ∀ (u : U) (ys : List Y), R ≤ ys.length → ∃ v, step u ys = Sum.inr v) :
    ∀ (n : ℕ) (vs : List (Option V)) (h : List (Option Y)),
      vs.length + n = q → n * R ≤ h.length →
      ∃ (b : Bool) (fuel : ℕ), absorbGo d step fuel vs none h = some (Sum.inr b) := by
  intro n
  induction n with
  | zero =>
      intro vs h hvs _
      have hnone : ddToDDE d vs = none := hQ.2 vs (by omega)
      rcases hdv : d.val vs with u | b
      · exfalso
        have : ddToDDE d vs = some u := by unfold ddToDDE; rw [hdv]
        rw [this] at hnone; exact absurd hnone (by simp)
      · exact ⟨b, 1, by rw [absorbGo, hdv]⟩
  | succ n ih =>
      intro vs h hvs hnR
      have hsome := hQ.1 vs (by omega)
      rcases hdv : d.val vs with u | b
      · have hRle : R ≤ h.length := by rw [Nat.succ_mul] at hnR; omega
        obtain ⟨ov, h', hbound, hchain⟩ :=
          absorbGo_round_reduce d step R hR R u [] vs h (by simp) hRle
        have hvs' : (vs ++ [ov]).length + n = q := by
          simp only [List.length_append, List.length_singleton]; omega
        have hnR' : n * R ≤ h'.length := by rw [Nat.succ_mul] at hnR; omega
        obtain ⟨b, fuel, hfuel⟩ := ih (vs ++ [ov]) h' hvs' hnR'
        obtain ⟨fuel', hfuel'⟩ := hchain (Sum.inr b) ⟨fuel, hfuel⟩
        exact ⟨b, fuel' + 1, by rw [absorbGo, hdv]; exact hfuel'⟩
      · exfalso
        have : ddToDDE d vs = none := by unfold ddToDDE; rw [hdv]
        rw [this] at hsome; simp at hsome

end AbsorbQueryBound

/-! ## The query-budgeted converter DPI and the `Δ`-swap

The two packaged laws a protocol needs to substitute one ideal primitive for another *inside* a
construction, Maurer-style:

* `maxAdvantage_filterQueries_applyDDC_le` — a `q`-query distinguisher of `α·P₁` vs `α·P₂` is at
  most a `q·R`-query distinguisher of `P₁` vs `P₂`, `R` the converter's Def 3.8 round bound
  (converter monotonicity, with honest query accounting: pad → absorb → run-length bound).
* `maxAdvantage_filterQueries_swap_le` — `Δ` is symmetric at the filtered surface: the padded
  distinguisher class is closed under flipping the verdict bit, so the signed sup swaps sides.
  (CR18's Thm 4.17-style bounds are stated one-directionally; this is the paper's implicit
  "Δ is a distance" step, cf. the axiomatized `edist_comm` of the abstract-crypto metric layer.) -/

section BudgetedDPI

universe u' v' w' z'
variable {U : Type u'} {V : Type w'} {X : Type z'} {Y : Type v'}

/-- **The absorbed distinguisher's query bound**: an exactly-`q` outer distinguisher absorbed
along a round-bound-`R` step makes at most `q·R` base queries. -/
theorem queriesAtMostN_absorb_of_roundBound (d : PFunDDS.DDD U V)
    (step : U → List Y → X ⊕ V) {R : ℕ}
    (hR : PFunConverter.DDC.AnswersWithin step R)
    {q : ℕ} (hQE : QueriesExactly (PFunDDS.ddToDDE d) q) :
    PFunDDS.Cache.QueriesAtMostN (absorb d step) (q * R) := by
  intro h hlen
  obtain ⟨b, fuel, hfuel⟩ :=
    absorbGo_none_reaches_verdict d step q R hQE hR q [] h (by simp) hlen
  exact ⟨b, absorbFun_eq_of_go hfuel⟩

/-- **The query-budgeted converter DPI** (converter monotonicity): for a protocol step with
Def 3.8 round bound `R` applied to two function-backed resources, a `q`-query distinguisher of
the applied systems is at most a `q·R`-query distinguisher of the resources.
The route is pad (exactly-`q`) → absorb (the DPI) → the absorbed run is `q·R`-bounded, on which
the resource-side `[q·R]` filter is invisible. -/
theorem maxAdvantage_filterQueries_applyDDC_le [Nonempty U]
    (step : U → List Y → X ⊕ V) {R : ℕ}
    (hR : PFunConverter.DDC.AnswersWithin step R)
    (q : ℕ) (P₁ P₂ : PFunPDS X Y)
    (hb₁ : PFunPDS.IsRandomFunction P₁) (hb₂ : PFunPDS.IsRandomFunction P₂) :
    Δ(⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₁,
        ⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₂)
      ≤ Δ(⌈q * R⌉ P₁, ⌈q * R⌉ P₂) := by
  classical
  have dummy : U := Classical.arbitrary U
  have hb₁' : ∀ s ∈ P₁.support, ∃ f : X → Y, s = PFunDDS.functionEvaluator f :=
    fun s hs => hb₁ s (Finsupp.mem_support_iff.mp hs)
  have hb₂' : ∀ s ∈ P₂.support, ∃ f : X → Y, s = PFunDDS.functionEvaluator f :=
    fun s hs => hb₂ s (Finsupp.mem_support_iff.mp hs)
  have hP₁ : CondEquiv.TotalOnNonempty P₁ := by
    intro s hs xs hxs
    obtain ⟨f, rfl⟩ := hb₁' s hs
    rw [PFunDDS.dom_functionEvaluator]; exact hxs
  have hP₂ : CondEquiv.TotalOnNonempty P₂ := by
    intro s hs xs hxs
    obtain ⟨f, rfl⟩ := hb₂' s hs
    rw [PFunDDS.dom_functionEvaluator]; exact hxs
  have hS₁ : CondEquiv.TotalOnNonempty
      (PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₁) := by
    intro s hs xs hxs
    obtain ⟨p, hp, rfl⟩ := Dist.mem_support_fTransform _ _ hs
    obtain ⟨f, rfl⟩ := hb₁' p hp
    exact PFunConverter.DDC.mem_dom_apply_ofStep_functionEvaluator_of_answersWithin
      step hR f hxs
  have hS₂ : CondEquiv.TotalOnNonempty
      (PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₂) := by
    intro s hs xs hxs
    obtain ⟨p, hp, rfl⟩ := Dist.mem_support_fTransform _ _ hs
    obtain ⟨f, rfl⟩ := hb₂' p hp
    exact PFunConverter.DDC.mem_dom_apply_ofStep_functionEvaluator_of_answersWithin
      step hR f hxs
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  have hQ := PFunDDS.padDDDDist_queriesExactly_support dummy q D
  have hbound : ∀ dA ∈ (Dist.fTransform (fun dd => absorb dd step)
      (PFunDDS.padDDDDist dummy q D)).support, ∀ f : X → Y, ∀ n,
      (PFunDDS.Cache.dRun dA f n).length ≤ q * R := by
    intro dA hdA f n
    obtain ⟨dd, hdd, rfl⟩ := Dist.mem_support_fTransform _ _ hdA
    exact PFunDDS.Cache.dRun_length_le_of_QueriesAtMostN _ f _
      (queriesAtMostN_absorb_of_roundBound dd step hR (hQ dd hdd)) n
  calc advantage D (⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₁)
        (⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₂)
      = advantage (PFunDDS.padDDDDist dummy q D)
          (⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₁)
          (⌈q⌉ PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₂) :=
        (advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D _ _ hS₁ hS₂).symm
    _ = advantage (PFunDDS.padDDDDist dummy q D)
          (PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₁)
          (PFunPDS.applyDDC (PFunConverter.DDC.ofStep step) P₂) := by
        unfold advantage
        rw [verdictProb_filterQueries_eq_of_queriesExactly q _ _ hS₁ hQ,
          verdictProb_filterQueries_eq_of_queriesExactly q _ _ hS₂ hQ]
    _ = advantage (Dist.fTransform (fun dd => absorb dd step)
          (PFunDDS.padDDDDist dummy q D)) P₁ P₂ :=
        advantage_absorb step hR (PFunDDS.padDDDDist dummy q D) _ _ hP₁ hP₂
    _ = advantage (Dist.fTransform (fun dd => absorb dd step)
          (PFunDDS.padDDDDist dummy q D)) (⌈q * R⌉ P₁) (⌈q * R⌉ P₂) := by
        unfold advantage
        rw [PFunDDS.Cache.verdictProb_filterQueries_eq_of_dRunBounded (q * R) _ P₁ hb₁'
            (fun d hd f _ n => hbound d hd f n),
          PFunDDS.Cache.verdictProb_filterQueries_eq_of_dRunBounded (q * R) _ P₂ hb₂'
            (fun d hd f _ n => hbound d hd f n)]
    _ ≤ Δ(⌈q * R⌉ P₁, ⌈q * R⌉ P₂) :=
        advantage_le_maxAdvantage _ _ _
          (Dist.fTransform_isProbDist _ (PFunDDS.padDDDDist_isProbDist dummy q D hD))

/-- The verdict-flipped distinguisher: same queries, negated verdict bit. -/
private def ddFlip (d : PFunDDS.DDD X Y) : PFunDDS.DDD X Y :=
  ⟨fun h => (d.val h).map id not, by
    intro h h' hpre b hb
    have hb' : Sum.map id not (d.val h) = Sum.inr b := hb
    show Sum.map id not (d.val h') = Sum.inr b
    rcases hd : d.val h with x | b₀ <;> rw [hd] at hb'
    · exact absurd hb' (by simp)
    · rw [d.property hpre b₀ hd]
      exact hb'⟩

/-- Flipping the verdict does not change the induced environment (the queries). -/
private theorem ddToDDE_ddFlip (d : PFunDDS.DDD X Y) :
    PFunDDS.ddToDDE (ddFlip d) = PFunDDS.ddToDDE d := by
  funext h
  show (match Sum.map id not (d.val h) with | Sum.inl x => some x | Sum.inr _ => none)
      = (match d.val h with | Sum.inl x => some x | Sum.inr _ => none)
  rcases d.val h with x | b <;> rfl

/-- Against *any* system, an exactly-`q` distinguisher's flip decides the complement: the padded
run stalls at round `q` (the transcript length is environment-driven), and the two verdicts are
the two readings of the stall bit. -/
private theorem verdict_ddFlip_iff (d : PFunDDS.DDD X Y) (s : PFunDDS.DDS X Y) {q : ℕ}
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q) :
    (PFunDDS.verdict (ddFlip d) s ↔ ¬ PFunDDS.verdict d s) := by
  have hlen : (PFunDDS.transcript s (PFunDDS.ddToDDE d) q).length = q :=
    transcript_length_eq (fun h hh => hQ.1 h hh) le_rfl
  have hstop : PFunDDS.ddToDDE d
      (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) q)) = none :=
    hQ.2 _ (by rw [PFunDDS.transcriptOutputs, List.length_map, hlen])
  obtain ⟨b₀, hb₀⟩ := PFunDDS.ddToDDE_eq_none_iff.mp hstop
  have hstopF : PFunDDS.ddToDDE (ddFlip d) (PFunDDS.transcriptOutputs
      (PFunDDS.transcript s (PFunDDS.ddToDDE (ddFlip d)) q)) = none := by
    rw [ddToDDE_ddFlip]; exact hstop
  rw [PFunDDS.Cache.verdict_iff_at_stall d s q hstop,
    PFunDDS.Cache.verdict_iff_at_stall (ddFlip d) s q hstopF, ddToDDE_ddFlip]
  show (Sum.map id not (d.val (PFunDDS.transcriptOutputs
      (PFunDDS.transcript s (PFunDDS.ddToDDE d) q))) = Sum.inr true) ↔ _
  rw [hb₀]
  cases b₀ <;> simp

/-- The flip complements the verdict probability: over an exactly-`q` distinguisher distribution,
`Pr[flip wins] + Pr[wins] = weight · weight` — against any system. -/
private theorem verdictProb_ddFlip_add (D : Dist (PFunDDS.DDD X Y)) {q : ℕ}
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q) (S : PFunPDS X Y) :
    verdictProb (Dist.fTransform ddFlip D) S + verdictProb D S = D.weight * S.weight := by
  unfold verdictProb
  rw [winProb_fTransform_left,
    GamePerf.winProb_congr_left D S
      (fun d hd s => verdict_ddFlip_iff d s (hQ d hd)),
    add_comm]
  exact GamePerf.winProb_add_compl PFunDDS.verdict D S

/-- **`Δ` is symmetric at the filtered surface**: for weight-equal total systems the padded
distinguisher class is closed under verdict-flip, so the signed sup swaps its arguments.  This is
the paper's implicit "Δ is a distance" step (cf. `edist_comm` in the abstract-crypto metric). -/
theorem maxAdvantage_filterQueries_swap_le [Nonempty X] (q : ℕ) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T)
    (hw : S.weight = T.weight) :
    Δ(⌈q⌉ T, ⌈q⌉ S) ≤ Δ(⌈q⌉ S, ⌈q⌉ T) := by
  classical
  have dummy : X := Classical.arbitrary X
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  rw [← advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D T S hT hS]
  have hQ := PFunDDS.padDDDDist_queriesExactly_support dummy q D
  have h₁ := verdictProb_ddFlip_add (PFunDDS.padDDDDist dummy q D) hQ (⌈q⌉ S)
  have h₂ := verdictProb_ddFlip_add (PFunDDS.padDDDDist dummy q D) hQ (⌈q⌉ T)
  have hwq : ((⌈q⌉ S).weight : ℝ) = ((⌈q⌉ T).weight : ℝ) := by
    show ((Dist.fTransform (PFunDDS.filterQueries q) S).weight : ℝ)
        = ((Dist.fTransform (PFunDDS.filterQueries q) T).weight : ℝ)
    rw [Dist.weight_fTransform, Dist.weight_fTransform, hw]
  have hflip : advantage (PFunDDS.padDDDDist dummy q D) (⌈q⌉ T) (⌈q⌉ S)
      = advantage (Dist.fTransform ddFlip (PFunDDS.padDDDDist dummy q D)) (⌈q⌉ S) (⌈q⌉ T) := by
    unfold advantage
    have h₁' : (verdictProb (Dist.fTransform ddFlip (PFunDDS.padDDDDist dummy q D)) (⌈q⌉ S) : ℝ)
        + (verdictProb (PFunDDS.padDDDDist dummy q D) (⌈q⌉ S) : ℝ)
        = ((PFunDDS.padDDDDist dummy q D).weight : ℝ) * ((⌈q⌉ S).weight : ℝ) := by
      exact h₁
    have h₂' : (verdictProb (Dist.fTransform ddFlip (PFunDDS.padDDDDist dummy q D)) (⌈q⌉ T) : ℝ)
        + (verdictProb (PFunDDS.padDDDDist dummy q D) (⌈q⌉ T) : ℝ)
        = ((PFunDDS.padDDDDist dummy q D).weight : ℝ) * ((⌈q⌉ T).weight : ℝ) := by
      exact h₂
    rw [hwq] at h₁'
    linarith
  rw [hflip]
  exact advantage_le_maxAdvantage _ _ _
    (Dist.fTransform_isProbDist _ (PFunDDS.padDDDDist_isProbDist dummy q D hD))

/-- **`Δ` is symmetric at the filtered surface** — the equality form (`edist_comm` of the
abstract-crypto metric layer, at the padded surface). -/
theorem maxAdvantage_filterQueries_comm [Nonempty X] (q : ℕ) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T)
    (hw : S.weight = T.weight) :
    Δ(⌈q⌉ S, ⌈q⌉ T) = Δ(⌈q⌉ T, ⌈q⌉ S) :=
  le_antisymm (maxAdvantage_filterQueries_swap_le q T S hT hS hw.symm)
    (maxAdvantage_filterQueries_swap_le q S T hS hT hw)

end BudgetedDPI

end RandomSystems.CR18
