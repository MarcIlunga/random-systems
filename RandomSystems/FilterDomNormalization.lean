/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CompatibleMetric

/-!
# Domain-filter distinguisher normalization

This file contains the deterministic suppression half of finite-query
normalization for `PFunPDS.filterDom`.  A rejected query is answered internally
with `none`; later queries are still simulated, because `fullyDefined` deletes a
rejected query from its kept prefix and can therefore admit a later query.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped RandomSystems.CR18 RandomSystems.CR18.CondEquiv PFunDDS

universe u v

attribute [local instance] Classical.propDecidable

variable {X : Type u} {Y : Type v}

namespace PFunDDS

/-! ## Accepted-history scan -/

/-- Scan a raw query history and retain exactly the queries whose addition
keeps the accumulated history inside `P`. -/
noncomputable def keepAdmitted (P : List X -> Prop) : List X -> List X :=
  List.foldl (fun acc x => if P (acc ++ [x]) then acc ++ [x] else acc) []

theorem keepAdmitted_append (P : List X -> Prop) (l : List X) (x : X) :
    keepAdmitted P (l ++ [x]) =
      if P (keepAdmitted P l ++ [x]) then keepAdmitted P l ++ [x]
      else keepAdmitted P l := by
  simp [keepAdmitted, List.foldl_append]

/-- Scanning a longer raw history can only extend the admitted history. -/
theorem keepAdmitted_prefix (P : List X -> Prop) {l₁ l₂ : List X}
    (hpre : l₁ <+: l₂) :
    keepAdmitted P l₁ <+: keepAdmitted P l₂ := by
  obtain ⟨tail, rfl⟩ := hpre
  induction tail generalizing l₁ with
  | nil =>
      simp
  | cons x tail ih =>
      have hstep :
          keepAdmitted P l₁ <+: keepAdmitted P (l₁ ++ [x]) := by
        rw [keepAdmitted_append]
        split
        · exact List.prefix_append _ _
        · exact List.prefix_rfl
      exact hstep.trans (by
        simpa [List.append_assoc] using ih (l₁ := l₁ ++ [x]))

/-- The admitted scan preserves its admission invariant. -/
theorem keepAdmitted_satisfies (P : List X -> Prop) (h0 : P []) :
    ∀ raw : List X, P (keepAdmitted P raw) := by
  intro raw
  induction raw using List.reverseRecOn with
  | nil =>
      exact h0
  | append_singleton raw x ih =>
      rw [keepAdmitted_append]
      split
      · assumption
      · exact ih

/-- For a total DDS, the kept prefix of `filterDom P` is precisely the
predicate-driven accepted-history scan. -/
theorem keptPrefix_filterDom_eq_keepAdmitted_of_total
    (P : List X -> Prop) (hP : PrefixClosed P) (s : DDS X Y)
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) (l : List X) :
    keptPrefix (filterDom P hP s) l = keepAdmitted P l := by
  classical
  unfold keptPrefix keepAdmitted
  let stepD : List X -> X -> List X := fun acc x =>
    if acc ++ [x] ∈ dom (filterDom P hP s) then acc ++ [x] else acc
  let stepP : List X -> X -> List X := fun acc x =>
    if P (acc ++ [x]) then acc ++ [x] else acc
  have hfold : forall (xs acc : List X),
      List.foldl stepD acc xs = List.foldl stepP acc xs := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
        intro acc
        have hiff : acc ++ [x] ∈ dom (filterDom P hP s) <-> P (acc ++ [x]) := by
          rw [mem_dom_filterDom]
          constructor
          · exact And.right
          · intro hp
            exact ⟨hs _ (by simp), hp⟩
        have hstep : stepD acc x = stepP acc x := by
          unfold stepD stepP
          by_cases hp : P (acc ++ [x])
          · rw [if_pos hp, if_pos (hiff.mpr hp)]
          · rw [if_neg hp, if_neg]
            exact fun hd => hp (hiff.mp hd)
        simp only [List.foldl_cons]
        rw [hstep]
        exact ih _
  exact hfold l []

/-! ## Suppression replay -/

/-- Replay `d` while consuming answers only for `P`-admitted queries.
Rejected queries are answered internally by `none`. -/
noncomputable def suppressViolatingGo (P : List X -> Prop) (d : DDD X Y) :
    Nat -> List X -> List (Option Y) -> List (Option Y) -> Option (X ⊕ Bool)
  | 0, _, _, _ => none
  | fuel + 1, xs, vs, h =>
      match d.val vs with
      | Sum.inr b => some (Sum.inr b)
      | Sum.inl x =>
          if P (xs ++ [x]) then
            match h with
            | [] => some (Sum.inl x)
            | oy :: h' => suppressViolatingGo P d fuel (xs ++ [x]) (vs ++ [oy]) h'
          else
            suppressViolatingGo P d fuel xs (vs ++ [none]) h

theorem suppressViolatingGo_mono (P : List X -> Prop) (d : DDD X Y) :
    forall {fuel xs vs h m},
      suppressViolatingGo P d fuel xs vs h = some m ->
      suppressViolatingGo P d (fuel + 1) xs vs h = some m := by
  intro fuel
  induction fuel with
  | zero => intro xs vs h m hm; simp [suppressViolatingGo] at hm
  | succ n ih =>
      intro xs vs h m hm
      rw [suppressViolatingGo] at hm ⊢
      cases hd : d.val vs with
      | inr b => simpa only [hd] using hm
      | inl x =>
          simp only [hd] at hm
          simp only
          by_cases hp : P (xs ++ [x])
          · rw [if_pos hp] at hm ⊢
            cases h with
            | nil => exact hm
            | cons oy h' => exact ih hm
          · rw [if_neg hp] at hm ⊢
            exact ih hm

theorem suppressViolatingGo_mono_le (P : List X -> Prop) (d : DDD X Y)
    {fuel fuel' xs vs h m} (hle : fuel <= fuel')
    (hm : suppressViolatingGo P d fuel xs vs h = some m) :
    suppressViolatingGo P d fuel' xs vs h = some m := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using hm
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by omega
      rw [he]
      exact suppressViolatingGo_mono P d ih

theorem suppressViolatingGo_append_of_inr (P : List X -> Prop) (d : DDD X Y) :
    forall {fuel xs vs h ext b},
      suppressViolatingGo P d fuel xs vs h = some (Sum.inr b) ->
      suppressViolatingGo P d fuel xs vs (h ++ ext) = some (Sum.inr b) := by
  intro fuel
  induction fuel with
  | zero => intro xs vs h ext b hm; simp [suppressViolatingGo] at hm
  | succ n ih =>
      intro xs vs h ext b hm
      rw [suppressViolatingGo] at hm ⊢
      cases hd : d.val vs with
      | inr b' => simpa only [hd] using hm
      | inl x =>
          simp only [hd] at hm
          simp only
          by_cases hp : P (xs ++ [x])
          · rw [if_pos hp] at hm ⊢
            cases h with
            | nil => simp at hm
            | cons oy h' => exact ih hm
          · rw [if_neg hp] at hm ⊢
            exact ih hm

theorem suppressViolatingGo_isSome_of_append (P : List X -> Prop) (d : DDD X Y) :
    forall {fuel xs vs h ext},
      (suppressViolatingGo P d fuel xs vs (h ++ ext)).isSome ->
      exists fuel', (suppressViolatingGo P d fuel' xs vs h).isSome := by
  intro fuel
  induction fuel with
  | zero => intro xs vs h ext hm; simp [suppressViolatingGo] at hm
  | succ n ih =>
      intro xs vs h ext hm
      rw [suppressViolatingGo] at hm
      cases hd : d.val vs with
      | inr b => exact ⟨1, by rw [suppressViolatingGo, hd]; rfl⟩
      | inl x =>
          simp only [hd] at hm
          by_cases hp : P (xs ++ [x])
          · rw [if_pos hp] at hm
            cases h with
            | nil => exact ⟨1, by simp [suppressViolatingGo, hd, hp]⟩
            | cons oy h' =>
                obtain ⟨fuel', hf⟩ := ih hm
                exact ⟨fuel' + 1, by
                  simpa [suppressViolatingGo, hd, hp] using hf⟩
          · rw [if_neg hp] at hm
            obtain ⟨fuel', hf⟩ := ih hm
            exact ⟨fuel' + 1, by
              simpa [suppressViolatingGo, hd, hp] using hf⟩

/-- The move eventually produced by the suppression replay, defaulting to
verdict `false` when internal rejected-query simulation never terminates. -/
noncomputable def suppressViolatingFun (P : List X -> Prop) (d : DDD X Y)
    (h : List (Option Y)) : X ⊕ Bool :=
  if hex : exists fuel, (suppressViolatingGo P d fuel [] [] h).isSome then
    (suppressViolatingGo P d hex.choose [] [] h).get hex.choose_spec
  else Sum.inr false

theorem suppressViolatingFun_eq_of_go {P : List X -> Prop} {d : DDD X Y}
    {h : List (Option Y)} {fuel : Nat} {m : X ⊕ Bool}
    (hm : suppressViolatingGo P d fuel [] [] h = some m) :
    suppressViolatingFun P d h = m := by
  have hex : exists fuel, (suppressViolatingGo P d fuel [] [] h).isSome :=
    ⟨fuel, by rw [hm]; rfl⟩
  unfold suppressViolatingFun
  rw [dif_pos hex]
  have h1 : suppressViolatingGo P d (max hex.choose fuel) [] [] h =
      some ((suppressViolatingGo P d hex.choose [] [] h).get hex.choose_spec) := by
    refine suppressViolatingGo_mono_le P d (le_max_left _ _) ?_
    rw [Option.some_get]
  have h2 : suppressViolatingGo P d (max hex.choose fuel) [] [] h = some m :=
    suppressViolatingGo_mono_le P d (le_max_right _ _) hm
  rw [h1] at h2
  exact Option.some.inj h2

theorem stopFinal_suppressViolatingFun (P : List X -> Prop) (d : DDD X Y) :
    StopFinal (suppressViolatingFun P d) := by
  intro h h' hpre b hb
  obtain ⟨ext, rfl⟩ := hpre
  by_cases hex : exists fuel, (suppressViolatingGo P d fuel [] [] h).isSome
  · have hval : suppressViolatingGo P d hex.choose [] [] h = some (Sum.inr b) := by
      unfold suppressViolatingFun at hb
      rw [dif_pos hex] at hb
      rw [← Option.some_get hex.choose_spec, hb]
    exact suppressViolatingFun_eq_of_go
      (suppressViolatingGo_append_of_inr P d hval)
  · have hb' : b = false := by
      unfold suppressViolatingFun at hb
      rw [dif_neg hex] at hb
      exact (Sum.inr.inj hb).symm
    subst hb'
    unfold suppressViolatingFun
    rw [dif_neg]
    rintro ⟨fuel, hs⟩
    exact hex (suppressViolatingGo_isSome_of_append P d hs)

/-- Suppress precisely the queries rejected by `filterDom P`, answering them
internally with `none` and forwarding admitted queries to the base system. -/
noncomputable def suppressViolating (P : List X -> Prop) (d : DDD X Y) : DDD X Y :=
  ⟨suppressViolatingFun P d, stopFinal_suppressViolatingFun P d⟩

@[simp] theorem suppressViolating_val (P : List X -> Prop) (d : DDD X Y) :
    (suppressViolating P d).val = suppressViolatingFun P d := rfl

/-! ## Deterministic verdict correspondence -/

theorem output_fullyDefined_filterDom_eq_none_of_not
    (P : List X -> Prop) (hP : PrefixClosed P) (s : DDS X Y)
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s)
    (raw accepted : List X) (x : X)
    (hkeep : keepAdmitted P raw = accepted)
    (hnot : ¬ P (accepted ++ [x])) :
    output (filterDom P hP s)⊥ (raw ++ [x]) (by
      rw [dom_fullyDefined]
      simp) = none := by
  rw [output_fullyDefined]
  simp only [List.dropLast_concat, List.getLast_append_singleton]
  simp only [keptPrefix_filterDom_eq_keepAdmitted_of_total P hP s hs raw, hkeep]
  rw [dif_neg]
  exact fun hdom => hnot hdom.2

theorem output_fullyDefined_filterDom_eq_of_admitted
    (P : List X -> Prop) (hP : PrefixClosed P) (s : DDS X Y)
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s)
    (raw accepted : List X) (x : X)
    (hkeep : keepAdmitted P raw = accepted)
    (hadmit : P (accepted ++ [x])) :
    output (filterDom P hP s)⊥ (raw ++ [x]) (by
      rw [dom_fullyDefined]
      simp) =
      output s⊥ (accepted ++ [x]) (by
        rw [dom_fullyDefined]
        simp) := by
  rw [output_fullyDefined, output_fullyDefined]
  simp only [List.dropLast_concat, List.getLast_append_singleton]
  simp only [keptPrefix_filterDom_eq_keepAdmitted_of_total P hP s hs raw, hkeep]
  have haccepted : accepted ∈ dom s ∨ accepted = [] := by
    rcases eq_or_ne accepted [] with hnil | hne
    · exact Or.inr hnil
    · exact Or.inl (hs accepted hne)
  simp only [keptPrefix_eq_self_of_mem_or_empty s haccepted]
  have hdom : accepted ++ [x] ∈ dom s := hs _ (by simp)
  rw [dif_pos ⟨hdom, hadmit⟩, dif_pos hdom]
  rfl

section SuppressRun

variable (P : List X -> Prop) (hP : PrefixClosed P)
  (d : DDD X Y) (s : DDS X Y)

/-- Joint evolution of the base interaction and the original interaction
against `filterDom P`.  Rejected queries extend only the filtered-side
transcript; admitted queries extend both. -/
inductive SuppressRun : List (X × Option Y) -> List (X × Option Y) -> Prop
  | init : SuppressRun [] []
  | reject {t T x} (hr : SuppressRun t T)
      (hd : d.val T↓ᵧ = Sum.inl x)
      (hnot : ¬ P (t↓ₓ ++ [x])) :
      SuppressRun t (T ++ [(x, none)])
  | accept {t T x y} (hr : SuppressRun t T)
      (hd : d.val T↓ᵧ = Sum.inl x)
      (hadmit : P (t↓ₓ ++ [x]))
      (hy : output s⊥ (t↓ₓ ++ [x]) (by rw [dom_fullyDefined]; simp) = some y) :
      SuppressRun (t ++ [(x, some y)]) (T ++ [(x, some y)])

variable {P hP d s}

theorem suppressRun_keepAdmitted :
    forall {t T}, SuppressRun P d s t T -> keepAdmitted P T↓ₓ = t↓ₓ := by
  intro t T hr
  induction hr with
  | init => rfl
  | reject hr hd hnot ih =>
      rw [transcriptInputs_append, keepAdmitted_append, ih, if_neg hnot]
  | accept hr hd hadmit hy ih =>
      rw [transcriptInputs_append, transcriptInputs_append,
        keepAdmitted_append, ih, if_pos hadmit]

/-- The base-side history of a suppression replay consists only of admitted
queries. -/
theorem suppressRun_admitted (h0 : P []) :
    forall {t T}, SuppressRun P d s t T -> P t↓ₓ := by
  intro t T hr
  induction hr with
  | init => exact h0
  | reject _hr _hd _hnot ih => exact ih
  | accept _hr _hd hadmit _hy _ih =>
      simpa only [transcriptInputs_append] using hadmit

theorem suppressViolatingGo_replay :
    forall {t T}, SuppressRun P d s t T ->
      forall {fuel h' m},
        suppressViolatingGo P d fuel t↓ₓ T↓ᵧ h' = some m ->
        exists fuel', suppressViolatingGo P d fuel' [] [] (t↓ᵧ ++ h') = some m := by
  intro t T hr
  induction hr with
  | init =>
      intro fuel h' m hm
      exact ⟨fuel, hm⟩
  | reject hr hd hnot ih =>
      rename_i t T x
      intro fuel h' m hm
      rw [transcriptOutputs_append] at hm
      refine ih (fuel := fuel + 1) ?_
      simpa [suppressViolatingGo, hd, hnot] using hm
  | accept hr hd hadmit hy ih =>
      rename_i t T x y
      intro fuel h' m hm
      rw [transcriptInputs_append, transcriptOutputs_append] at hm
      have hstep : suppressViolatingGo P d (fuel + 1) t↓ₓ T↓ᵧ (some y :: h') = some m := by
        simpa [suppressViolatingGo, hd, hadmit] using hm
      obtain ⟨fuel', hf⟩ := ih hstep
      refine ⟨fuel', ?_⟩
      rw [transcriptOutputs_append, List.append_assoc]
      exact hf

theorem suppressViolating_val_of_run {t T}
    (hr : SuppressRun P d s t T) {fuel m}
    (hgo : suppressViolatingGo P d fuel t↓ₓ T↓ᵧ [] = some m) :
    suppressViolatingFun P d t↓ᵧ = m := by
  obtain ⟨fuel', hf⟩ := suppressViolatingGo_replay hr hgo
  rw [List.append_nil] at hf
  exact suppressViolatingFun_eq_of_go hf

theorem suppressViolatingGo_extract :
    forall {fuel t T m}, SuppressRun P d s t T ->
      suppressViolatingGo P d fuel t↓ₓ T↓ᵧ [] = some m ->
      (exists T' x, SuppressRun P d s t T' ∧
        d.val T'↓ᵧ = Sum.inl x ∧ P (t↓ₓ ++ [x]) ∧ m = Sum.inl x) ∨
      (exists T' b, SuppressRun P d s t T' ∧
        d.val T'↓ᵧ = Sum.inr b ∧ m = Sum.inr b) := by
  intro fuel
  induction fuel with
  | zero => intro t T m hr hm; simp [suppressViolatingGo] at hm
  | succ n ih =>
      intro t T m hr hm
      rw [suppressViolatingGo] at hm
      cases hd : d.val T↓ᵧ with
      | inr b =>
          simp only [hd] at hm
          exact Or.inr ⟨T, b, hr, hd, by simpa using (Option.some.inj hm).symm⟩
      | inl x =>
          simp only [hd] at hm
          by_cases hp : P (t↓ₓ ++ [x])
          · rw [if_pos hp] at hm
            exact Or.inl ⟨T, x, hr, hd, hp, by simpa using (Option.some.inj hm).symm⟩
          · rw [if_neg hp] at hm
            have hr' : SuppressRun P d s t (T ++ [(x, none)]) :=
              SuppressRun.reject hr hd hp
            have hm' : suppressViolatingGo P d n t↓ₓ (T ++ [(x, none)])↓ᵧ [] = some m := by
              simpa [transcriptOutputs_append] using hm
            exact ih hr' hm'

theorem suppressRun_transcript_base :
    forall {t T}, SuppressRun P d s t T ->
      Transcript s (ddToDDE (suppressViolating P d)) t := by
  intro t T hr
  induction hr with
  | init => exact Transcript.nil
  | reject hr hd hnot ih => exact ih
  | accept hr hd hadmit hy ih =>
      rename_i t T x y
      have hmove : suppressViolatingFun P d t↓ᵧ = Sum.inl x := by
        apply suppressViolating_val_of_run hr (fuel := 1)
        simp [suppressViolatingGo, hd, hadmit]
      have hquery : ddToDDE (suppressViolating P d) t↓ᵧ = some x := by
        show (match (suppressViolating P d).val t↓ᵧ with
          | Sum.inl x => some x
          | Sum.inr _ => none) = some x
        rw [suppressViolating_val, hmove]
      have hsnoc := Transcript.snoc (S := s)
        (e := ddToDDE (suppressViolating P d)) ih hquery
      rw [hy] at hsnoc
      exact hsnoc

theorem suppressRun_transcript_filtered
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) :
    forall {t T}, SuppressRun P d s t T ->
      Transcript (filterDom P hP s) (ddToDDE d) T := by
  intro t T hr
  induction hr with
  | init => exact Transcript.nil
  | reject hr hd hnot ih =>
      rename_i t T x
      have hquery : ddToDDE d T↓ᵧ = some x := ddToDDE_eq_some_iff.mpr hd
      have hsnoc := Transcript.snoc (S := filterDom P hP s) (e := ddToDDE d) ih hquery
      have hout := output_fullyDefined_filterDom_eq_none_of_not P hP s hs
        T↓ₓ t↓ₓ x (suppressRun_keepAdmitted hr) hnot
      rw [hout] at hsnoc
      exact hsnoc
  | accept hr hd hadmit hy ih =>
      rename_i t T x y
      have hquery : ddToDDE d T↓ᵧ = some x := ddToDDE_eq_some_iff.mpr hd
      have hsnoc := Transcript.snoc (S := filterDom P hP s) (e := ddToDDE d) ih hquery
      have hout := output_fullyDefined_filterDom_eq_of_admitted P hP s hs
        T↓ₓ t↓ₓ x (suppressRun_keepAdmitted hr) hadmit
      rw [hout, hy] at hsnoc
      exact hsnoc

theorem suppressViolatingGo_replay_rev :
    forall {t T}, SuppressRun P d s t T ->
      forall {fuel h' m},
        suppressViolatingGo P d fuel [] [] (t↓ᵧ ++ h') = some m ->
        exists fuel', suppressViolatingGo P d fuel' t↓ₓ T↓ᵧ h' = some m := by
  intro t T hr
  induction hr with
  | init =>
      intro fuel h' m hm
      exact ⟨fuel, hm⟩
  | reject hr hd hnot ih =>
      rename_i t T x
      intro fuel h' m hm
      obtain ⟨fuel', hf⟩ := ih hm
      rcases fuel' with _ | n
      · simp [suppressViolatingGo] at hf
      · simp only [suppressViolatingGo, hd, if_neg hnot] at hf
        refine ⟨n, ?_⟩
        simpa [transcriptOutputs_append] using hf
  | accept hr hd hadmit hy ih =>
      rename_i t T x y
      intro fuel h' m hm
      have hm' : suppressViolatingGo P d fuel [] []
          (t↓ᵧ ++ (some y :: h')) = some m := by
        rw [transcriptOutputs_append, List.append_assoc] at hm
        exact hm
      obtain ⟨fuel', hf⟩ := ih hm'
      rcases fuel' with _ | n
      · simp [suppressViolatingGo] at hf
      · simp only [suppressViolatingGo, hd, if_pos hadmit] at hf
        refine ⟨n, ?_⟩
        simpa [transcriptInputs_append, transcriptOutputs_append] using hf

theorem suppressViolatingFun_go_of_ne_default
    {h : List (Option Y)} {m : X ⊕ Bool}
    (hv : suppressViolatingFun P d h = m) (hne : m ≠ Sum.inr false) :
    exists fuel, suppressViolatingGo P d fuel [] [] h = some m := by
  by_cases hex : exists fuel, (suppressViolatingGo P d fuel [] [] h).isSome
  · refine ⟨hex.choose, ?_⟩
    unfold suppressViolatingFun at hv
    rw [dif_pos hex] at hv
    rw [← Option.some_get hex.choose_spec, hv]
  · exfalso
    unfold suppressViolatingFun at hv
    rw [dif_neg hex] at hv
    exact hne hv.symm

/-- If suppression has consumed an answer history and is ready to forward a
query, its admitted-query state has one entry per consumed answer and the
forwarded query is an admitted extension. -/
theorem suppressViolatingGo_query_witness
    (P : List X -> Prop) (d : DDD X Y) :
    forall {fuel xs vs h x}, P xs ->
      suppressViolatingGo P d fuel xs vs h = some (Sum.inl x) ->
      exists accepted,
        P accepted /\ P (accepted ++ [x]) /\
          accepted.length = xs.length + h.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs vs h x _ hm
      simp [suppressViolatingGo] at hm
  | succ fuel ih =>
      intro xs vs h x hxs hm
      rw [suppressViolatingGo] at hm
      cases hd : d.val vs with
      | inr b => simp [hd] at hm
      | inl x' =>
          simp only [hd] at hm
          by_cases hp : P (xs ++ [x'])
          · rw [if_pos hp] at hm
            cases h with
            | nil =>
                have hxx : x' = x := by simpa using Option.some.inj hm
                subst x'
                exact ⟨xs, hxs, hp, by simp⟩
            | cons oy h =>
                obtain ⟨accepted, ha, hax, hlen⟩ := ih hp hm
                exact ⟨accepted, ha, hax, by simp at hlen ⊢; omega⟩
          · rw [if_neg hp] at hm
            exact ih hxs hm

/-- A `q`-bounded admitted-history predicate forces suppression to stop after
at most `q` externally answered queries. -/
theorem queriesAtMostN_suppressViolating
    (P : List X -> Prop) (q : ℕ) (hBound : QBounded P q)
    (h0 : P []) (d : DDD X Y) :
    Cache.QueriesAtMostN (suppressViolating P d) q := by
  intro h hh
  cases hm : suppressViolatingFun P d h with
  | inr b => exact ⟨b, by simpa [suppressViolating_val] using hm⟩
  | inl x =>
      exfalso
      obtain ⟨fuel, hgo⟩ := suppressViolatingFun_go_of_ne_default
        (P := P) (d := d) hm (by simp)
      obtain ⟨accepted, _ha, hax, hlen⟩ :=
        suppressViolatingGo_query_witness P d h0 hgo
      have hle := hBound (accepted ++ [x]) hax
      simp only [List.length_append, List.length_singleton] at hle
      omega

theorem suppressRun_of_transcript_base
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) :
    forall {t}, Transcript s (ddToDDE (suppressViolating P d)) t ->
      exists T, SuppressRun P d s t T := by
  intro t ht
  induction ht with
  | nil => exact ⟨[], SuppressRun.init⟩
  | snoc ht hquery ih =>
      rename_i t x
      obtain ⟨T, hr⟩ := ih
      have hmove : suppressViolatingFun P d t↓ᵧ = Sum.inl x := by
        rw [ddToDDE_eq_some_iff, suppressViolating_val] at hquery
        exact hquery
      obtain ⟨fuel, hgo⟩ := suppressViolatingFun_go_of_ne_default hmove (by simp)
      obtain ⟨fuel', hstate⟩ := suppressViolatingGo_replay_rev hr
        (h' := []) (by simpa using hgo)
      rcases suppressViolatingGo_extract hr hstate with hnext | hstop
      · obtain ⟨T', x', hr', hd, hp, hm⟩ := hnext
        have hxx : x' = x := Sum.inl.inj hm.symm
        subst x'
        have hprev : t↓ₓ ∈ dom s ∨ t↓ₓ = [] := by
          rcases eq_or_ne t↓ₓ [] with hnil | hne
          · exact Or.inr hnil
          · exact Or.inl (hs _ hne)
        let y : Y := output s (t↓ₓ ++ [x]) (hs _ (by simp))
        have hy : output s⊥ (t↓ₓ ++ [x]) (by rw [dom_fullyDefined]; simp) = some y := by
          exact output_fullyDefined_append_of_mem s t↓ₓ x hprev (hs _ (by simp))
        rw [hy]
        exact ⟨T' ++ [(x, some y)], SuppressRun.accept hr' hd hp hy⟩
      · obtain ⟨T', b, hr', hd, hm⟩ := hstop
        cases hm

theorem suppressRun_of_transcript_filtered
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) :
    forall {T}, Transcript (filterDom P hP s) (ddToDDE d) T ->
      exists t, SuppressRun P d s t T := by
  intro T hT
  induction hT with
  | nil => exact ⟨[], SuppressRun.init⟩
  | snoc hT hquery ih =>
      rename_i T x
      obtain ⟨t, hr⟩ := ih
      have hd : d.val T↓ᵧ = Sum.inl x := ddToDDE_eq_some_iff.mp hquery
      have hkeep : keepAdmitted P T↓ₓ = t↓ₓ := suppressRun_keepAdmitted hr
      by_cases hp : P (t↓ₓ ++ [x])
      · have hout := output_fullyDefined_filterDom_eq_of_admitted P hP s hs
          T↓ₓ t↓ₓ x hkeep hp
        have hprev : t↓ₓ ∈ dom s ∨ t↓ₓ = [] := by
          rcases eq_or_ne t↓ₓ [] with hnil | hne
          · exact Or.inr hnil
          · exact Or.inl (hs _ hne)
        let y : Y := output s (t↓ₓ ++ [x]) (hs _ (by simp))
        have hy : output s⊥ (t↓ₓ ++ [x]) (by rw [dom_fullyDefined]; simp) = some y := by
          exact output_fullyDefined_append_of_mem s t↓ₓ x hprev (hs _ (by simp))
        rw [hout, hy]
        exact ⟨t ++ [(x, some y)], SuppressRun.accept hr hd hp hy⟩
      · have hout := output_fullyDefined_filterDom_eq_none_of_not P hP s hs
          T↓ₓ t↓ₓ x hkeep hp
        rw [hout]
        exact ⟨t, SuppressRun.reject hr hd hp⟩

/-- Deterministic suppression exactly reproduces interaction with the domain
filter on every total base system. -/
theorem verdict_suppressViolating_iff_filterDom
    (P : List X -> Prop) (hP : PrefixClosed P) (d : DDD X Y) (s : DDS X Y)
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) :
    verdict (suppressViolating P d) s ↔ verdict d (filterDom P hP s) := by
  constructor
  · rintro ⟨n, hn⟩
    let t := transcript s (ddToDDE (suppressViolating P d)) n
    have ht : Transcript s (ddToDDE (suppressViolating P d)) t :=
      (transcript_mem_iff s _ t).mpr ⟨n, rfl⟩
    obtain ⟨T, hr⟩ := suppressRun_of_transcript_base hs ht
    have hfun : suppressViolatingFun P d t↓ᵧ = Sum.inr true := by
      simpa [t, suppressViolating_val] using hn
    obtain ⟨fuel, hgo⟩ := suppressViolatingFun_go_of_ne_default hfun (by simp)
    obtain ⟨fuel', hstate⟩ := suppressViolatingGo_replay_rev hr
      (h' := []) (by simpa using hgo)
    rcases suppressViolatingGo_extract hr hstate with hquery | hstop
    · obtain ⟨T', x, hr', hd, hp, hm⟩ := hquery
      cases hm
    · obtain ⟨T', b, hr', hd, hm⟩ := hstop
      have hb : b = true := Sum.inr.inj hm.symm
      subst b
      have hTf : Transcript (filterDom P hP s) (ddToDDE d) T' :=
        suppressRun_transcript_filtered hs hr'
      obtain ⟨k, hk⟩ := (transcript_mem_iff (filterDom P hP s) (ddToDDE d) T').mp hTf
      exact ⟨k, by rw [hk]; exact hd⟩
  · rintro ⟨n, hn⟩
    let T := transcript (filterDom P hP s) (ddToDDE d) n
    have hT : Transcript (filterDom P hP s) (ddToDDE d) T :=
      (transcript_mem_iff (filterDom P hP s) _ T).mpr ⟨n, rfl⟩
    obtain ⟨t, hr⟩ := suppressRun_of_transcript_filtered hs hT
    have hd : d.val T↓ᵧ = Sum.inr true := by simpa [T] using hn
    have hgo : suppressViolatingGo P d 1 t↓ₓ T↓ᵧ [] = some (Sum.inr true) := by
      simp [suppressViolatingGo, hd]
    have hfun : suppressViolatingFun P d t↓ᵧ = Sum.inr true :=
      suppressViolating_val_of_run hr hgo
    have htb : Transcript s (ddToDDE (suppressViolating P d)) t :=
      suppressRun_transcript_base hr
    obtain ⟨k, hk⟩ := (transcript_mem_iff s (ddToDDE (suppressViolating P d)) t).mp htb
    exact ⟨k, by rw [hk, suppressViolating_val]; exact hfun⟩

end SuppressRun

/-! ## History-dependent respecting padding -/

/-- Choose the original distinguisher's next query when it preserves `P`;
otherwise choose a `QExtensible` witness.  The result carries the proof that
it extends the current admitted history. -/
noncomputable def padRespectingNext
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (d : DDD X Y) (xs : {l : List X // P l}) (vs : List (Option Y))
    (hlt : xs.1.length < q) : {x : X // P (xs.1 ++ [x])} := by
  classical
  by_cases horig : ∃ x, d.val vs = Sum.inl x ∧ P (xs.1 ++ [x])
  · exact ⟨horig.choose, horig.choose_spec.2⟩
  · exact ⟨(hExt xs.1 xs.2 hlt).choose, (hExt xs.1 xs.2 hlt).choose_spec⟩

/-- Replay state for respecting padding.  The first component is the padded
query history, intrinsically certified to satisfy `P`; the second component
is the answer history already exposed to the original distinguisher. -/
noncomputable def padRespectingState
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) (h : List (Option Y)) :
    {l : List X // P l} × List (Option Y) :=
  h.foldl (fun st oy =>
    if hlt : st.1.1.length < q then
      let x := padRespectingNext P q hExt d st.1 st.2 hlt
      (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy])
    else
      (st.1, st.2 ++ [oy])) (⟨[], h0⟩, [])

@[simp]
theorem padRespectingState_snd
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) (h : List (Option Y)) :
    (padRespectingState P q hExt h0 d h).2 = h := by
  let step := fun (st : {l : List X // P l} × List (Option Y)) oy =>
    if hlt : st.1.1.length < q then
      let x := padRespectingNext P q hExt d st.1 st.2 hlt
      (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy])
    else (st.1, st.2 ++ [oy])
  have hfold : ∀ (l : List (Option Y)) st,
      (l.foldl step st).2 = st.2 ++ l := by
    intro l
    induction l with
    | nil => intro st; simp
    | cons oy l ih =>
        intro st
        simp only [List.foldl_cons]
        rw [ih]
        unfold step
        split <;> simp [List.append_assoc]
  unfold padRespectingState
  simpa [step] using hfold h (⟨[], h0⟩, [])

/-- Before the query budget is exhausted, the replay state contains one
certified admitted query for every supplied answer. -/
theorem padRespectingState_fst_length_of_lt
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) (h : List (Option Y))
    (hlt : h.length < q) :
    (padRespectingState P q hExt h0 d h).1.1.length = h.length := by
  let step := fun (st : {l : List X // P l} × List (Option Y)) oy =>
    if hlt : st.1.1.length < q then
      let x := padRespectingNext P q hExt d st.1 st.2 hlt
      (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy])
    else (st.1, st.2 ++ [oy])
  have hfold : ∀ (l : List (Option Y)) st,
      st.1.1.length = st.2.length → st.2.length + l.length < q →
      (l.foldl step st).1.1.length = st.1.1.length + l.length := by
    intro l
    induction l with
    | nil => intro st _ _; simp
    | cons oy l ih =>
        intro st hlen hbudget
        have hst : st.1.1.length < q := by simp at hbudget; omega
        simp only [List.foldl_cons]
        let x := padRespectingNext P q hExt d st.1 st.2 hst
        let st' : {l : List X // P l} × List (Option Y) :=
          (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy])
        have hstep : step st oy = st' := by simp [step, hst, st', x]
        rw [hstep, ih st']
        · simp [st']
          omega
        · simp [st', hlen]
        · simp [st'] at ⊢
          simp at hbudget
          omega
  unfold padRespectingState
  simpa [step] using hfold h (⟨[], h0⟩, []) rfl (by simpa using hlt)

/-- One-step replay equation while the padding budget remains. -/
theorem padRespectingState_append_of_lt
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) (h : List (Option Y)) (oy : Option Y)
    (hlt : h.length < q) :
    padRespectingState P q hExt h0 d (h ++ [oy]) =
      let st := padRespectingState P q hExt h0 d h
      let x := padRespectingNext P q hExt d st.1 st.2 (by
        rw [padRespectingState_fst_length_of_lt P q hExt h0 d h hlt]
        exact hlt)
      (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy]) := by
  rw [show padRespectingState P q hExt h0 d (h ++ [oy]) =
      List.foldl (fun st oy =>
        if hlt : st.1.1.length < q then
          let x := padRespectingNext P q hExt d st.1 st.2 hlt
          (⟨st.1.1 ++ [x.1], x.2⟩, st.2 ++ [oy])
        else (st.1, st.2 ++ [oy]))
        (padRespectingState P q hExt h0 d h) [oy] by
    unfold padRespectingState
    rw [List.foldl_append]]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [dif_pos (by
    rw [padRespectingState_fst_length_of_lt P q hExt h0 d h hlt]
    exact hlt)]

/-- Pad a distinguisher to exactly `q` queries using history-dependent
`QExtensible` witnesses.  Original queries are retained whenever they extend
the accumulated admitted history; an inadmissible query is replaced by a
certified extension. -/
noncomputable def padRespecting
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) : DDD X Y := by
  classical
  refine ⟨fun h =>
    if hlt : h.length < q then
      let st := padRespectingState P q hExt h0 d h
      Sum.inl (padRespectingNext P q hExt d st.1 st.2 (by
        rw [padRespectingState_fst_length_of_lt P q hExt h0 d h hlt]
        exact hlt)).1
    else
      match d.val (h.take q) with
      | Sum.inr b => Sum.inr b
      | Sum.inl _ => Sum.inr false, ?_⟩
  intro h h' hpre b hstop
  by_cases hlt : h.length < q
  · simp only [hlt, dite_true] at hstop
    cases hstop
  · have hge : q ≤ h.length := le_of_not_gt hlt
    have hge' : q ≤ h'.length := le_trans hge hpre.length_le
    have htake : h'.take q = h.take q := by
      rcases hpre with ⟨t, rfl⟩
      simpa using (List.take_append_of_le_length (l₂ := t) hge)
    simp only [hlt, not_lt.mpr hge', dite_false] at hstop ⊢
    rw [htake]
    cases hd : d.val (h.take q) with
    | inl x => simp only [hd] at hstop ⊢; cases hstop; rfl
    | inr b' => simp only [hd, Sum.inr.injEq] at hstop ⊢; exact hstop

@[simp]
theorem padRespecting_val
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) (h : List (Option Y)) :
    (padRespecting P q hExt h0 d).val h =
      if hlt : h.length < q then
        let st := padRespectingState P q hExt h0 d h
        Sum.inl (padRespectingNext P q hExt d st.1 st.2 (by
          rw [padRespectingState_fst_length_of_lt P q hExt h0 d h hlt]
          exact hlt)).1
      else
        match d.val (h.take q) with
        | Sum.inr b => Sum.inr b
        | Sum.inl _ => Sum.inr false := rfl

@[simp]
theorem ddToDDE_padRespecting_of_lt
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) {h : List (Option Y)} (hlt : h.length < q) :
    (ddToDDE (padRespecting P q hExt h0 d)) h = some
      (padRespectingNext P q hExt d
        (padRespectingState P q hExt h0 d h).1
        (padRespectingState P q hExt h0 d h).2 (by
          rw [padRespectingState_fst_length_of_lt P q hExt h0 d h hlt]
          exact hlt)).1 := by
  simp [ddToDDE, padRespecting, hlt]

@[simp]
theorem ddToDDE_padRespecting_of_ge
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) {h : List (Option Y)} (hle : q ≤ h.length) :
    (ddToDDE (padRespecting P q hExt h0 d)) h = none := by
  unfold ddToDDE padRespecting
  simp only [not_lt.mpr hle, dite_false]
  cases d.val (h.take q) <;> rfl

/-- Respecting padding makes exactly `q` queries. -/
theorem queriesExactly_ddToDDE_padRespecting
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) :
    QueriesExactly (ddToDDE (padRespecting P q hExt h0 d)) q := by
  constructor
  · intro h hlt
    rw [ddToDDE_padRespecting_of_lt P q hExt h0 d hlt]
    simp
  · intro h hle
    exact ddToDDE_padRespecting_of_ge P q hExt h0 d hle

/-- When the original query is a certified extension of the accumulated
history, respecting padding retains that query. -/
theorem padRespectingNext_eq_of_query
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (d : DDD X Y) (xs : {l : List X // P l}) (vs : List (Option Y))
    (hlt : xs.1.length < q) (x : X)
    (hd : d.val vs = Sum.inl x) (hp : P (xs.1 ++ [x])) :
    (padRespectingNext P q hExt d xs vs hlt).1 = x := by
  classical
  let hex : ∃ x, d.val vs = Sum.inl x ∧ P (xs.1 ++ [x]) := ⟨x, hd, hp⟩
  unfold padRespectingNext
  rw [dif_pos hex]
  have hchosen := (Classical.choose_spec hex).1
  have hsame : (Sum.inl x : X ⊕ Bool) = Sum.inl (Classical.choose hex) :=
    hd.symm.trans hchosen
  exact (Sum.inl.inj hsame).symm

/-- Replay invariant for respecting padding.  On every original transcript
whose visible input history satisfies `P`, the padded interaction has the
same transcript through that prefix, and its certified state is exactly the
original input history. -/
theorem padRespecting_replay_of_transcript
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P []) (d : DDD X Y) (s : DDS X Y)
    (hRespect : forall t, Transcript s (ddToDDE d) t -> P t↓ₓ) :
    forall {t}, Transcript s (ddToDDE d) t ->
      transcript s (ddToDDE (padRespecting P q hExt h0 d)) t.length = t ∧
        (padRespectingState P q hExt h0 d t↓ᵧ).1.1 = t↓ₓ := by
  intro t ht
  induction ht with
  | nil =>
      constructor
      · rfl
      · change (padRespectingState P q hExt h0 d []).1.1 = []
        rfl
  | snoc ht hquery ih =>
      rename_i t x
      let oy := output s⊥ (t↓ₓ ++ [x]) (by rw [dom_fullyDefined]; simp)
      have hfull : P (t ++ [(x, oy)])↓ₓ :=
        hRespect _ (Transcript.snoc ht hquery)
      have hlt : t.length < q := by
        have hle := hBound _ hfull
        simp only [transcriptInputs_append, List.length_append,
          List.length_singleton] at hle
        rw [transcriptInputs_length] at hle
        omega
      have hd : d.val t↓ᵧ = Sum.inl x := ddToDDE_eq_some_iff.mp hquery
      have hpnext : P
          ((padRespectingState P q hExt h0 d t↓ᵧ).1.1 ++ [x]) := by
        rw [ih.2]
        simpa only [transcriptInputs_append] using hfull
      have hstateLt :
          (padRespectingState P q hExt h0 d t↓ᵧ).1.1.length < q := by
        rw [ih.2, transcriptInputs_length]
        exact hlt
      have hnext :
          (padRespectingNext P q hExt d
            (padRespectingState P q hExt h0 d t↓ᵧ).1
            (padRespectingState P q hExt h0 d t↓ᵧ).2 hstateLt).1 = x := by
        apply padRespectingNext_eq_of_query P q hExt d
        · simpa using hd
        · exact hpnext
      have hpadQuery :
          ddToDDE (padRespecting P q hExt h0 d)
              (transcript s (ddToDDE (padRespecting P q hExt h0 d)) t.length)↓ᵧ =
            some x := by
        rw [ih.1]
        rw [ddToDDE_padRespecting_of_lt P q hExt h0 d (by
          rw [transcriptOutputs_length]
          exact hlt)]
        exact congrArg some hnext
      constructor
      · simp only [List.length_append, List.length_singleton]
        rw [transcript_succ_fire hpadQuery, ih.1]
      · rw [transcriptOutputs_append,
          padRespectingState_append_of_lt P q hExt h0 d _ oy (by
            rw [transcriptOutputs_length]
            exact hlt)]
        simp only
        rw [hnext, ih.2]
        simp only [transcriptInputs_append]

/-- At the exact padding boundary, `padRespecting` returns `true` exactly
when the original distinguisher does on the same answer history. -/
theorem padRespecting_true_iff_of_length_eq
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (h0 : P []) (d : DDD X Y) {h : List (Option Y)} (hlen : h.length = q) :
    (padRespecting P q hExt h0 d).val h = Sum.inr true ↔
      d.val h = Sum.inr true := by
  have hge : ¬ h.length < q := by omega
  rw [padRespecting_val]
  rw [dif_neg hge]
  rw [List.take_of_length_le (by omega)]
  cases d.val h <;> simp

/-- Respecting padding preserves the verdict of any `q`-bounded
distinguisher whose realized transcripts satisfy `P`.  The padded run follows
the original to its stopping prefix and only then appends certified queries. -/
theorem verdict_padRespecting_iff
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P []) (d : DDD X Y) (s : DDS X Y)
    (hAtMost : Cache.QueriesAtMostN d q)
    (hRespect : forall t, Transcript s (ddToDDE d) t -> P t↓ₓ) :
    verdict (padRespecting P q hExt h0 d) s ↔ verdict d s := by
  let padded := padRespecting P q hExt h0 d
  let t := transcript s (ddToDDE d) q
  let T := transcript s (ddToDDE padded) q
  have ht : Transcript s (ddToDDE d) t :=
    (transcript_mem_iff s (ddToDDE d) t).mpr ⟨q, rfl⟩
  have hp : P t↓ₓ := hRespect t ht
  have hlen : t.length ≤ q := by
    rw [← transcriptInputs_length t]
    exact hBound _ hp
  have hstop : ddToDDE d t↓ᵧ = none := by
    by_cases hq : q ≤ t.length
    · have heq : t.length = q := le_antisymm hlen hq
      obtain ⟨b, hb⟩ := hAtMost t↓ᵧ (by
        rw [transcriptOutputs_length, heq])
      rw [ddToDDE_eq_none_iff]
      exact ⟨b, hb⟩
    · cases hfire : ddToDDE d t↓ᵧ with
      | none => rfl
      | some x =>
          have heq := transcript_length_eq_of_fire s (ddToDDE d) hfire
          exact False.elim (hq (by rw [heq]))
  have hreplay := padRespecting_replay_of_transcript
    P q hExt hBound h0 d s hRespect ht
  have hQ : QueriesExactly (ddToDDE padded) q :=
    queriesExactly_ddToDDE_padRespecting P q hExt h0 d
  have htake : T.take t.length = t := by
    rw [show T.take t.length =
        (transcript s (ddToDDE padded) t.length) by
      exact transcript_take hQ.1 hlen (le_refl q)]
    exact hreplay.1
  have hpre : t↓ᵧ <+: T↓ᵧ := by
    have hpref : t <+: T := by
      rw [← htake]
      exact List.take_prefix t.length T
    simpa [transcriptOutputs] using hpref.map Prod.snd
  obtain ⟨b, hb⟩ := ddToDDE_eq_none_iff.mp hstop
  have hbT : d.val T↓ᵧ = Sum.inr b := d.property hpre b hb
  have hTlen : T↓ᵧ.length = q := by
    rw [transcriptOutputs_length]
    exact transcript_length_eq hQ.1 (le_refl q)
  rw [verdict_iff_at_exact padded s q hQ,
    padRespecting_true_iff_of_length_eq P q hExt h0 d hTlen,
    Cache.verdict_iff_at_stall d s q hstop]
  rw [hbT, hb]

/-- Against a total system, padding a suppressed distinguisher with
respecting extensions preserves its verdict. -/
theorem verdict_padRespecting_suppressViolating_iff_of_total
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P []) (d : DDD X Y) (s : DDS X Y)
    (hs : forall l : List X, l ≠ [] -> l ∈ dom s) :
    verdict (padRespecting P q hExt h0 (suppressViolating P d)) s ↔
      verdict (suppressViolating P d) s := by
  apply verdict_padRespecting_iff P q hExt hBound h0
  · exact queriesAtMostN_suppressViolating P q hBound h0 d
  · intro t ht
    obtain ⟨T, hr⟩ := suppressRun_of_transcript_base
      (P := P) (d := d) (s := s) hs ht
    exact suppressRun_admitted h0 hr

end PFunDDS

/-- Law-level lift of deterministic domain-filter suppression. -/
theorem verdictProb_suppressViolating_eq_filterDom
    (P : List X -> Prop) (hP : PrefixClosed P)
    (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) :
    verdictProb (Dist.fTransform (PFunDDS.suppressViolating P) D) S =
      verdictProb D (PFunPDS.filterDom P hP S) := by
  unfold verdictProb PFunPDS.filterDom
  rw [winProb_fTransform_left, winProb_fTransform_right]
  refine winProb_congr_support D S ?_
  intro s hs d
  exact PFunDDS.verdict_suppressViolating_iff_filterDom P hP d s (hS s hs)

/-- Suppression preserves the achieved signed advantage exactly: filtered
interaction on the original distinguisher is base interaction on its
suppressed pushforward. -/
theorem advantage_suppressViolating_eq_filterDom
    (P : List X -> Prop) (hP : PrefixClosed P)
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S)
    (hT : CondEquiv.TotalOnNonempty T) :
    advantage D (PFunPDS.filterDom P hP S) (PFunPDS.filterDom P hP T) =
      advantage (Dist.fTransform (PFunDDS.suppressViolating P) D) S T := by
  unfold advantage
  rw [verdictProb_suppressViolating_eq_filterDom P hP D S hS,
    verdictProb_suppressViolating_eq_filterDom P hP D T hT]

/-- Law-level verdict equivalence between suppression and its exact-`q`
respecting padding. -/
theorem verdictProb_padRespecting_suppressViolating_eq
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P [])
    (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) :
    verdictProb
        (Dist.fTransform
          (PFunDDS.padRespecting P q hExt h0 ∘ PFunDDS.suppressViolating P) D) S =
      verdictProb (Dist.fTransform (PFunDDS.suppressViolating P) D) S := by
  unfold verdictProb
  rw [winProb_fTransform_left, winProb_fTransform_left]
  refine winProb_congr_support D S ?_
  intro s hs d
  exact PFunDDS.verdict_padRespecting_suppressViolating_iff_of_total
    P q hExt hBound h0 d s (hS s hs)

/-- Exact respecting padding preserves the suppressed distinguisher's signed
advantage against total base systems. -/
theorem advantage_padRespecting_suppressViolating_eq
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P [])
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S)
    (hT : CondEquiv.TotalOnNonempty T) :
    advantage
        (Dist.fTransform
          (PFunDDS.padRespecting P q hExt h0 ∘ PFunDDS.suppressViolating P) D) S T =
      advantage (Dist.fTransform (PFunDDS.suppressViolating P) D) S T := by
  unfold advantage
  rw [verdictProb_padRespecting_suppressViolating_eq P q hExt hBound h0 D S hS,
    verdictProb_padRespecting_suppressViolating_eq P q hExt hBound h0 D T hT]

/-- The domination orientation used by domain-filter normalization.  In fact
the two advantages are equal. -/
theorem advantage_suppressViolating_le_padRespecting
    (P : List X -> Prop) (q : ℕ) (hExt : QExtensible P q)
    (hBound : QBounded P q) (h0 : P [])
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S)
    (hT : CondEquiv.TotalOnNonempty T) :
    advantage (Dist.fTransform (PFunDDS.suppressViolating P) D) S T ≤
      advantage
        (Dist.fTransform
          (PFunDDS.padRespecting P q hExt h0 ∘ PFunDDS.suppressViolating P) D) S T :=
  le_of_eq (advantage_padRespecting_suppressViolating_eq
    P q hExt hBound h0 D S T hS hT).symm

/-! ## Raw finite-query normalization

The finite support of a probabilistic distinguisher and of the two systems
gives one uniform round after every successful verdict on those supports.
Truncation at the following round preserves all such verdicts and makes the
distinguisher stop everywhere; ordinary CR18 padding then supplies the exact
query count expected by the fixed-round Theorem 4.17 proof. -/

/-- CR18 §4.10.1 finite-query normalization for arbitrary total probability
systems.  This discharges `DeltaFiniteQueryNormalization` from the standing
system assumptions instead of exposing it at paper-facing call sites. -/
theorem deltaFiniteQueryNormalization_of_totalOnNonempty [Nonempty X]
    (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S)
    (hT : CondEquiv.TotalOnNonempty T) :
    DeltaFiniteQueryNormalization S T := by
  classical
  intro D hD
  let i :=
    (D.support ×ˢ (S.support ∪ T.support)).sup fun p =>
      if h : PFunDDS.verdict p.1 p.2 then Nat.find h else 0
  let q := i + 1
  let Dtrunc :=
    Dist.fTransform (PFunDDS.truncDDD q) D
  let Dexact :=
    PFunDDS.padDDDDist (Classical.arbitrary X) q Dtrunc

  have hwitness :
      ∀ d ∈ D.support, ∀ s ∈ S.support ∪ T.support,
        ∀ h : PFunDDS.verdict d s, Nat.find h < q := by
    intro d hd s hs h
    have hmem : (d, s) ∈ D.support ×ˢ (S.support ∪ T.support) :=
      Finset.mem_product.mpr ⟨hd, hs⟩
    have hle := Finset.le_sup
      (f := fun p =>
        if h : PFunDDS.verdict p.1 p.2 then Nat.find h else 0) hmem
    dsimp only at hle
    rw [dif_pos h] at hle
    simp only [q]
    omega

  have hverdictTrunc :
      ∀ R : PFunPDS X Y, R.support ⊆ S.support ∪ T.support →
        verdictProb Dtrunc R = verdictProb D R := by
    intro R hR
    unfold verdictProb Dtrunc
    rw [winProb_fTransform_left]
    refine GamePerf.winProb_congr_support D R fun d hd s hs => ?_
    constructor
    · exact PFunDDS.verdict_of_verdict_truncDDD
    · intro h
      exact PFunDDS.verdict_truncDDD_of_lt
        (hwitness d hd s (hR hs) h) (Nat.find_spec h)

  have hverdictTruncFilter :
      ∀ R : PFunPDS X Y, CondEquiv.TotalOnNonempty R →
        verdictProb Dtrunc (⌈q⌉ R) = verdictProb Dtrunc R := by
    intro R hR
    unfold verdictProb PFunPDS.filterQueries
    rw [winProb_fTransform_right]
    refine GamePerf.winProb_congr_support Dtrunc R fun d hd s hs => ?_
    obtain ⟨d₀, _, rfl⟩ := mem_support_fTransform _ _ hd
    have htranscript :
        PFunDDS.transcript (PFunDDS.filterQueries q s)
            (PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)) q =
          PFunDDS.transcript s
            (PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)) q :=
      PFunDDS.transcript_filterQueries_eq_of_le
        s q (hR s hs) _ le_rfl
    have hstop :
        PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)
          ((PFunDDS.transcript s
            (PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)) q)↓ᵧ) = none :=
      PFunDDS.ddToDDE_truncDDD_stall q d₀ s
    have hstopFiltered :
        PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)
          ((PFunDDS.transcript (PFunDDS.filterQueries q s)
            (PFunDDS.ddToDDE (PFunDDS.truncDDD q d₀)) q)↓ᵧ) = none := by
      rw [htranscript]
      exact hstop
    rw [PFunDDS.Cache.verdict_iff_at_stall _ _ q hstopFiltered,
      PFunDDS.Cache.verdict_iff_at_stall _ _ q hstop, htranscript]

  have hverdictExact :
      ∀ R : PFunPDS X Y, CondEquiv.TotalOnNonempty R →
        verdictProb Dexact R = verdictProb Dtrunc R := by
    intro R hR
    have hQ := PFunDDS.padDDDDist_queriesExactly_support
      (Classical.arbitrary X) q Dtrunc
    calc
      verdictProb Dexact R
          = verdictProb Dexact (⌈q⌉ R) := by
              symm
              exact verdictProb_filterQueries_eq_of_queriesExactly
                q Dexact R hR hQ
      _ = verdictProb Dtrunc (⌈q⌉ R) := by
              exact verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty
                (Classical.arbitrary X) q Dtrunc R hR
      _ = verdictProb Dtrunc R := hverdictTruncFilter R hR

  refine ⟨i, Dexact, ?_, ?_, ?_⟩
  · exact PFunDDS.padDDDDist_isProbDist
      (Classical.arbitrary X) q Dtrunc
      (Dist.fTransform_isProbDist _ hD)
  · simpa only [q] using
      PFunDDS.padDDDDist_queriesExactly_support
        (Classical.arbitrary X) q Dtrunc
  · unfold advantage
    rw [hverdictExact T hT, hverdictExact S hS,
      hverdictTrunc T Finset.subset_union_right,
      hverdictTrunc S Finset.subset_union_left]

/-- **CR18 Theorem 4.17 under a common prefix-closed restriction.**
Conditional equivalence, MBO stripping, and the blind-game bound all use the
same restricted history domain; totality is required only of the unrestricted
systems. -/
theorem maxAdvantage_filterDom_le_blindMaxWinProb_of_condEquiv [Nonempty X]
    (P : List X → Prop) (hP : PrefixClosed P)
    (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y)
    (hCE : Shat |≡ T)
    (hmono : MonotoneMBO Shat := by cr18_standing)
    (hShat : Shat.isProbDist := by cr18_standing)
    (hT : T.isProbDist := by cr18_standing)
    (hShatTot : CondEquiv.TotalOnNonempty Shat := by cr18_standing)
    (hTTot : CondEquiv.TotalOnNonempty T := by cr18_standing) :
    (Δ(PFunPDS.filterDom P hP (PFunPDS.ignoreMBO Shat),
        PFunPDS.filterDom P hP T) : ℝ) ≤
      (Γᵇ (PFunPDS.filterDom P hP Shat) : ℝ) := by
  classical
  let outputs :
      {Z : Type v} → PFunDDS.DDS X Z → List X → List (Option Z) :=
    fun {Z} s xs =>
      List.ofFn fun k : Fin xs.length =>
        PFunDDS.output s⊥ (xs.take (k.1 + 1)) (by
          rw [PFunDDS.dom_fullyDefined]
          change xs.take (k.1 + 1) ≠ []
          rw [← List.length_pos_iff_ne_nil, List.length_take]
          omega)
  let badSoFar :
      PFunDDS.DDS X (Y × Bool) → List X → Bool :=
    fun g xs =>
      (outputs g xs).any fun oy =>
        match oy with
        | none => false
        | some (_, bad) => bad
  let completeGame :
      PFunDDS.DDS X (Y × Bool) → PFunDDS.DDS X (Option Y × Bool) :=
    fun g =>
      PFunDDS.historyEvaluator fun xs hxs =>
        (Option.map Prod.fst
            (PFunDDS.output g⊥ xs (by
              rw [PFunDDS.dom_fullyDefined]
              exact hxs)),
          badSoFar g xs)
  let ShatFull : PFunPDS X (Option Y × Bool) :=
    Dist.fTransform
      (fun g => completeGame (PFunDDS.filterDom P hP g)) Shat
  let completeSystem :
      PFunDDS.DDS X Y → PFunDDS.DDS X (Option Y) :=
    fun s =>
      PFunDDS.historyEvaluator fun xs hxs =>
        PFunDDS.output s⊥ xs (by
          rw [PFunDDS.dom_fullyDefined]
          exact hxs)
  let Tfull : PFunPDS X (Option Y) :=
    Dist.fTransform
      (fun t => completeSystem (PFunDDS.filterDom P hP t)) T

  have completeSystem_eq :
      ∀ s : PFunDDS.DDS X Y,
        completeSystem s = s⊥ := by
    intro s
    apply Subtype.ext
    funext xs
    apply Part.ext'
    · change xs ≠ [] ↔ xs ≠ []
      rfl
    · intro h₁ h₂
      rfl

  have outputs_nil :
      ∀ {Z : Type v} (s : PFunDDS.DDS X Z),
        outputs s [] = [] := by
    intro Z s
    simp [outputs]

  have outputs_append :
      ∀ {Z : Type v} (s : PFunDDS.DDS X Z)
        (xs : List X) (x : X),
        outputs s (xs ++ [x]) =
          outputs s xs ++
            [PFunDDS.output s⊥ (xs ++ [x]) (by
              rw [PFunDDS.dom_fullyDefined]
              simp)] := by
    intro Z s xs x
    unfold outputs
    simp only [List.length_append, List.length_singleton]
    change
      List.ofFn
          (fun k : Fin (xs.length + 1) =>
            PFunDDS.output s⊥ ((xs ++ [x]).take (k.1 + 1)) _) =
        List.ofFn
            (fun k : Fin xs.length =>
              PFunDDS.output s⊥ (xs.take (k.1 + 1)) _) ++
          [PFunDDS.output s⊥ (xs ++ [x]) _]
    rw [List.ofFn_succ', List.concat_eq_append]
    apply congrArg₂ (· ++ ·)
    · apply congrArg List.ofFn
      funext k
      apply PFunDDS.output_congr
      simp [List.take_append_of_le_length]
    · congr 1
      apply PFunDDS.output_congr
      simp

  have outputs_filterMap :
      ∀ {Z : Type v}
        (s : PFunDDS.DDS X Z)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (raw : List X),
        (outputs (PFunDDS.filterDom P hP s) raw).filterMap id =
          (outputs s (PFunDDS.keepAdmitted P raw)).filterMap id := by
    intro Z s hs raw
    induction raw using List.reverseRecOn with
    | nil => simp [PFunDDS.keepAdmitted, outputs]
    | append_singleton raw x ih =>
        rw [outputs_append, PFunDDS.keepAdmitted_append]
        by_cases hadmit :
            P (PFunDDS.keepAdmitted P raw ++ [x])
        · rw [if_pos hadmit, outputs_append]
          have hout :=
            PFunDDS.output_fullyDefined_filterDom_eq_of_admitted
              P hP s hs raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          have hprevious :
              PFunDDS.keepAdmitted P raw ∈ PFunDDS.dom s ∨
                PFunDDS.keepAdmitted P raw = [] := by
            rcases eq_or_ne (PFunDDS.keepAdmitted P raw) [] with hnil | hne
            · exact Or.inr hnil
            · exact Or.inl (hs _ hne)
          have hproper :=
            PFunDDS.output_fullyDefined_append_of_mem
              s (PFunDDS.keepAdmitted P raw) x hprevious
                (hs _ (by simp))
          rw [hout, hproper]
          simpa using ih
        · rw [if_neg hadmit]
          have hout :=
            PFunDDS.output_fullyDefined_filterDom_eq_none_of_not
              P hP s hs raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          rw [hout]
          simpa using ih

  have outputs_total_map_some :
      ∀ {Z : Type v}
        (s : PFunDDS.DDS X Z)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (xs : List X),
        ∃ ys : List Z, outputs s xs = ys.map some := by
    intro Z s hs xs
    let ys : List Z :=
      List.ofFn fun k : Fin xs.length =>
        PFunDDS.output s (xs.take (k.1 + 1))
          (hs _ (by
            rw [← List.length_pos_iff_ne_nil, List.length_take]
            omega))
    refine ⟨ys, ?_⟩
    unfold outputs ys
    rw [← List.ofFn_comp']
    apply congrArg List.ofFn
    funext k
    have hprefix :
        xs.take k.1 ∈ PFunDDS.dom s ∨ xs.take k.1 = [] := by
      rcases eq_or_ne (xs.take k.1) [] with hnil | hne
      · exact Or.inr hnil
      · exact Or.inl (hs _ hne)
    have hnext :
        xs.take k.1 ++ [xs.get k] ∈ PFunDDS.dom s :=
      hs _ (by
        intro hnil
        have := congrArg List.length hnil
        simp at this)
    have hout :=
      PFunDDS.output_fullyDefined_append_of_mem
        s (xs.take k.1) (xs.get k) hprefix hnext
    have htake :
        xs.take (k.1 + 1) = xs.take k.1 ++ [xs.get k] := by
      rw [List.take_succ_eq_append_getElem k.2, List.get_eq_getElem]
    simpa only [htake] using hout

  have output_full_eq_some :
      ∀ {Z : Type v}
        (s : PFunDDS.DDS X Z)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (l : List X) (hne : l ≠ []),
        PFunDDS.output s⊥ l (by
          rw [PFunDDS.dom_fullyDefined]
          exact hne) =
          some (PFunDDS.output s l (hs l hne)) := by
    intro Z s hs l hne
    have hdecomp : l.dropLast ++ [l.getLast hne] = l :=
      List.dropLast_append_getLast hne
    have hprevious :
        l.dropLast ∈ PFunDDS.dom s ∨ l.dropLast = [] := by
      rcases eq_or_ne l.dropLast [] with hnil | hnonempty
      · exact Or.inr hnil
      · exact Or.inl (hs _ hnonempty)
    have hout :=
      PFunDDS.output_fullyDefined_append_of_mem
        s l.dropLast (l.getLast hne) hprevious
          (hs _ (by simpa [hdecomp] using hne))
    calc
      PFunDDS.output s⊥ l _ =
          PFunDDS.output s⊥
            (l.dropLast ++ [l.getLast hne]) _ :=
        PFunDDS.output_congr _ hdecomp.symm _ _
      _ = some
            (PFunDDS.output s
              (l.dropLast ++ [l.getLast hne])
              (hs _ (by simp))) := hout
      _ = some (PFunDDS.output s l (hs l hne)) := by
        congr 1
        exact PFunDDS.output_congr s hdecomp _ _

  have outputs_filter_isSome :
      ∀ {Z W : Type v}
        (s : PFunDDS.DDS X Z) (t : PFunDDS.DDS X W)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (ht : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom t)
        (raw : List X),
        (outputs (PFunDDS.filterDom P hP s) raw).map Option.isSome =
          (outputs (PFunDDS.filterDom P hP t) raw).map Option.isSome := by
    intro Z W s t hs ht raw
    induction raw using List.reverseRecOn with
    | nil => simp [outputs]
    | append_singleton raw x ih =>
        rw [outputs_append, outputs_append,
          List.map_append, List.map_append]
        by_cases hadmit :
            P (PFunDDS.keepAdmitted P raw ++ [x])
        · have hsout :=
            PFunDDS.output_fullyDefined_filterDom_eq_of_admitted
              P hP s hs raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          have htout :=
            PFunDDS.output_fullyDefined_filterDom_eq_of_admitted
              P hP t ht raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          have hsproper :
              ∃ y, PFunDDS.output s⊥
                (PFunDDS.keepAdmitted P raw ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            have hprevious :
                PFunDDS.keepAdmitted P raw ∈ PFunDDS.dom s ∨
                  PFunDDS.keepAdmitted P raw = [] := by
              rcases eq_or_ne (PFunDDS.keepAdmitted P raw) [] with hnil | hne
              · exact Or.inr hnil
              · exact Or.inl (hs _ hne)
            refine
              ⟨PFunDDS.output s
                (PFunDDS.keepAdmitted P raw ++ [x])
                (hs _ (by simp)), ?_⟩
            exact PFunDDS.output_fullyDefined_append_of_mem
              s (PFunDDS.keepAdmitted P raw) x hprevious
                (hs _ (by simp))
          have htproper :
              ∃ y, PFunDDS.output t⊥
                (PFunDDS.keepAdmitted P raw ++ [x])
                (by rw [PFunDDS.dom_fullyDefined]; simp) = some y := by
            have hprevious :
                PFunDDS.keepAdmitted P raw ∈ PFunDDS.dom t ∨
                  PFunDDS.keepAdmitted P raw = [] := by
              rcases eq_or_ne (PFunDDS.keepAdmitted P raw) [] with hnil | hne
              · exact Or.inr hnil
              · exact Or.inl (ht _ hne)
            refine
              ⟨PFunDDS.output t
                (PFunDDS.keepAdmitted P raw ++ [x])
                (ht _ (by simp)), ?_⟩
            exact PFunDDS.output_fullyDefined_append_of_mem
              t (PFunDDS.keepAdmitted P raw) x hprevious
                (ht _ (by simp))
          obtain ⟨sy, hsy⟩ := hsproper
          obtain ⟨ty, hty⟩ := htproper
          rw [hsout, htout, hsy, hty]
          simpa using ih
        · have hsout :=
            PFunDDS.output_fullyDefined_filterDom_eq_none_of_not
              P hP s hs raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          have htout :=
            PFunDDS.output_fullyDefined_filterDom_eq_none_of_not
              P hP t ht raw (PFunDDS.keepAdmitted P raw) x rfl hadmit
          rw [hsout, htout]
          simpa using ih

  have filterMap_length_of_isSome :
      ∀ {Z : Type v} {a b : List (Option Z)},
        a.map Option.isSome = b.map Option.isSome →
          (a.filterMap id).length = (b.filterMap id).length := by
    intro Z a b h
    have hlength :
        ∀ l : List (Option Z),
          (l.filterMap id).length =
            (l.map Option.isSome).count true := by
      intro l
      induction l with
      | nil => rfl
      | cons o l ih =>
          cases o with
          | none =>
              change
                (l.filterMap id).length =
                  (l.map Option.isSome).count true
              exact ih
          | some y =>
              change
                (y :: l.filterMap id).length =
                  (true :: l.map Option.isSome).count true
              simp only [List.length_cons, List.count_cons]
              exact congrArg Nat.succ ih
    rw [hlength a, h, ← hlength b]

  have filterMap_map_some :
      ∀ {Z : Type v} (ys : List Z),
        (ys.map some).filterMap id = ys := by
    intro Z ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
        change y :: (ys.map some).filterMap id = y :: ys
        rw [ih]

  have outputs_filterMap_length :
      ∀ {Z : Type v}
        (s : PFunDDS.DDS X Z)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (raw : List X),
        ((outputs (PFunDDS.filterDom P hP s) raw).filterMap id).length =
          (PFunDDS.keepAdmitted P raw).length := by
    intro Z s hs raw
    rw [outputs_filterMap s hs raw]
    obtain ⟨ys, hys⟩ :=
      outputs_total_map_some s hs (PFunDDS.keepAdmitted P raw)
    have hlength :
        ys.length = (PFunDDS.keepAdmitted P raw).length := by
      have h := congrArg List.length hys
      simpa [outputs] using h.symm
    rw [hys]
    have hfilter : (ys.map some).filterMap id = ys :=
      filterMap_map_some ys
    rw [hfilter, hlength]

  have optionList_eq_iff_filterMap :
      ∀ {Z : Type v} {a b : List (Option Z)},
        a.map Option.isSome = b.map Option.isSome →
          (a = b ↔ a.filterMap id = b.filterMap id) := by
    intro Z a b hshape
    constructor
    · intro h
      rw [h]
    · intro hfiltered
      induction a generalizing b with
      | nil =>
          cases b with
          | nil => rfl
          | cons ob b =>
              simp at hshape
      | cons oa as ih =>
          cases b with
          | nil =>
              simp at hshape
          | cons ob bs =>
              simp only [List.map_cons, List.cons.injEq] at hshape
              rcases hshape with ⟨hhead, htail⟩
              cases oa with
              | none =>
                  cases ob with
                  | none =>
                      have hfiltered' :
                          as.filterMap id = bs.filterMap id := by
                        simpa using hfiltered
                      rw [ih htail hfiltered']
                  | some y =>
                      simp at hhead
              | some ya =>
                  cases ob with
                  | none =>
                      simp at hhead
                  | some yb =>
                      have hfiltered' :
                          ya :: as.filterMap id =
                            yb :: bs.filterMap id := by
                        simpa using hfiltered
                      have hparts := List.cons.inj hfiltered'
                      have hvalue := hparts.1
                      have htails := ih htail hparts.2
                      rw [hvalue, htails]

  have outputs_filter_eq_iff_compact :
      ∀ {Z : Type v}
        (s t : PFunDDS.DDS X Z)
        (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
        (ht : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom t)
        (raw : List X) (zs : List (Option Z)),
        (outputs (PFunDDS.filterDom P hP t) raw).map Option.isSome =
            zs.map Option.isSome →
          (outputs (PFunDDS.filterDom P hP s) raw = zs ↔
            outputs s (PFunDDS.keepAdmitted P raw) =
              (zs.filterMap id).map some) := by
    intro Z s t hs ht raw zs hshape
    have hshapeS :
        (outputs (PFunDDS.filterDom P hP s) raw).map Option.isSome =
          zs.map Option.isSome :=
      (outputs_filter_isSome s t hs ht raw).trans hshape
    rw [optionList_eq_iff_filterMap hshapeS,
      outputs_filterMap s hs raw]
    obtain ⟨ys, hys⟩ :=
      outputs_total_map_some s hs (PFunDDS.keepAdmitted P raw)
    rw [hys]
    have hfilter : (ys.map some).filterMap id = ys :=
      filterMap_map_some ys
    rw [hfilter]
    exact
      ⟨fun h => congrArg (List.map some) h,
        fun h =>
          (List.map_injective_iff.mpr
            (Option.some_injective Z)) h⟩

  have outputs_eq_iff_get :
      ∀ {Z : Type v}
        (s : PFunDDS.DDS X Z)
        (xs : List X) (ys : List (Option Z)),
        ∀ hlength : xs.length = ys.length,
          (outputs s xs = ys ↔
            ∀ k : Fin xs.length,
              PFunDDS.output s⊥ (xs.take (k.1 + 1)) (by
                rw [PFunDDS.dom_fullyDefined]
                change xs.take (k.1 + 1) ≠ []
                rw [← List.length_pos_iff_ne_nil, List.length_take]
                omega) =
                ys.get (Fin.cast hlength k)) := by
    intro Z s xs ys hlength
    constructor
    · intro h k
      have hk : k.1 < (outputs s xs).length := by
        simpa [outputs] using k.2
      have hget := List.getElem_of_eq h (i := k.1) hk
      simpa [outputs, List.get_eq_getElem] using hget
    · intro h
      apply List.ext_getElem
      · simp [outputs, hlength]
      · intro n hn₁ hn₂
        have hn : n < xs.length := by
          simpa [outputs] using hn₁
        have hget := h ⟨n, hn⟩
        simpa [outputs, List.get_eq_getElem] using hget

  have badSoFar_mono :
      ∀ (g : PFunDDS.DDS X (Y × Bool))
        {xs₁ xs₂ : List X},
        xs₁ <+: xs₂ →
          badSoFar g xs₁ = true →
            badSoFar g xs₂ = true := by
    intro g xs₁ xs₂ hprefix
    obtain ⟨tail, rfl⟩ := hprefix
    induction tail using List.reverseRecOn with
    | nil => simp
    | append_singleton tail x ih =>
        rw [← List.append_assoc]
        intro hbad
        have hprevious := ih hbad
        unfold badSoFar at hprevious ⊢
        rw [outputs_append, List.any_append, hprevious]
        simp

  have completeGame_isGame :
      ∀ g : PFunDDS.DDS X (Y × Bool),
        (completeGame g).IsGame := by
    intro g
    exact PFunDDS.historyEvaluator_pair_isGame_of_monotone
      (fun xs hxs =>
        Option.map Prod.fst
          (PFunDDS.output g⊥ xs (by
            rw [PFunDDS.dom_fullyDefined]
            exact hxs)))
      (badSoFar g)
      (fun hprefix =>
        Bool.le_iff_imp.mpr (badSoFar_mono g hprefix))

  have any_bit_filterMap :
      ∀ (os : List (Option (Y × Bool))),
        os.any (fun oy =>
            match oy with
            | none => false
            | some (_, bad) => bad) =
          (os.filterMap id).any Prod.snd := by
    intro os
    induction os with
    | nil => rfl
    | cons o os ih =>
        cases o <;> simp [ih]

  have badSoFar_filter :
      ∀ (g : PFunDDS.DDS X (Y × Bool))
        (hg : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom g)
        (raw : List X),
        badSoFar (PFunDDS.filterDom P hP g) raw =
          badSoFar g (PFunDDS.keepAdmitted P raw) := by
    intro g hg raw
    unfold badSoFar
    rw [any_bit_filterMap, any_bit_filterMap,
      outputs_filterMap g hg raw]

  have badSoFar_eq_output_bit :
      ∀ (g : PFunDDS.DDS X (Y × Bool)),
        g.IsGame →
        ∀ htotal : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom g,
        ∀ (xs : List X) (hxs : xs ≠ []),
          badSoFar g xs =
            (PFunDDS.output g xs (htotal xs hxs)).2 := by
    intro g hgame htotal xs hxs
    induction xs using List.reverseRecOn with
    | nil => simp at hxs
    | append_singleton xs x ih =>
        have hprevious :
            xs ∈ PFunDDS.dom g ∨ xs = [] := by
          rcases eq_or_ne xs [] with hnil | hnonempty
          · exact Or.inr hnil
          · exact Or.inl (htotal xs hnonempty)
        have hlast :=
          PFunDDS.output_fullyDefined_append_of_mem
            g xs x hprevious (htotal (xs ++ [x]) (by simp))
        unfold badSoFar
        rw [outputs_append, List.any_append, hlast]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        change
          (badSoFar g xs ||
              (PFunDDS.output g (xs ++ [x])
                (htotal _ (by simp))).2) =
            (PFunDDS.output g (xs ++ [x])
              (htotal _ (by simp))).2
        by_cases hfinal :
            (PFunDDS.output g (xs ++ [x])
              (htotal _ (by simp))).2 = true
        · simp [hfinal]
        · have hfinalFalse :
              (PFunDDS.output g (xs ++ [x])
                (htotal _ (by simp))).2 = false := by
            simpa using hfinal
          have hprefixFalse : badSoFar g xs = false := by
            rcases eq_or_ne xs [] with hnil | hnonempty
            · simp [hnil, badSoFar, outputs]
            · rw [ih hnonempty]
              exact PFunDDS.outputBit_false_of_isGame
                hgame (by simp) hnonempty
                (htotal xs hnonempty)
                (htotal (xs ++ [x]) (by simp))
                hfinalFalse
          rw [hprefixFalse, hfinalFalse]
          rfl

  have ignore_completeGame :
      ∀ g : PFunDDS.DDS X (Y × Bool),
        PFunDDS.ignoreMBO (completeGame g) =
          (PFunDDS.ignoreMBO g)⊥ := by
    intro g
    apply Subtype.ext
    funext xs
    apply Part.ext'
    · change xs ≠ [] ↔ xs ≠ []
      rfl
    · intro h₁ h₂
      have hxs : xs ≠ [] := by
        simpa [completeGame] using h₁
      change
        Option.map Prod.fst
            (PFunDDS.output g⊥ xs (by
              rw [PFunDDS.dom_fullyDefined]
              exact hxs)) =
          PFunDDS.output ((PFunDDS.ignoreMBO g)⊥) xs h₂
      symm
      exact PFunDDS.output_fullyDefined_ignoreMBO g xs h₂
        (by
          rw [PFunDDS.dom_fullyDefined]
          exact hxs)

  have outputs_ignoreMBO :
      ∀ (g : PFunDDS.DDS X (Y × Bool)) (raw : List X),
        outputs (PFunDDS.ignoreMBO g) raw =
          (outputs g raw).map (Option.map Prod.fst) := by
    intro g raw
    unfold outputs
    rw [← List.ofFn_comp']
    apply congrArg List.ofFn
    funext k
    exact PFunDDS.output_fullyDefined_ignoreMBO g _ _ _

  have optionPairList_eq_tagFalse :
      ∀ (os : List (Option (Y × Bool)))
        (zs : List (Option Y)),
        (os = zs.map (Option.map fun y => (y, false)) ↔
          os.map (Option.map Prod.fst) = zs ∧
            os.any (fun oy =>
              match oy with
              | none => false
              | some (_, bad) => bad) = false) := by
    intro os
    induction os with
    | nil =>
        intro zs
        cases zs <;> simp
    | cons o os ih =>
        intro zs
        cases zs with
        | nil => simp
        | cons z zs =>
            cases o <;> cases z
            · simp [ih]
            · simp
            · rename_i p
              cases p
              simp
            · rename_i p y
              cases p with
              | mk y' bad =>
                  cases bad <;> simp [ih, and_assoc]

  have completeGame_outputs_false :
      ∀ (g : PFunDDS.DDS X (Y × Bool))
        (raw : List X) (zs : List (Option Y))
        (hlength : raw.length = zs.length),
        ((∀ k : Fin raw.length,
            Option.map Prod.fst
                (PFunDDS.output g⊥
                  (raw.take (k.1 + 1)) (by
                    rw [PFunDDS.dom_fullyDefined]
                    change raw.take (k.1 + 1) ≠ []
                    rw [← List.length_pos_iff_ne_nil,
                      List.length_take]
                    omega)) =
              zs.get (Fin.cast hlength k)) ∧
            badSoFar g raw = false ↔
          outputs g raw =
            zs.map (Option.map fun y => (y, false))) := by
    intro g raw zs hlength
    rw [optionPairList_eq_tagFalse]
    constructor
    · rintro ⟨hout, hbad⟩
      refine ⟨?_, hbad⟩
      rw [← outputs_ignoreMBO]
      rw [outputs_eq_iff_get
        (PFunDDS.ignoreMBO g) raw zs hlength]
      intro k
      have h := hout k
      rw [PFunDDS.output_fullyDefined_ignoreMBO g]
      exact h
    · rintro ⟨hout, hbad⟩
      refine ⟨?_, hbad⟩
      rw [← outputs_ignoreMBO] at hout
      rw [outputs_eq_iff_get
        (PFunDDS.ignoreMBO g) raw zs hlength] at hout
      intro k
      have h := hout k
      rw [← PFunDDS.output_fullyDefined_ignoreMBO g]
      exact h

  have massY_Tfull :
      ∀ {i : ℕ}
        (zs : Vector (Option Y) (i + 1))
        (xs : Vector X (i + 1)),
        CondEquiv.massY Tfull i zs xs =
          T.mass fun t =>
            outputs (PFunDDS.filterDom P hP t) xs.toList =
              zs.toList := by
    intro i zs xs
    simp only [Tfull, completeSystem]
    rw [CondEquiv.massY_fTransform_historyEvaluator]
    refine Dist.mass_congr T fun t => ?_
    rw [outputs_eq_iff_get
      (PFunDDS.filterDom P hP t) xs.toList zs.toList
      (by simp)]
    constructor
    · intro h k
      let k' : Fin zs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      simpa [k'] using h k'
    · intro h k
      let k' : Fin xs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      simpa [k'] using h k'

  have massY_eq_mass_outputs :
      ∀ (R : PFunPDS X Y),
        CondEquiv.TotalOnNonempty R →
        ∀ {i : ℕ} (ys : Vector Y (i + 1))
          (xs : Vector X (i + 1)),
          CondEquiv.massY R i ys xs =
            R.mass fun s =>
              outputs s xs.toList =
                ys.toList.map some := by
    intro R htotal i ys xs
    unfold CondEquiv.massY PFunPDS.cumulativeBehavior
    refine mass_congr_support R fun s hs => ?_
    rw [outputs_eq_iff_get s xs.toList
      (ys.toList.map some) (by simp)]
    constructor
    · intro h k
      let k' : Fin ys.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      obtain ⟨hdom, hout⟩ := h k'
      have hne : xs.toList.take (k.1 + 1) ≠ [] :=
        CondEquiv.take_succ_ne_nil
          (l := xs.toList) (by simp) k.1
      rw [output_full_eq_some s (htotal s hs) _ hne]
      have : hdom = htotal s hs _ hne :=
        Subsingleton.elim _ _
      subst hdom
      simpa [k'] using congrArg some hout
    · intro h k
      let k' : Fin xs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      have hne : xs.toList.take (k.1 + 1) ≠ [] :=
        CondEquiv.take_succ_ne_nil
          (l := xs.toList) (by simp) k.1
      let hdom := htotal s hs _ hne
      refine ⟨hdom, ?_⟩
      have hout := h k'
      rw [output_full_eq_some s (htotal s hs) _ hne] at hout
      have hout' :
          some (PFunDDS.output s
              (xs.toList.take (k.1 + 1))
              (htotal s hs _ hne)) =
            some (ys.toList.get k) := by
        simpa [k'] using hout
      have hvalue := Option.some.inj hout'
      simpa [k'] using hvalue

  have massYA_ShatFull :
      ∀ {i : ℕ}
        (zs : Vector (Option Y) (i + 1))
        (xs : Vector X (i + 1)),
        CondEquiv.massYAfalse ShatFull i zs xs =
          Shat.mass fun g =>
            outputs (PFunDDS.filterDom P hP g) xs.toList =
              zs.toList.map
                (Option.map fun y => (y, false)) := by
    intro i zs xs
    simp only [ShatFull, completeGame]
    rw [CondEquiv.massYAfalse_fTransform_historyEvaluator
      Shat
      (fun g xs hxs =>
        Option.map Prod.fst
          (PFunDDS.output
            (PFunDDS.filterDom P hP g)⊥ xs (by
              rw [PFunDDS.dom_fullyDefined]
              exact hxs)))
      (fun g =>
        badSoFar (PFunDDS.filterDom P hP g))
      (fun g => badSoFar_mono
        (PFunDDS.filterDom P hP g))]
    refine Dist.mass_congr Shat fun g => ?_
    rw [← completeGame_outputs_false
      (PFunDDS.filterDom P hP g)
      xs.toList zs.toList (by simp)]
    constructor
    · rintro ⟨hout, hbad⟩
      refine ⟨?_, hbad⟩
      intro k
      let k' : Fin zs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      simpa [k'] using hout k'
    · rintro ⟨hout, hbad⟩
      refine ⟨?_, hbad⟩
      intro k
      let k' : Fin xs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      simpa [k'] using hout k'

  have massYA_eq_mass_outputs_false :
      ∀ (R : PFunPDS X (Y × Bool)),
        CondEquiv.TotalOnNonempty R →
        ∀ {i : ℕ} (ys : Vector Y (i + 1))
          (xs : Vector X (i + 1)),
          CondEquiv.massYAfalse R i ys xs =
            R.mass fun g =>
              outputs g xs.toList =
                ys.toList.map
                  (fun y => some (y, false)) := by
    intro R htotal i ys xs
    unfold CondEquiv.massYAfalse
    refine mass_congr_support R fun g hg => ?_
    rw [outputs_eq_iff_get g xs.toList
      (ys.toList.map fun y => some (y, false)) (by simp)]
    constructor
    · intro h k
      let k' : Fin ys.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      obtain ⟨hdom, hy, hbad⟩ := h k'
      have hne : xs.toList.take (k.1 + 1) ≠ [] :=
        CondEquiv.take_succ_ne_nil
          (l := xs.toList) (by simp) k.1
      rw [output_full_eq_some g (htotal g hg) _ hne]
      have : hdom = htotal g hg _ hne :=
        Subsingleton.elim _ _
      subst hdom
      have hpair :
          PFunDDS.output g
              (xs.toList.take (k.1 + 1))
              (htotal g hg _ hne) =
            (ys.toList.get k', false) := by
        apply Prod.ext
        · exact hy
        · exact hbad
      simpa [k'] using congrArg some hpair
    · intro h k
      let k' : Fin xs.toList.length :=
        ⟨k.1, by simpa using k.2⟩
      have hne : xs.toList.take (k.1 + 1) ≠ [] :=
        CondEquiv.take_succ_ne_nil
          (l := xs.toList) (by simp) k.1
      let hdom := htotal g hg _ hne
      refine ⟨hdom, ?_, ?_⟩
      · have hout := h k'
        rw [output_full_eq_some g (htotal g hg) _ hne] at hout
        have hout' :
            some (PFunDDS.output g
                (xs.toList.take (k.1 + 1))
                (htotal g hg _ hne)) =
              some (ys.toList.get k, false) := by
          simpa [k'] using hout
        exact congrArg Prod.fst (Option.some.inj hout')
      · have hout := h k'
        rw [output_full_eq_some g (htotal g hg) _ hne] at hout
        have hout' :
            some (PFunDDS.output g
                (xs.toList.take (k.1 + 1))
                (htotal g hg _ hne)) =
              some (ys.toList.get k, false) := by
          simpa [k'] using hout
        exact congrArg Prod.snd (Option.some.inj hout')

  have massA_ShatFull :
      ∀ (raw : List X),
        PFunDDS.keepAdmitted P raw ≠ [] →
          CondEquiv.massAfalse ShatFull raw =
            CondEquiv.massAfalse Shat
              (PFunDDS.keepAdmitted P raw) := by
    intro raw hadmitted
    simp only [ShatFull, completeGame]
    rw [CondEquiv.massAfalse_fTransform_historyEvaluator
      Shat
      (fun g xs hxs =>
        Option.map Prod.fst
          (PFunDDS.output
            (PFunDDS.filterDom P hP g)⊥ xs (by
              rw [PFunDDS.dom_fullyDefined]
              exact hxs)))
      (fun g =>
        badSoFar (PFunDDS.filterDom P hP g))
      (by
        intro hnil
        subst raw
        exact hadmitted (by rfl))]
    unfold CondEquiv.massAfalse
    refine mass_congr_support Shat fun g hg => ?_
    rw [badSoFar_filter g (hShatTot g hg) raw,
      badSoFar_eq_output_bit g (hmono g hg)
        (hShatTot g hg)
        (PFunDDS.keepAdmitted P raw) hadmitted]
    let hdom :=
      hShatTot g hg (PFunDDS.keepAdmitted P raw) hadmitted
    constructor
    · intro hbad
      exact ⟨hdom, hbad⟩
    · rintro ⟨h, hbad⟩
      have : h = hdom := Subsingleton.elim _ _
      subst h
      exact hbad

  have massY_compact :
      ∀ (t₀ : PFunDDS.DDS X Y)
        (ht₀ : ∀ l : List X, l ≠ [] →
          l ∈ PFunDDS.dom t₀)
        {i j : ℕ}
        (zs : Vector (Option Y) (i + 1))
        (xs : Vector X (i + 1))
        (ays : Vector Y (j + 1))
        (axs : Vector X (j + 1)),
        axs.toList =
            PFunDDS.keepAdmitted P xs.toList →
          ays.toList = zs.toList.filterMap id →
          (outputs (PFunDDS.filterDom P hP t₀)
              xs.toList).map Option.isSome =
            zs.toList.map Option.isSome →
          CondEquiv.massY Tfull i zs xs =
            CondEquiv.massY T j ays axs := by
    intro t₀ ht₀ i j zs xs ays axs haxs hays hshape
    rw [massY_Tfull, massY_eq_mass_outputs T hTTot]
    refine mass_congr_support T fun t ht => ?_
    rw [outputs_filter_eq_iff_compact
      t t₀ (hTTot t ht) ht₀
      xs.toList zs.toList hshape]
    rw [haxs, hays]

  have massYA_compact :
      ∀ (t₀ : PFunDDS.DDS X Y)
        (ht₀ : ∀ l : List X, l ≠ [] →
          l ∈ PFunDDS.dom t₀)
        {i j : ℕ}
        (zs : Vector (Option Y) (i + 1))
        (xs : Vector X (i + 1))
        (ays : Vector Y (j + 1))
        (axs : Vector X (j + 1)),
        axs.toList =
            PFunDDS.keepAdmitted P xs.toList →
          ays.toList = zs.toList.filterMap id →
          (outputs (PFunDDS.filterDom P hP t₀)
              xs.toList).map Option.isSome =
            zs.toList.map Option.isSome →
          CondEquiv.massYAfalse ShatFull i zs xs =
            CondEquiv.massYAfalse Shat j ays axs := by
    intro t₀ ht₀ i j zs xs ays axs haxs hays hshape
    let tagged :=
      zs.toList.map
        (Option.map fun y => (y, false))
    have htagTotal :
        ∀ l : List X, l ≠ [] →
          l ∈ PFunDDS.dom (PFunDDS.tagFalse t₀) :=
      fun l hne =>
        (PFunDDS.mem_dom_tagFalse t₀ l).mpr (ht₀ l hne)
    have htagMask :
        tagged.map Option.isSome =
          zs.toList.map Option.isSome := by
      dsimp only [tagged]
      induction zs.toList with
      | nil => rfl
      | cons o os ih =>
          cases o with
          | none =>
              change false :: _ = false :: _
              rw [ih]
          | some y =>
              change true :: _ = true :: _
              rw [ih]
    have hshapeTagged :
        (outputs
            (PFunDDS.filterDom P hP
              (PFunDDS.tagFalse t₀))
            xs.toList).map Option.isSome =
          tagged.map Option.isSome :=
      (outputs_filter_isSome
        (PFunDDS.tagFalse t₀) t₀
        htagTotal ht₀ xs.toList).trans
        (hshape.trans htagMask.symm)
    have htagFilter :
        tagged.filterMap id =
          (zs.toList.filterMap id).map
            fun y => (y, false) := by
      dsimp only [tagged]
      induction zs.toList with
      | nil => rfl
      | cons o os ih =>
          cases o <;> simpa using ih
    rw [massYA_ShatFull,
      massYA_eq_mass_outputs_false Shat hShatTot]
    refine mass_congr_support Shat fun g hg => ?_
    rw [outputs_filter_eq_iff_compact
      g (PFunDDS.tagFalse t₀)
      (hShatTot g hg) htagTotal
      xs.toList tagged hshapeTagged]
    rw [htagFilter, haxs, hays]
    simp [List.map_map, Function.comp_def]

  have mass_eq_weight_on_support :
      ∀ {Z : Type (max u v)} (D : Dist Z) (Q : Z → Prop),
        (∀ z ∈ D.support, Q z) →
          D.mass Q = D.weight := by
    intro Z D Q hQ
    unfold Dist.mass Dist.weight
    refine Finsupp.sum_congr fun z hz => ?_
    rw [if_pos (hQ z hz)]

  have mass_eq_zero_off_support :
      ∀ {Z : Type (max u v)} (D : Dist Z) (Q : Z → Prop),
        (∀ z ∈ D.support, ¬ Q z) →
          D.mass Q = 0 := by
    intro Z D Q hQ
    calc
      D.mass Q = D.mass (fun _ => False) := by
        apply mass_congr_support
        intro z hz
        simp [hQ z hz]
      _ = 0 :=
        Dist.mass_eq_zero_of_forall_not D (by simp)

  have hShatFullProb : ShatFull.isProbDist := by
    dsimp only [ShatFull]
    exact Dist.fTransform_isProbDist _ hShat

  have hTfullProb : Tfull.isProbDist := by
    dsimp only [Tfull]
    exact Dist.fTransform_isProbDist _ hT

  have hShatFullTotal :
      CondEquiv.TotalOnNonempty ShatFull := by
    dsimp only [ShatFull, completeGame]
    exact CondEquiv.totalOnNonempty_fTransform_historyEvaluator
      Shat
      (fun g xs hxs =>
        (Option.map Prod.fst
            (PFunDDS.output
              (PFunDDS.filterDom P hP g)⊥ xs (by
                rw [PFunDDS.dom_fullyDefined]
                exact hxs)),
          badSoFar (PFunDDS.filterDom P hP g) xs))

  have hTfullTotal :
      CondEquiv.TotalOnNonempty Tfull := by
    dsimp only [Tfull, completeSystem]
    exact CondEquiv.totalOnNonempty_fTransform_historyEvaluator
      T
      (fun t xs hxs =>
        PFunDDS.output
          (PFunDDS.filterDom P hP t)⊥ xs (by
            rw [PFunDDS.dom_fullyDefined]
            exact hxs))

  have hShatFullMono : MonotoneMBO ShatFull := by
    intro g hg
    dsimp only [ShatFull] at hg
    obtain ⟨g₀, _hg₀, rfl⟩ :=
      Dist.mem_support_fTransform _ _ hg
    exact completeGame_isGame
      (PFunDDS.filterDom P hP g₀)

  have hTfullDom :
      ∀ {xs : List X}, xs ≠ [] →
        CondEquiv.massDom Tfull xs = 1 :=
    fun hxs =>
      CondEquiv.massDom_eq_one_of_totalOnNonempty
        Tfull hTfullProb hTfullTotal hxs

  have hTne : T ≠ 0 := by
    intro hz
    have h := hT
    rw [hz] at h
    simp [Dist.isProbDist, Dist.weight] at h
  obtain ⟨t₀, ht₀⟩ :=
    Finsupp.support_nonempty_iff.mpr hTne
  have ht₀total := hTTot t₀ ht₀

  have hCEfull : ShatFull |≡ Tfull := by
    intro i xs zs hA _hD
    let raw := xs.toList
    let outs := zs.toList
    by_cases hshape :
        (outputs (PFunDDS.filterDom P hP t₀) raw).map
            Option.isSome =
          outs.map Option.isSome
    · by_cases hadmitted :
          PFunDDS.keepAdmitted P raw = []
      · have hcompact : outs.filterMap id = [] := by
          apply List.eq_nil_of_length_eq_zero
          calc
            (outs.filterMap id).length =
                ((outputs
                  (PFunDDS.filterDom P hP t₀) raw).filterMap id).length :=
              (filterMap_length_of_isSome hshape).symm
            _ = (PFunDDS.keepAdmitted P raw).length :=
              outputs_filterMap_length t₀ ht₀total raw
            _ = 0 := by rw [hadmitted]; rfl
        have hmassY :
            CondEquiv.massY Tfull i zs xs = 1 := by
          rw [massY_Tfull]
          change T.mass (fun t =>
            outputs (PFunDDS.filterDom P hP t) raw =
              outs) = 1
          calc
            T.mass (fun t =>
                outputs (PFunDDS.filterDom P hP t) raw =
                  outs) =
                T.weight := by
                  apply mass_eq_weight_on_support
                  intro t ht
                  rw [outputs_filter_eq_iff_compact
                    t t₀ (hTTot t ht) ht₀total
                    raw outs hshape]
                  rw [hadmitted, outputs_nil, hcompact]
                  rfl
            _ = 1 := hT.weight_eq
        let tagged :=
          outs.map (Option.map fun y => (y, false))
        have htagMask :
            tagged.map Option.isSome =
              outs.map Option.isSome := by
          dsimp only [tagged]
          induction outs with
          | nil => rfl
          | cons o os ih =>
              cases o with
              | none =>
                  change false :: _ = false :: _
                  rw [ih]
              | some y =>
                  change true :: _ = true :: _
                  rw [ih]
        have htagFilter :
            tagged.filterMap id = [] := by
          have hfilter :
              tagged.filterMap id =
                (outs.filterMap id).map
                  fun y => (y, false) := by
            dsimp only [tagged]
            induction outs with
            | nil => rfl
            | cons o os ih =>
                cases o <;> simpa using ih
          rw [hfilter, hcompact]
          rfl
        have hmassYA :
            CondEquiv.massYAfalse ShatFull i zs xs = 1 := by
          rw [massYA_ShatFull]
          change Shat.mass (fun g =>
            outputs (PFunDDS.filterDom P hP g) raw =
              tagged) = 1
          calc
            Shat.mass (fun g =>
                outputs (PFunDDS.filterDom P hP g) raw =
                  tagged) =
                Shat.weight := by
                  apply mass_eq_weight_on_support
                  intro g hg
                  have hshapeG :
                      (outputs
                          (PFunDDS.filterDom P hP g)
                          raw).map Option.isSome =
                        tagged.map Option.isSome :=
                    (outputs_filter_isSome
                      g t₀ (hShatTot g hg) ht₀total raw).trans
                      (hshape.trans htagMask.symm)
                  rw [optionList_eq_iff_filterMap hshapeG,
                    outputs_filterMap g (hShatTot g hg) raw,
                    hadmitted, outputs_nil, htagFilter]
                  rfl
            _ = 1 := hShat.weight_eq
        have hraw : raw ≠ [] := by
          simp [raw]
        have hmassA :
            CondEquiv.massAfalse ShatFull xs.toList = 1 := by
          rw [show xs.toList = raw by rfl]
          simp only [ShatFull, completeGame]
          rw [CondEquiv.massAfalse_fTransform_historyEvaluator
            Shat
            (fun g xs hxs =>
              Option.map Prod.fst
                (PFunDDS.output
                  (PFunDDS.filterDom P hP g)⊥ xs (by
                    rw [PFunDDS.dom_fullyDefined]
                    exact hxs)))
            (fun g =>
              badSoFar (PFunDDS.filterDom P hP g))
            hraw]
          calc
            Shat.mass (fun g =>
                badSoFar
                  (PFunDDS.filterDom P hP g) raw =
                    false) =
                Shat.weight := by
                  apply mass_eq_weight_on_support
                  intro g hg
                  rw [badSoFar_filter
                    g (hShatTot g hg) raw, hadmitted]
                  rfl
            _ = 1 := hShat.weight_eq
        have hmassDom :
            CondEquiv.massDom Tfull xs.toList = 1 :=
          hTfullDom (by simp)
        rw [hmassYA, hmassDom, hmassY, hmassA]
      · let admitted :=
          PFunDDS.keepAdmitted P raw
        let compact := outs.filterMap id
        have hcompactLength :
            compact.length = admitted.length := by
          dsimp only [compact, admitted]
          calc
            (outs.filterMap id).length =
                ((outputs
                  (PFunDDS.filterDom P hP t₀)
                  raw).filterMap id).length :=
              (filterMap_length_of_isSome hshape).symm
            _ = (PFunDDS.keepAdmitted P raw).length :=
              outputs_filterMap_length
                t₀ ht₀total raw
        let j := admitted.length - 1
        have hadmittedLength :
            admitted.length = j + 1 := by
          dsimp only [j]
          have hpositive : 0 < admitted.length := by
            rw [List.length_pos_iff]
            dsimp only [admitted]
            exact hadmitted
          omega
        have hcompactLength' :
            compact.length = j + 1 := by
          rw [hcompactLength, hadmittedLength]
        let axs : Vector X (j + 1) :=
          ⟨admitted.toArray,
            by simpa using hadmittedLength⟩
        let ays : Vector Y (j + 1) :=
          ⟨compact.toArray,
            by simpa using hcompactLength'⟩
        have haxs :
            axs.toList =
              PFunDDS.keepAdmitted P raw := by
          simp [axs, admitted]
        have hays :
            ays.toList = outs.filterMap id := by
          simp [ays, compact]
        have hmassA :=
          massA_ShatFull raw hadmitted
        have hAbase :
            CondEquiv.massAfalse Shat axs.toList ≠ 0 := by
          rw [haxs, ← hmassA]
          simpa only [raw] using hA
        have hdomBase :
            CondEquiv.massDom T axs.toList = 1 :=
          CondEquiv.massDom_eq_one_of_totalOnNonempty
            T hT hTTot (by
              simpa [haxs] using hadmitted)
        have hbase :=
          hCE j axs ays hAbase
            (by rw [hdomBase]; exact one_ne_zero)
        have hdomFull :
            CondEquiv.massDom Tfull xs.toList = 1 :=
          hTfullDom (by simp)
        rw [hdomBase] at hbase
        rw [massYA_compact
              t₀ ht₀total zs xs ays axs
              haxs hays hshape,
          massY_compact
              t₀ ht₀total zs xs ays axs
              haxs hays hshape,
          show CondEquiv.massAfalse ShatFull xs.toList =
              CondEquiv.massAfalse Shat
                (PFunDDS.keepAdmitted P raw) by
            simpa only [raw] using hmassA,
          hdomFull]
        simpa only [raw] using hbase
    · have hmassY :
          CondEquiv.massY Tfull i zs xs = 0 := by
        rw [massY_Tfull]
        change T.mass (fun t =>
          outputs (PFunDDS.filterDom P hP t) raw =
            outs) = 0
        apply mass_eq_zero_off_support
        intro t ht hout
        apply hshape
        exact
          (outputs_filter_isSome
            t₀ t ht₀total (hTTot t ht) raw).trans
            (congrArg (List.map Option.isSome) hout)
      have htagMask :
          (outs.map
              (Option.map fun y => (y, false))).map
              Option.isSome =
            outs.map Option.isSome := by
        induction outs with
        | nil => rfl
        | cons o os ih =>
            cases o with
            | none =>
                change false :: _ = false :: _
                rw [ih]
            | some y =>
                change true :: _ = true :: _
                rw [ih]
      have hmassYA :
          CondEquiv.massYAfalse ShatFull i zs xs = 0 := by
        rw [massYA_ShatFull]
        change Shat.mass (fun g =>
          outputs (PFunDDS.filterDom P hP g) raw =
            outs.map
              (Option.map fun y => (y, false))) = 0
        apply mass_eq_zero_off_support
        intro g hg hout
        apply hshape
        exact
          (outputs_filter_isSome
            t₀ g ht₀total (hShatTot g hg) raw).trans
            ((congrArg
              (List.map Option.isSome) hout).trans htagMask)
      rw [hmassYA, hmassY]
      simp

  have hfullBound :
      (Δ(PFunPDS.ignoreMBO ShatFull, Tfull) : ℝ) ≤
        (Γᵇ ShatFull : ℝ) := by
    refine maxAdvantage_le_of_deltaFiniteQueryNormalization
      (PFunPDS.ignoreMBO ShatFull) Tfull
      (blindMaxWinProb_nonneg (hShat.nonNeg.fTransform _))
      (deltaFiniteQueryNormalization_of_totalOnNonempty
        (PFunPDS.ignoreMBO ShatFull) Tfull
        (totalOnNonempty_ignoreMBO hShatFullTotal)
        hTfullTotal) ?_
    intro i D hD hQ
    exact
      advantage_le_blindMaxWinProb_of_condEquiv
        D ShatFull Tfull i
        hShatFullProb hTfullProb hCEfull hShatFullMono
        hShatFullTotal hTfullTotal hQ hD

  let liftDDD :
      PFunDDS.DDD X Y → PFunDDS.DDD X (Option Y) :=
    fun d =>
      ⟨fun hs => d.val (hs.map Option.join), by
        intro hs hs' hprefix bad hbad
        exact d.property
          (hprefix.map Option.join) bad hbad⟩

  let flattenTranscript :
      List (X × Option (Option Y)) →
        List (X × Option Y) :=
    List.map fun p => (p.1, p.2.join)

  have flattenTranscript_inputs :
      ∀ history : List (X × Option (Option Y)),
        PFunDDS.transcriptInputs
            (flattenTranscript history) =
          PFunDDS.transcriptInputs history := by
    intro history
    simp [flattenTranscript, PFunDDS.transcriptInputs,
      List.map_map, Function.comp_def]

  have flattenTranscript_outputs :
      ∀ history : List (X × Option (Option Y)),
        PFunDDS.transcriptOutputs
            (flattenTranscript history) =
          (PFunDDS.transcriptOutputs history).map
            Option.join := by
    intro history
    simp [flattenTranscript, PFunDDS.transcriptOutputs,
      List.map_map, Function.comp_def]

  have output_completeSystem :
      ∀ (s : PFunDDS.DDS X Y)
        (xs : List X) (hxs : xs ≠ []),
        PFunDDS.output (completeSystem s)⊥ xs (by
          rw [PFunDDS.dom_fullyDefined]
          exact hxs) =
          some (PFunDDS.output s⊥ xs (by
            rw [PFunDDS.dom_fullyDefined]
            exact hxs)) := by
    intro s xs hxs
    rw [output_full_eq_some
      (completeSystem s)
      (by
        intro l hl
        rw [PFunDDS.dom_historyEvaluator]
        exact hl)
      xs hxs]
    rfl

  have ddToDDE_liftDDD :
      ∀ (d : PFunDDS.DDD X Y)
        (hs : List (Option (Option Y))),
        PFunDDS.ddToDDE (liftDDD d) hs =
          PFunDDS.ddToDDE d (hs.map Option.join) := by
    intro d hs
    rfl

  have transcript_completeSystem :
      ∀ (s : PFunDDS.DDS X Y)
        (d : PFunDDS.DDD X Y) (n : ℕ),
        flattenTranscript
            (PFunDDS.transcript
              (completeSystem s)
              (PFunDDS.ddToDDE (liftDDD d)) n) =
          PFunDDS.transcript s
            (PFunDDS.ddToDDE d) n := by
    intro s d n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [PFunDDS.transcript]
        let completed :=
          PFunDDS.transcript
            (completeSystem s)
            (PFunDDS.ddToDDE (liftDDD d)) n
        let original :=
          PFunDDS.transcript s
            (PFunDDS.ddToDDE d) n
        have hinputs :
            PFunDDS.transcriptInputs completed =
              PFunDDS.transcriptInputs original := by
          calc
            PFunDDS.transcriptInputs completed =
                PFunDDS.transcriptInputs
                  (flattenTranscript completed) :=
              (flattenTranscript_inputs completed).symm
            _ = PFunDDS.transcriptInputs original :=
              congrArg PFunDDS.transcriptInputs ih
        have houtputs :
            (PFunDDS.transcriptOutputs completed).map
                Option.join =
              PFunDDS.transcriptOutputs original := by
          calc
            (PFunDDS.transcriptOutputs completed).map
                Option.join =
                PFunDDS.transcriptOutputs
                  (flattenTranscript completed) :=
              (flattenTranscript_outputs completed).symm
            _ = PFunDDS.transcriptOutputs original :=
              congrArg PFunDDS.transcriptOutputs ih
        have hmove :
            PFunDDS.ddToDDE (liftDDD d)
                (PFunDDS.transcriptOutputs completed) =
              PFunDDS.ddToDDE d
                (PFunDDS.transcriptOutputs original) := by
          rw [ddToDDE_liftDDD, houtputs]
        cases hquery :
            PFunDDS.ddToDDE d
              (PFunDDS.transcriptOutputs original) with
        | none =>
            have hquery' :
                PFunDDS.ddToDDE (liftDDD d)
                    (PFunDDS.transcriptOutputs completed) =
                  none := hmove.trans hquery
            dsimp only [original] at hquery
            dsimp only [completed] at hquery'
            rw [hquery']
            exact ih
        | some x =>
            have hquery' :
                PFunDDS.ddToDDE (liftDDD d)
                    (PFunDDS.transcriptOutputs completed) =
                  some x := hmove.trans hquery
            dsimp only [original] at hquery
            dsimp only [completed] at hquery'
            rw [hquery']
            simp only [flattenTranscript, List.map_append, List.map]
            have hresponse :
                Option.join
                    (PFunDDS.output (completeSystem s)⊥
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp)) =
                  PFunDDS.output s⊥
                    (PFunDDS.transcriptInputs original ++ [x])
                    (by
                      rw [PFunDDS.dom_fullyDefined]
                      simp) := by
              calc
                _ = Option.join
                    (some (PFunDDS.output s⊥
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp))) :=
                  congrArg Option.join
                    (output_completeSystem s
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by simp))
                _ = PFunDDS.output s⊥
                    (PFunDDS.transcriptInputs completed ++ [x])
                    (by
                      rw [PFunDDS.dom_fullyDefined]
                      simp) := rfl
                _ = PFunDDS.output s⊥
                    (PFunDDS.transcriptInputs original ++ [x])
                    (by
                      rw [PFunDDS.dom_fullyDefined]
                      simp) :=
                  PFunDDS.output_congr s⊥
                    (congrArg (fun xs => xs ++ [x]) hinputs)
                    _ _
            exact congrArg₂ (· ++ ·) ih
              (congrArg (fun y => [(x, y)]) hresponse)

  have verdict_completeSystem :
      ∀ (d : PFunDDS.DDD X Y)
        (s : PFunDDS.DDS X Y),
        PFunDDS.verdict (liftDDD d) (completeSystem s) ↔
          PFunDDS.verdict d s := by
    intro d s
    unfold PFunDDS.verdict
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hvalue :
          (liftDDD d).val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript
                  (completeSystem s)
                  (PFunDDS.ddToDDE (liftDDD d)) n)) =
            d.val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE d) n)) := by
        change
          d.val
              ((PFunDDS.transcriptOutputs
                (PFunDDS.transcript
                  (completeSystem s)
                  (PFunDDS.ddToDDE (liftDDD d)) n)).map
                    Option.join) =
            d.val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE d) n))
        rw [← flattenTranscript_outputs]
        exact congrArg
          (fun history =>
            d.val (PFunDDS.transcriptOutputs history))
          (transcript_completeSystem s d n)
      rw [hvalue] at hn
      exact hn
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hvalue :
          (liftDDD d).val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript
                  (completeSystem s)
                  (PFunDDS.ddToDDE (liftDDD d)) n)) =
            d.val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE d) n)) := by
        change
          d.val
              ((PFunDDS.transcriptOutputs
                (PFunDDS.transcript
                  (completeSystem s)
                  (PFunDDS.ddToDDE (liftDDD d)) n)).map
                    Option.join) =
            d.val
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript s
                  (PFunDDS.ddToDDE d) n))
        rw [← flattenTranscript_outputs]
        exact congrArg
          (fun history =>
            d.val (PFunDDS.transcriptOutputs history))
          (transcript_completeSystem s d n)
      rw [hvalue]
      exact hn

  have verdictProb_completeSystem :
      ∀ (D : Dist (PFunDDS.DDD X Y))
        (S : PFunPDS X Y),
        verdictProb (Dist.fTransform liftDDD D)
            (Dist.fTransform completeSystem S) =
          verdictProb D S := by
    intro D S
    unfold verdictProb
    rw [winProb_fTransform_left, winProb_fTransform_right]
    refine winProb_congr_support D S ?_
    intro s _ d
    exact verdict_completeSystem d s

  have advantage_completeSystem :
      ∀ (D : Dist (PFunDDS.DDD X Y))
        (S U : PFunPDS X Y),
        advantage (Dist.fTransform liftDDD D)
            (Dist.fTransform completeSystem S)
            (Dist.fTransform completeSystem U) =
          advantage D S U := by
    intro D S U
    unfold advantage
    rw [verdictProb_completeSystem D U,
      verdictProb_completeSystem D S]

  have completeSystem_filterDom_T :
      Dist.fTransform completeSystem
          (PFunPDS.filterDom P hP T) =
        Tfull := by
    unfold PFunPDS.filterDom Tfull
    rw [Dist.fTransform_comp]
    rfl

  have completeSystem_filterDom_ignore :
      Dist.fTransform completeSystem
          (PFunPDS.filterDom P hP
            (PFunPDS.ignoreMBO Shat)) =
        PFunPDS.ignoreMBO ShatFull := by
    unfold PFunPDS.filterDom PFunPDS.ignoreMBO
      PFunPDS.stripMBO ShatFull
    rw [Dist.fTransform_comp, Dist.fTransform_comp,
      Dist.fTransform_comp]
    congr 1
    funext g
    simp only [Function.comp_apply]
    calc
      completeSystem
          (PFunDDS.filterDom P hP
            (PFunDDS.stripMBO g)) =
          (PFunDDS.filterDom P hP
            (PFunDDS.stripMBO g))⊥ :=
        completeSystem_eq _
      _ = (PFunDDS.filterDom P hP g)⁻ᴹ⊥ := by
        rfl
      _ = PFunDDS.stripMBO
          (completeGame (PFunDDS.filterDom P hP g)) :=
        (ignore_completeGame
          (PFunDDS.filterDom P hP g)).symm

  have hDelta :
      (Δ(PFunPDS.filterDom P hP
          (PFunPDS.ignoreMBO Shat),
        PFunPDS.filterDom P hP T) : ℝ) ≤
        (Δ(PFunPDS.ignoreMBO ShatFull, Tfull) : ℝ) := by
    refine maxAdvantage_le_of_forall_advantage_le ?_
    intro D hD
    have hDfull :
        (Dist.fTransform liftDDD D).isProbDist :=
      Dist.fTransform_isProbDist liftDDD hD
    calc
      advantage D
          (PFunPDS.filterDom P hP
            (PFunPDS.ignoreMBO Shat))
          (PFunPDS.filterDom P hP T) =
          advantage (Dist.fTransform liftDDD D)
            (Dist.fTransform completeSystem
              (PFunPDS.filterDom P hP
                (PFunPDS.ignoreMBO Shat)))
            (Dist.fTransform completeSystem
              (PFunPDS.filterDom P hP T)) :=
        (advantage_completeSystem D
          (PFunPDS.filterDom P hP
            (PFunPDS.ignoreMBO Shat))
          (PFunPDS.filterDom P hP T)).symm
      _ = advantage (Dist.fTransform liftDDD D)
          (PFunPDS.ignoreMBO ShatFull) Tfull := by
        rw [completeSystem_filterDom_ignore,
          completeSystem_filterDom_T]
      _ ≤ Δ(PFunPDS.ignoreMBO ShatFull, Tfull) :=
        advantage_le_maxAdvantage
          (Dist.fTransform liftDDD D)
          (PFunPDS.ignoreMBO ShatFull) Tfull hDfull

  let lowerWinner :
      PFunDDS.Winner X (Option Y) →
        PFunDDS.Winner X Y :=
    fun w hs => w (hs.map some)

  have lowerWinner_blind :
      ∀ (w : PFunDDS.Winner X (Option Y)),
        IsBlind w → IsBlind (lowerWinner w) := by
    intro w hw hs₁ hs₂ hlength
    exact hw (hs₁.map some) (hs₂.map some) (by
      simpa using hlength)

  have transcriptOutputs_eq_outputs :
      ∀ {Z : Type v} (s : PFunDDS.DDS X Z)
        (e : PFunDDS.DDE X Z) (n : ℕ),
        PFunDDS.transcriptOutputs
            (PFunDDS.transcript s e n) =
          outputs s
            (PFunDDS.transcriptInputs
              (PFunDDS.transcript s e n)) := by
    intro Z s e n
    induction n with
    | zero =>
        simp [PFunDDS.transcript, PFunDDS.transcriptInputs,
          PFunDDS.transcriptOutputs, outputs_nil]
    | succ n ih =>
        simp only [PFunDDS.transcript]
        cases hquery :
            e (PFunDDS.transcriptOutputs
              (PFunDDS.transcript s e n)) with
        | none =>
            simp only
            exact ih
        | some x =>
            simp only
            rw [transcriptInputs_append,
              transcriptOutputs_append, outputs_append, ih]

  have any_output_bit :
      ∀ {Z : Type v} (os : List (Option (Z × Bool))),
        (os.any fun oy =>
            match oy with
            | none => false
            | some (_, bad) => bad) = true ↔
          ∃ y : Z,
            (some (y, true) : Option (Z × Bool)) ∈ os := by
    intro Z os
    rw [List.any_eq_true]
    constructor
    · rintro ⟨oy, hoy, hbad⟩
      cases oy with
      | none =>
          simp at hbad
      | some p =>
          rcases p with ⟨y, bad⟩
          simp only at hbad
          subst bad
          exact ⟨y, hoy⟩
    · rintro ⟨y, hy⟩
      exact ⟨some (y, true), hy, rfl⟩

  have output_completeGame :
      ∀ (g : PFunDDS.DDS X (Y × Bool))
        (xs : List X) (hxs : xs ≠ []),
        PFunDDS.output (completeGame g)⊥ xs (by
          rw [PFunDDS.dom_fullyDefined]
          exact hxs) =
          some
            (Option.map Prod.fst
                (PFunDDS.output g⊥ xs (by
                  rw [PFunDDS.dom_fullyDefined]
                  exact hxs)),
              badSoFar g xs) := by
    intro g xs hxs
    rw [output_full_eq_some
      (completeGame g)
      (by
        intro l hl
        rw [PFunDDS.dom_historyEvaluator]
        exact hl)
      xs hxs]
    rfl

  have outputs_completeGame_any :
      ∀ (g : PFunDDS.DDS X (Y × Bool))
        (raw : List X),
        ((outputs (completeGame g) raw).any fun oy =>
            match oy with
            | none => false
            | some (_, bad) => bad) =
          badSoFar g raw := by
    intro g raw
    induction raw using List.reverseRecOn with
    | nil =>
        simp [outputs_nil, badSoFar]
    | append_singleton raw x ih =>
        rw [outputs_append, List.any_append, ih,
          output_completeGame g (raw ++ [x]) (by simp)]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        cases hlast : badSoFar g (raw ++ [x]) with
        | false =>
            have hprevious :
                badSoFar g raw = false := by
              cases hprevious : badSoFar g raw with
              | false =>
                  rfl
              | true =>
                  have hcontra :=
                    badSoFar_mono g
                      (show raw <+: raw ++ [x] from
                        ⟨[x], rfl⟩)
                      hprevious
                  rw [hlast] at hcontra
                  contradiction
            simp [hprevious]
        | true =>
            simp

  have wins_iff_badSoFar :
      ∀ (w : PFunDDS.Winner X Y)
        (g : PFunDDS.DDS X (Y × Bool)),
        winsDDS w g ↔
          ∃ n,
            badSoFar g
              (PFunDDS.transcriptInputs
                (PFunDDS.transcript g
                  (PFunDDS.winnerView w) n)) = true := by
    intro w g
    unfold winsDDS
    constructor
    · rintro ⟨n, y, hy⟩
      refine ⟨n, ?_⟩
      unfold badSoFar
      rw [← transcriptOutputs_eq_outputs]
      exact (any_output_bit _).2 ⟨y, hy⟩
    · rintro ⟨n, hbad⟩
      unfold badSoFar at hbad
      rw [← transcriptOutputs_eq_outputs] at hbad
      obtain ⟨y, hy⟩ := (any_output_bit _).1 hbad
      exact ⟨n, y, hy⟩

  have wins_completeGame_iff_badSoFar :
      ∀ (w : PFunDDS.Winner X (Option Y))
        (g : PFunDDS.DDS X (Y × Bool)),
        winsDDS w (completeGame g) ↔
          ∃ n,
            badSoFar g
              (PFunDDS.transcriptInputs
                (PFunDDS.transcript (completeGame g)
                  (PFunDDS.winnerView w) n)) = true := by
    intro w g
    unfold winsDDS
    constructor
    · rintro ⟨n, y, hy⟩
      refine ⟨n, ?_⟩
      have hany :
          ((PFunDDS.transcriptOutputs
              (PFunDDS.transcript (completeGame g)
                (PFunDDS.winnerView w) n)).any fun oy =>
            match oy with
            | none => false
            | some (_, bad) => bad) = true := by
        rw [List.any_eq_true]
        exact ⟨some (y, true), hy, rfl⟩
      rw [transcriptOutputs_eq_outputs,
        outputs_completeGame_any] at hany
      exact hany
    · rintro ⟨n, hbad⟩
      have hany :
          ((outputs (completeGame g)
              (PFunDDS.transcriptInputs
                (PFunDDS.transcript (completeGame g)
                  (PFunDDS.winnerView w) n))).any fun oy =>
            match oy with
            | none => false
            | some (_, bad) => bad) = true := by
        rw [outputs_completeGame_any, hbad]
      rw [← transcriptOutputs_eq_outputs] at hany
      rw [List.any_eq_true] at hany
      obtain ⟨oy, hoy, hbad⟩ := hany
      cases oy with
      | none =>
          simp at hbad
      | some p =>
          rcases p with ⟨y, bad⟩
          simp only at hbad
          subst bad
          exact ⟨n, y, hoy⟩

  have completeGame_transcript :
      ∀ (w : PFunDDS.Winner X (Option Y))
        (g : PFunDDS.DDS X (Y × Bool)) (n : ℕ),
        let completed :=
          PFunDDS.transcript (completeGame g)
            (PFunDDS.winnerView w) n
        let original :=
          PFunDDS.transcript g
            (PFunDDS.winnerView (lowerWinner w)) n
        PFunDDS.transcriptInputs completed =
            PFunDDS.transcriptInputs original ∧
          (PFunDDS.transcriptOutputs completed).map
              (Option.map Prod.fst) =
            ((PFunDDS.transcriptOutputs original).map
              (Option.map Prod.fst)).map some := by
    intro w g n
    induction n with
    | zero =>
        simp [PFunDDS.transcript, PFunDDS.transcriptInputs,
          PFunDDS.transcriptOutputs]
    | succ n ih =>
        simp only [PFunDDS.transcript]
        let completed :=
          PFunDDS.transcript (completeGame g)
            (PFunDDS.winnerView w) n
        let original :=
          PFunDDS.transcript g
            (PFunDDS.winnerView (lowerWinner w)) n
        have hmove :
            PFunDDS.winnerView w
                (PFunDDS.transcriptOutputs completed) =
              PFunDDS.winnerView (lowerWinner w)
                (PFunDDS.transcriptOutputs original) := by
          unfold PFunDDS.winnerView lowerWinner
          exact congrArg w ih.2
        cases hquery :
            PFunDDS.winnerView (lowerWinner w)
              (PFunDDS.transcriptOutputs original) with
        | none =>
            have hquery' :
                PFunDDS.winnerView w
                    (PFunDDS.transcriptOutputs completed) =
                  none :=
              hmove.trans hquery
            dsimp only [completed] at hquery'
            rw [hquery']
            simp only
            exact ih
        | some x =>
            have hquery' :
                PFunDDS.winnerView w
                    (PFunDDS.transcriptOutputs completed) =
                  some x :=
              hmove.trans hquery
            dsimp only [completed] at hquery'
            rw [hquery']
            simp only [transcriptInputs_append,
              transcriptOutputs_append, List.map_append,
              List.map]
            have hresponse :
                Option.map Prod.fst
                    (PFunDDS.output (completeGame g)⊥
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp)) =
                  some (Option.map Prod.fst
                    (PFunDDS.output g⊥
                      (PFunDDS.transcriptInputs original ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp))) := by
              calc
                _ = Option.map Prod.fst
                    (some
                      (Option.map Prod.fst
                          (PFunDDS.output g⊥
                            (PFunDDS.transcriptInputs completed ++ [x])
                            (by
                              rw [PFunDDS.dom_fullyDefined]
                              simp)),
                        badSoFar g
                          (PFunDDS.transcriptInputs completed ++ [x]))) :=
                  congrArg (Option.map Prod.fst)
                    (output_completeGame g
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by simp))
                _ = some (Option.map Prod.fst
                    (PFunDDS.output g⊥
                      (PFunDDS.transcriptInputs completed ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp))) := rfl
                _ = some (Option.map Prod.fst
                    (PFunDDS.output g⊥
                      (PFunDDS.transcriptInputs original ++ [x])
                      (by
                        rw [PFunDDS.dom_fullyDefined]
                        simp))) :=
                  congrArg
                    (fun oy => some (Option.map Prod.fst oy))
                    (PFunDDS.output_congr g⊥
                      (congrArg (fun xs => xs ++ [x]) ih.1)
                      _ _)
            exact ⟨congrArg (fun xs => xs ++ [x]) ih.1,
              congrArg₂ (· ++ ·) ih.2
                (congrArg (fun y => [y]) hresponse)⟩

  have wins_completeGame :
      ∀ (w : PFunDDS.Winner X (Option Y))
        (g : PFunDDS.DDS X (Y × Bool)),
        winsDDS w (completeGame g) ↔
          winsDDS (lowerWinner w) g := by
    intro w g
    rw [wins_completeGame_iff_badSoFar,
      wins_iff_badSoFar]
    constructor
    · rintro ⟨n, hbad⟩
      refine ⟨n, ?_⟩
      rw [← (completeGame_transcript w g n).1]
      exact hbad
    · rintro ⟨n, hbad⟩
      refine ⟨n, ?_⟩
      rw [(completeGame_transcript w g n).1]
      exact hbad

  have winProb_completeGame :
      ∀ W : Dist (PFunDDS.Winner X (Option Y)),
        winProb W ShatFull =
          winProb (Dist.fTransform lowerWinner W)
            (PFunPDS.filterDom P hP Shat) := by
    intro W
    unfold winProb ShatFull PFunPDS.filterDom
    rw [winProb_fTransform_right,
      winProb_fTransform_left,
      winProb_fTransform_right]
    refine winProb_congr_support W Shat ?_
    intro g _ w
    exact wins_completeGame w
      (PFunDDS.filterDom P hP g)

  have hGamma :
      Γᵇ ShatFull ≤
        Γᵇ (PFunPDS.filterDom P hP Shat) := by
    unfold blindMaxWinProb
    refine Real.sSup_le ?_
      (blindMaxWinProb_nonneg (hShat.nonNeg.fTransform _))
    rintro _ ⟨W, ⟨hblind, hW⟩, rfl⟩
    have hWlower :
        (Dist.fTransform lowerWinner W).isProbDist :=
      Dist.fTransform_isProbDist lowerWinner hW
    have hblindLower :
        IsBlindDist
          (Dist.fTransform lowerWinner W) := by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ :=
        mem_support_fTransform lowerWinner W hw'
      exact lowerWinner_blind w (hblind w hw)
    calc
      winProb W ShatFull =
          winProb (Dist.fTransform lowerWinner W)
            (PFunPDS.filterDom P hP Shat) :=
        winProb_completeGame W
      _ ≤ Γᵇ (PFunPDS.filterDom P hP Shat) :=
        winProb_le_blindMaxWinProb
          (Dist.fTransform lowerWinner W)
          (PFunPDS.filterDom P hP Shat)
          hblindLower hWlower

  have hGammaReal :
      (Γᵇ ShatFull : ℝ) ≤
        (Γᵇ (PFunPDS.filterDom P hP Shat) : ℝ) := by
    exact_mod_cast hGamma

  exact hDelta.trans (hfullBound.trans hGammaReal)

/-- The common-restriction endpoint specialized to a weighted query budget.
This is the form used by CBC's `θr`; all converter realization is discharged
by the general `restrictionFn` law. -/
theorem restrict_advantage_le_blind_game_of_cond_equiv [Nonempty X]
    (cost : X → ℕ) (r : ℕ)
    (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y)
    (hCE : Shat |≡ T)
    (hmono : MonotoneMBO Shat := by cr18_standing)
    (hShat : Shat.isProbDist := by cr18_standing)
    (hT : T.isProbDist := by cr18_standing)
    (hShatTot : CondEquiv.TotalOnNonempty Shat := by cr18_standing)
    (hTTot : CondEquiv.TotalOnNonempty T := by cr18_standing) :
    (Δ(Dist.fTransform
          (PFunConverter.apply (PFunConverter.restrictionFn
            (fun xs => (xs.map cost).sum ≤ r)))
          (PFunPDS.ignoreMBO Shat),
        Dist.fTransform
          (PFunConverter.apply (PFunConverter.restrictionFn
            (fun xs => (xs.map cost).sum ≤ r))) T) : ℝ) ≤
      (Γᵇ (Dist.fTransform
        (PFunConverter.apply (PFunConverter.restrictionFn
          (fun xs => (xs.map cost).sum ≤ r))) Shat) : ℝ) := by
  let P : List X → Prop := fun xs => (xs.map cost).sum ≤ r
  have hP : PrefixClosed P := by
    rintro xs _ ⟨tail, rfl⟩ h
    simp only [P, List.map_append, List.sum_append] at h ⊢
    omega
  change
    Δ(RandomSystems.CR18.StrictContext.applyLaw
        (PFunConverter.restrictionFn P) (PFunPDS.ignoreMBO Shat),
      RandomSystems.CR18.StrictContext.applyLaw
        (PFunConverter.restrictionFn P) T) ≤
      (Γᵇ (RandomSystems.CR18.StrictContext.applyLaw
        (PFunConverter.restrictionFn P) Shat) : ℝ)
  rw [StrictContext.apply_law_restrictionFn P hP,
    StrictContext.apply_law_restrictionFn P hP,
    StrictContext.apply_law_restrictionFn P hP]
  exact maxAdvantage_filterDom_le_blindMaxWinProb_of_condEquiv
    P hP Shat T hCE

end RandomSystems.CR18
