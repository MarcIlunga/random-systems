/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.GameBased
import RandomSystems.Complexity.GameHop
import RandomSystems.Complexity.IidGames
import RandomSystems.Complexity.Tactics
import RandomSystems.GameOf
import RandomSystems.Lemma415
import RandomSystems.RelateGameDistinguishing
import RandomSystems.RelateGameDistinguishing

/-!
# Converter bridge

CR18 converter reductions prove an equality of the form

`winProb W (convert G) = winProb (rho W) G`.

This file turns that equality, plus a cost law for the same `rho`, into a
costed reduction between the corresponding winning-game problems.
-/

namespace RandomSystems.CR18
namespace Complexity

noncomputable section

universe u v u' v'

variable {X : Type u} {Y : Type v} {U : Type u'} {V : Type v'}

/-- A Boolean distinguisher functional, viewed extensionally as a predicate on
deterministic systems.  This is the CR18 `w` in `wc`, specialized to
distinguishing verdicts. -/
abbrev DistinguisherFunctional (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunDDS.DDS X Y → Bool

namespace DistinguisherFunctional

/-- Compose a distinguisher functional with a converter action on systems:
CR18's `wc = w ∘ c`. -/
def composeConverter
    (convertDDS : PFunDDS.DDS X Y → PFunDDS.DDS U V)
    (D : DistinguisherFunctional U V) :
    DistinguisherFunctional X Y :=
  D ∘ convertDDS

@[simp] theorem composeConverter_apply
    (convertDDS : PFunDDS.DDS X Y → PFunDDS.DDS U V)
    (D : DistinguisherFunctional U V) (S : PFunDDS.DDS X Y) :
    composeConverter convertDDS D S = D (convertDDS S) :=
  rfl

end DistinguisherFunctional

/-- The raw DDS action of a one-call converter.  A target history `us` is
implemented by the base history `us.map toInner`; the last base reply is
translated with the last target query. -/
def oneCallApplyRaw
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) : PFunDDS.Raw U V :=
  fun us =>
    match us.getLast? with
    | none => Part.none
    | some u => Part.map (toOuter u) (S.1 (us.map toInner))

/-- The concrete system-side action of a one-call converter. -/
def oneCallApplyDDS
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) : PFunDDS.DDS U V :=
  ⟨oneCallApplyRaw toInner toOuter S, by
    constructor
    · simp [oneCallApplyRaw]
    · intro l₁ l₂ hprefix hne hdom
      rw [PFun.mem_dom] at hdom ⊢
      obtain ⟨v₂, hv₂⟩ := hdom
      obtain ⟨u₁, hu₁⟩ : ∃ u : U, l₁.getLast? = some u := by
        exact ⟨l₁.getLast hne, List.getLast?_eq_some_getLast hne⟩
      obtain ⟨l, rfl⟩ := hprefix
      have hbase₂ : l₁.map toInner ++ l.map toInner ∈ PFunDDS.dom S := by
        cases hlast₂ : (l₁ ++ l).getLast? with
        | none =>
            have hnil : l₁ ++ l = [] := List.getLast?_eq_none_iff.mp hlast₂
            have hnil₁ : l₁ = [] := by
              cases l₁ with
              | nil => rfl
              | cons u us =>
                  simp at hnil
            exact False.elim (hne hnil₁)
        | some u₂ =>
            rw [oneCallApplyRaw, hlast₂, Part.mem_map_iff] at hv₂
            obtain ⟨y₂, hy₂, _⟩ := hv₂
            have hy₂' : y₂ ∈ S.1 (l₁.map toInner ++ l.map toInner) := by
              simpa [List.map_append] using hy₂
            simpa [PFunDDS.dom] using ⟨y₂, hy₂'⟩
      have hbase₁ : l₁.map toInner ∈ PFunDDS.dom S := by
        exact PFunDDS.prefix_closed S
          (by exact ⟨l.map toInner, by simp⟩)
          (by simpa using hne)
          hbase₂
      refine ⟨toOuter u₁ (PFunDDS.output S (l₁.map toInner) hbase₁), ?_⟩
      rw [oneCallApplyRaw, hu₁, Part.mem_map_iff]
      refine ⟨PFunDDS.output S (l₁.map toInner) hbase₁, ?_, rfl⟩
      exact Part.get_mem _
    ⟩

theorem mem_dom_oneCallApplyDDS
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) (us : List U) :
    us ∈ PFunDDS.dom (oneCallApplyDDS toInner toOuter S) ↔
      us.map toInner ∈ PFunDDS.dom S := by
  change (oneCallApplyRaw toInner toOuter S us).Dom ↔ (S.1 (us.map toInner)).Dom
  cases hlast : us.getLast? with
  | none =>
      have hus : us = [] := List.getLast?_eq_none_iff.mp hlast
      subst hus
      simp [oneCallApplyRaw]
      intro hdom
      exact PFunDDS.empty_not_mem S (by
        rw [PFunDDS.dom, PFun.mem_dom]
        exact Part.dom_iff_mem.mp hdom)
  | some u =>
      rw [oneCallApplyRaw, hlast, Part.map_Dom]

theorem keptPrefix_oneCallApplyDDS_map
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) (us : List U) :
    (PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us).map toInner =
      PFunDDS.keptPrefix S (us.map toInner) := by
  classical
  let stepT : List U → U → List U :=
    fun acc u => if acc ++ [u] ∈ PFunDDS.dom (oneCallApplyDDS toInner toOuter S) then
      acc ++ [u] else acc
  let stepB : List X → X → List X :=
    fun acc x => if acc ++ [x] ∈ PFunDDS.dom S then acc ++ [x] else acc
  have hfold :
      ∀ xs accT accB, accT.map toInner = accB →
        (List.foldl stepT accT xs).map toInner =
          List.foldl stepB accB (xs.map toInner) := by
    intro xs
    induction xs with
    | nil =>
        intro accT accB hacc
        simp [hacc]
    | cons u xs ih =>
        intro accT accB hacc
        by_cases hdomT : accT ++ [u] ∈ PFunDDS.dom (oneCallApplyDDS toInner toOuter S)
        · have hdomB : accB ++ [toInner u] ∈ PFunDDS.dom S := by
            have h := (mem_dom_oneCallApplyDDS toInner toOuter S (accT ++ [u])).mp hdomT
            simpa [List.map_append, hacc] using h
          have hdomT' :
              ∃ y, y ∈ (oneCallApplyDDS toInner toOuter S).1 (accT ++ [u]) := by
            simpa [PFunDDS.dom, PFun.mem_dom] using hdomT
          have hdomB' : ∃ y, y ∈ S.1 (accB ++ [toInner u]) := by
            simpa [PFunDDS.dom, PFun.mem_dom] using hdomB
          have hnext :
              (accT ++ [u]).map toInner = accB ++ [toInner u] := by
            simp [List.map_append, hacc]
          simpa [List.foldl_cons, stepT, stepB, hdomT', hdomB'] using
            ih (accT ++ [u]) (accB ++ [toInner u]) hnext
        · have hdomB : ¬ accB ++ [toInner u] ∈ PFunDDS.dom S := by
            intro hB
            apply hdomT
            apply (mem_dom_oneCallApplyDDS toInner toOuter S (accT ++ [u])).mpr
            simpa [List.map_append, hacc] using hB
          have hdomT' :
              ¬ ∃ y, y ∈ (oneCallApplyDDS toInner toOuter S).1 (accT ++ [u]) := by
            intro h
            apply hdomT
            simpa [PFunDDS.dom, PFun.mem_dom] using h
          have hdomB' : ¬ ∃ y, y ∈ S.1 (accB ++ [toInner u]) := by
            intro h
            apply hdomB
            simpa [PFunDDS.dom, PFun.mem_dom] using h
          simpa [List.foldl_cons, stepT, stepB, hdomT', hdomB'] using
            ih accT accB hacc
  simpa [PFunDDS.keptPrefix, stepT, stepB] using hfold us [] [] rfl

theorem output_oneCallApplyDDS
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) (us : List U) (u : U)
    (h : us ++ [u] ∈ PFunDDS.dom (oneCallApplyDDS toInner toOuter S)) :
    PFunDDS.output (oneCallApplyDDS toInner toOuter S) (us ++ [u]) h =
      toOuter u (PFunDDS.output S (us.map toInner ++ [toInner u])
        (by
          have hbase := (mem_dom_oneCallApplyDDS toInner toOuter S (us ++ [u])).mp h
          simpa [List.map_append] using hbase)) := by
  unfold PFunDDS.output oneCallApplyDDS oneCallApplyRaw
  simp [List.map_append]

theorem output_fullyDefined_oneCallApplyDDS_append
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) (us : List U) (u : U) :
    PFunDDS.output (PFunDDS.fullyDefined (oneCallApplyDDS toInner toOuter S)) (us ++ [u]) (by
      rw [PFunDDS.dom_fullyDefined]
      simp) =
      Option.map (toOuter u)
        (PFunDDS.output (PFunDDS.fullyDefined S) (us.map toInner ++ [toInner u]) (by
          rw [PFunDDS.dom_fullyDefined]
          simp)) := by
  rw [PFunDDS.output_fullyDefined, PFunDDS.output_fullyDefined]
  by_cases hbase :
      PFunDDS.keptPrefix S (us.map toInner) ++ [toInner u] ∈ PFunDDS.dom S
  · have htarget :
        PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us ++ [u] ∈
          PFunDDS.dom (oneCallApplyDDS toInner toOuter S) := by
      apply (mem_dom_oneCallApplyDDS toInner toOuter S
        (PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us ++ [u])).mpr
      simpa [List.map_append, keptPrefix_oneCallApplyDDS_map toInner toOuter S us] using hbase
    rw [dif_pos (by simpa [List.dropLast_concat, List.getLast_concat] using htarget)]
    rw [dif_pos (by simpa [List.dropLast_concat, List.getLast_concat] using hbase)]
    simp only [List.dropLast_concat, List.getLast_concat]
    rw [output_oneCallApplyDDS toInner toOuter S
      (PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us) u htarget]
    simp [keptPrefix_oneCallApplyDDS_map toInner toOuter S us]
  · have htarget :
        ¬ PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us ++ [u] ∈
          PFunDDS.dom (oneCallApplyDDS toInner toOuter S) := by
      intro ht
      apply hbase
      have h := (mem_dom_oneCallApplyDDS toInner toOuter S
        (PFunDDS.keptPrefix (oneCallApplyDDS toInner toOuter S) us ++ [u])).mp ht
      simpa [List.map_append, keptPrefix_oneCallApplyDDS_map toInner toOuter S us] using h
    rw [dif_neg (by simpa [List.dropLast_concat, List.getLast_concat] using htarget)]
    rw [dif_neg (by simpa [List.dropLast_concat, List.getLast_concat] using hbase)]
    simp

/-- Replay a one-call converter against a base-side output history.

Each target query `u` becomes one base query.  If the base reply is `some y`,
the target distinguisher receives `some (toOuter u y)`; if the base reply is
`none`, it receives `none`.  Once the target distinguisher has stopped, later
base-side replies are ignored. -/
def oneCallTargetOutputsAux
    (toOuter : U → Y → V) (d : PFunDDS.DDD U V) :
    List (Option V) → List (Option Y) → List (Option V)
  | vs, [] => vs
  | vs, y? :: ys =>
      match d.val vs with
      | Sum.inr _ => vs
      | Sum.inl u => oneCallTargetOutputsAux toOuter d (vs ++ [Option.map (toOuter u) y?]) ys

/-- Target-side output history induced by a base-side output history through a
one-call converter. -/
def oneCallTargetOutputs
    (toOuter : U → Y → V) (d : PFunDDS.DDD U V)
    (ys : List (Option Y)) : List (Option V) :=
  oneCallTargetOutputsAux toOuter d [] ys

/-- If replay has reached a target-side stop after a base history, extending the
base history does not change the replayed target history. -/
theorem oneCallTargetOutputsAux_append_of_stop
    (toOuter : U → Y → V) (d : PFunDDS.DDD U V)
    {vs : List (Option V)} {ys ys' : List (Option Y)} {b : Bool}
    (hstop : d.val (oneCallTargetOutputsAux toOuter d vs ys) = Sum.inr b) :
    oneCallTargetOutputsAux toOuter d vs (ys ++ ys') =
      oneCallTargetOutputsAux toOuter d vs ys := by
  induction ys generalizing vs with
  | nil =>
      cases hd : d.val vs with
      | inl u =>
          simp [oneCallTargetOutputsAux, hd] at hstop
      | inr b₀ =>
          cases ys' <;> simp [oneCallTargetOutputsAux, hd]
  | cons y? ys ih =>
      cases hd : d.val vs with
      | inl u =>
          simpa [oneCallTargetOutputsAux, hd] using
            ih (vs := vs ++ [Option.map (toOuter u) y?])
              (by simpa [oneCallTargetOutputsAux, hd] using hstop)
      | inr b₀ =>
          simp [oneCallTargetOutputsAux, hd]

/-- If replay is ready to issue target query `u`, one additional base-side reply
adds the converted target-side reply. -/
theorem oneCallTargetOutputsAux_append_of_query
    (toOuter : U → Y → V) (d : PFunDDS.DDD U V)
    {vs : List (Option V)} {ys : List (Option Y)} {u : U} (y? : Option Y)
    (hquery : d.val (oneCallTargetOutputsAux toOuter d vs ys) = Sum.inl u) :
    oneCallTargetOutputsAux toOuter d vs (ys ++ [y?]) =
      oneCallTargetOutputsAux toOuter d vs ys ++ [Option.map (toOuter u) y?] := by
  induction ys generalizing vs with
  | nil =>
      cases hd : d.val vs with
      | inl u₀ =>
          simp [oneCallTargetOutputsAux, hd] at hquery ⊢
          subst hquery
          rfl
      | inr b =>
          simp [oneCallTargetOutputsAux, hd] at hquery
  | cons y₀ ys ih =>
      cases hd : d.val vs with
      | inl u₀ =>
          simpa [oneCallTargetOutputsAux, hd] using
            ih (vs := vs ++ [Option.map (toOuter u₀) y₀])
              (by simpa [oneCallTargetOutputsAux, hd] using hquery)
      | inr b =>
          simp [oneCallTargetOutputsAux, hd] at hquery

/-- The raw base-side DDD obtained by composing a target-side DDD with a
one-call converter. -/
def composeOneCallDDDStep
    (toInner : U → X) (toOuter : U → Y → V) (d : PFunDDS.DDD U V) :
    List (Option Y) → X ⊕ Bool :=
  fun ys =>
    match d.val (oneCallTargetOutputs toOuter d ys) with
    | Sum.inl u => Sum.inl (toInner u)
    | Sum.inr b => Sum.inr b

/-- Composing a DDD with a one-call converter preserves final verdicts. -/
theorem composeOneCallDDDStep_stopFinal
    (toInner : U → X) (toOuter : U → Y → V) (d : PFunDDS.DDD U V) :
    PFunDDS.StopFinal (composeOneCallDDDStep toInner toOuter d) := by
  intro h h' hprefix b hb
  obtain ⟨tail, rfl⟩ := hprefix
  unfold composeOneCallDDDStep at hb ⊢
  dsimp [oneCallTargetOutputs] at hb ⊢
  have hstop :
      d.val (oneCallTargetOutputsAux toOuter d [] h) = Sum.inr b := by
    cases hd : d.val (oneCallTargetOutputsAux toOuter d [] h) with
    | inl u =>
        simp [hd] at hb
    | inr b₀ =>
        simpa [hd] using hb
  rw [oneCallTargetOutputsAux_append_of_stop toOuter d hstop]
  simp [hstop]

/-- Compose a target-side DDD with a concrete one-call converter. -/
def composeOneCallDDD
    (toInner : U → X) (toOuter : U → Y → V) (d : PFunDDS.DDD U V) :
    PFunDDS.DDD X Y :=
  ⟨composeOneCallDDDStep toInner toOuter d,
    composeOneCallDDDStep_stopFinal toInner toOuter d⟩

@[simp] theorem ddToDDE_composeOneCallDDD
    (toInner : U → X) (toOuter : U → Y → V)
    (d : PFunDDS.DDD U V) (ys : List (Option Y)) :
    PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d) ys =
      Option.map toInner (PFunDDS.ddToDDE d (oneCallTargetOutputs toOuter d ys)) := by
  cases hd : d.val (oneCallTargetOutputs toOuter d ys) with
  | inl u =>
      simp [PFunDDS.ddToDDE, composeOneCallDDD, composeOneCallDDDStep, hd]
  | inr b =>
      simp [PFunDDS.ddToDDE, composeOneCallDDD, composeOneCallDDDStep, hd]

theorem transcript_oneCallApplyDDS_align
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunDDS.DDS X Y) (d : PFunDDS.DDD U V) (n : ℕ) :
    PFunDDS.transcriptInputs
        (PFunDDS.transcript S
          (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n) =
      (PFunDDS.transcriptInputs
        (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
          (PFunDDS.ddToDDE d) n)).map toInner ∧
    PFunDDS.transcriptOutputs
        (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
          (PFunDDS.ddToDDE d) n) =
      oneCallTargetOutputs toOuter d
        (PFunDDS.transcriptOutputs
          (PFunDDS.transcript S
            (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n)) := by
  classical
  induction n with
  | zero =>
      simp [PFunDDS.transcript, PFunDDS.transcriptInputs, PFunDDS.transcriptOutputs,
        oneCallTargetOutputs, oneCallTargetOutputsAux]
  | succ n ih =>
      rcases ih with ⟨ihx, ihy⟩
      let tB := PFunDDS.transcript S
        (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n
      let tT := PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
        (PFunDDS.ddToDDE d) n
      have hbaseEnv :
          PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)
              (PFunDDS.transcriptOutputs tB) =
            Option.map toInner (PFunDDS.ddToDDE d (PFunDDS.transcriptOutputs tT)) := by
        dsimp [tB, tT]
        rw [ddToDDE_composeOneCallDDD, ← ihy]
      cases htarget : PFunDDS.ddToDDE d (PFunDDS.transcriptOutputs tT) with
      | none =>
          have hbase :
              PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)
                (PFunDDS.transcriptOutputs tB) = none := by
            simpa [htarget] using hbaseEnv
          have htargetReplay :
              PFunDDS.ddToDDE d
                (oneCallTargetOutputs toOuter d (PFunDDS.transcriptOutputs tB)) = none := by
            simpa [tB, tT, ihy] using htarget
          constructor
          · simp [PFunDDS.transcript, tB, tT, hbase, htarget, ihx]
          · simp [PFunDDS.transcript, tB, hbase, htargetReplay, ihy]
      | some u =>
          have hbase :
              PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)
                (PFunDDS.transcriptOutputs tB) = some (toInner u) := by
            simpa [htarget] using hbaseEnv
          have htargetReplay :
              PFunDDS.ddToDDE d
                (oneCallTargetOutputs toOuter d (PFunDDS.transcriptOutputs tB)) = some u := by
            simpa [tB, tT, ihy] using htarget
          constructor
          · simp [PFunDDS.transcript, tB, tT, hbase, htarget,
              PFunDDS.transcriptInputs, List.map_append]
            simpa [PFunDDS.transcriptInputs, List.map_map, Function.comp_def] using ihx
          · have hquery :
                d.val (oneCallTargetOutputs toOuter d (PFunDDS.transcriptOutputs tB)) =
                  Sum.inl u := by
              unfold PFunDDS.ddToDDE at htargetReplay
              cases hd : d.val (oneCallTargetOutputs toOuter d (PFunDDS.transcriptOutputs tB)) with
              | inl u₀ =>
                  simp [hd] at htargetReplay
                  cases htargetReplay
                  rfl
              | inr b =>
                  simp [hd] at htargetReplay
            have hbase' :
                PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)
                  (PFunDDS.transcriptOutputs
                    (PFunDDS.transcript S
                      (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n)) =
                    some (toInner u) := by
              simpa [tB] using hbase
            have htarget' :
                PFunDDS.ddToDDE d
                  (PFunDDS.transcriptOutputs
                    (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
                      (PFunDDS.ddToDDE d) n)) = some u := by
              simpa [tT] using htarget
            rw [transcript_succ_fire htarget', transcript_succ_fire hbase']
            rw [output_fullyDefined_oneCallApplyDDS_append toInner toOuter S
              (PFunDDS.transcriptInputs
                (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
                  (PFunDDS.ddToDDE d) n)) u]
            simp [PFunDDS.transcriptOutputs, PFunDDS.transcriptInputs, List.map_append]
            have ihx' :
                List.map Prod.fst
                    (PFunDDS.transcript S
                      (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n) =
                  List.map (toInner ∘ Prod.fst)
                    (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
                      (PFunDDS.ddToDDE d) n) := by
              simpa [PFunDDS.transcriptInputs, List.map_map, Function.comp_def] using ihx
            simp [← ihx']
            have ihy' :
                List.map Prod.snd
                    (PFunDDS.transcript (oneCallApplyDDS toInner toOuter S)
                      (PFunDDS.ddToDDE d) n) =
                  oneCallTargetOutputs toOuter d
                    (List.map Prod.snd
                      (PFunDDS.transcript S
                        (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n)) := by
              simpa [PFunDDS.transcriptOutputs] using ihy
            rw [ihy']
            have hquery' :
                d.val
                    (oneCallTargetOutputs toOuter d
                      (List.map Prod.snd
                        (PFunDDS.transcript S
                          (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n))) =
                  Sum.inl u := by
              simpa [tB, PFunDDS.transcriptOutputs] using hquery
            unfold oneCallTargetOutputs
            have hqueryAux :
                d.val
                    (oneCallTargetOutputsAux toOuter d []
                      (List.map Prod.snd
                        (PFunDDS.transcript S
                          (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n))) =
                  Sum.inl u := by
              simpa [oneCallTargetOutputs] using hquery'
            rw [oneCallTargetOutputsAux_append_of_query (toOuter := toOuter) (d := d)
              (hquery := hqueryAux)]
            simp

theorem verdict_composeOneCallDDD
    (toInner : U → X) (toOuter : U → Y → V)
    (d : PFunDDS.DDD U V) (S : PFunDDS.DDS X Y) :
    PFunDDS.verdict (composeOneCallDDD toInner toOuter d) S ↔
      PFunDDS.verdict d (oneCallApplyDDS toInner toOuter S) := by
  unfold PFunDDS.verdict
  constructor
  · rintro ⟨n, hn⟩
    use n
    have houts := (transcript_oneCallApplyDDS_align toInner toOuter S d n).2
    have hstop :
        d.val
            (oneCallTargetOutputs toOuter d
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript S
                  (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n))) =
          Sum.inr true := by
      change composeOneCallDDDStep toInner toOuter d
          (PFunDDS.transcriptOutputs
            (PFunDDS.transcript S
              (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n)) =
        Sum.inr true at hn
      unfold composeOneCallDDDStep at hn
      cases hd :
          d.val
            (oneCallTargetOutputs toOuter d
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript S
                  (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n))) with
      | inl u =>
          simp [hd] at hn
      | inr b =>
          simpa [hd] using hn
    simpa [houts] using hstop
  · rintro ⟨n, hn⟩
    use n
    have houts := (transcript_oneCallApplyDDS_align toInner toOuter S d n).2
    have hstop :
        d.val
            (oneCallTargetOutputs toOuter d
              (PFunDDS.transcriptOutputs
                (PFunDDS.transcript S
                  (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n))) =
          Sum.inr true := by
      simpa [houts] using hn
    change composeOneCallDDDStep toInner toOuter d
        (PFunDDS.transcriptOutputs
          (PFunDDS.transcript S
            (PFunDDS.ddToDDE (composeOneCallDDD toInner toOuter d)) n)) =
      Sum.inr true
    unfold composeOneCallDDDStep
    simp [hstop]

/-- Lift the one-call converter action to probabilistic systems. -/
noncomputable def oneCallApplyPDS
    (toInner : U → X) (toOuter : U → Y → V)
    (S : PFunPDS X Y) : PFunPDS U V :=
  Dist.fTransform (oneCallApplyDDS toInner toOuter) S

/-- Lift one-call DDD composition to probabilistic distinguishers. -/
noncomputable def composeOneCallDDDDist
    (toInner : U → X) (toOuter : U → Y → V)
    (D : Dist (PFunDDS.DDD U V)) : Dist (PFunDDS.DDD X Y) :=
  Dist.fTransform (composeOneCallDDD toInner toOuter) D

/-- Verdict probability is invariant under the concrete one-call converter
composition. -/
theorem verdictProb_oneCallApplyPDS
    (toInner : U → X) (toOuter : U → Y → V)
    (D : Dist (PFunDDS.DDD U V)) (S : PFunPDS X Y) :
    verdictProb D (oneCallApplyPDS toInner toOuter S) =
      verdictProb (composeOneCallDDDDist toInner toOuter D) S := by
  unfold verdictProb oneCallApplyPDS composeOneCallDDDDist
  rw [winProb_fTransform_game, winProb_fTransform]
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun d _ => ?_
  refine Finsupp.sum_congr fun s _ => ?_
  by_cases h : PFunDDS.verdict d (oneCallApplyDDS toInner toOuter s)
  · have hc : PFunDDS.verdict (composeOneCallDDD toInner toOuter d) s :=
      (verdict_composeOneCallDDD toInner toOuter d s).mpr h
    simp [h, hc]
  · have hc : ¬ PFunDDS.verdict (composeOneCallDDD toInner toOuter d) s := by
      intro hs
      exact h ((verdict_composeOneCallDDD toInner toOuter d s).mp hs)
    simp [h, hc]

/-- Distinguishing advantage is invariant under the concrete one-call converter
composition. -/
theorem advantage_oneCallApplyPDS
    (toInner : U → X) (toOuter : U → Y → V)
    (D : Dist (PFunDDS.DDD U V)) (S T : PFunPDS X Y) :
    advantage D (oneCallApplyPDS toInner toOuter S) (oneCallApplyPDS toInner toOuter T) =
      advantage (composeOneCallDDDDist toInner toOuter D) S T := by
  unfold advantage
  rw [verdictProb_oneCallApplyPDS toInner toOuter D T,
    verdictProb_oneCallApplyPDS toInner toOuter D S]

/-- The one-call DDD transformer preserves probability distributions. -/
theorem composeOneCallDDDDist_isProbDist
    (toInner : U → X) (toOuter : U → Y → V)
    (D : Dist (PFunDDS.DDD U V)) (hD : D.isProbDist) :
    (composeOneCallDDDDist toInner toOuter D).isProbDist :=
  Dist.fTransform_isProbDist (composeOneCallDDD toInner toOuter) hD

theorem maxAdvantage_oneCallApplyPDS_le
    (toInner : U → X) (toOuter : U → Y → V)
    (S T : PFunPDS X Y) :
    Δ(oneCallApplyPDS toInner toOuter S, oneCallApplyPDS toInner toOuter T) ≤
      Δ(S, T) := by
  unfold maxAdvantage
  refine csSup_le ?_ ?_
  · exact RandomSystems.CR18.advantage_image_nonempty
      (oneCallApplyPDS toInner toOuter S) (oneCallApplyPDS toInner toOuter T)
  · rintro b ⟨D, hD, rfl⟩
    change advantage D (oneCallApplyPDS toInner toOuter S) (oneCallApplyPDS toInner toOuter T) ≤
      sSup ((fun D => advantage D S T) '' {D | D.isProbDist})
    rw [advantage_oneCallApplyPDS]
    exact advantage_le_maxAdvantage (composeOneCallDDDDist toInner toOuter D) S T
      (composeOneCallDDDDist_isProbDist toInner toOuter D hD)

/-- The fixed query list encoded by `xs : Fin q → X`. -/
def fixedQueryInputs {q : Nat} (xs : Fin q → X) : List X :=
  (List.Vector.ofFn xs).toList

@[simp] theorem fixedQueryInputs_length {q : Nat} (xs : Fin q → X) :
    (fixedQueryInputs xs).length = q := by
  simp [fixedQueryInputs]

theorem fixedQueryInputs_ne_nil {q : Nat} (xs : Fin q → X) (hq : 0 < q) :
    fixedQueryInputs xs ≠ [] := by
  intro hnil
  have hlen : (fixedQueryInputs xs).length = 0 := by
    simp [hnil]
  simp [fixedQueryInputs] at hlen
  omega

theorem fixedQueryInputs_take_succ_ne_nil {q : Nat} (xs : Fin q → X) (i : Fin q) :
    (fixedQueryInputs xs).take (i.1 + 1) ≠ [] := by
  have hlen : ((fixedQueryInputs xs).take (i.1 + 1)).length = i.1 + 1 := by
    simp [fixedQueryInputs]
  intro hnil
  have hzero : ((fixedQueryInputs xs).take (i.1 + 1)).length = 0 := by
    simp [hnil]
  omega

theorem fixedQueryInputs_take_succ_eq_take_append {q : Nat}
    (xs : Fin q → X) (i : Fin q) :
    (fixedQueryInputs xs).take (i.1 + 1) =
      (fixedQueryInputs xs).take i.1 ++ [xs i] := by
  rw [← List.take_concat_get' (fixedQueryInputs xs) i.1 (by
    simp [fixedQueryInputs, i.2])]
  simp [fixedQueryInputs]

/-- The visible output tuple obtained by asking `S` the fixed queries `xs`. -/
def fixedQueryOutputs {q : Nat} (xs : Fin q → X) (S : PFunDDS.DDS X Y)
    (h : fixedQueryInputs xs ∈ PFunDDS.dom S) : Fin q → Y :=
  fun i => PFunDDS.output S ((fixedQueryInputs xs).take (i.1 + 1)) (by
    exact PFunDDS.prefix_closed S (List.take_prefix _ _)
      (fixedQueryInputs_take_succ_ne_nil xs i) h)

/-- System-side action of the fixed-query converter: a target `Unit` query
returns the tuple of replies to the fixed inner queries.  The `0 < q` endpoint
lemmas below match Boneh-Shoup's `ℓ ≥ 1` construction. -/
def fixedQueryApplyRaw {q : Nat} (xs : Fin q → X) (S : PFunDDS.DDS X Y) :
    PFunDDS.Raw Unit (Fin q → Y) :=
  fun us => ⟨us ≠ [] ∧ fixedQueryInputs xs ∈ PFunDDS.dom S,
    fun h => fixedQueryOutputs xs S h.2⟩

/-- Concrete DDS induced by the fixed-query converter. -/
def fixedQueryApplyDDS {q : Nat} (xs : Fin q → X) (S : PFunDDS.DDS X Y) :
    PFunDDS.DDS Unit (Fin q → Y) :=
  ⟨fixedQueryApplyRaw xs S, by
    constructor
    · simp [fixedQueryApplyRaw]
    · intro l₁ _l₂ _ hne hdom
      exact ⟨hne, hdom.2⟩⟩

theorem fixedQueryOutputs_functionEvaluator {q : Nat}
    (xs : Fin q → X) (f : X → Y)
    (h : fixedQueryInputs xs ∈ PFunDDS.dom (PFunDDS.functionEvaluator f)) :
    fixedQueryOutputs xs (PFunDDS.functionEvaluator f) h = fun i => f (xs i) := by
  funext i
  unfold fixedQueryOutputs
  calc
    PFunDDS.output (PFunDDS.functionEvaluator f)
        ((fixedQueryInputs xs).take (i.1 + 1)) _
        = PFunDDS.output (PFunDDS.functionEvaluator f)
            ((fixedQueryInputs xs).take i.1 ++ [xs i]) (by
              rw [PFunDDS.dom_functionEvaluator]
              simp) := by
            exact PFunDDS.output_congr _
              (fixedQueryInputs_take_succ_eq_take_append xs i) _ _
    _ = f (xs i) := by
            exact PFunDDS.functionEvaluator_output f ((fixedQueryInputs xs).take i.1) (xs i) _

theorem fixedQueryApplyDDS_functionEvaluator {q : Nat}
    (xs : Fin q → X) (f : X → Y) (hq : 0 < q) :
    fixedQueryApplyDDS xs (PFunDDS.functionEvaluator f) =
      PFunDDS.functionEvaluator (fun _ : Unit => fun i => f (xs i)) := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro out
  constructor
  · intro h
    change ∃ hd : us ≠ [] ∧ fixedQueryInputs xs ∈
        PFunDDS.dom (PFunDDS.functionEvaluator f),
        fixedQueryOutputs xs (PFunDDS.functionEvaluator f) hd.2 = out at h
    rcases h with ⟨hd, hout⟩
    change ∃ hr : us ≠ [], (fun _ : Unit => fun i => f (xs i)) (us.getLast hr) = out
    exact ⟨hd.1, by simpa [fixedQueryOutputs_functionEvaluator] using hout⟩
  · intro h
    change ∃ hr : us ≠ [], (fun _ : Unit => fun i => f (xs i)) (us.getLast hr) = out at h
    rcases h with ⟨hr, hout⟩
    change ∃ hd : us ≠ [] ∧ fixedQueryInputs xs ∈
        PFunDDS.dom (PFunDDS.functionEvaluator f),
        fixedQueryOutputs xs (PFunDDS.functionEvaluator f) hd.2 = out
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · rw [PFunDDS.dom_functionEvaluator]
      exact fixedQueryInputs_ne_nil xs hq
    · simpa [fixedQueryOutputs_functionEvaluator] using hout

/-- Lift the fixed-query converter to probabilistic systems. -/
noncomputable def fixedQueryApplyPDS {q : Nat}
    (xs : Fin q → X) (S : PFunPDS X Y) : PFunPDS Unit (Fin q → Y) :=
  Dist.fTransform (fixedQueryApplyDDS xs) S

theorem fixedQueryApplyPDS_ofFunDist {q : Nat}
    (xs : Fin q → X) (Df : Dist (X → Y)) (hq : 0 < q) :
    fixedQueryApplyPDS xs (PFunPDS.ofFunDist Df) =
      sampleSystem (Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Df) := by
  unfold fixedQueryApplyPDS PFunPDS.ofFunDist sampleSystem
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  congr 1
  funext f
  exact fixedQueryApplyDDS_functionEvaluator xs f hq

theorem fixedQueryOutputs_filterQueries_functionEvaluator {q : Nat}
    (xs : Fin q → X) (f : X → Y)
    (h : fixedQueryInputs xs ∈
      PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) :
    fixedQueryOutputs xs (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) h =
      fun i => f (xs i) := by
  funext i
  unfold fixedQueryOutputs
  calc
    PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
        ((fixedQueryInputs xs).take (i.1 + 1)) _
        = PFunDDS.output (PFunDDS.functionEvaluator f)
            ((fixedQueryInputs xs).take (i.1 + 1)) _ := by
            rfl
    _ = PFunDDS.output (PFunDDS.functionEvaluator f)
            ((fixedQueryInputs xs).take i.1 ++ [xs i]) (by
              rw [PFunDDS.dom_functionEvaluator]
              simp) := by
            exact PFunDDS.output_congr _
              (fixedQueryInputs_take_succ_eq_take_append xs i) _ _
    _ = f (xs i) := by
            exact PFunDDS.functionEvaluator_output f ((fixedQueryInputs xs).take i.1) (xs i) _

theorem fixedQueryApplyDDS_filterQueries_functionEvaluator {q : Nat}
    (xs : Fin q → X) (f : X → Y) (hq : 0 < q) :
    fixedQueryApplyDDS xs (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) =
      PFunDDS.functionEvaluator (fun _ : Unit => fun i => f (xs i)) := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro out
  constructor
  · intro h
    change ∃ hd : us ≠ [] ∧ fixedQueryInputs xs ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)),
        fixedQueryOutputs xs (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) hd.2 = out at h
    rcases h with ⟨hd, hout⟩
    change ∃ hr : us ≠ [], (fun _ : Unit => fun i => f (xs i)) (us.getLast hr) = out
    exact ⟨hd.1, by simpa [fixedQueryOutputs_filterQueries_functionEvaluator] using hout⟩
  · intro h
    change ∃ hr : us ≠ [], (fun _ : Unit => fun i => f (xs i)) (us.getLast hr) = out at h
    rcases h with ⟨hr, hout⟩
    change ∃ hd : us ≠ [] ∧ fixedQueryInputs xs ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)),
        fixedQueryOutputs xs (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) hd.2 = out
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · rw [PFunDDS.mem_dom_filterQueries]
      constructor
      · rw [PFunDDS.dom_functionEvaluator]
        exact fixedQueryInputs_ne_nil xs hq
      · simp
    · simpa [fixedQueryOutputs_filterQueries_functionEvaluator] using hout

theorem fixedQueryApplyPDS_filterQueries_ofFunDist {q : Nat}
    (xs : Fin q → X) (Df : Dist (X → Y)) (hq : 0 < q) :
    fixedQueryApplyPDS xs (PFunPDS.filterQueries q (PFunPDS.ofFunDist Df)) =
      sampleSystem (Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Df) := by
  unfold fixedQueryApplyPDS PFunPDS.filterQueries PFunPDS.ofFunDist sampleSystem
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  congr 1
  funext f
  exact fixedQueryApplyDDS_filterQueries_functionEvaluator xs f hq

/-- Read a length-`q` output tuple from the first `q` replies.  If any reply is
missing, the tuple is absent. -/
noncomputable def outputTuple? {q : Nat} (ys : List (Option Y)) :
    Option (Fin q → Y) := by
  classical
  exact if h : ∀ i : Fin q, ∃ y, ys[i.1]? = some (some y) then
    some (fun i => Classical.choose (h i))
  else none

theorem outputTuple?_of_get? {q : Nat} {ys : List (Option Y)}
    {yv : Fin q → Y} (h : ∀ i : Fin q, ys[i.1]? = some (some (yv i))) :
    outputTuple? ys = some yv := by
  classical
  unfold outputTuple?
  have hall : ∀ i : Fin q, ∃ y, ys[i.1]? = some (some y) := fun i => ⟨yv i, h i⟩
  rw [dif_pos hall]
  congr
  funext i
  have hs := Classical.choose_spec (hall i)
  exact Option.some.inj (Option.some.inj (hs.symm.trans (h i)))

/-- Compose a one-sample adversary with the fixed-query converter.  It asks the
fixed inputs, then applies the sample adversary to the vector of replies. -/
def fixedQuerySampleDDDStep {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) :
    List (Option Y) → X ⊕ Bool :=
  fun ys =>
    if h : ys.length < q then Sum.inl (xs ⟨ys.length, h⟩)
    else Sum.inr ((outputTuple? (ys.take q)).any Aadv)

theorem fixedQuerySampleDDDStep_stopFinal {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) :
    PFunDDS.StopFinal (fixedQuerySampleDDDStep xs Aadv) := by
  intro h h' hprefix b hb
  obtain ⟨tail, rfl⟩ := hprefix
  unfold fixedQuerySampleDDDStep at hb ⊢
  by_cases hh : h.length < q
  · simp [hh] at hb
  · have hq_h : q ≤ h.length := by omega
    have hq_append' : q ≤ h.length + tail.length := by omega
    simp [not_lt_of_ge hq_h] at hb
    have ht : @outputTuple? Y q ((h ++ tail).take q) = @outputTuple? Y q (h.take q) := by
      rw [List.take_append_of_le_length hq_h]
    simp [List.length_append, not_lt_of_ge hq_append', ht, hb]

/-- Fixed-query PRF-side adversary induced by a one-sample PRG adversary. -/
def fixedQuerySampleDDD {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) :
    PFunDDS.DDD X Y :=
  ⟨fixedQuerySampleDDDStep xs Aadv, fixedQuerySampleDDDStep_stopFinal xs Aadv⟩

@[simp] theorem ddToDDE_fixedQuerySampleDDD {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y))
    (ys : List (Option Y)) :
    PFunDDS.ddToDDE (fixedQuerySampleDDD xs Aadv) ys =
      if h : ys.length < q then some (xs ⟨ys.length, h⟩) else none := by
  by_cases h : ys.length < q
  · simp [PFunDDS.ddToDDE, fixedQuerySampleDDD, fixedQuerySampleDDDStep, h]
  · simp [PFunDDS.ddToDDE, fixedQuerySampleDDD, fixedQuerySampleDDDStep, h]

theorem fixedQuerySampleDDD_queriesExactly {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) :
    QueriesExactly (PFunDDS.ddToDDE (fixedQuerySampleDDD xs Aadv)) q := by
  constructor
  · intro h hlen
    simp [hlen]
  · intro h hlen
    simp [not_lt_of_ge hlen]

theorem fixedQueryInputs_get? {q : Nat}
    (xs : Fin q → X) (i : Fin q) :
    (fixedQueryInputs xs)[i.1]? = some (xs i) := by
  simp [fixedQueryInputs]

theorem fixedQueryInputs_getElem {q : Nat}
    (xs : Fin q → X) (i : Fin q)
    (h : i.1 < (fixedQueryInputs xs).length) :
    (fixedQueryInputs xs)[i.1] = xs i := by
  simp [fixedQueryInputs]

theorem fixedQuerySampleDDD_transcript_filterQueries_functionEvaluator_prefix {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) (f : X → Y) :
    ∀ n, n ≤ q →
      PFunDDS.transcript (⟦q⟧ eval[f])
          (PFunDDS.ddToDDE (fixedQuerySampleDDD xs Aadv)) n =
        ((fixedQueryInputs xs).take n).map (fun x => (x, some (f x))) := by
  intro n hn
  induction n with
  | zero => simp [PFunDDS.transcript]
  | succ n ih =>
      have hnq : n < q := by omega
      have ih' := ih (by omega)
      have hquery :
          PFunDDS.ddToDDE (fixedQuerySampleDDD xs Aadv)
            (PFunDDS.transcriptOutputs
              (PFunDDS.transcript (⟦q⟧ eval[f])
                (PFunDDS.ddToDDE (fixedQuerySampleDDD xs Aadv)) n)) =
          some (xs ⟨n, hnq⟩) := by
        rw [ih']
        simp only [PFunDDS.transcriptOutputs]
        rw [ddToDDE_fixedQuerySampleDDD]
        have hlen_eq :
            (List.map (Prod.snd) (((fixedQueryInputs xs).take n).map
              fun x => (x, some (f x)))).length = n := by
          simp [List.length_take, fixedQueryInputs_length, Nat.min_eq_left (Nat.le_of_lt hnq)]
        have hlen_lt :
            (List.map (Prod.snd) (((fixedQueryInputs xs).take n).map
              fun x => (x, some (f x)))).length < q := by
          omega
        rw [dif_pos hlen_lt]
        congr
      rw [transcript_succ_fire hquery, ih']
      let lprev := PFunDDS.transcriptInputs
        (((fixedQueryInputs xs).take n).map (fun x => (x, some (f x))))
      have hprev_len : lprev.length < q := by
        simp [lprev, PFunDDS.transcriptInputs, List.length_take, fixedQueryInputs_length,
          Nat.min_eq_left (Nat.le_of_lt hnq), hnq]
      have hout :
          PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))
            (lprev ++ [xs ⟨n, hnq⟩])
            (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
          some (f (xs ⟨n, hnq⟩)) := by
        rw [PFunDDS.output_fullyDefined_filterQueries_of_total_lt
          (S := PFunDDS.functionEvaluator f) (q := q)
          (hS := fun l hl => by rw [PFunDDS.dom_functionEvaluator]; exact hl)
          (l := lprev) (x := xs ⟨n, hnq⟩)]
        · rw [PFunDDS.functionEvaluator_output]
        · exact hprev_len
      change ((fixedQueryInputs xs).take n).map (fun x => (x, some (f x))) ++
          [(xs ⟨n, hnq⟩,
            PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))
              (lprev ++ [xs ⟨n, hnq⟩]) _)] =
        ((fixedQueryInputs xs).take (n + 1)).map (fun x => (x, some (f x)))
      rw [hout]
      have htake := fixedQueryInputs_take_succ_eq_take_append xs ⟨n, hnq⟩
      rw [htake]
      simp

theorem fixedQuerySampleDDD_verdict_filterQueries_functionEvaluator {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) (f : X → Y) :
    PFunDDS.verdict (fixedQuerySampleDDD xs Aadv) (⟦q⟧ eval[f]) ↔
      Aadv (fun i : Fin q => f (xs i)) = true := by
  rw [PFunDDS.verdict_iff_at_exact _ _ q (fixedQuerySampleDDD_queriesExactly xs Aadv)]
  rw [fixedQuerySampleDDD_transcript_filterQueries_functionEvaluator_prefix xs Aadv f q (le_refl q)]
  have htake : (fixedQueryInputs xs).take q = fixedQueryInputs xs := by
    rw [List.take_of_length_le]
    simp [fixedQueryInputs]
  rw [htake]
  unfold fixedQuerySampleDDD fixedQuerySampleDDDStep
  simp only [PFunDDS.transcriptOutputs, List.map_map]
  have htuple : outputTuple?
      (List.take q (List.map (Prod.snd ∘ fun x => (x, some (f x))) (fixedQueryInputs xs))) =
      some (fun i : Fin q => f (xs i)) := by
    apply outputTuple?_of_get?
    intro i
    simp [fixedQueryInputs_getElem xs i]
  simp [htuple]

/-- Point mass on a deterministic distinguisher. -/
noncomputable abbrev pointDistinguisher
    (d : PFunDDS.DDD X Y) : Dist (PFunDDS.DDD X Y) :=
  Finsupp.single d 1

theorem pointDistinguisher_isProbDist
    (d : PFunDDS.DDD X Y) : (pointDistinguisher d).isProbDist := by
  exact Dist.isProbDist_single d

theorem sampleDDD_verdict_functionEvaluator {A : Type u}
    (Aadv : SampleSolver A) (a : A) :
    PFunDDS.verdict (sampleDDD Aadv) eval[fun _ : Unit => a] ↔
      Aadv a = true := by
  rw [PFunDDS.verdict_iff_at_exact _ _ 1 (sampleDDD_queriesExactly Aadv)]
  simp [PFunDDS.transcript, PFunDDS.ddToDDE, sampleDDD, sampleDDDStep,
    PFunDDS.transcriptOutputs, PFunDDS.output, PFunDDS.fullyDefined,
    PFunDDS.dom, PFunDDS.functionEvaluator]

theorem verdictProb_sampleDDD_sampleSystem {A : Type u}
    (Aadv : SampleSolver A) (D : Dist A) :
    verdictProb (pointDistinguisher (sampleDDD Aadv)) (sampleSystem D) =
      D.mass (fun a => Aadv a = true) := by
  classical
  unfold pointDistinguisher verdictProb GamePerf.winProb
  rw [Finsupp.sum_single_index]
  · simp only [one_mul]
    calc
      Finsupp.sum (sampleSystem D)
          (fun g gp => gp * if PFunDDS.verdict (sampleDDD Aadv) g then 1 else 0)
          = (sampleSystem D).mass (fun g => PFunDDS.verdict (sampleDDD Aadv) g) := by
            unfold Dist.mass
            apply Finsupp.sum_congr
            intro g gp
            by_cases hv : PFunDDS.verdict (sampleDDD Aadv) g <;> simp [hv]
      _ = D.mass (fun a => Aadv a = true) := by
            unfold sampleSystem
            rw [Dist.mass_fTransform]
            apply Dist.mass_congr
            intro a
            exact sampleDDD_verdict_functionEvaluator Aadv a
  · simp

theorem verdictProb_fixedQuerySampleDDD_filterQueries_ofFunDist {q : Nat}
    (xs : Fin q → X) (Aadv : SampleSolver (Fin q → Y)) (Df : Dist (X → Y)) :
    verdictProb (pointDistinguisher (fixedQuerySampleDDD xs Aadv))
      (PFunPDS.filterQueries q (PFunPDS.ofFunDist Df)) =
      Df.mass (fun f => Aadv (fun i : Fin q => f (xs i)) = true) := by
  classical
  unfold pointDistinguisher verdictProb GamePerf.winProb
  rw [Finsupp.sum_single_index]
  · simp only [one_mul]
    calc
      Finsupp.sum (PFunPDS.filterQueries q (PFunPDS.ofFunDist Df))
          (fun g gp => gp * if PFunDDS.verdict (fixedQuerySampleDDD xs Aadv) g then 1 else 0)
          = (PFunPDS.filterQueries q (PFunPDS.ofFunDist Df)).mass
              (fun g => PFunDDS.verdict (fixedQuerySampleDDD xs Aadv) g) := by
            unfold Dist.mass
            apply Finsupp.sum_congr
            intro g gp
            by_cases hv : PFunDDS.verdict (fixedQuerySampleDDD xs Aadv) g <;> simp [hv]
      _ = Df.mass (fun f => Aadv (fun i : Fin q => f (xs i)) = true) := by
            unfold PFunPDS.filterQueries PFunPDS.ofFunDist
            rw [Dist.mass_fTransform, Dist.mass_fTransform]
            apply Dist.mass_congr
            intro f
            exact fixedQuerySampleDDD_verdict_filterQueries_functionEvaluator xs Aadv f
  · simp

/-- A fixed-query transcript/output-vector distance is bounded by the raw
filtered CR18 distinguishing distance.  The distinguisher asks `xs` and uses
the canonical positive statistical-distance event as its verdict. -/
theorem statDist_evalDist_le_maxAdvantage_filterQueries_ofFunDist {q : Nat}
    [Fintype Y] (xs : Fin q → X) (Df Dg : Dist (X → Y))
    (hDf : Df.isProbDist) (hDg : Dg.isProbDist) :
    (RandomSystems.statDist
        (Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Df)
        (Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Dg) : ℝ) ≤
      Δ(⌈q⌉ PFunPDS.ofFunDist Df, ⌈q⌉ PFunPDS.ofFunDist Dg) := by
  classical
  let R := Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Df
  let I := Dist.fTransform (fun f : X → Y => fun i : Fin q => f (xs i)) Dg
  let test : SampleSolver (Fin q → Y) := fun ys => decide (R ys < I ys)
  let D := pointDistinguisher (fixedQuerySampleDDD xs test)
  have hR : verdictProb D (⌈q⌉ PFunPDS.ofFunDist Df) =
      R.mass (fun ys => R ys < I ys) := by
    rw [show D = pointDistinguisher (fixedQuerySampleDDD xs test) from rfl,
      verdictProb_fixedQuerySampleDDD_filterQueries_ofFunDist]
    unfold R
    rw [Dist.mass_fTransform]
    exact Dist.mass_congr Df (fun _ => by simp [test, R])
  have hI : verdictProb D (⌈q⌉ PFunPDS.ofFunDist Dg) =
      I.mass (fun ys => R ys < I ys) := by
    rw [show D = pointDistinguisher (fixedQuerySampleDDD xs test) from rfl,
      verdictProb_fixedQuerySampleDDD_filterQueries_ofFunDist]
    unfold I
    rw [Dist.mass_fTransform]
    exact Dist.mass_congr Dg (fun _ => by simp [test, I])
  have hweight : R.weight = I.weight := by
    rw [show R = Dist.fTransform
        (fun f : X → Y => fun i : Fin q => f (xs i)) Df from rfl,
      show I = Dist.fTransform
        (fun f : X → Y => fun i : Fin q => f (xs i)) Dg from rfl,
      Dist.weight_fTransform, Dist.weight_fTransform]
    exact hDf.weight_eq.trans hDg.weight_eq.symm
  change (RandomSystems.statDist R I : ℝ) ≤ _
  calc
    (RandomSystems.statDist R I : ℝ) =
        (RandomSystems.statDist I R : ℝ) := by
      rw [RandomSystems.statDist_symm_of_eq_weight R I hweight]
    _ = (I.mass (fun ys => R ys < I ys) : ℝ) -
          (R.mass (fun ys => R ys < I ys) : ℝ) :=
      RandomSystems.statDist_eq_mass_sub_mass_pos I R
    _ = advantage D (⌈q⌉ PFunPDS.ofFunDist Df)
          (⌈q⌉ PFunPDS.ofFunDist Dg) := by
      unfold advantage
      rw [hR, hI]
    _ ≤ Δ(⌈q⌉ PFunPDS.ofFunDist Df, ⌈q⌉ PFunPDS.ofFunDist Dg) :=
      advantage_le_maxAdvantage D _ _ (pointDistinguisher_isProbDist _)

/-- The performance equality expected from a converter application. -/
abbrev WinningConverterPerfEq
    (convert : WinningGame X Y → WinningGame U V)
    (rho : WinnerSolver U V → WinnerSolver X Y)
    (G : WinningGame X Y) : Prop :=
  ∀ W : WinnerSolver U V, winProb W (convert G) = winProb (rho W) G

/-- The cost side condition for the converter-induced solver map. -/
abbrev WinningConverterCostBound
    {LabelC LabelG : Type*}
    (rho : WinnerSolver U V → WinnerSolver X Y)
    (gammaC : WinnerSolver U V → Cost LabelC)
    (gammaG : WinnerSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  ∀ W : WinnerSolver U V, gammaG (rho W) ≤ costMap (gammaC W)

/-- The single named hypothesis for a converter-induced costed reduction. -/
abbrev WinningConverterReductionHyp
    {LabelC LabelG : Type*}
    (convert : WinningGame X Y → WinningGame U V)
    (rho : WinnerSolver U V → WinnerSolver X Y)
    (G : WinningGame X Y)
    (gammaC : WinnerSolver U V → Cost LabelC)
    (gammaG : WinnerSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  WinningConverterPerfEq convert rho G ∧ WinningConverterCostBound rho gammaC gammaG costMap

/-- The costed reduction induced by a converter equality. -/
abbrev WinningConverterCostedReduction
    {LabelC LabelG : Type*}
    (convert : WinningGame X Y → WinningGame U V)
    (rho : WinnerSolver U V → WinnerSolver X Y)
    (G : WinningGame X Y)
    (gammaC : WinnerSolver U V → Cost LabelC)
    (gammaG : WinnerSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  @IsCostedReduction
    (WinningGame U V) (WinnerSolver U V) ℝ
    (WinningGame X Y) (WinnerSolver X Y) ℝ
    _ (winningProblem U V) _ (winningProblem X Y)
    LabelC LabelG
    (convert G) G (_root_.id : ℝ → ℝ) rho
    gammaC gammaG costMap

section WinningConverterReduction

variable {LabelC LabelG : Type*}
variable {convert : WinningGame X Y → WinningGame U V}
variable {rho : WinnerSolver U V → WinnerSolver X Y}
variable {G : WinningGame X Y}
variable {gammaC : WinnerSolver U V → Cost LabelC}
variable {gammaG : WinnerSolver X Y → Cost LabelG}
variable {costMap : Cost LabelC → Cost LabelG}

theorem winningConverter_isCostedReduction
    (h : WinningConverterReductionHyp convert rho G gammaC gammaG costMap) :
    WinningConverterCostedReduction convert rho G gammaC gammaG costMap := by
  cr18_reduction_from h with [WinningConverterCostedReduction, winningProblem, pfunWinningProblem]

end WinningConverterReduction

/-- Apply a system converter to both sides of a distinguishing game. -/
def convertDistinguishingGame
    (convert : PFunPDS X Y → PFunPDS U V)
    (p : DistinguishingGame X Y) : DistinguishingGame U V :=
  (convert p.1, convert p.2)

@[simp] theorem convertDistinguishingGame_left
    (convert : PFunPDS X Y → PFunPDS U V)
    (p : DistinguishingGame X Y) :
    (convertDistinguishingGame convert p).1 = convert p.1 :=
  rfl

@[simp] theorem convertDistinguishingGame_right
    (convert : PFunPDS X Y → PFunPDS U V)
    (p : DistinguishingGame X Y) :
    (convertDistinguishingGame convert p).2 = convert p.2 :=
  rfl

/-- The performance equality expected from composing a distinguisher with a
converter. -/
abbrev DistinguishingConverterPerfEq
    (convert : PFunPDS X Y → PFunPDS U V)
    (rho : DistinguisherSolver U V → DistinguisherSolver X Y)
    (p : DistinguishingGame X Y) : Prop :=
  ∀ D : DistinguisherSolver U V,
    advantage D (convert p.1) (convert p.2) = advantage (rho D) p.1 p.2

theorem oneCallApplyPDS_distinguishingPerfEq
    (toInner : U → X) (toOuter : U → Y → V)
    (p : DistinguishingGame X Y) :
    DistinguishingConverterPerfEq
      (oneCallApplyPDS toInner toOuter)
      (composeOneCallDDDDist toInner toOuter) p := by
  intro D
  exact advantage_oneCallApplyPDS toInner toOuter D p.1 p.2

/-- The cost side condition for the converter-induced distinguisher map. -/
abbrev DistinguishingConverterCostBound
    {LabelC LabelG : Type*}
    (rho : DistinguisherSolver U V → DistinguisherSolver X Y)
    (gammaC : DistinguisherSolver U V → Cost LabelC)
    (gammaG : DistinguisherSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  ∀ D : DistinguisherSolver U V, gammaG (rho D) ≤ costMap (gammaC D)

/-- The single named hypothesis for a converter-induced distinguishing
reduction. -/
abbrev DistinguishingConverterReductionHyp
    {LabelC LabelG : Type*}
    (convert : PFunPDS X Y → PFunPDS U V)
    (rho : DistinguisherSolver U V → DistinguisherSolver X Y)
    (p : DistinguishingGame X Y)
    (gammaC : DistinguisherSolver U V → Cost LabelC)
    (gammaG : DistinguisherSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  DistinguishingConverterPerfEq convert rho p ∧
    DistinguishingConverterCostBound rho gammaC gammaG costMap

/-- The costed reduction induced by a distinguishing-converter equality. -/
abbrev DistinguishingConverterCostedReduction
    {LabelC LabelG : Type*}
    (convert : PFunPDS X Y → PFunPDS U V)
    (rho : DistinguisherSolver U V → DistinguisherSolver X Y)
    (p : DistinguishingGame X Y)
    (gammaC : DistinguisherSolver U V → Cost LabelC)
    (gammaG : DistinguisherSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG) : Prop :=
  @IsCostedReduction
    (DistinguishingGame U V) (DistinguisherSolver U V) ℝ
    (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ
    _ (distinguishingProblem U V) _ (distinguishingProblem X Y)
    LabelC LabelG
    (convertDistinguishingGame convert p) p (_root_.id : ℝ → ℝ) rho
    gammaC gammaG costMap

section DistinguishingConverterReduction

variable {LabelC LabelG : Type*}
variable {convert : PFunPDS X Y → PFunPDS U V}
variable {rho : DistinguisherSolver U V → DistinguisherSolver X Y}
variable {p : DistinguishingGame X Y}
variable {gammaC : DistinguisherSolver U V → Cost LabelC}
variable {gammaG : DistinguisherSolver X Y → Cost LabelG}
variable {costMap : Cost LabelC → Cost LabelG}

theorem distinguishingConverter_isCostedReduction
    (h : DistinguishingConverterReductionHyp convert rho p gammaC gammaG costMap) :
    DistinguishingConverterCostedReduction convert rho p gammaC gammaG costMap := by
  cr18_reduction_from h with [DistinguishingConverterCostedReduction, convertDistinguishingGame,
    distinguishingProblem, pfunDistinguishingProblem]

end DistinguishingConverterReduction

theorem oneCallApplyPDS_distinguishingCostedReduction
    {LabelC LabelG : Type*}
    (toInner : U → X) (toOuter : U → Y → V)
    (p : DistinguishingGame X Y)
    (gammaC : DistinguisherSolver U V → Cost LabelC)
    (gammaG : DistinguisherSolver X Y → Cost LabelG)
    (costMap : Cost LabelC → Cost LabelG)
    (hcost : DistinguishingConverterCostBound
      (composeOneCallDDDDist toInner toOuter) gammaC gammaG costMap) :
    DistinguishingConverterCostedReduction
      (oneCallApplyPDS toInner toOuter)
      (composeOneCallDDDDist toInner toOuter) p gammaC gammaG costMap := by
  apply distinguishingConverter_isCostedReduction
  exact ⟨oneCallApplyPDS_distinguishingPerfEq toInner toOuter p, hcost⟩

end

end Complexity
end RandomSystems.CR18
