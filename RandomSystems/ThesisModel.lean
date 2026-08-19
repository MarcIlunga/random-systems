/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContextSharedDomain
import RandomSystems.BoundedAttainment

/-!
# The thesis's environment model, realized inside the CR18 carrier
(Lanzenberger, *Theory of Random Systems and Games*, Defs 2.11, 2.12, 2.17, 2.26)

The repository's random-systems layer was built against CR18: an environment
is the `⊥`-totalized `DDE X Y = List (Option Y) → Option X` (CR18 Def 3.6)
played against the completion `s⊥` (CR18 Def 3.3).  The thesis has **no `⊥`
channel at all**: its environment (Def 2.11) is a *partial* function
`e : Y* →. X` with prefix-closed domain, and Def 2.12 *requires* the
environment to be compatible with the system — it must never query outside
the system's domain.  Everything downstream (equivalence Def 2.17, advantage
Def 2.26) quantifies over compatible environments only.

This file makes the thesis objects first-class and reconciles the two models:

* `PartialDDE` — thesis Def 2.11 verbatim: `e : List Y →. X`, prefix-closed
  domain.  No `⊥` on either side of the arrow.
* `thesisTranscript` / `thesisTranscriptDist` — thesis Def 2.12 and its
  fn. 5: the transcript recurrence `xᵢ = e(y₁…yᵢ₋₁)`, `yᵢ = s(x₁…xᵢ)`, and
  the `tr(·,e)`-transformation of the law.  Transcript entries are `X × Y` —
  no `Option`.
* `Compatible` — thesis Def 2.12's side condition, per pair `(s, e)` along
  the actual run: whenever `e` produces the next query, `s` answers it.
* `ThesisEquivalent` / `ThesisAdv` — thesis Def 2.17 and Def 2.26, with the
  thesis's own quantifier (compatible deterministic environments).

## The reconciliation theorems

**Embedding (no hypotheses beyond the thesis's own compatibility).**
`PartialDDE.toDDE` totalizes a thesis environment into a CR18 one;
`transcript_toDDE_eq_someMap_thesisTranscript` proves the CR18 interaction
against `s⊥` computes exactly the thesis interaction (the `⊥` channel is
never exercised), so the CR18 transcript law is the injective `someMap`
pushforward of the thesis law (`transcriptDist_toDDE_eq`).  Corollaries:
every thesis-side statistical distance is a CR18 `Adv`-witness
(`delta_thesisTranscriptDist_le_adv`), and CR18 equivalence implies thesis
equivalence (`thesisEquivalent_of_equivalent`).

**Pruning (the converse, on the objects the thesis admits).**  On laws with
one shared support domain — exactly thesis Def 2.14's PDS discipline,
`PFunPDS.HasFixedDomain` — CR18's `⊥` channel buys the environment *nothing*:
rejection is a public function of the query history, so the rejection-pruning
machine of `StrictContextSharedDomain` compiles any CR18 environment into a
compatible thesis environment (`prunedPartialDDE`) with the *same*
distinguishing power (`delta_transcriptDist_eq_delta_thesis_pruned`).

**Headlines.**  On shared-domain laws the two models agree exactly:

* `equivalent_iff_thesisEquivalent` — CR18 `Equivalent` (all totalized
  environments) ↔ thesis Def 2.17 (compatible partial environments);
* `adv_eq_thesisAdv` — CR18 `Adv` (thesis Def 2.26 read on the totalized
  carrier) = the thesis's own compatible-environment supremum.

Off the shared-domain subcarrier the two models genuinely differ: the
totalized environment observes the support's domain pattern through `⊥`
answers (`papers/notes/RS_SOURCE_CONTRACT.md` §5, receipt LM-C), which is
why thesis Theorem 2.31/2.32 carry the Def 2.14 domain clause.
-/

namespace RandomSystems.CR18.ThesisModel

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.StrictContextSharedDomain
open scoped PFunDDS

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Thesis Definition 2.11: partial deterministic environments -/

/-- Thesis Def 2.11: a deterministic discrete environment for an
`(X, Y)`-DDS (a `(Y, X)`-DDE) is a **partial** function `e : Y* →. X` with
prefix-closed domain.  There is no `⊥` in the input alphabet and no stop
symbol in the output: stopping *is* undefinedness. -/
def PartialDDE (X : Type u) (Y : Type v) : Type (max u v) :=
  { environment : List Y →. X //
    ∀ ⦃shorter longer : List Y⦄, shorter <+: longer →
      longer ∈ environment.Dom → shorter ∈ environment.Dom }

/-- The query projection of a thesis transcript (`t' ∈ X*` of Def 2.21's
notation): first components. -/
def transcriptQueries (t : List (X × Y)) : List X :=
  t.map Prod.fst

/-- The answer projection of a thesis transcript: second components. -/
def transcriptAnswers (t : List (X × Y)) : List Y :=
  t.map Prod.snd

@[simp] theorem transcriptQueries_nil :
    transcriptQueries ([] : List (X × Y)) = [] := rfl

@[simp] theorem transcriptAnswers_nil :
    transcriptAnswers ([] : List (X × Y)) = [] := rfl

@[simp] theorem transcriptQueries_append_singleton (t : List (X × Y))
    (p : X × Y) :
    transcriptQueries (t ++ [p]) = transcriptQueries t ++ [p.1] := by
  simp [transcriptQueries]

@[simp] theorem transcriptAnswers_append_singleton (t : List (X × Y))
    (p : X × Y) :
    transcriptAnswers (t ++ [p]) = transcriptAnswers t ++ [p.2] := by
  simp [transcriptAnswers]

/-! ## Thesis Definition 2.12: the transcript

The recurrence `xᵢ = e(y₁,…,yᵢ₋₁)`, `yᵢ = s(x₁,…,xᵢ)`.  The thesis presents
the transcript only for compatible pairs; to keep the Lean function total we
stop the recurrence when either the environment is undefined (the thesis's
"the environment stops") or the system would reject (unreachable under
Def 2.12's compatibility, `Compatible` below). -/

/-- Thesis Def 2.12: the transcript of a system `s` in a partial environment
`e`, presented (like `PFunDDS.transcript`) as the function sending a step
count to the transcript prefix after that many rounds. -/
def thesisTranscript (system : PFunDDS.DDS X Y) (environment : PartialDDE X Y) :
    ℕ → List (X × Y)
  | 0 => []
  | n + 1 =>
      if he : (environment.1
          (transcriptAnswers (thesisTranscript system environment n))).Dom then
        if hs : transcriptQueries (thesisTranscript system environment n) ++
            [(environment.1
              (transcriptAnswers (thesisTranscript system environment n))).get he]
            ∈ PFunDDS.dom system then
          thesisTranscript system environment n ++
            [((environment.1
                (transcriptAnswers (thesisTranscript system environment n))).get he,
              PFunDDS.output system
                (transcriptQueries (thesisTranscript system environment n) ++
                  [(environment.1
                    (transcriptAnswers
                      (thesisTranscript system environment n))).get he]) hs)]
        else thesisTranscript system environment n
      else thesisTranscript system environment n

@[simp] theorem thesisTranscript_zero (system : PFunDDS.DDS X Y)
    (environment : PartialDDE X Y) :
    thesisTranscript system environment 0 = [] := rfl

/-- Thesis Def 2.12, stall step: if the environment is undefined on the
current answer history, the transcript ends. -/
theorem thesisTranscript_succ_stall {system : PFunDDS.DDS X Y}
    {environment : PartialDDE X Y} {n : ℕ}
    (hstop : ¬ (environment.1
      (transcriptAnswers (thesisTranscript system environment n))).Dom) :
    thesisTranscript system environment (n + 1) =
      thesisTranscript system environment n := by
  simp only [thesisTranscript]
  rw [dif_neg hstop]

/-- Thesis Def 2.12, firing step: if the environment produces `x` and the
system answers it, the round `(x, s(x₁…xₙx))` is appended. -/
theorem thesisTranscript_succ_fire {system : PFunDDS.DDS X Y}
    {environment : PartialDDE X Y} {n : ℕ} {x : X}
    (hx : x ∈ environment.1
      (transcriptAnswers (thesisTranscript system environment n)))
    (hs : transcriptQueries (thesisTranscript system environment n) ++ [x]
      ∈ PFunDDS.dom system) :
    thesisTranscript system environment (n + 1) =
      thesisTranscript system environment n ++
        [(x, PFunDDS.output system
          (transcriptQueries (thesisTranscript system environment n) ++ [x]) hs)] := by
  have hdom : (environment.1
      (transcriptAnswers (thesisTranscript system environment n))).Dom :=
    Part.dom_iff_mem.mpr ⟨x, hx⟩
  have hget : (environment.1
      (transcriptAnswers (thesisTranscript system environment n))).get hdom = x :=
    Part.get_eq_of_mem hx hdom
  simp only [thesisTranscript]
  rw [dif_pos hdom]
  simp only [hget]
  rw [dif_pos hs]

/-- The queries of a thesis transcript prefix are an accepted input history
of the system (or the prefix is still empty): only answered rounds are ever
appended. -/
theorem thesisTranscript_queries_mem_or_eq_nil (system : PFunDDS.DDS X Y)
    (environment : PartialDDE X Y) (n : ℕ) :
    transcriptQueries (thesisTranscript system environment n)
        ∈ PFunDDS.dom system ∨
      transcriptQueries (thesisTranscript system environment n) = [] := by
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
      by_cases he : (environment.1
          (transcriptAnswers (thesisTranscript system environment n))).Dom
      · by_cases hs : transcriptQueries (thesisTranscript system environment n) ++
            [(environment.1
              (transcriptAnswers (thesisTranscript system environment n))).get he]
            ∈ PFunDDS.dom system
        · rw [thesisTranscript_succ_fire (Part.get_mem he) hs,
            transcriptQueries_append_singleton]
          exact Or.inl hs
        · simp only [thesisTranscript]
          rw [dif_pos he, dif_neg hs]
          exact ih
      · rw [thesisTranscript_succ_stall he]
        exact ih

/-! ## Thesis Definition 2.12's side condition: compatibility -/

/-- Thesis Def 2.12: "we require the environment `e` to be **compatible**
with `s`, i.e., the environment must not query `s` outside of the system's
domain.  Formally, `yᵢ = s(x₁,…,xᵢ)` is defined whenever
`xᵢ = e(y₁,…,yᵢ₋₁)` is defined" — stated along the actual run of the pair. -/
def Compatible (system : PFunDDS.DDS X Y) (environment : PartialDDE X Y) : Prop :=
  ∀ (n : ℕ) (x : X),
    x ∈ environment.1
      (transcriptAnswers (thesisTranscript system environment n)) →
    transcriptQueries (thesisTranscript system environment n) ++ [x]
      ∈ PFunDDS.dom system

/-- Thesis Defs 2.17/2.26 quantify over environments compatible with the
random system: an environment is compatible with a law when it is compatible
with every representative atom. -/
def CompatibleWithLaw (S : PFunPDS X Y) (environment : PartialDDE X Y) : Prop :=
  ∀ system ∈ S.support, Compatible system environment

/-- Thesis Def 2.12 fn. 5 (as quoted at Def 2.17): `tr(S, e)` is the
`tr(·,e)`-transformation of the law `S` — here, of the length-`n` prefix,
for each `n`. -/
def thesisTranscriptDist (S : PFunPDS X Y) (environment : PartialDDE X Y)
    (n : ℕ) : Dist (List (X × Y)) :=
  Dist.fTransform (fun system => thesisTranscript system environment n) S

/-- Thesis Def 2.17: two PDS are equivalent when their transcript
distributions agree in every compatible deterministic environment.  (The
thesis's "same domain" clause is carried by the `PFunPDS.HasFixedDomain`
hypotheses of the reconciliation headline, not baked into the relation.) -/
def ThesisEquivalent (S T : PFunPDS X Y) : Prop :=
  ∀ environment : PartialDDE X Y,
    CompatibleWithLaw S environment → CompatibleWithLaw T environment →
    ∀ n : ℕ,
      thesisTranscriptDist S environment n = thesisTranscriptDist T environment n

/-- Thesis Def 2.26: the optimal distinguishing advantage as the thesis
itself defines it — the supremum of transcript statistical distance over
**compatible** partial deterministic environments (and prefix lengths). -/
def ThesisAdv (S T : PFunPDS X Y) : ℝ :=
  sSup {a : ℝ | ∃ environment : PartialDDE X Y,
    CompatibleWithLaw S environment ∧ CompatibleWithLaw T environment ∧
    ∃ n : ℕ, a = (δ (thesisTranscriptDist S environment n)
      (thesisTranscriptDist T environment n) : ℝ)}

/-! ## The `someMap` comparison: thesis transcripts inside CR18 transcripts -/

/-- The evident injection of thesis transcripts (`X × Y` rounds) into CR18
transcripts (`X × Option Y` rounds): every answer is a real answer. -/
def someMap (t : List (X × Y)) : List (X × Option Y) :=
  t.map fun p => (p.1, some p.2)

theorem someMap_injective : Function.Injective (someMap (X := X) (Y := Y)) := by
  refine List.map_injective_iff.mpr ?_
  intro p q hpq
  cases p
  cases q
  simpa [Prod.ext_iff] using hpq

@[simp] theorem someMap_nil : someMap ([] : List (X × Y)) = [] := rfl

@[simp] theorem someMap_append_singleton (t : List (X × Y)) (p : X × Y) :
    someMap (t ++ [p]) = someMap t ++ [(p.1, some p.2)] := by
  simp [someMap]

@[simp] theorem transcriptInputs_someMap (t : List (X × Y)) :
    (someMap t)↓ₓ = transcriptQueries t := by
  simp [someMap, PFunDDS.transcriptInputs, transcriptQueries]

@[simp] theorem transcriptOutputs_someMap (t : List (X × Y)) :
    (someMap t)↓ᵧ = (transcriptAnswers t).map some := by
  simp [someMap, PFunDDS.transcriptOutputs, transcriptAnswers]

/-! ## Totalization: a thesis environment as a CR18 environment -/

@[simp] theorem filterMap_id_map_some (answers : List Y) :
    (answers.map some).filterMap id = answers := by
  simp

/-- The CR18 realization of a thesis environment: on an all-answered history
consult the partial function (undefined = stop `⊣`); on any history
containing `⊥` — which a compatible interaction never produces — stop. -/
def PartialDDE.toDDE (environment : PartialDDE X Y) : PFunDDS.DDE X Y :=
  fun history =>
    if h : (∀ answer ∈ history, Option.isSome answer) ∧
        (environment.1 (history.filterMap id)).Dom then
      some ((environment.1 (history.filterMap id)).get h.2)
    else none

/-- The totalized environment fires exactly the thesis environment's query on
an all-answered history. -/
theorem toDDE_map_some_fire {environment : PartialDDE X Y} {answers : List Y}
    {x : X} (hx : x ∈ environment.1 answers) :
    environment.toDDE (answers.map some) = some x := by
  have hrw : (answers.map some).filterMap id = answers :=
    filterMap_id_map_some answers
  have hx' : x ∈ environment.1 ((answers.map some).filterMap id) := by
    rw [hrw]
    exact hx
  have hdom : (environment.1 ((answers.map some).filterMap id)).Dom :=
    Part.dom_iff_mem.mpr ⟨x, hx'⟩
  unfold PartialDDE.toDDE
  rw [dif_pos ⟨by simp, hdom⟩]
  exact congrArg some (Part.get_eq_of_mem hx' _)

/-- The totalized environment stops exactly where the thesis environment is
undefined on an all-answered history. -/
theorem toDDE_map_some_stall {environment : PartialDDE X Y} {answers : List Y}
    (hstop : ¬ (environment.1 answers).Dom) :
    environment.toDDE (answers.map some) = none := by
  have hrw : (answers.map some).filterMap id = answers :=
    filterMap_id_map_some answers
  unfold PartialDDE.toDDE
  rw [dif_neg]
  intro hcontra
  exact hstop (hrw ▸ hcontra.2)

/-! ## The embedding: CR18 computes the thesis semantics

Against a compatible environment the CR18 interaction with `s⊥` never
exercises the `⊥` channel, and the two transcripts advance in lockstep. -/

/-- **Thesis Def 2.12 inside CR18 Def 3.7.**  For a compatible pair, the
CR18 transcript of `s` against the totalized environment is exactly the
thesis transcript with every answer marked `some`. -/
theorem transcript_toDDE_eq_someMap_thesisTranscript
    (system : PFunDDS.DDS X Y) (environment : PartialDDE X Y)
    (compatible : Compatible system environment) :
    ∀ n : ℕ, PFunDDS.transcript system environment.toDDE n =
      someMap (thesisTranscript system environment n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases he : (environment.1
          (transcriptAnswers (thesisTranscript system environment n))).Dom
      · -- the environment fires: both transcripts append the same round
        have hx : (environment.1
            (transcriptAnswers (thesisTranscript system environment n))).get he
            ∈ environment.1
              (transcriptAnswers (thesisTranscript system environment n)) :=
          Part.get_mem he
        set x := (environment.1
          (transcriptAnswers (thesisTranscript system environment n))).get he
        have hs := compatible n x hx
        have hfire : environment.toDDE
            ((PFunDDS.transcript system environment.toDDE n)↓ᵧ) = some x := by
          rw [ih, transcriptOutputs_someMap]
          exact toDDE_map_some_fire hx
        have houtput : PFunDDS.output (system⊥)
            ((PFunDDS.transcript system environment.toDDE n)↓ₓ ++ [x])
            (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
            some (PFunDDS.output system
              (transcriptQueries (thesisTranscript system environment n) ++ [x])
              hs) := by
          have hlist : (PFunDDS.transcript system environment.toDDE n)↓ₓ ++ [x]
              = transcriptQueries (thesisTranscript system environment n) ++ [x] := by
            rw [ih, transcriptInputs_someMap]
          refine (PFunDDS.output_congr (system⊥) hlist _ (by
            rw [PFunDDS.dom_fullyDefined]
            simp)).trans ?_
          exact PFunDDS.output_fullyDefined_append_of_mem system
            (transcriptQueries (thesisTranscript system environment n)) x
            (thesisTranscript_queries_mem_or_eq_nil system environment n) hs
        rw [transcript_succ_fire hfire, houtput,
          thesisTranscript_succ_fire hx hs, someMap_append_singleton, ih]
      · -- the environment stops: both transcripts stall
        have hstall : environment.toDDE
            ((PFunDDS.transcript system environment.toDDE n)↓ᵧ) = none := by
          rw [ih, transcriptOutputs_someMap]
          exact toDDE_map_some_stall he
        rw [transcript_succ_stall hstall, thesisTranscript_succ_stall he, ih]

/-- Pushforwards along two maps that agree on the support agree. -/
theorem fTransform_congr_support {A : Type*} {B : Type*} (S : Dist A)
    {f g : A → B} (h : ∀ a ∈ S.support, f a = g a) :
    Dist.fTransform f S = Dist.fTransform g S := by
  unfold Dist.fTransform
  exact Finsupp.sum_congr fun a ha => by rw [h a ha]

/-- Pushforward functoriality, stated instance-free for the transcript
carriers (the `Dist.fTransform_comp` in `Dist.lean` sits in a section with
ambient `Fintype`/`Nonempty` variables). -/
theorem fTransform_comp' {A B C : Type*} (g : B → C) (f : A → B) (S : Dist A) :
    Dist.fTransform g (Dist.fTransform f S) = Dist.fTransform (g ∘ f) S := by
  show Finsupp.mapDomain g (Finsupp.mapDomain f S) = Finsupp.mapDomain (g ∘ f) S
  rw [Finsupp.mapDomain_comp]

/-- **Thesis Def 2.12 fn. 5 inside the CR18 law.**  The CR18 transcript law
at the totalized environment is the `someMap` pushforward of the thesis
transcript law. -/
theorem transcriptDist_toDDE_eq (S : PFunPDS X Y)
    (environment : PartialDDE X Y)
    (compatible : CompatibleWithLaw S environment) (n : ℕ) :
    transcriptDist S environment.toDDE n =
      Dist.fTransform someMap (thesisTranscriptDist S environment n) := by
  unfold transcriptDist thesisTranscriptDist
  rw [fTransform_comp']
  exact fTransform_congr_support S fun system hsystem =>
    transcript_toDDE_eq_someMap_thesisTranscript system environment
      (compatible system hsystem) n

/-- The thesis-side statistical distance per compatible environment equals
the CR18 distance at the totalized environment: `someMap` is injective, so
the pushforward loses nothing (thesis Def 2.4 / Lemma 2.7 at equality).

`hT` is the signed carrier's cost: `δ_fTransform_eq_of_injective` reads back
the pushforward through a left inverse, and that step needs the *second* law
to be a genuine distribution.  `Dist.NonNeg` is enough — no normalization is
used — so this stays below the `isProbDist` layer. -/
theorem delta_thesisTranscriptDist_eq {S T : PFunPDS X Y}
    {environment : PartialDDE X Y}
    (compatibleLeft : CompatibleWithLaw S environment)
    (compatibleRight : CompatibleWithLaw T environment) (hT : T.NonNeg)
    (n : ℕ) :
    δ (thesisTranscriptDist S environment n)
        (thesisTranscriptDist T environment n) =
      δ (transcriptDist S environment.toDDE n)
        (transcriptDist T environment.toDDE n) := by
  rw [transcriptDist_toDDE_eq S environment compatibleLeft n,
    transcriptDist_toDDE_eq T environment compatibleRight n,
    δ_fTransform_eq_of_injective someMap_injective]
  exact hT.fTransform _

/-- Thesis Def 2.26 ≤ CR18 `Adv`: every compatible thesis environment is
realized by a totalized CR18 environment with the same transcript distance.

Both laws must be non-negative here: the CR18 supremum is only bounded above
(`bddAbove_adv_set`) for genuine distributions. -/
theorem delta_thesisTranscriptDist_le_adv (S T : PFunPDS X Y)
    {environment : PartialDDE X Y}
    (compatibleLeft : CompatibleWithLaw S environment)
    (compatibleRight : CompatibleWithLaw T environment)
    (hS : S.NonNeg) (hT : T.NonNeg) (n : ℕ) :
    (δ (thesisTranscriptDist S environment n)
      (thesisTranscriptDist T environment n) : ℝ) ≤ Adv S T :=
  le_csSup (bddAbove_adv_set hS hT)
    ⟨environment.toDDE, n, by
      rw [delta_thesisTranscriptDist_eq compatibleLeft compatibleRight hT n]⟩

/-- CR18 equivalence implies thesis Def 2.17 equivalence: the totalized
environments include (the realizations of) all compatible partial ones.
No shared-domain hypothesis is needed for this direction. -/
theorem thesisEquivalent_of_equivalent {S T : PFunPDS X Y}
    (h : Equivalent S T) : ThesisEquivalent S T := by
  intro environment compatibleLeft compatibleRight n
  have hlaw := h environment.toDDE n
  rw [transcriptDist_toDDE_eq S environment compatibleLeft n,
    transcriptDist_toDDE_eq T environment compatibleRight n] at hlaw
  ext t
  have happly := congrArg (fun d => d (someMap t)) hlaw
  simpa [Dist.fTransform_injective_apply _ someMap someMap_injective]
    using happly

/-! ## The pruned thesis environment

The converse direction.  `StrictContextSharedDomain`'s replay machine
(`pruneRun`/`prunedDDD`) simulates a CR18 environment against a known common
domain, synthesizes every `⊥` answer itself, and forwards only accepted
queries.  Read as a *partial* function of the real answers, that machine
**is** a thesis environment, and on shared-domain atoms it is compatible. -/

/-- The pruned CR18 environment (the query view of
`StrictContextSharedDomain.prunedDDD`; the verdict function is irrelevant
for the environment view). -/
def prunedNext (e : PFunDDS.DDE X Y) (D : Set (List X)) (q : ℕ) :
    PFunDDS.DDE X Y :=
  PFunDDS.ddToDDE (prunedDDD e D q fun _ => false)

theorem prunedNext_def (e : PFunDDS.DDE X Y) (D : Set (List X)) (q : ℕ) :
    prunedNext e D q = PFunDDS.ddToDDE (prunedDDD e D q fun _ => false) := rfl

/-- The pruning replay as a **thesis** environment (Def 2.11): a partial
function of the real (all-answered) history.  Undefined exactly where the
pruned distinguisher stops; prefix-closedness is the finality of the pruned
verdict (`StopFinal`). -/
def prunedPartialDDE (e : PFunDDS.DDE X Y) (D : Set (List X)) (q : ℕ) :
    PartialDDE X Y :=
  ⟨fun answers => Part.ofOption (prunedNext e D q (answers.map some)), by
    intro shorter longer hprefix hdom
    rw [PFun.mem_dom] at hdom ⊢
    obtain ⟨x, hx⟩ := hdom
    rw [Part.mem_ofOption] at hx
    rcases hshorter : prunedNext e D q (shorter.map some) with _ | x'
    · exfalso
      obtain ⟨b, hb⟩ := PFunDDS.ddToDDE_eq_none_iff.mp hshorter
      have hlonger : prunedNext e D q (longer.map some) = none :=
        PFunDDS.ddToDDE_eq_none_iff.mpr
          ⟨b, (prunedDDD e D q fun _ => false).2 (hprefix.map some) b hb⟩
      rw [Option.mem_def, hlonger] at hx
      simp at hx
    · exact ⟨x', by rw [Part.mem_ofOption, Option.mem_def]⟩⟩

/-- Every answer in a pruned-environment CR18 transcript is a real answer:
the pruned interaction never receives the completion symbol on a
shared-domain atom. -/
theorem transcript_prunedNext_isSome {D : Set (List X)} {s : PFunDDS.DDS X Y}
    (hdom : PFunDDS.dom s = D) (e : PFunDDS.DDE X Y) (q j : ℕ) :
    ∀ p ∈ PFunDDS.transcript s (prunedNext e D q) j, (p.2).isSome := by
  obtain ⟨f', -, htranscript, -, -⟩ :=
    transcript_prunedDDD (s := s) e q (fun _ => false) hdom j
  intro p hp
  rw [prunedNext_def, htranscript] at hp
  exact (List.mem_filter.mp hp).2

/-- When the pruned environment forwards a query, the shared-domain atom
answers it: the machine only forwards accepted queries. -/
theorem transcript_prunedNext_fire_accepted {D : Set (List X)}
    {s : PFunDDS.DDS X Y} (hdom : PFunDDS.dom s = D) (e : PFunDDS.DDE X Y)
    (q : ℕ) {j : ℕ} {x : X}
    (hfire : prunedNext e D q
      ((PFunDDS.transcript s (prunedNext e D q) j)↓ᵧ) = some x) :
    ∃ hs : (PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x]
        ∈ PFunDDS.dom s,
      PFunDDS.output (s⊥)
          ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x])
          (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
        some (PFunDDS.output s
          ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x]) hs) := by
  -- the appended answer at step `j + 1` is a real answer
  have hmem : (x, PFunDDS.output (s⊥)
      ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]))
      ∈ PFunDDS.transcript s (prunedNext e D q) (j + 1) := by
    rw [transcript_succ_fire hfire]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hsome := transcript_prunedNext_isSome hdom e q (j + 1) _ hmem
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  -- the current inputs are a kept prefix: accepted or empty
  obtain ⟨f', -, htranscript, -, -⟩ :=
    transcript_prunedDDD (s := s) e q (fun _ => false) hdom j
  have hinputs : (PFunDDS.transcript s (prunedNext e D q) j)↓ₓ
      ∈ PFunDDS.dom s ∨
      (PFunDDS.transcript s (prunedNext e D q) j)↓ₓ = [] := by
    rw [prunedNext_def, htranscript]
    have hkept : (properSteps (PFunDDS.transcript s e f'))↓ₓ =
        PFunDDS.keptPrefix s ((PFunDDS.transcript s e f')↓ₓ) :=
      keptTranscriptInputs_transcript s e f'
    rw [hkept]
    rcases PFunDDS.keptPrefix_mem_or s ((PFunDDS.transcript s e f')↓ₓ) with
      hmem' | hempty
    · exact Or.inl hmem'
    · exact Or.inr hempty
  obtain ⟨hs, houtput⟩ := PFunDDS.mem_of_output_fullyDefined_append_eq_some s
    ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ) x hinputs hy
  refine ⟨hs, ?_⟩
  have hy' : PFunDDS.output (s⊥)
      ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) = some y := hy
  rw [hy', houtput]

/-- **The pruned machine is a thesis interaction.**  Against a shared-domain
atom, the thesis transcript of the pruned partial environment is (the
`someMap` unmarking of) the CR18 transcript of the pruned environment. -/
theorem someMap_thesisTranscript_prunedPartialDDE {D : Set (List X)}
    {s : PFunDDS.DDS X Y} (hdom : PFunDDS.dom s = D) (e : PFunDDS.DDE X Y)
    (q : ℕ) :
    ∀ j : ℕ, someMap (thesisTranscript s (prunedPartialDDE e D q) j) =
      PFunDDS.transcript s (prunedNext e D q) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have hanswers : (transcriptAnswers
          (thesisTranscript s (prunedPartialDDE e D q) j)).map some =
          (PFunDDS.transcript s (prunedNext e D q) j)↓ᵧ := by
        rw [← ih, transcriptOutputs_someMap]
      have hqueries : transcriptQueries
          (thesisTranscript s (prunedPartialDDE e D q) j) =
          (PFunDDS.transcript s (prunedNext e D q) j)↓ₓ := by
        rw [← ih, transcriptInputs_someMap]
      rcases hnext : prunedNext e D q
          ((PFunDDS.transcript s (prunedNext e D q) j)↓ᵧ) with _ | x
      · -- both stall
        have hestall : ¬ ((prunedPartialDDE e D q).1
            (transcriptAnswers
              (thesisTranscript s (prunedPartialDDE e D q) j))).Dom := by
          intro hcontra
          obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hcontra
          rw [show (prunedPartialDDE e D q).1
              (transcriptAnswers (thesisTranscript s (prunedPartialDDE e D q) j))
              = Part.ofOption (prunedNext e D q
                ((transcriptAnswers
                  (thesisTranscript s (prunedPartialDDE e D q) j)).map some))
              from rfl, Part.mem_ofOption, Option.mem_def, hanswers, hnext]
            at hy
          simp at hy
        rw [transcript_succ_stall hnext, thesisTranscript_succ_stall hestall, ih]
      · -- both fire, with the same accepted query and the same real answer
        obtain ⟨hs, houtput⟩ :=
          transcript_prunedNext_fire_accepted hdom e q hnext
        have hx : x ∈ (prunedPartialDDE e D q).1
            (transcriptAnswers
              (thesisTranscript s (prunedPartialDDE e D q) j)) := by
          rw [show (prunedPartialDDE e D q).1
              (transcriptAnswers (thesisTranscript s (prunedPartialDDE e D q) j))
              = Part.ofOption (prunedNext e D q
                ((transcriptAnswers
                  (thesisTranscript s (prunedPartialDDE e D q) j)).map some))
              from rfl, Part.mem_ofOption, Option.mem_def, hanswers, hnext]
        have hsThesis : transcriptQueries
            (thesisTranscript s (prunedPartialDDE e D q) j) ++ [x]
            ∈ PFunDDS.dom s := by
          rw [hqueries]
          exact hs
        rw [transcript_succ_fire hnext, houtput,
          thesisTranscript_succ_fire hx hsThesis, someMap_append_singleton, ih]
        show PFunDDS.transcript s (prunedNext e D q) j ++
            [(x, some (PFunDDS.output s
              (transcriptQueries
                (thesisTranscript s (prunedPartialDDE e D q) j) ++ [x])
              hsThesis))] =
          PFunDDS.transcript s (prunedNext e D q) j ++
            [(x, some (PFunDDS.output s
              ((PFunDDS.transcript s (prunedNext e D q) j)↓ₓ ++ [x]) hs))]
        exact congrArg
          (fun z => PFunDDS.transcript s (prunedNext e D q) j ++ [(x, some z)])
          (PFunDDS.output_congr s (by rw [hqueries]) hsThesis hs)

/-- **The pruned environment is compatible** (thesis Def 2.12) with every
shared-domain atom: it only ever forwards queries the common domain accepts. -/
theorem compatible_prunedPartialDDE {D : Set (List X)} {s : PFunDDS.DDS X Y}
    (hdom : PFunDDS.dom s = D) (e : PFunDDS.DDE X Y) (q : ℕ) :
    Compatible s (prunedPartialDDE e D q) := by
  intro j x hx
  have hanswers : (transcriptAnswers
      (thesisTranscript s (prunedPartialDDE e D q) j)).map some =
      (PFunDDS.transcript s (prunedNext e D q) j)↓ᵧ := by
    rw [← someMap_thesisTranscript_prunedPartialDDE hdom e q j,
      transcriptOutputs_someMap]
  have hqueries : transcriptQueries
      (thesisTranscript s (prunedPartialDDE e D q) j) =
      (PFunDDS.transcript s (prunedNext e D q) j)↓ₓ := by
    rw [← someMap_thesisTranscript_prunedPartialDDE hdom e q j,
      transcriptInputs_someMap]
  have hfire : prunedNext e D q
      ((PFunDDS.transcript s (prunedNext e D q) j)↓ᵧ) = some x := by
    rw [show (prunedPartialDDE e D q).1
        (transcriptAnswers (thesisTranscript s (prunedPartialDDE e D q) j))
        = Part.ofOption (prunedNext e D q
          ((transcriptAnswers
            (thesisTranscript s (prunedPartialDDE e D q) j)).map some))
        from rfl, Part.mem_ofOption, Option.mem_def, hanswers] at hx
    exact hx
  obtain ⟨hs, -⟩ := transcript_prunedNext_fire_accepted hdom e q hfire
  rw [hqueries]
  exact hs

/-! ## Rejection pruning at the law level -/

/-- On a shared-domain law, the pruned environment's CR18 transcript law is
the `properSteps` pushforward of the unpruned law: after `q` real rounds the
machine has settled on the proper part of the genuine `q`-step transcript. -/
theorem transcript_prunedNext_eq_properSteps {D : Set (List X)}
    {s : PFunDDS.DDS X Y} (hdom : PFunDDS.dom s = D) (e : PFunDDS.DDE X Y)
    (q : ℕ) :
    PFunDDS.transcript s (prunedNext e D q) q =
      properSteps (PFunDDS.transcript s e q) := by
  obtain ⟨f', hf'q, htranscript, hrun, -⟩ :=
    transcript_prunedDDD (s := s) e q (fun _ => false) hdom q
  rcases he : e ((PFunDDS.transcript s e f')↓ᵧ) with _ | x
  · -- the unpruned environment stalled at `f'`: the transcript froze there
    have hfreeze : PFunDDS.transcript s e q = PFunDDS.transcript s e f' :=
      transcript_freeze he hf'q
    rw [prunedNext_def, htranscript, hfreeze]
  · -- the unpruned environment fires at `f'`: the budget must be exhausted
    have hge : ¬ (PFunDDS.transcript s e f').length < q := by
      intro hlen
      have hreallen : (PFunDDS.transcript s
          (PFunDDS.ddToDDE (prunedDDD e D q fun _ => false)) q).length < q := by
        rw [htranscript]
        exact Nat.lt_of_le_of_lt (length_properSteps_le _) hlen
      have hstallreal := PFunDDS.transcript_stall_of_length_lt hreallen
      rw [PFunDDS.ddToDDE_eq_none_iff] at hstallreal
      obtain ⟨b, hb⟩ := hstallreal
      have hb' : prunedMove e D q (fun _ => false)
          ((PFunDDS.transcript s
            (PFunDDS.ddToDDE (prunedDDD e D q fun _ => false)) q)↓ᵧ) =
          Sum.inr b := hb
      rw [prunedMove_of_fire (by rw [hrun]; exact he), hrun, if_pos hlen] at hb'
      simp at hb'
    have hf'eq : f' = q := by
      have hlenle := transcript_length_le (s := s) (e := e) f'
      omega
    rw [prunedNext_def, htranscript, hf'eq]

/-- Law form of `transcript_prunedNext_eq_properSteps`. -/
theorem transcriptDist_prunedNext_eq_fTransform_properSteps
    (S : PFunPDS X Y) {D : Set (List X)} (hdom : PFunPDS.HasFixedDomain S D)
    (e : PFunDDS.DDE X Y) (q : ℕ) :
    transcriptDist S (prunedNext e D q) q =
      Dist.fTransform properSteps (transcriptDist S e q) := by
  unfold transcriptDist
  rw [fTransform_comp']
  exact fTransform_congr_support S fun s hs =>
    transcript_prunedNext_eq_properSteps (hdom s hs) e q

/-- The unpruned law is recovered from the pruned law by the replay machine:
`pruneRun` re-inserts the deterministically rejected rounds. -/
theorem transcriptDist_eq_fTransform_pruneRun (S : PFunPDS X Y)
    {D : Set (List X)} (hdom : PFunPDS.HasFixedDomain S D) (e : PFunDDS.DDE X Y)
    (q : ℕ) :
    transcriptDist S e q =
      Dist.fTransform (fun t => (pruneRun e D q (t↓ᵧ)).1)
        (transcriptDist S (prunedNext e D q) q) := by
  rw [transcriptDist_prunedNext_eq_fTransform_properSteps S hdom e q]
  unfold transcriptDist
  rw [fTransform_comp', fTransform_comp']
  refine (fTransform_congr_support S fun s hs => ?_).symm
  show (pruneRun e D q ((properSteps (PFunDDS.transcript s e q))↓ᵧ)).1 =
    PFunDDS.transcript s e q
  have hreplay := pruneRun_properOutputs (s := s) e (hdom s hs) q []
  rw [List.append_nil] at hreplay
  rw [hreplay]

/-- **Rejection pruning for transcript distances**: on shared-domain laws,
every CR18 environment's transcript distance is attained by the pruned
environment, whose interaction is `⊥`-free.

`hT` is the signed carrier's cost: both halves are data-processing steps
(`δ_fTransform_le`), which need the law being pushed forward on the *right*
to be non-negative.  `Dist.NonNeg` suffices; nothing here uses weight. -/
theorem delta_transcriptDist_eq_delta_pruned (S T : PFunPDS X Y)
    {D : Set (List X)} (hdomS : PFunPDS.HasFixedDomain S D)
    (hdomT : PFunPDS.HasFixedDomain T D) (hT : T.NonNeg)
    (e : PFunDDS.DDE X Y) (q : ℕ) :
    δ (transcriptDist S e q) (transcriptDist T e q) =
      δ (transcriptDist S (prunedNext e D q) q)
        (transcriptDist T (prunedNext e D q) q) := by
  refine le_antisymm ?_ ?_
  · rw [transcriptDist_eq_fTransform_pruneRun S hdomS e q,
      transcriptDist_eq_fTransform_pruneRun T hdomT e q]
    exact δ_fTransform_le _ _ (transcriptDist_nonNeg hT _ _)
  · rw [transcriptDist_prunedNext_eq_fTransform_properSteps S hdomS e q,
      transcriptDist_prunedNext_eq_fTransform_properSteps T hdomT e q]
    exact δ_fTransform_le _ _ (transcriptDist_nonNeg hT _ _)

/-- The pruned environment's CR18 law is the `someMap` image of its thesis
law — the pruned interaction is a genuine thesis interaction. -/
theorem transcriptDist_prunedNext_eq_someMap_thesis (S : PFunPDS X Y)
    {D : Set (List X)} (hdom : PFunPDS.HasFixedDomain S D) (e : PFunDDS.DDE X Y)
    (q n : ℕ) :
    transcriptDist S (prunedNext e D q) n =
      Dist.fTransform someMap
        (thesisTranscriptDist S (prunedPartialDDE e D q) n) := by
  unfold transcriptDist thesisTranscriptDist
  rw [fTransform_comp']
  exact fTransform_congr_support S fun s hs =>
    (someMap_thesisTranscript_prunedPartialDDE (hdom s hs) e q n).symm

/-- **Attainment of the CR18 distance by a compatible thesis environment.**
On shared-domain laws, every CR18 environment/prefix pair is matched by the
pruned *thesis* environment with exactly the same statistical distance. -/
theorem delta_transcriptDist_eq_delta_thesis_pruned (S T : PFunPDS X Y)
    {D : Set (List X)} (hdomS : PFunPDS.HasFixedDomain S D)
    (hdomT : PFunPDS.HasFixedDomain T D) (hT : T.NonNeg)
    (e : PFunDDS.DDE X Y) (q : ℕ) :
    δ (transcriptDist S e q) (transcriptDist T e q) =
      δ (thesisTranscriptDist S (prunedPartialDDE e D q) q)
        (thesisTranscriptDist T (prunedPartialDDE e D q) q) := by
  rw [delta_transcriptDist_eq_delta_pruned S T hdomS hdomT hT e q,
    transcriptDist_prunedNext_eq_someMap_thesis S hdomS e q q,
    transcriptDist_prunedNext_eq_someMap_thesis T hdomT e q q,
    δ_fTransform_eq_of_injective someMap_injective]
  exact hT.fTransform _

/-! ## The headlines: on thesis-admissible objects the two models agree -/

/-- **Thesis Def 2.17 = CR18 equivalence on shared-domain laws.**  The
forward direction is the totalization embedding (no domain hypothesis); the
backward direction is rejection pruning: the `⊥`-totalized environments see
nothing the compatible partial environments do not. -/
theorem equivalent_iff_thesisEquivalent {S T : PFunPDS X Y}
    {D : Set (List X)} (hdomS : PFunPDS.HasFixedDomain S D)
    (hdomT : PFunPDS.HasFixedDomain T D) :
    Equivalent S T ↔ ThesisEquivalent S T := by
  constructor
  · exact thesisEquivalent_of_equivalent
  · intro h e n
    have hthesis := h (prunedPartialDDE e D n)
      (fun s hs => compatible_prunedPartialDDE (hdomS s hs) e n)
      (fun s hs => compatible_prunedPartialDDE (hdomT s hs) e n) n
    rw [transcriptDist_eq_fTransform_pruneRun S hdomS e n,
      transcriptDist_eq_fTransform_pruneRun T hdomT e n,
      transcriptDist_prunedNext_eq_someMap_thesis S hdomS e n n,
      transcriptDist_prunedNext_eq_someMap_thesis T hdomT e n n, hthesis]

/-- The defining set of `ThesisAdv` is nonempty: the nowhere-defined
environment is compatible with everything. -/
theorem thesisAdv_set_nonempty (S T : PFunPDS X Y) :
    {a : ℝ | ∃ environment : PartialDDE X Y,
      CompatibleWithLaw S environment ∧ CompatibleWithLaw T environment ∧
      ∃ n : ℕ, a = (δ (thesisTranscriptDist S environment n)
        (thesisTranscriptDist T environment n) : ℝ)}.Nonempty := by
  refine ⟨_, ⟨⟨fun _ => Part.none, fun _ _ _ h => absurd h ?_⟩,
    fun _ _ => fun _ x hx => absurd hx (Part.notMem_none x),
    fun _ _ => fun _ x hx => absurd hx (Part.notMem_none x), 0, rfl⟩⟩
  intro hcontra
  rw [PFun.mem_dom] at hcontra
  obtain ⟨x, hx⟩ := hcontra
  exact Part.notMem_none x hx

/-- The defining set of `ThesisAdv` is bounded above by the left law's
weight (thesis Def 2.4: `δ` is dominated by the first argument's weight).

On the signed carrier `δ_le_weight` needs both laws non-negative — a signed
`T` can push `δ` above `|S|` — so both hypotheses are the bound itself, not
bookkeeping.  `Dist.NonNeg` is the whole requirement; the bound is stated in
terms of `S.weight`, so no normalization is assumed. -/
theorem bddAbove_thesisAdv_set (S T : PFunPDS X Y)
    (hS : S.NonNeg) (hT : T.NonNeg) :
    BddAbove {a : ℝ | ∃ environment : PartialDDE X Y,
      CompatibleWithLaw S environment ∧ CompatibleWithLaw T environment ∧
      ∃ n : ℕ, a = (δ (thesisTranscriptDist S environment n)
        (thesisTranscriptDist T environment n) : ℝ)} := by
  refine ⟨(S.weight : ℝ), ?_⟩
  rintro a ⟨environment, -, -, n, rfl⟩
  have hδ := δ_le_weight (μ := thesisTranscriptDist S environment n)
    (ν := thesisTranscriptDist T environment n)
    (hS.fTransform _) (hT.fTransform _)
  have hweight : (thesisTranscriptDist S environment n).weight = S.weight :=
    Dist.weight_fTransform _ S
  rw [hweight] at hδ
  exact_mod_cast hδ

/-- **Thesis Def 2.26 = CR18 `Adv` on shared-domain laws.**  `≥` is the
totalization embedding; `≤` is rejection pruning: every CR18 environment's
distance is attained by a compatible thesis environment.

Both suprema are only bounded above for non-negative laws, so on the signed
carrier the identity carries `Dist.NonNeg` on each side.  That is the whole
requirement — neither supremum is normalized, so `isProbDist` would be
strictly more than the statement needs. -/
theorem adv_eq_thesisAdv {S T : PFunPDS X Y} {D : Set (List X)}
    (hdomS : PFunPDS.HasFixedDomain S D) (hdomT : PFunPDS.HasFixedDomain T D)
    (hS : S.NonNeg) (hT : T.NonNeg) :
    Adv S T = ThesisAdv S T := by
  refine le_antisymm ?_ ?_
  · -- pruning: every CR18 witness is a thesis witness
    refine csSup_le ⟨_, (fun _ => none), 0, rfl⟩ ?_
    rintro a ⟨e, n, rfl⟩
    refine le_csSup (bddAbove_thesisAdv_set S T hS hT)
      ⟨prunedPartialDDE e D n,
        fun s hs => compatible_prunedPartialDDE (hdomS s hs) e n,
        fun s hs => compatible_prunedPartialDDE (hdomT s hs) e n, n, ?_⟩
    rw [delta_transcriptDist_eq_delta_thesis_pruned S T hdomS hdomT hT e n]
  · -- embedding: every thesis witness is a CR18 witness
    refine csSup_le (thesisAdv_set_nonempty S T) ?_
    rintro a ⟨environment, compatibleLeft, compatibleRight, n, rfl⟩
    exact delta_thesisTranscriptDist_le_adv S T compatibleLeft
      compatibleRight hS hT n

/-! ## CR18 Definition 3.3, footnote 6: the worked example, kernel-checked

CR18's own regression datum for the completion `s⊥`: "if `s` is defined for
all binary input sequences but `X` also contains the symbol `2`, then
`s⊥(0,2,1,2,1) = s(0,1,1)` and `s⊥(0,2,1,2,1,2) = ⊥` because `s(0,1,1,2)` is
undefined" (CR18 p. 58, fn. 6; checked in the PDF — the `.txt` extraction is
not authoritative).  The theorems below certify that the repository's
`PFunDDS.keptPrefix`/`PFunDDS.fullyDefined` implement exactly Definition
3.3's deletion pass — no more, no less — on the source's own example.  The
witness system answers with its retained history, so the first identity also
pins the internal state to `[0, 1, 1]`: a rejected input "is not seen" and
does not advance the state, and prefix-closedness (Def 3.2) is what keeps
the retained subsequence inside the domain (`PFunDDS.keptPrefix_mem_or`). -/

namespace Footnote6

/-- CR18 fn. 6's system: defined on every nonempty binary input sequence,
over an alphabet that also contains the extra symbol `2`; it answers with
the input history it has actually retained. -/
def binaryTrace : PFunDDS.DDS (Fin 3) (List (Fin 3)) :=
  ⟨fun l => ⟨l ≠ [] ∧ ∀ x ∈ l, x ≠ 2, fun _ => l⟩, by
    refine ⟨by simp, ?_⟩
    intro l₁ l₂ hprefix hne hdom
    exact ⟨hne, fun x hx => hdom.2 x (hprefix.subset hx)⟩⟩

private theorem mem_dom_binaryTrace {l : List (Fin 3)}
    (h : l ≠ [] ∧ ∀ x ∈ l, x ≠ 2) : l ∈ PFunDDS.dom binaryTrace := h

private theorem not_mem_dom_binaryTrace {l : List (Fin 3)}
    (h : ¬ (l ≠ [] ∧ ∀ x ∈ l, x ≠ 2)) : l ∉ PFunDDS.dom binaryTrace := h

private theorem keptPrefix_binaryTrace_0 :
    PFunDDS.keptPrefix binaryTrace [0] = [0] := by
  rw [show ([0] : List (Fin 3)) = [] ++ [0] from rfl,
    PFunDDS.keptPrefix_append_singleton,
    show PFunDDS.keptPrefix binaryTrace ([] : List (Fin 3)) = [] from rfl,
    if_pos (mem_dom_binaryTrace (by decide))]

private theorem keptPrefix_binaryTrace_02 :
    PFunDDS.keptPrefix binaryTrace [0, 2] = [0] := by
  rw [show ([0, 2] : List (Fin 3)) = [0] ++ [2] from rfl,
    PFunDDS.keptPrefix_append_singleton, keptPrefix_binaryTrace_0,
    if_neg (not_mem_dom_binaryTrace (by decide))]

private theorem keptPrefix_binaryTrace_021 :
    PFunDDS.keptPrefix binaryTrace [0, 2, 1] = [0, 1] := by
  rw [show ([0, 2, 1] : List (Fin 3)) = [0, 2] ++ [1] from rfl,
    PFunDDS.keptPrefix_append_singleton, keptPrefix_binaryTrace_02,
    if_pos (mem_dom_binaryTrace (by decide))]
  rfl

private theorem keptPrefix_binaryTrace_0212 :
    PFunDDS.keptPrefix binaryTrace [0, 2, 1, 2] = [0, 1] := by
  rw [show ([0, 2, 1, 2] : List (Fin 3)) = [0, 2, 1] ++ [2] from rfl,
    PFunDDS.keptPrefix_append_singleton, keptPrefix_binaryTrace_021,
    if_neg (not_mem_dom_binaryTrace (by decide))]

private theorem keptPrefix_binaryTrace_02121 :
    PFunDDS.keptPrefix binaryTrace [0, 2, 1, 2, 1] = [0, 1, 1] := by
  rw [show ([0, 2, 1, 2, 1] : List (Fin 3)) = [0, 2, 1, 2] ++ [1] from rfl,
    PFunDDS.keptPrefix_append_singleton, keptPrefix_binaryTrace_0212,
    if_pos (mem_dom_binaryTrace (by decide))]
  rfl

/-- Reading `s⊥` one step past an arbitrary input history: the Definition
3.3 evaluation rule in closed form (the deletion pass on the earlier
history, then the candidate test). -/
private theorem output_fullyDefined_append_eval (s : PFunDDS.DDS (Fin 3) (List (Fin 3)))
    (l : List (Fin 3)) (x : Fin 3) :
    PFunDDS.output (s⊥) (l ++ [x])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      if hcand : PFunDDS.keptPrefix s l ++ [x] ∈ PFunDDS.dom s then
        some (PFunDDS.output s (PFunDDS.keptPrefix s l ++ [x]) hcand)
      else none := by
  rw [PFunDDS.output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  simp only [hdrop, hlast]

/-- CR18 fn. 6, first identity: `s⊥(0,2,1,2,1) = s(0,1,1)`.  The retained
history is exactly `[0,1,1]` — the two rejected `2`s were deleted, nothing
else was. -/
theorem output_fullyDefined_footnote6_accepts :
    PFunDDS.output (binaryTrace⊥) [0, 2, 1, 2, 1]
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      some [0, 1, 1] := by
  have h := output_fullyDefined_append_eval binaryTrace [0, 2, 1, 2] 1
  simp only [keptPrefix_binaryTrace_0212] at h
  rw [dif_pos (mem_dom_binaryTrace (by decide))] at h
  exact h

/-- CR18 fn. 6, second identity: `s⊥(0,2,1,2,1,2) = ⊥` because `s(0,1,1,2)`
is undefined. -/
theorem output_fullyDefined_footnote6_rejects :
    PFunDDS.output (binaryTrace⊥) [0, 2, 1, 2, 1, 2]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  have h := output_fullyDefined_append_eval binaryTrace [0, 2, 1, 2, 1] 2
  simp only [keptPrefix_binaryTrace_02121] at h
  rw [dif_neg (not_mem_dom_binaryTrace (by decide))] at h
  exact h

end Footnote6

end

end RandomSystems.CR18.ThesisModel
