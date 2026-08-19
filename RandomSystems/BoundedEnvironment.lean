/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Bounded environments on the CR18 surface

This module packages the exact bridge from bounded deterministic environments
to CR18 partial-function environments.  It also hosts the corresponding
law-level bounded-chooser adaptive transcript supremum, since that endpoint is
defined by embedding chooser families through `boundedDDE` and comparing them
with the full CR18 q-query-total environment supremum.

Source status:

* source-theorem bridge; candidate for upstream: a q-round total environment
  `choose_i : Y^i -> X` embeds into a CR18 `DDE X Y = List (Option Y) -> Option X`
  by answering exactly concrete output histories of length `< q` and stopping
  otherwise.  There is no default query for histories containing `⊥` or for
  histories past the budget.

Migration note: bounded choosers are a compatibility/support interface.  Public
H-technique statements should quantify over CR18 law-level environments
(`ProbPDE`) or deterministic `QQueryEnvironment`s; use this module only to
bridge old bounded-environment source theorems into that surface.
-/

noncomputable section

namespace RandomSystems
namespace CR18

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- Convert a list of optional outputs to a concrete output history, failing
exactly when some entry is `⊥`. -/
def concreteOutputHistory : List (Option Y) → Option (List Y)
  | [] => some []
  | none :: _ => none
  | some y :: ys => (concreteOutputHistory ys).map (fun zs => y :: zs)

@[simp]
theorem concreteOutputHistory_map_some (ys : List Y) :
    concreteOutputHistory (ys.map some) = some ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp [concreteOutputHistory, ih]

/-- **Source-theorem bridge; candidate for upstream.** Embed a bounded
deterministic environment into CR18's partial environment type.

The embedded environment only answers concrete histories of length `< q`; it
stops on histories containing `⊥` and after the q-query budget. -/
def boundedDDE
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    PFunDDS.DDE X Y :=
  fun ys =>
    match concreteOutputHistory ys with
    | none => none
    | some concrete =>
        if h : concrete.length < q then
          some (choose ⟨concrete.length, h⟩ (fun j => concrete.get j))
        else
          none

/-- The bounded environment answers concrete histories before the query budget
with exactly the bounded chooser's next query. -/
@[simp]
theorem boundedDDE_apply_map_some_of_lt
    (choose : (i : Fin q) → (Fin i.1 → Y) → X)
    (ys : List Y) (hlen : ys.length < q) :
    boundedDDE choose (ys.map some) =
      some (choose ⟨ys.length, hlen⟩ (fun j => ys.get j)) := by
  simp [boundedDDE, hlen]

/-- **Support lemma forced by formalization; candidate for upstream.** Same as
`boundedDDE_apply_map_some_of_lt`, but with the history length identified with
an existing bounded index.  This avoids dependent-cast noise in transcript
bridges. -/
theorem boundedDDE_apply_map_some_of_length_eq
    (choose : (i : Fin q) → (Fin i.1 → Y) → X)
    (ys : List Y) (i : Fin q) (hlen_eq : ys.length = i.1) :
    boundedDDE choose (ys.map some) =
      some (choose i (fun j => ys.get ⟨j.1, by rw [hlen_eq]; exact j.2⟩)) := by
  have hlen : ys.length < q := by
    rw [hlen_eq]
    exact i.2
  rw [boundedDDE_apply_map_some_of_lt _ _ hlen]
  cases i with
  | mk n hn =>
      dsimp at hlen_eq hlen ⊢
      cases hlen_eq
      rfl

/-- **Source-theorem bridge; candidate for upstream.** A bounded deterministic
environment as a deterministic CR18 PDE random variable over the unit
experiment. -/
def boundedEnvironment
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    PFunPDE.RV PUnit X Y :=
  fun _ => boundedDDE choose

/-- **Source-theorem bridge; candidate for upstream.** The CR18 environment
obtained from a q-round bounded chooser is q-query-total. -/
theorem boundedEnvironment_KQueryTotal
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    PFunPDE.RV.KQueryTotal
      (boundedEnvironment choose) q := by
  intro _ ys hlen
  refine ⟨choose ⟨ys.length, hlen⟩ (fun j => ys.get j), ?_⟩
  simp [boundedEnvironment, boundedDDE_apply_map_some_of_lt, hlen]

/-- **Support lemma forced by formalization; candidate for upstream.** A bounded
chooser supplies the nonempty environment subtype needed by transcript-law
adaptive supremums. -/
theorem boundedEnvironment_subtype_nonempty
    (choose : (i : Fin q) → (Fin i.1 → Y) → X) :
    Nonempty
      {E : PFunPDE.RV PUnit X Y //
        PFunPDE.RV.KQueryTotal E q} :=
  ⟨⟨boundedEnvironment choose, boundedEnvironment_KQueryTotal choose⟩⟩

namespace PFunPDS
namespace Prob

/-- **Source-theorem bridge; candidate for upstream.** Law-level bounded-chooser
adaptive transcript advantage: the supremum restricted to deterministic
q-round choosers `choose_i : Y^i -> X`, embedded exactly as CR18 partial
environments by `RandomSystems.CR18.boundedDDE`.

This is the law-level counterpart of the old bounded `advantageAdaptive` index
set.  It takes only the two PDS laws; representatives and sample spaces are
construction details of compatibility adapters. -/
noncomputable def boundedAdaptiveTranscriptAdvantage {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) : ℝ :=
  sSup ((fun choose : (i : Fin q) → (Fin i.1 → Y) → X =>
      (RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) S
          (boundedDDE choose))
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) T
          (boundedDDE choose)) : ℝ)) ''
    Set.univ)

/-- **Support lemma forced by formalization; candidate for upstream.** The image
defining the law-level bounded-chooser adaptive transcript advantage is bounded
above by `1`. -/
theorem boundedAdaptiveTranscriptAdvantage_image_bddAbove {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    BddAbove ((fun choose : (i : Fin q) → (Fin i.1 → Y) → X =>
      (RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) S
          (boundedDDE choose))
        (PFunPDS.Prob.deterministicTranscriptDist (q := q) T
          (boundedDDE choose)) : ℝ)) ''
      Set.univ) := by
  refine ⟨1, ?_⟩
  rintro x ⟨choose, _hchoose, rfl⟩
  have hstat : RandomSystems.statDist
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S
        (boundedDDE choose))
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) T
        (boundedDDE choose)) ≤
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S
        (boundedDDE choose)).weight :=
    RandomSystems.statDist_le_weight
      (PFunPDE.deterministicTranscriptLawDist_nonNeg S _)
      (PFunPDE.deterministicTranscriptLawDist_nonNeg T _)
  have hweight :
      (PFunPDS.Prob.deterministicTranscriptDist (q := q) S
        (boundedDDE choose)).weight ≤ 1 := by
    rw [← PFunPDS.Prob.transcriptDist_ofDDE (q := q) S (boundedDDE choose)]
    exact PFunPDS.Prob.transcriptDist_weight_le_one
      (q := q) S (PFunPDE.Prob.ofDDE (boundedDDE choose))
  exact_mod_cast le_trans hstat hweight

/-- **Support lemma forced by formalization; candidate for upstream.** The
law-level bounded-chooser transcript advantage is nonnegative, including the
empty chooser-index case where the supremum is Mathlib's `sSup ∅ = 0`. -/
theorem boundedAdaptiveTranscriptAdvantage_nonneg {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    0 ≤ boundedAdaptiveTranscriptAdvantage (q := q) S T := by
  unfold boundedAdaptiveTranscriptAdvantage
  exact RandomSystems.sSup_image_univ_nonneg_of_forall _
    (boundedAdaptiveTranscriptAdvantage_image_bddAbove S T) (by
      intro choose
      exact statDist_nonneg _ _)

/-- **Source-theorem bridge; candidate for upstream.** The bounded-chooser
supremum is a sub-supremum of the full law-level CR18 q-query-total environment
supremum. -/
theorem boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    boundedAdaptiveTranscriptAdvantage (q := q) S T ≤
      PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T := by
  unfold boundedAdaptiveTranscriptAdvantage PFunPDS.Prob.adaptiveTranscriptAdvantage
  refine RandomSystems.sSup_image_univ_le_sSup_image_univ_of_forall_exists _ _
    (PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove (q := q) S T) ?nonneg ?map
  · intro E
    exact statDist_nonneg _ _
  · intro choose
    let k : PFunPDE.QQueryEnvironment X Y q :=
      ⟨boundedDDE choose, by
        intro ys hlen
        refine ⟨choose ⟨ys.length, hlen⟩ (fun j => ys.get j), ?_⟩
        exact boundedDDE_apply_map_some_of_lt (q := q) choose ys hlen⟩
    refine ⟨k, ?_⟩
    simp [k]

end Prob
end PFunPDS

end CR18
end RandomSystems
