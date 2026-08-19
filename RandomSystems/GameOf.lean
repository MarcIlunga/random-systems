/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SystemMBO
import RandomSystems.CR18TacticsCore
import RandomSystems.Theorem417
import RandomSystems.BlindAbsorption
import RandomSystems.DistSimp
import RandomSystems.StrictContext

/-!
# CR18 §4.11.1 — the game-enhancement constructor `gameOf` (UPSTREAM-CANDIDATE)

CR18 Theorem 4.17 starts from a base `(X,Y)`-system `S` for which *one can define an MBO* `A₀,A₁,…`,
**resulting** in a game `Ŝ` characterized by `pŜ_{YⁱAᵢ|Xⁱ}` with `Ŝ⁻ = S` (CR18_LN.txt:5600,5624-5633).
The MBO is "defined (for any system)" purely from the visible transcript — e.g. Example 4.15
(CR18_LN.txt:5585-5589): "`Aᵢ = 0` iff for any two distinct inputs the corresponding two outputs are
distinct", a *monotone* condition on the input/output transcript.

This file supplies exactly that missing constructor. `gameEnhance` (in `Theorem417.lean`) only *copies*
an already-existing MBO from a second system; it cannot enhance a plain `S : PFunPDS X Y` with a fresh
transcript-predicate. `gameOf S cond` does: it attaches to each realization `s ← S` the MBO bit
`cond (transcript)`, producing `Ŝ : PFunPDS X (Y × Bool)`.

The two standing facts the Theorem-4.17 chain needs are then *proved*, not assumed:

* `ignoreMBO_gameOf : (gameOf S cond)⁻ᴹ = S`  — CR18 eq. `Ŝ⁻ = S` (CR18_LN.txt:5628).
* `monotoneMBO_gameOf : MonotoneMBO (gameOf S cond)` from `cond` monotone — CR18 Def 3.22/4.16: the
  bit `Aᵢ` is monotone (once `1`, stays `1`), which here is exactly prefix-monotonicity of `cond`.

This is the keystone (root cause of MODELING_REVIEW findings #1–#6, #11): every free-`Ŝ` scaffold was
dodging this construction.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open Classical
open scoped RandomSystems.CR18.CondEquiv
open scoped RandomSystems.CR18

universe u v

variable {X : Type u} {Y : Type v}

/-- Scanning a list while accepting exactly those next elements that keep the accumulated length at
most `q` returns `l.take q`.

UPSTREAM-CANDIDATE: list-level core of the `[q]`/`fullyDefined` kept-prefix API. -/
theorem foldl_keepUntil_length_eq_take {X : Type*} (q : ℕ) (l : List X) :
    List.foldl (fun acc x => if (acc ++ [x]).length ≤ q then acc ++ [x] else acc) [] l
      = l.take q := by
  classical
  let step : List X → X → List X := fun acc x =>
    if (acc ++ [x]).length ≤ q then acc ++ [x] else acc
  have haux : ∀ (xs acc : List X), acc.length ≤ q →
      List.foldl step acc xs = acc ++ xs.take (q - acc.length) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simp [step]
    | cons x xs ih =>
        intro acc hacc
        by_cases hlt : acc.length < q
        · have hstep : step acc x = acc ++ [x] := by
            unfold step
            rw [if_pos]
            simp
            omega
          simp only [List.foldl_cons]
          rw [hstep]
          rw [ih (acc ++ [x])]
          · simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
            rw [List.append_assoc]
            cases hn : q - acc.length with
            | zero => omega
            | succ n =>
                have hsub : q - (acc.length + 1) = n := by omega
                simp [hsub]
          · simp
            omega
        · have hstep : step acc x = acc := by
            unfold step
            rw [if_neg]
            simp
            omega
          have hlen : acc.length = q := by omega
          simp only [List.foldl_cons]
          rw [hstep]
          rw [ih acc hacc]
          simp [hlen]
  simpa [step] using haux l [] (Nat.zero_le q)

namespace PFunDDS

/-- `keptPrefix` depends only on the domain of the DDS, not on its output type or output function.

UPSTREAM-CANDIDATE: domain-congruence API for `keptPrefix`. -/
theorem keptPrefix_eq_of_dom_iff {X Y Z : Type*} (S : DDS X Y) (T : DDS X Z)
    (hdom : ∀ l : List X, l ∈ dom S ↔ l ∈ dom T) (l : List X) :
    keptPrefix S l = keptPrefix T l := by
  classical
  unfold keptPrefix
  let stepS : List X → X → List X := fun acc x =>
    if acc ++ [x] ∈ dom S then acc ++ [x] else acc
  let stepT : List X → X → List X := fun acc x =>
    if acc ++ [x] ∈ dom T then acc ++ [x] else acc
  have hfold : ∀ (xs acc : List X), List.foldl stepS acc xs = List.foldl stepT acc xs := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons x xs ih =>
        intro acc
        have hstep : stepS acc x = stepT acc x := by
          unfold stepS stepT
          by_cases hS : acc ++ [x] ∈ dom S
          · rw [if_pos hS, if_pos ((hdom (acc ++ [x])).mp hS)]
          · rw [if_neg hS, if_neg]
            intro hT
            exact hS ((hdom (acc ++ [x])).mpr hT)
        simp only [List.foldl_cons]
        rw [hstep]
        exact ih _
  exact hfold l []

/-- For any DDS total on nonempty input histories, the `[q]` filter makes the fully-defined completion
keep exactly the first `q` raw queries.

UPSTREAM-CANDIDATE: `[q]`/`fullyDefined` API lemma. -/
theorem keptPrefix_filterQueries_eq_take_of_total {X Y : Type*} (S : DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ dom S) (l : List X) :
    keptPrefix (filterQueries q S) l = l.take q := by
  classical
  unfold keptPrefix
  let stepD : List X → X → List X := fun acc x =>
    if acc ++ [x] ∈ dom (filterQueries q S) then acc ++ [x] else acc
  let stepQ : List X → X → List X := fun acc x =>
    if (acc ++ [x]).length ≤ q then acc ++ [x] else acc
  have hfold : List.foldl stepD [] l = List.foldl stepQ [] l := by
    have hgen : ∀ (xs acc : List X), List.foldl stepD acc xs = List.foldl stepQ acc xs := by
      intro xs
      induction xs with
      | nil =>
          intro acc
          rfl
      | cons x xs ih =>
          intro acc
          have hiff : acc ++ [x] ∈ dom (filterQueries q S) ↔ (acc ++ [x]).length ≤ q := by
            rw [mem_dom_filterQueries]
            constructor
            · intro h
              exact h.2
            · intro hlen
              exact ⟨hS (acc ++ [x]) (by simp), hlen⟩
          have hstep : stepD acc x = stepQ acc x := by
            unfold stepD stepQ
            by_cases hlen : (acc ++ [x]).length ≤ q
            · rw [if_pos ((hiff).mpr hlen), if_pos hlen]
            · rw [if_neg, if_neg hlen]
              intro hdom
              exact hlen ((hiff).mp hdom)
          simp only [List.foldl_cons]
          rw [hstep]
          exact ih _
    exact hgen l []
  rw [hfold]
  exact foldl_keepUntil_length_eq_take q l

/-- A `[q]`-filtered function evaluator keeps exactly the first `q` raw queries.

UPSTREAM-CANDIDATE: zero-hypothesis specialization of the generic `[q]` kept-prefix normalizer for
stateless function evaluators. -/
theorem keptPrefix_filterQueries_functionEvaluator {X Y : Type*} (q : ℕ) (f : X → Y)
    (l : List X) :
    keptPrefix (filterQueries q (functionEvaluator f)) l = l.take q := by
  exact keptPrefix_filterQueries_eq_take_of_total (functionEvaluator f) q
    (fun xs hxs => by
      rw [dom_functionEvaluator]
      exact hxs) l

/-- A total system filtered to `[q]` returns `⊥` once the kept prefix already has length at least `q`.

UPSTREAM-CANDIDATE: post-budget output normalization for `[q]` and `fullyDefined`. -/
theorem output_fullyDefined_filterQueries_of_total_ge {X Y : Type*} (S : DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ dom S) (l : List X) (x : X)
    (hle : q ≤ l.length) (hdom : l ++ [x] ∈ dom (filterQueries q S)⊥) :
    output (filterQueries q S)⊥ (l ++ [x]) hdom = none := by
  rw [output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  rw [hdrop, hlast, keptPrefix_filterQueries_eq_take_of_total S q hS l]
  rw [dif_neg]
  intro hcand
  rw [mem_dom_filterQueries] at hcand
  have htake : (l.take q).length = q := by simp [List.length_take, hle]
  have hcandlen : (l.take q ++ [x]).length = q + 1 := by simp [htake]
  omega

/-- A total system filtered to `[q]` agrees with the original system before the budget is exhausted.

UPSTREAM-CANDIDATE: pre-budget output normalization for `[q]` and `fullyDefined`. -/
theorem output_fullyDefined_filterQueries_of_total_lt {X Y : Type*} (S : DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ dom S) (l : List X) (x : X)
    (hlt : l.length < q) (hdom : l ++ [x] ∈ dom (filterQueries q S)⊥) :
    output (filterQueries q S)⊥ (l ++ [x]) hdom =
      some (output S (l ++ [x]) (hS (l ++ [x]) (by simp))) := by
  rw [output_fullyDefined]
  have hdrop : (l ++ [x]).dropLast = l := by simp
  have hlast : (l ++ [x]).getLast (by simp) = x := by simp
  have htake : l.take q = l := List.take_of_length_le (Nat.le_of_lt hlt)
  have hdom : l ++ [x] ∈ dom (filterQueries q S) := by
    rw [mem_dom_filterQueries]
    exact ⟨hS (l ++ [x]) (by simp), by simp; omega⟩
  rw [hdrop, hlast, keptPrefix_filterQueries_eq_take_of_total S q hS l, htake,
    dif_pos hdom, output_filterQueries]

/-- **Deterministic game-enhancement (CR18 §4.11.1)**: enhance a deterministic `(X,Y)`-system `s` with
the transcript-predicate `cond` to a `(X,Y × Bool)`-game. The domain is unchanged; on an in-domain `l`
the output is `(output s l, cond (ioTranscript s l))` — `s`'s answer paired with the MBO bit read off
the visible transcript.

**Thesis reconciliation (Def. 2.20).** Lanzenberger's thesis presents an MC for a fixed DDS `s` as an
input-history predicate `A_s : X* → {0,1}`. This constructor is the CR18/RandomSystems way to generate that
per-realization predicate from a uniform transcript predicate: `A_s(l) = cond (ioTranscript s l)`. This
keeps output-dependent events such as collisions tight without making the winner observe the MBO bit. -/
def gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) : DDS X (Y × Bool) :=
  ⟨fun l => ⟨(s.1 l).Dom, fun h => ((s.1 l).get h, cond (ioTranscript s l h))⟩, by
    refine ⟨fun h => empty_not_mem s h, fun hpre hne hdom => prefix_closed s hpre hne hdom⟩⟩

@[simp] theorem dom_gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) :
    dom (gameOfDDS cond s) = dom s := rfl

/-- Adding a transcript-defined MBO does not change the prefix retained by the fully-defined
completion: `keptPrefix` only scans the input domain, and `gameOfDDS` preserves that domain.

UPSTREAM-CANDIDATE: generic `keptPrefix` invariance under MBO enhancement. -/
theorem keptPrefix_gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) (l : List X) :
    keptPrefix (gameOfDDS cond s) l = keptPrefix s l :=
  keptPrefix_eq_of_dom_iff _ _ (fun xs => by rw [dom_gameOfDDS]) l

/-- Combining `gameOfDDS` domain invariance with the `[q]` filter: a total base system enhanced
with any transcript-defined MBO keeps exactly the first `q` raw queries under `fullyDefined`.

UPSTREAM-CANDIDATE: generic `[q]`/MBO/`fullyDefined` kept-prefix normalizer. -/
theorem keptPrefix_gameOfDDS_filterQueries_eq_take_of_total
    (cond : List (X × Y) → Bool) (S : DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ dom S) (l : List X) :
    keptPrefix (gameOfDDS cond (filterQueries q S)) l = l.take q := by
  rw [keptPrefix_gameOfDDS, keptPrefix_filterQueries_eq_take_of_total S q hS l]

theorem output_gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) (l : List X)
    (h : l ∈ dom (gameOfDDS cond s)) (h' : l ∈ dom s) :
    output (gameOfDDS cond s) l h
      = (output s l h', cond (ioTranscript s l h')) := rfl

/-- **The MBO bit of `gameOfDDS` along a history** is `cond` of the transcript prefix. -/
theorem outputBit_gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) (l : List X)
    (h : l ∈ dom (gameOfDDS cond s)) (h' : l ∈ dom s) :
    (output (gameOfDDS cond s) l h).2 = cond (ioTranscript s l h') := by
  rw [output_gameOfDDS cond s l h h']

/-- **`Ŝ⁻ = S` at the deterministic layer** (CR18 eq. `Ŝ⁻ = S`, CR18_LN.txt:5628): stripping the MBO
from `gameOfDDS cond s` recovers `s` — the `Y`-component of the enhanced output is `s`'s output. -/
@[simp] theorem ignoreMBO_gameOfDDS (cond : List (X × Y) → Bool) (s : DDS X Y) :
    ignoreMBO (gameOfDDS cond s) = s := by
  apply Subtype.ext
  funext l
  show ((gameOfDDS cond s).1 l).map Prod.fst = s.1 l
  apply Part.ext'
  · rfl
  · intro h₁ h₂; rfl

/-- **`cond` is a monotone transcript-predicate** (CR18 Def 3.22 / Def 4.16: the MBO is monotone,
"`Aᵢ = 1 ⟹ Aⱼ = 1` for `j ≥ i`"): if `t₁` is a prefix of `t₂` and `cond t₁` already fired, so does
`cond t₂`. Example 4.15's input/output-collision condition is monotone in exactly this sense. -/
def MonotoneCond (cond : List (X × Y) → Bool) : Prop :=
  ∀ {t₁ t₂ : List (X × Y)}, t₁ <+: t₂ → cond t₁ ≤ cond t₂

end PFunDDS

open PFunDDS

/-- If the environment fires at round `n`, the transcript has not stalled earlier, hence its prefix
has exact length `n`.

UPSTREAM-CANDIDATE: generic transcript/stall API for CR18 Def. 3.7. -/
theorem PFunDDS.transcript_length_eq_of_fire {X Y : Type*} (s : PFunDDS.DDS X Y)
    (e : PFunDDS.DDE X Y) :
    ∀ {n : ℕ} {x : X}, e (PFunDDS.transcript s e n)↓ᵧ = some x →
      (PFunDDS.transcript s e n).length = n := by
  intro n
  induction n with
  | zero =>
      intro x hfire
      simp
  | succ n ih =>
      intro x hfire
      rcases hprev : e (PFunDDS.transcript s e n)↓ᵧ with _ | y
      · rw [transcript_succ_stall hprev] at hfire
        rw [hprev] at hfire
        cases hfire
      · rw [transcript_succ_fire hprev]
        simp [ih hprev]

/-- In a run against `[q]S`, once the clock has reached `q`, every further system reply is `⊥`.
The transcript output suffix after round `q` is therefore a list of `none`s.

UPSTREAM-CANDIDATE: generic post-budget transcript-tail API for `[q]` filters. -/
theorem PFunDDS.transcript_outputs_filterQueries_tail_of_total {X Y : Type*}
    (S : PFunDDS.DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom S) (e : PFunDDS.DDE X Y) :
    ∀ {n : ℕ}, q ≤ n →
      ∃ k : ℕ,
        (PFunDDS.transcript (PFunDDS.filterQueries q S) e n)↓ᵧ =
          (PFunDDS.transcript (PFunDDS.filterQueries q S) e q)↓ᵧ ++
            List.replicate k (none : Option Y) := by
  intro n
  induction n with
  | zero =>
      intro hq
      obtain rfl : q = 0 := Nat.le_zero.mp hq
      exact ⟨0, by simp⟩
  | succ n ih =>
      intro hq
      by_cases hqn : q ≤ n
      · obtain ⟨k, hk⟩ := ih hqn
        rcases hfire : e (PFunDDS.transcript (PFunDDS.filterQueries q S) e n)↓ᵧ with _ | x
        · refine ⟨k, ?_⟩
          rw [transcript_succ_stall hfire]
          exact hk
        · refine ⟨k + 1, ?_⟩
          have hlen : (PFunDDS.transcript (PFunDDS.filterQueries q S) e n).length = n :=
            PFunDDS.transcript_length_eq_of_fire (PFunDDS.filterQueries q S) e hfire
          have hout :
              PFunDDS.output (PFunDDS.filterQueries q S)⊥
                ((PFunDDS.transcript (PFunDDS.filterQueries q S) e n)↓ₓ ++ [x])
                (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) = none := by
            exact PFunDDS.output_fullyDefined_filterQueries_of_total_ge S q hS
              (PFunDDS.transcript (PFunDDS.filterQueries q S) e n)↓ₓ x
              (by rw [transcriptInputs_length, hlen]; exact hqn) _
          have hrep : List.replicate k (none : Option Y) ++ [none] =
              List.replicate (k + 1) (none : Option Y) := by
            simpa using (List.replicate_add k 1 (none : Option Y)).symm
          rw [transcript_succ_fire hfire, transcriptOutputs_append, hout, hk]
          rw [List.append_assoc, hrep]
      · obtain rfl : q = n + 1 := by omega
        exact ⟨0, by simp⟩

/-- If a distinguisher keeps querying along the synthetic `⊥` tail after round `q`, then the actual
run against `[q]S` reaches that same tail.

UPSTREAM-CANDIDATE: post-budget tail reachability for CR18 §4.10.1 padding. -/
theorem PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total {X Y : Type*}
    (S : PFunDDS.DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom S) (d : PFunDDS.DDD X Y) :
    ∀ k : ℕ,
      (∀ j : ℕ, j < k →
        ∃ x : X,
          d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
            List.replicate j (none : Option Y)) = Sum.inl x) →
      (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ᵧ =
        (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
          List.replicate k (none : Option Y) := by
  intro k
  induction k with
  | zero =>
      intro _hall
      simp
  | succ k ih =>
      intro hall
      have hprev :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ᵧ =
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
              List.replicate k (none : Option Y) := by
        exact ih (fun j hj => hall j (by omega))
      obtain ⟨x, hx⟩ := hall k (by omega)
      have hfire :
          PFunDDS.ddToDDE d
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ᵧ =
            some x := by
        change (match d.val
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ᵧ with
          | Sum.inl y => some y
          | Sum.inr _ => none) = some x
        rw [hprev, hx]
      have hlen :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k)).length =
            q + k :=
        PFunDDS.transcript_length_eq_of_fire (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) hfire
      have hout :
          PFunDDS.output (PFunDDS.filterQueries q S)⊥
            ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ₓ ++ [x])
            (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) = none := by
        exact PFunDDS.output_fullyDefined_filterQueries_of_total_ge S q hS
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) (q + k))↓ₓ x
          (by rw [transcriptInputs_length, hlen]; omega) _
      have hrep : List.replicate k (none : Option Y) ++ [none] =
          List.replicate (k + 1) (none : Option Y) := by
        simpa using (List.replicate_add k 1 (none : Option Y)).symm
      rw [show q + (k + 1) = q + k + 1 by omega]
      rw [transcript_succ_fire hfire, transcriptOutputs_append, hout, hprev]
      rw [List.append_assoc, hrep]

/-- A raw distinguisher's verdict against `[q]S` is equivalent to its eventual verdict on the actual
round-`q` reply prefix followed by a synthetic `⊥` tail.

UPSTREAM-CANDIDATE: deterministic filtered-verdict normalization for CR18 §4.10.1 padding. -/
theorem PFunDDS.verdict_filterQueries_iff_tail_of_total {X Y : Type*}
    (S : PFunDDS.DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom S) (d : PFunDDS.DDD X Y) :
    PFunDDS.verdict d (PFunDDS.filterQueries q S) ↔
      ∃ k : ℕ,
        d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
          List.replicate k (none : Option Y)) = Sum.inr true := by
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := hv
    by_cases hqn : q ≤ n
    · obtain ⟨k, hk⟩ :=
        PFunDDS.transcript_outputs_filterQueries_tail_of_total S q hS (PFunDDS.ddToDDE d) hqn
      exact ⟨k, by rwa [← hk]⟩
    · have hnq : n < q := Nat.lt_of_not_ge hqn
      have hstop : PFunDDS.ddToDDE d
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n)↓ᵧ = none := by
        change (match d.val
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n)↓ᵧ with
          | Sum.inl y => some y
          | Sum.inr _ => none) = none
        rw [hn]
      have hfreeze : PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q =
          PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n :=
        transcript_freeze hstop (Nat.le_of_lt hnq)
      exact ⟨0, by rw [hfreeze]; simpa using hn⟩
  · rintro ⟨k, hk⟩
    revert hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases hall : ∀ j : ℕ, j < k →
            ∃ x : X,
              d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                List.replicate j (none : Option Y)) = Sum.inl x
        · have htrace :=
            PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total S q hS d k hall
          exact ⟨q + k, by rwa [htrace]⟩
        · have hbad : ∃ j : ℕ, j < k ∧
              ¬ ∃ x : X,
                d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                  List.replicate j (none : Option Y)) = Sum.inl x := by
            by_contra hnone
            apply hall
            intro j hj
            by_contra hnot
            exact hnone ⟨j, hj, hnot⟩
          obtain ⟨j, hjk, hnotQuery⟩ := hbad
          cases hdj : d.val
              ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                List.replicate j (none : Option Y)) with
          | inl x =>
              exact False.elim (hnotQuery ⟨x, hdj⟩)
          | inr b =>
              have hpre :
                  ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                    List.replicate j (none : Option Y)) <+:
                  ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                    List.replicate k (none : Option Y)) := by
                refine ⟨List.replicate (k - j) (none : Option Y), ?_⟩
                rw [List.append_assoc]
                congr 1
                have hle : j ≤ k := Nat.le_of_lt hjk
                have hrep := (List.replicate_add j (k - j) (none : Option Y)).symm
                simp [Nat.add_sub_of_le hle] at hrep ⊢
              have hfinal := d.property hpre b hdj
              rw [hfinal] at hk
              cases hk
              exact ih j hjk (by simpa using hdj)

/-- Pad a raw distinguisher to make exactly `q` queries against a `[q]`-filtered system.

Before the `q`-th reply, it follows the original distinguisher while the original is still querying;
if the original has already stopped, it issues the fixed dummy query. At length `q`, it stops and uses
the verdict the original distinguisher would eventually emit after the filtered system keeps returning
`none` replies. If the original never emits `true` on that post-filter tail, the padded verdict is
`false`.

This is the deterministic core of CR18 §4.10.1 padding/WLOG for the current raw `DDD` API. The dummy
query is an explicit parameter: exact positive-query padding is impossible without some input value. -/
noncomputable def PFunDDS.padDDD (dummy : X) (q : ℕ) (d : PFunDDS.DDD X Y) :
    PFunDDS.DDD X Y := by
  classical
  refine ⟨fun h =>
    if hlt : h.length < q then
      match d.val h with
      | Sum.inl x => Sum.inl x
      | Sum.inr _ => Sum.inl dummy
    else
      Sum.inr (decide (∃ n : ℕ,
        d.val (h.take q ++ List.replicate n (none : Option Y)) = Sum.inr true)), ?_⟩
  intro h h' hpre b hstop
  by_cases hlt : h.length < q
  · simp only [hlt, dite_true] at hstop
    cases hd : d.val h with
    | inl x => simp [hd] at hstop
    | inr b' => simp [hd] at hstop
  · have hge : q ≤ h.length := le_of_not_gt hlt
    have hge' : q ≤ h'.length := le_trans hge hpre.length_le
    have hlt' : ¬ h'.length < q := not_lt.mpr hge'
    have htake : h'.take q = h.take q := by
      rcases hpre with ⟨t, rfl⟩
      simpa using (List.take_append_of_le_length (l₂ := t) hge)
    simp only [hlt, hlt', dite_false, Sum.inr.injEq] at hstop ⊢
    rw [htake]
    exact hstop

@[simp] theorem PFunDDS.ddToDDE_padDDD_of_lt (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hlt : h.length < q) :
    (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) h =
      match d.val h with
      | Sum.inl x => some x
      | Sum.inr _ => some dummy := by
  unfold PFunDDS.ddToDDE PFunDDS.padDDD
  simp only [hlt, dite_true]
  cases d.val h <;> rfl

@[simp] theorem PFunDDS.padDDD_val_of_lt (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hlt : h.length < q) :
    (PFunDDS.padDDD dummy q d).val h =
      match d.val h with
      | Sum.inl x => Sum.inl x
      | Sum.inr _ => Sum.inl dummy := by
  simp [PFunDDS.padDDD, hlt]

@[simp] theorem PFunDDS.ddToDDE_padDDD_of_ge (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hle : q ≤ h.length) :
    (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) h = none := by
  unfold PFunDDS.ddToDDE PFunDDS.padDDD
  simp [not_lt.mpr hle]

/-- Once the padded distinguisher has seen at least `q` replies, its verdict is the original
distinguisher's eventual verdict on the post-filter `none` tail. -/
theorem PFunDDS.padDDD_val_of_ge (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hle : q ≤ h.length) :
    (PFunDDS.padDDD dummy q d).val h =
      Sum.inr (decide (∃ n : ℕ,
        d.val (h.take q ++ List.replicate n (none : Option Y)) = Sum.inr true)) := by
  classical
  unfold PFunDDS.padDDD
  simp [not_lt.mpr hle]

/-- The padded distinguisher returns verdict `true` after budget `q` exactly when the original
distinguisher eventually returns `true` after the first `q` replies followed by `none`s. -/
theorem PFunDDS.padDDD_true_iff_of_ge (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hle : q ≤ h.length) :
    (PFunDDS.padDDD dummy q d).val h = Sum.inr true ↔
      ∃ n : ℕ, d.val (h.take q ++ List.replicate n (none : Option Y)) = Sum.inr true := by
  classical
  rw [PFunDDS.padDDD_val_of_ge dummy q d hle]
  by_cases htail : ∃ n : ℕ,
      d.val (h.take q ++ List.replicate n (none : Option Y)) = Sum.inr true
  · simp [htail]
  · simp [htail]

/-- Length-exact spelling of `padDDD_true_iff_of_ge`, used when the padded run has just completed its
`q` queries. -/
theorem PFunDDS.padDDD_true_iff_of_length_eq (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) {h : List (Option Y)} (hlen : h.length = q) :
    (PFunDDS.padDDD dummy q d).val h = Sum.inr true ↔
      ∃ n : ℕ, d.val (h ++ List.replicate n (none : Option Y)) = Sum.inr true := by
  rw [PFunDDS.padDDD_true_iff_of_ge dummy q d (by omega)]
  rw [List.take_of_length_le (by omega)]

/-- The padded distinguisher makes exactly `q` queries. -/
theorem queriesExactly_ddToDDE_padDDD (dummy : X) (q : ℕ) (d : PFunDDS.DDD X Y) :
    QueriesExactly (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q := by
  constructor
  · intro h hlt
    rw [PFunDDS.ddToDDE_padDDD_of_lt dummy q d hlt]
    cases d.val h <;> simp
  · intro h hle
    exact PFunDDS.ddToDDE_padDDD_of_ge dummy q d hle

/-- A padded distinguisher's verdict is exactly the original distinguisher's eventual verdict after
the padded run's first `q` replies, followed by post-budget `⊥` replies.

UPSTREAM-CANDIDATE: generic verdict characterization for CR18 §4.10.1 padding. -/
theorem PFunDDS.verdict_padDDD_iff_tail (dummy : X) (q : ℕ)
    (d : PFunDDS.DDD X Y) (s : PFunDDS.DDS X Y) :
    PFunDDS.verdict (PFunDDS.padDDD dummy q d) s ↔
      ∃ n : ℕ,
        d.val ((PFunDDS.transcript s (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ ++
          List.replicate n (none : Option Y)) = Sum.inr true := by
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := hv
    let p : PFunDDS.DDD X Y := PFunDDS.padDDD dummy q d
    have hQ : QueriesExactly (PFunDDS.ddToDDE p) q := queriesExactly_ddToDDE_padDDD dummy q d
    have hlenq : ((PFunDDS.transcript s (PFunDDS.ddToDDE p) q)↓ᵧ).length = q := by
      rw [transcriptOutputs_length]
      exact transcript_length_eq hQ.1 (le_refl q)
    have hstop : PFunDDS.ddToDDE p ((PFunDDS.transcript s (PFunDDS.ddToDDE p) q)↓ᵧ) = none :=
      hQ.2 _ (by rw [hlenq])
    by_cases hnq : q ≤ n
    · have hfreeze : PFunDDS.transcript s (PFunDDS.ddToDDE p) n =
          PFunDDS.transcript s (PFunDDS.ddToDDE p) q :=
        transcript_freeze hstop hnq
      have hptrue : p.val ((PFunDDS.transcript s (PFunDDS.ddToDDE p) q)↓ᵧ) = Sum.inr true := by
        simpa [p, hfreeze] using hn
      exact (PFunDDS.padDDD_true_iff_of_length_eq dummy q d hlenq).mp hptrue
    · have hlt : n < q := Nat.lt_of_not_ge hnq
      have hlenn : (PFunDDS.transcript s (PFunDDS.ddToDDE p) n).length = n :=
        transcript_length_eq hQ.1 (Nat.le_of_lt hlt)
      have hlenout : ((PFunDDS.transcript s (PFunDDS.ddToDDE p) n)↓ᵧ).length < q := by
        rw [transcriptOutputs_length, hlenn]
        exact hlt
      rw [PFunDDS.padDDD_val_of_lt dummy q d hlenout] at hn
      cases hd : d.val ((PFunDDS.transcript s (PFunDDS.ddToDDE p) n)↓ᵧ) <;> rw [hd] at hn <;>
        cases hn
  · intro htail
    refine ⟨q, ?_⟩
    let p : PFunDDS.DDD X Y := PFunDDS.padDDD dummy q d
    have hQ : QueriesExactly (PFunDDS.ddToDDE p) q := queriesExactly_ddToDDE_padDDD dummy q d
    have hlenq : ((PFunDDS.transcript s (PFunDDS.ddToDDE p) q)↓ᵧ).length = q := by
      rw [transcriptOutputs_length]
      exact transcript_length_eq hQ.1 (le_refl q)
    exact (PFunDDS.padDDD_true_iff_of_length_eq dummy q d hlenq).mpr htail

/-- If the original distinguisher keeps querying for the first `n ≤ q` rounds against `[q]S`,
then padding with dummy queries does not change the transcript through round `n`.

UPSTREAM-CANDIDATE: generic pre-budget run-comparison API for CR18 §4.10.1 padding. -/
theorem PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before
    (dummy : X) (S : PFunDDS.DDS X Y) (q : ℕ) (d : PFunDDS.DDD X Y) :
    ∀ n : ℕ, n ≤ q →
      (∀ j : ℕ, j < n →
        ∃ x : X,
          d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
            = Sum.inl x) →
      PFunDDS.transcript (PFunDDS.filterQueries q S)
          (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) n =
        PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n := by
  intro n
  induction n with
  | zero =>
      intro _hle _hall
      rfl
  | succ n ih =>
      intro hle hall
      have hprefix :
          PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) n =
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n := by
        exact ih (by omega) (fun j hj => hall j (by omega))
      obtain ⟨x, hx⟩ := hall n (by omega)
      have hfireOrig :
          PFunDDS.ddToDDE d
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n)↓ᵧ =
            some x := by
        change (match d.val
            (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n)↓ᵧ with
          | Sum.inl y => some y
          | Sum.inr _ => none) = some x
        rw [hx]
      have hlenout :
          ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) n)↓ᵧ).length < q := by
        rw [transcriptOutputs_length]
        have hlen :=
          PFunDDS.transcript_length_eq_of_fire (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d)
            hfireOrig
        rw [hlen]
        omega
      have hfirePad :
          PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)
            (PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) n)↓ᵧ = some x := by
        rw [hprefix]
        rw [PFunDDS.ddToDDE_padDDD_of_lt dummy q d hlenout]
        rw [hx]
      rw [transcript_succ_fire hfirePad, transcript_succ_fire hfireOrig, hprefix]

/-- Padding a raw distinguisher to exactly `q` queries preserves its verdict against a `[q]`-filtered
total deterministic system.

UPSTREAM-CANDIDATE: deterministic CR18 §4.10.1 padding equivalence for filtered systems. -/
theorem PFunDDS.verdict_padDDD_filterQueries_iff_of_total
    (dummy : X) (S : PFunDDS.DDS X Y) (q : ℕ)
    (hS : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom S) (d : PFunDDS.DDD X Y) :
    PFunDDS.verdict (PFunDDS.padDDD dummy q d) (PFunDDS.filterQueries q S) ↔
      PFunDDS.verdict d (PFunDDS.filterQueries q S) := by
  constructor
  · intro hp
    obtain ⟨k, hk⟩ :=
      (PFunDDS.verdict_padDDD_iff_tail dummy q d (PFunDDS.filterQueries q S)).mp hp
    apply (PFunDDS.verdict_filterQueries_iff_tail_of_total S q hS d).mpr
    by_cases hall : ∀ j : ℕ, j < q →
        ∃ x : X,
          d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
            = Sum.inl x
    · have hprefix :=
        PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before dummy S q d q (le_refl q)
          hall
      exact ⟨k, by rwa [hprefix] at hk⟩
    · have hbad : ∃ j : ℕ, j < q ∧
          ¬ ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
              = Sum.inl x := by
        by_contra hnone
        apply hall
        intro j hj
        by_contra hnot
        exact hnone ⟨j, hj, hnot⟩
      let j : ℕ := Nat.find hbad
      have hj_spec : j < q ∧
          ¬ ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
              = Sum.inl x := Nat.find_spec hbad
      have hmin : ∀ r : ℕ, r < j →
          ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) r)↓ᵧ)
              = Sum.inl x := by
        intro r hr
        by_contra hnot
        exact Nat.find_min hbad hr ⟨by omega, hnot⟩
      have hprefixj :
          PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) j =
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j :=
        PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before dummy S q d j
          (by omega) hmin
      let p : PFunDDS.DDD X Y := PFunDDS.padDDD dummy q d
      have hQp : QueriesExactly (PFunDDS.ddToDDE p) q := queriesExactly_ddToDDE_padDDD dummy q d
      have hpadNoEarly : ∀ h : List (Option Y), h.length < q →
          (PFunDDS.ddToDDE p h).isSome := hQp.1
      have htake :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) q).take j =
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) j :=
        transcript_take hpadNoEarly (by omega) (le_refl q)
      have hprePad :
          PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) j <+:
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) q := by
        rw [← htake]
        exact List.take_prefix j _
      have hpreOut :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ <+:
            (PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ := by
        rw [← hprefixj]
        simpa [p, PFunDDS.transcriptOutputs] using hprePad.map Prod.snd
      cases hdj : d.val
          ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ) with
      | inl x =>
          exact False.elim (hj_spec.2 ⟨x, hdj⟩)
      | inr b =>
          have hpadStop :
              d.val
                ((PFunDDS.transcript (PFunDDS.filterQueries q S)
                  (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ) = Sum.inr b :=
            d.property hpreOut b hdj
          have htailPre :
              (PFunDDS.transcript (PFunDDS.filterQueries q S)
                (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ <+:
                (PFunDDS.transcript (PFunDDS.filterQueries q S)
                  (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ ++
                  List.replicate k (none : Option Y) := by
            exact List.prefix_append _ _
          have htailStop :
              d.val
                ((PFunDDS.transcript (PFunDDS.filterQueries q S)
                  (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ ++
                  List.replicate k (none : Option Y)) = Sum.inr b :=
            d.property htailPre b hpadStop
          have hb : b = true := by
            have heq : (Sum.inr true : X ⊕ Bool) = Sum.inr b := by
              rw [← hk, htailStop]
            exact (Sum.inr.inj heq).symm
          subst b
          have hstopOrig :
              PFunDDS.ddToDDE d
                (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ =
                none := by
            change (match d.val
                (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ with
              | Sum.inl y => some y
              | Sum.inr _ => none) = none
            rw [hdj]
          have hfreeze :
              PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q =
                PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j :=
            transcript_freeze hstopOrig (by omega)
          exact ⟨0, by rw [hfreeze]; simpa using hdj⟩
  · intro hd
    obtain ⟨k, hk⟩ := (PFunDDS.verdict_filterQueries_iff_tail_of_total S q hS d).mp hd
    apply (PFunDDS.verdict_padDDD_iff_tail dummy q d (PFunDDS.filterQueries q S)).mpr
    by_cases hall : ∀ j : ℕ, j < q →
        ∃ x : X,
          d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
            = Sum.inl x
    · have hprefix :=
        PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before dummy S q d q (le_refl q)
          hall
      exact ⟨k, by rwa [hprefix]⟩
    · have hbad : ∃ j : ℕ, j < q ∧
          ¬ ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
              = Sum.inl x := by
        by_contra hnone
        apply hall
        intro j hj
        by_contra hnot
        exact hnone ⟨j, hj, hnot⟩
      let j : ℕ := Nat.find hbad
      have hj_spec : j < q ∧
          ¬ ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ)
              = Sum.inl x := Nat.find_spec hbad
      have hmin : ∀ r : ℕ, r < j →
          ∃ x : X,
            d.val ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) r)↓ᵧ)
              = Sum.inl x := by
        intro r hr
        by_contra hnot
        exact Nat.find_min hbad hr ⟨by omega, hnot⟩
      have hprefixj :
          PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) j =
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j :=
        PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before dummy S q d j
          (by omega) hmin
      let p : PFunDDS.DDD X Y := PFunDDS.padDDD dummy q d
      have hQp : QueriesExactly (PFunDDS.ddToDDE p) q := queriesExactly_ddToDDE_padDDD dummy q d
      have hpadNoEarly : ∀ h : List (Option Y), h.length < q →
          (PFunDDS.ddToDDE p h).isSome := hQp.1
      have htake :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) q).take j =
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) j :=
        transcript_take hpadNoEarly (by omega) (le_refl q)
      have hprePad :
          PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) j <+:
            PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE p) q := by
        rw [← htake]
        exact List.take_prefix j _
      have hpreOut :
          (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ <+:
            (PFunDDS.transcript (PFunDDS.filterQueries q S)
              (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ := by
        rw [← hprefixj]
        simpa [p, PFunDDS.transcriptOutputs] using hprePad.map Prod.snd
      cases hdj : d.val
          ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ) with
      | inl x =>
          exact False.elim (hj_spec.2 ⟨x, hdj⟩)
      | inr b =>
          have hstopOrig :
              PFunDDS.ddToDDE d
                (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ =
                none := by
            change (match d.val
                (PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j)↓ᵧ with
              | Sum.inl y => some y
              | Sum.inr _ => none) = none
            rw [hdj]
          have hfreeze :
              PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q =
                PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) j :=
            transcript_freeze hstopOrig (by omega)
          have horigTailStop :
              d.val
                ((PFunDDS.transcript (PFunDDS.filterQueries q S) (PFunDDS.ddToDDE d) q)↓ᵧ ++
                  List.replicate k (none : Option Y)) = Sum.inr b := by
            rw [hfreeze]
            exact d.property (List.prefix_append _ _) b hdj
          have hb : b = true := by
            have heq : (Sum.inr true : X ⊕ Bool) = Sum.inr b := by
              rw [← hk, horigTailStop]
            exact (Sum.inr.inj heq).symm
          subst b
          have hpadStop :
              d.val
                ((PFunDDS.transcript (PFunDDS.filterQueries q S)
                  (PFunDDS.ddToDDE (PFunDDS.padDDD dummy q d)) q)↓ᵧ) = Sum.inr true :=
            d.property hpreOut true hdj
          exact ⟨0, by simpa using hpadStop⟩

/-- Distribution-level finite-query padding: push a probabilistic raw distinguisher through
`PFunDDS.padDDD`. -/
noncomputable def PFunDDS.padDDDDist (dummy : X) (q : ℕ)
    (D : Dist (PFunDDS.DDD X Y)) : Dist (PFunDDS.DDD X Y) :=
  Dist.fTransform (PFunDDS.padDDD dummy q) D

/-- Padding a probabilistic distinguisher preserves total probability mass. -/
theorem PFunDDS.padDDDDist_isProbDist (dummy : X) (q : ℕ)
    (D : Dist (PFunDDS.DDD X Y)) (hD : D.isProbDist) :
    (PFunDDS.padDDDDist dummy q D).isProbDist := by
  unfold PFunDDS.padDDDDist
  exact Dist.fTransform_isProbDist (PFunDDS.padDDD dummy q) hD

/-- Every deterministic distinguisher in the support of the padded distribution makes exactly `q`
queries. -/
theorem PFunDDS.padDDDDist_queriesExactly_support (dummy : X) (q : ℕ)
    (D : Dist (PFunDDS.DDD X Y)) :
    ∀ d ∈ (PFunDDS.padDDDDist dummy q D).support,
      QueriesExactly (PFunDDS.ddToDDE d) q := by
  intro d hd
  unfold PFunDDS.padDDDDist at hd
  obtain ⟨d₀, _hd₀, rfl⟩ := mem_support_fTransform _ _ hd
  exact queriesExactly_ddToDDE_padDDD dummy q d₀

/-- Padding a distinguisher distribution preserves verdict probability against a filtered total PDS.

UPSTREAM-CANDIDATE: probabilistic CR18 §4.10.1 padding equivalence for filtered systems. -/
theorem verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty
    (dummy : X) (q : ℕ) (D : Dist (PFunDDS.DDD X Y)) (S : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) :
    verdictProb (PFunDDS.padDDDDist dummy q D) (⌈q⌉ S) =
      verdictProb D (⌈q⌉ S) := by
  unfold verdictProb PFunDDS.padDDDDist PFunPDS.filterQueries
  rw [winProb_fTransform]
  rw [winProb_fTransform_game]
  rw [winProb_fTransform_game]
  unfold GamePerf.winProb
  refine Finsupp.sum_congr fun d _hd => ?_
  refine Finsupp.sum_congr fun s hs => ?_
  have hiff :=
    PFunDDS.verdict_padDDD_filterQueries_iff_of_total dummy s q (hS s hs) d
  by_cases hp : PFunDDS.verdict (PFunDDS.padDDD dummy q d) (PFunDDS.filterQueries q s)
  · have ho : PFunDDS.verdict d (PFunDDS.filterQueries q s) := hiff.mp hp
    simp [hp, ho]
  · have ho : ¬ PFunDDS.verdict d (PFunDDS.filterQueries q s) := fun h => hp (hiff.mpr h)
    simp [hp, ho]

/-- Padding preserves signed advantage against filtered total systems.

UPSTREAM-CANDIDATE: advantage-level CR18 §4.10.1 padding equivalence for filtered systems. -/
theorem advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty
    (dummy : X) (q : ℕ) (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T) :
    advantage (PFunDDS.padDDDDist dummy q D) (⌈q⌉ S) (⌈q⌉ T) =
      advantage D (⌈q⌉ S) (⌈q⌉ T) := by
  unfold advantage
  rw [verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D T hT]
  rw [verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D S hS]

/-- Pushforwards of function evaluators are total on every nonempty history.

UPSTREAM-CANDIDATE: PFunPDS support-totality automation for function-evaluator systems. -/
theorem PFunPDS.ofFunDist_totalOnNonempty (Df : Dist (X → Y)) :
    CondEquiv.TotalOnNonempty (PFunPDS.ofFunDist Df) := by
  intro s hs xs hxs
  unfold PFunPDS.ofFunDist at hs
  obtain ⟨f, _hf, rfl⟩ := mem_support_fTransform _ _ hs
  rw [PFunDDS.dom_functionEvaluator]
  exact hxs

/-- Pushforwards of permutation evaluators are total on every nonempty history.

UPSTREAM-CANDIDATE: PFunPDS support-totality automation for permutation systems. -/
theorem PFunPDS.ofPermDist_totalOnNonempty (X : Type u) (Dσ : Dist (Equiv.Perm X)) :
    CondEquiv.TotalOnNonempty (PFunPDS.ofPermDist X Dσ) := by
  intro s hs xs hxs
  unfold PFunPDS.ofPermDist at hs
  obtain ⟨σ, _hσ, rfl⟩ := mem_support_fTransform _ _ hs
  rw [PFunDDS.dom_functionEvaluator]
  exact hxs

/-- The random-function PDS is total on every nonempty history.

UPSTREAM-CANDIDATE: PFunPDS support-totality automation for `𝖱`. -/
theorem PFunPDS.URF_totalOnNonempty [Fintype (X → Y)] [Nonempty (X → Y)] :
    CondEquiv.TotalOnNonempty (PFunPDS.URF : PFunPDS X Y) := by
  unfold PFunPDS.URF
  exact PFunPDS.ofFunDist_totalOnNonempty _

/-- The random-permutation PDS is total on every nonempty history.

UPSTREAM-CANDIDATE: PFunPDS support-totality automation for `𝖯`. -/
theorem PFunPDS.URP_totalOnNonempty (X : Type u) [Fintype X] :
    CondEquiv.TotalOnNonempty (PFunPDS.URP X) := by
  unfold PFunPDS.URP
  exact PFunPDS.ofPermDist_totalOnNonempty X _

/-- **The game-enhancement constructor `gameOf` (CR18 §4.11.1, UPSTREAM-CANDIDATE)**: enhance a base
`(X,Y)`-PDS `S` with a transcript-predicate `cond` to the game `Ŝ : PFunPDS X (Y × Bool)`, the
pushforward of `S` along the per-realization `gameOfDDS cond`. This is "one defines an MBO for `S`,
resulting in the game `Ŝ`" (CR18_LN.txt:5600,5624-5625). -/
noncomputable def gameOf (S : PFunPDS X Y) (cond : List (X × Y) → Bool) :
    PFunPDS X (Y × Bool) :=
  Dist.fTransform (PFunDDS.gameOfDDS cond) S

/-- Filtering commutes with adding a transcript-defined MBO at the deterministic-system level. -/
theorem PFunDDS.filterQueries_gameOfDDS
    (s : PFunDDS.DDS X Y) (cond : List (X × Y) → Bool) (q : ℕ) :
    PFunDDS.filterQueries q (PFunDDS.gameOfDDS cond s) =
      PFunDDS.gameOfDDS cond (PFunDDS.filterQueries q s) := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · rfl
  · intro h₁ h₂
    simp only [PFunDDS.filterQueries, PFunDDS.gameOfDDS, PFunDDS.ioTranscript]
    congr 2

/-- Filtering commutes with adding a transcript-defined MBO by `gameOf`.

This is the structural bridge from the paper expression `[q]R̂` to the constructed form
`gameOf ([q]R) cond`. -/
theorem PFunPDS.filterQueries_gameOf
    (S : PFunPDS X Y) (cond : List (X × Y) → Bool) (q : ℕ) :
    (⌈q⌉ (gameOf S cond)) = gameOf (⌈q⌉ S) cond := by
  unfold PFunPDS.filterQueries gameOf
  simp only [dist_simp]
  congr 1

/-- **CR18 eq. `Ŝ⁻ = S` (CR18_LN.txt:5628)**: ignoring the MBO of `gameOf S cond` returns the base `S`.
A standing fact of the construction — *proved*, never assumed. -/
@[simp] theorem ignoreMBO_gameOf (S : PFunPDS X Y) (cond : List (X × Y) → Bool) :
    PFunPDS.ignoreMBO (gameOf S cond) = S := by
  unfold gameOf PFunPDS.ignoreMBO PFunPDS.stripMBO
  simp only [dist_simp]
  rw [show (PFunDDS.ignoreMBO ∘ PFunDDS.gameOfDDS cond) = id from
    funext fun s => PFunDDS.ignoreMBO_gameOfDDS cond s]
  show Dist.fTransform id S = S
  rw [show (id : PFunDDS.DDS X Y → PFunDDS.DDS X Y) = fun a => a from rfl]
  exact Finsupp.mapDomain_id

/-- **CR18 Def 3.22 — `gameOf S cond` is a monotone-MBO game** when `cond` is a monotone
transcript-predicate. A standing fact of the construction — *proved* from `cond` monotone, never
assumed (this is exactly what the free-`Ŝ` scaffolds dodged). -/
theorem monotoneMBO_gameOf (S : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) :
    MonotoneMBO (gameOf S cond) := by
  intro g hg
  obtain ⟨s, _, rfl⟩ := mem_support_fTransform _ _ hg
  intro l hl
  have hldom : l ∈ dom s := hl
  -- `IsMBO` = the `Bool` projection of the output history is monotone in the index.
  intro i j hij
  simp only []
  -- the `Bool` at index `k` is `cond (ioTranscript s (l.take (k+1)))`
  have hbit : ∀ k : Fin (PFunDDS.outputHistory (gameOfDDS cond s) l hl).length,
      ((PFunDDS.outputHistory (gameOfDDS cond s) l hl).get k).2
        = cond (ioTranscript s (l.take (k.1 + 1))
            (prefix_closed s (List.take_prefix (k.1 + 1) l)
              (by
                have hk := k.2; simp only [PFunDDS.outputHistory, List.length_ofFn] at hk
                rw [← List.length_pos_iff_ne_nil, List.length_take]; omega)
              hldom)) := by
    intro k
    have hkl : (k.1 : ℕ) < l.length := by
      have hk := k.2; simpa only [PFunDDS.outputHistory, List.length_ofFn] using hk
    simp only [PFunDDS.outputHistory, List.get_ofFn, Fin.val_cast]
    rw [outputBit_gameOfDDS cond s _ _
      (prefix_closed s (List.take_prefix (k.1 + 1) l)
        (by rw [← List.length_pos_iff_ne_nil, List.length_take]; omega) hldom)]
  rw [hbit i, hbit j]
  have hile : (i.1 : ℕ) + 1 ≤ j.1 + 1 := Nat.succ_le_succ hij
  have hjlen : (j.1 : ℕ) < l.length := by
    have hj := j.2; simpa only [PFunDDS.outputHistory, List.length_ofFn] using hj
  rw [ioTranscript_take s l hldom (i.1 + 1) (by omega) _,
      ioTranscript_take s l hldom (j.1 + 1) (by omega) _]
  exact hcond (List.take_prefix_take_left hile)

/-! ## The two remaining standing facts of `gameOf S cond`, and the public Theorem 4.17

The keystone constructor `gameOf` already proves the eq. `Ŝ⁻ = S` (`ignoreMBO_gameOf`) and monotonicity
(`monotoneMBO_gameOf`). For the Theorem-4.17 chain we also need that the enhancement is a probability
distribution and is total on the histories under discussion — both **inherited from the base `S`** since
`gameOfDDS` leaves the domain unchanged (`dom_gameOfDDS`) and is a pushforward (weight-preserving). These
are proved here, never assumed: the public theorem takes only the base `S, T` and the MBO `cond`. -/

/-- `gameOf S cond` is a probability distribution when `S` is — `gameOf` is a pushforward of `S`. -/
theorem gameOf_isProbDist (S : PFunPDS X Y) (cond : List (X × Y) → Bool) (hS : S.isProbDist) :
    (gameOf S cond).isProbDist := by
  unfold gameOf
  exact Dist.fTransform_isProbDist _ hS

/-- `gameOf S cond` is total on the histories under discussion when `S` is — `gameOfDDS` leaves the
domain unchanged (`dom_gameOfDDS`), so every realization accepts every nonempty input history iff its
base does. -/
theorem gameOf_totalOnNonempty (S : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hS : CondEquiv.TotalOnNonempty S) : CondEquiv.TotalOnNonempty (gameOf S cond) := by
  intro g hg xs hxs
  obtain ⟨s, hs, rfl⟩ := mem_support_fTransform _ _ hg
  rw [PFunDDS.dom_gameOfDDS]
  exact hS s hs xs hxs

/-- Bounded totality is inherited by `gameOf S cond`, because `gameOfDDS` leaves the input domain
unchanged. This is the filtered-system version of `gameOf_totalOnNonempty`.

UPSTREAM-CANDIDATE: bounded totality preservation for game enhancement by a transcript MBO. -/
theorem gameOf_totalUpTo (S : PFunPDS X Y) (cond : List (X × Y) → Bool) (q : ℕ)
    (hS : TotalUpTo S q) : TotalUpTo (gameOf S cond) q := by
  intro g hg xs hxs hlen
  obtain ⟨s, hs, rfl⟩ := mem_support_fTransform _ _ hg
  rw [PFunDDS.dom_gameOfDDS]
  exact hS s hs xs hxs hlen

/-- **CR18 Theorem 4.17 (the paper-facing endpoint, base objects in)**: *if for an `(X,Y)`-system `S` one
can define an MBO `cond` such that the resulting game `Ŝ := gameOf S cond` is conditionally equivalent to
`T` (`Ŝ |≡ T`, Def 4.19), then `∆(S,T) ≤ Γ(bŜ)`* (CR18_LN.txt:5600-5605) — the distinguishing advantage
of any `D` between `S` and `T` is bounded by the **non-adaptive** (blind) game-winning probability of `Ŝ`.

Faithful to the cardinal rule: the inputs are the **base** systems `S T : PFunPDS X Y`, the query budget
`i`, the free distinguisher `D`, and the **MBO `cond`** ("one can define an MBO"). The derived game
`Ŝ := gameOf S cond` is **constructed in the statement**, and its standing facts are *proved*, not
assumed: `ignoreMBO Ŝ = S` (`ignoreMBO_gameOf`, eq. `Ŝ⁻ = S`), `MonotoneMBO Ŝ` (`monotoneMBO_gameOf`,
from `cond` monotone, Def 3.22), `Ŝ.isProbDist` and `TotalOnNonempty Ŝ` (inherited from `S`). The only
genuine Def-4.19 hypothesis is `gameOf S cond |≡ T`. The proof rewrites `ignoreMBO Ŝ = S` and applies the
absorbed blind helper (`advantage_le_blindMaxWinProb_of_condEquiv`, the free-`Ŝ` proof ingredient renamed
by MODELING_REVIEW #3 / fix F1.2), which **derives** blindness via the copying converter `T̃` rather than
assuming it (no `hblind` on `D`).

(`RelateGameDistinguishing.maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` — the misnamed Lemma-4.16 corollary — was renamed to
`advantage_le_maxWinProb_of_gameEquiv` by MODELING_REVIEW #4 / fix F1.4, freeing the canonical bare name
`maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` for this base-object endpoint. Fix F1.1 then applied that name here, renaming the former
`theorem_4_17_base` to the bare `maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf`.) -/
theorem advantage_le_blindMaxWinProb_gameOf_of_totalUpTo (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (cond : List (X × Y) → Bool)
    (i : ℕ) (hcond : PFunDDS.MonotoneCond cond)
    (hS : S.isProbDist) (hT : T.isProbDist) (hCE : gameOf S cond |≡ T)
    (hStot : TotalUpTo S (i + 1)) (hTtot : TotalUpTo T (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D S T : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ) := by
  have hSU : TotalUpTo (gameOf S cond) (i + 1) :=
    gameOf_totalUpTo S cond (i + 1) hStot
  have key := advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo D (gameOf S cond) T i
    (gameOf_isProbDist S cond hS) hT hCE (monotoneMBO_gameOf S cond hcond)
    hSU hTtot hQ hD
  rwa [ignoreMBO_gameOf S cond] at key

theorem advantage_le_blindMaxWinProb_gameOf (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (cond : List (X × Y) → Bool)
    (i : ℕ) (hcond : PFunDDS.MonotoneCond cond)
    (hS : S.isProbDist) (hT : T.isProbDist) (hCE : gameOf S cond |≡ T)
    (hStot : CondEquiv.TotalOnNonempty S) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D S T : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ) := by
  exact advantage_le_blindMaxWinProb_gameOf_of_totalUpTo D S T cond i hcond hS hT hCE
    (TotalUpTo_of_totalOnNonempty hStot (i + 1))
    (TotalUpTo_of_totalOnNonempty hTtot (i + 1)) hQ hD

/-! ### The `Δ` supremum bridge

The per-distinguisher theorem above is intentionally fixed-query: it consumes a support proof that every
deterministic distinguisher makes exactly `i+1` queries. The raw CR18 notation `Δ(S,T)`, however, is a
supremum over `DDD` distributions whose type only enforces final verdicts. CR18 §4.10.1 supplies the
missing WLOG step: collapse/pad an arbitrary raw distinguisher to a finite exact-query representative
without decreasing its advantage against the systems under discussion.

The following two declarations isolate that missing step at the generic `Δ` layer. They are not
switching-specific and not H-coefficient facts. Concrete protocol proofs should eventually call a
query-filtered corollary obtained from this bridge, rather than adding `QueriesExactly` to public
security statements. -/

/-- **CR18 §4.10.1 finite-query normalization for `Δ`** (UPSTREAM-CANDIDATE). Every probabilistic raw
distinguisher can be replaced by a probabilistic exact-query distinguisher whose signed advantage is at
least as large against the chosen pair `S,T`.

This is the generic padding/WLOG statement missing from the representative-level `maxAdvantage` API.
The witness budget is written as `i+1` to match the already-proved Lemma-4.16/Theorem-4.17 chain. -/
def DeltaFiniteQueryNormalization (S T : PFunPDS X Y) : Prop :=
  ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
    ∃ i : ℕ, ∃ D' : Dist (PFunDDS.DDD X Y),
      D'.isProbDist ∧
      (∀ d ∈ D'.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) ∧
      advantage D S T ≤ advantage D' S T

/-- Filtered finite-query normalization, the tighter CR18 §4.10.1 target for protocol proofs. For the
`[q]`-filtered pair, every raw distinguisher is dominated by an exact-`q` normal-form distinguisher.

This is the theorem we actually need for switching-style statements. The `q = i+1` indexing reflects
the existing Lemma-4.16/Theorem-4.17 chain; a later cleanup should either add a `q = 0` branch or
refactor the lower-level exact-query lemmas to accept `q` directly. -/
def DeltaFilteredFiniteQueryNormalization (q : ℕ) (S T : PFunPDS X Y) : Prop :=
  ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
    ∃ D' : Dist (PFunDDS.DDD X Y),
      D'.isProbDist ∧
      (∀ d ∈ D'.support, QueriesExactly (PFunDDS.ddToDDE d) q) ∧
      advantage D (⌈q⌉ S) (⌈q⌉ T) ≤ advantage D' (⌈q⌉ S) (⌈q⌉ T)

/-- Reduce filtered finite-query normalization to the concrete padded-distinguisher advantage
preservation lemma. This is the next proof boundary after constructing `padDDD`: show that padding a
raw distinguisher with post-filter `none` replies does not decrease its signed advantage against
`⌈q⌉S,⌈q⌉T`. -/
theorem deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage
    (dummy : X) (q : ℕ) (S T : PFunPDS X Y)
    (hAdv : ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
      advantage D (⌈q⌉ S) (⌈q⌉ T) ≤
        advantage (PFunDDS.padDDDDist dummy q D) (⌈q⌉ S) (⌈q⌉ T)) :
    DeltaFilteredFiniteQueryNormalization q S T := by
  intro D hD
  refine ⟨PFunDDS.padDDDDist dummy q D,
    PFunDDS.padDDDDist_isProbDist dummy q D hD,
    PFunDDS.padDDDDist_queriesExactly_support dummy q D,
    hAdv D hD⟩

/-- Filtered finite-query normalization from CR18 §4.10.1 padding. The only system-side hypothesis is
support-totality of the two base PDSs; the exact-query witness is the generic padded distinguisher
distribution.

UPSTREAM-CANDIDATE: filtered finite-query normalization theorem. -/
theorem deltaFilteredFiniteQueryNormalization_of_totalOnNonempty
    (dummy : X) (q : ℕ) (S T : PFunPDS X Y)
    (hS : CondEquiv.TotalOnNonempty S) (hT : CondEquiv.TotalOnNonempty T) :
    DeltaFilteredFiniteQueryNormalization q S T := by
  refine deltaFilteredFiniteQueryNormalization_of_padDDDDist_advantage dummy q S T ?_
  intro D _hD
  exact le_of_eq (advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D S T hS hT).symm

/-- Generic `sSup` lift for the finite-query normalization bridge. If every exact-query normalized
distinguisher is bounded by `B`, then the raw CR18 maximum `Δ(S,T)` is bounded by `B`. -/
theorem maxAdvantage_le_of_deltaFiniteQueryNormalization
    (S T : PFunPDS X Y) {B : ℝ} (hB : 0 ≤ B)
    (hNorm : DeltaFiniteQueryNormalization S T)
    (hExact : ∀ i (D : Dist (PFunDDS.DDD X Y)), D.isProbDist →
      (∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) →
      advantage D S T ≤ B) :
    (Δ(S, T) : ℝ) ≤ B := by
  unfold maxAdvantage
  apply Real.sSup_le
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨i, D', hD', hQ, hle⟩ := hNorm D hD
    exact hle.trans (hExact i D' hD' hQ)
  · exact hB

/-- `sSup` lift for the filtered normalization target. This is the exact order-theoretic shell needed
by protocol proofs once the filtered padding construction is proved.

UPSTREAM-CANDIDATE: filtered finite-query `maxAdvantage` normalization shell. -/
theorem maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact
    (q : ℕ) (S T : PFunPDS X Y) {B : ℝ} (hB : 0 ≤ B)
    (hNorm : DeltaFilteredFiniteQueryNormalization q S T)
    (hExact : ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
      (∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q) →
      advantage D (⌈q⌉ S) (⌈q⌉ T) ≤ B) :
    (Δ(⌈q⌉ S, ⌈q⌉ T) : ℝ) ≤ B := by
  unfold maxAdvantage
  apply Real.sSup_le
  · rintro _ ⟨D, hD, rfl⟩
    obtain ⟨D', hD', hQ, hle⟩ := hNorm D hD
    exact hle.trans (hExact D' hD' hQ)
  · exact hB

/-- Successor-indexed wrapper for the lower Theorem-4.17 proof, whose fixed-query transcript algebra
is stated for `i + 1` rounds. -/
theorem maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization
    (q : ℕ) (S T : PFunPDS X Y) {B : ℝ} (hB : 0 ≤ B)
    (hNorm : DeltaFilteredFiniteQueryNormalization (q + 1) S T)
    (hExact : ∀ D : Dist (PFunDDS.DDD X Y), D.isProbDist →
      (∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (q + 1)) →
      advantage D (⌈q + 1⌉ S) (⌈q + 1⌉ T) ≤ B) :
    (Δ(⌈q + 1⌉ S, ⌈q + 1⌉ T) : ℝ) ≤ B :=
  maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact
    (q + 1) S T hB hNorm hExact

/-- Exact-zero distinguishers have system-independent verdicts: no query transcript is ever observed,
so the verdict is only `d.val []`.

UPSTREAM-CANDIDATE: generic zero-query CR18 distinguisher normalizer. -/
theorem PFunDDS.verdict_congr_of_queriesExactly_zero
    (d : PFunDDS.DDD X Y) (s t : PFunDDS.DDS X Y)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) 0) :
    PFunDDS.verdict d s ↔ PFunDDS.verdict d t := by
  rw [PFunDDS.verdict_iff_at_exact d s 0 hQ,
    PFunDDS.verdict_iff_at_exact d t 0 hQ]
  simp [PFunDDS.transcript, PFunDDS.transcriptOutputs]

/-- A distribution of exact-zero distinguishers has the same verdict probability against any two
probability-distribution systems.

UPSTREAM-CANDIDATE: probability-level zero-query CR18 distinguisher normalizer. -/
theorem verdictProb_eq_of_queriesExactly_zero
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) 0)
    (hw : S.weight = T.weight) :
    verdictProb D S = verdictProb D T := by
  unfold verdictProb GamePerf.winProb
  refine Finsupp.sum_congr fun d hd => ?_
  have hQd := hQ d hd
  by_cases hv : d.val [] = Sum.inr true
  · have hvs : ∀ s : PFunDDS.DDS X Y, PFunDDS.verdict d s := by
      intro s
      rw [PFunDDS.verdict_iff_at_exact d s 0 hQd]
      simpa [PFunDDS.transcript, PFunDDS.transcriptOutputs] using hv
    calc
      S.sum (fun s sp => D d * sp * if PFunDDS.verdict d s then 1 else 0)
          = S.sum (fun _ sp => D d * sp) := by
              refine Finsupp.sum_congr fun s _ => ?_
              simp [hvs s]
      _ = D d * S.weight := by rw [Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
      _ = D d * T.weight := by rw [hw]
      _ = T.sum (fun _ tp => D d * tp) := by rw [Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
      _ = T.sum (fun t tp => D d * tp * if PFunDDS.verdict d t then 1 else 0) := by
              refine (Finsupp.sum_congr fun t _ => ?_).symm
              simp [hvs t]
  · have hnvs : ∀ s : PFunDDS.DDS X Y, ¬ PFunDDS.verdict d s := by
      intro s hs
      apply hv
      rw [PFunDDS.verdict_iff_at_exact d s 0 hQd] at hs
      simpa [PFunDDS.transcript, PFunDDS.transcriptOutputs] using hs
    calc
      S.sum (fun s sp => D d * sp * if PFunDDS.verdict d s then 1 else 0)
          = 0 := by
              unfold Finsupp.sum
              refine Finset.sum_eq_zero fun s _ => ?_
              simp [hnvs s]
      _ = T.sum (fun t tp => D d * tp * if PFunDDS.verdict d t then 1 else 0) := by
              symm
              unfold Finsupp.sum
              apply Finset.sum_eq_zero
              intro t _
              simp [hnvs t]

/-- Exact-zero distinguishers have zero signed advantage between probability-distribution systems. -/
theorem advantage_eq_zero_of_queriesExactly_zero
    (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X Y)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) 0)
    (hw : S.weight = T.weight) :
    advantage D S T = 0 := by
  unfold advantage
  rw [verdictProb_eq_of_queriesExactly_zero D S T hQ hw]
  ring

/-- Zero-query filtered systems have zero maximal distinguishing advantage after the generic filtered
normalization bridge is supplied. -/
theorem maxAdvantage_filterQueries_zero_le_of_deltaFilteredFiniteQueryNormalization
    (S T : PFunPDS X Y) {B : ℝ} (hB : 0 ≤ B)
    (hw : (⌈0⌉ S).weight = (⌈0⌉ T).weight)
    (hNorm : DeltaFilteredFiniteQueryNormalization 0 S T) :
    (Δ(⌈0⌉ S, ⌈0⌉ T) : ℝ) ≤ B := by
  refine maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact
    0 S T hB hNorm ?_
  intro D _hD hQ
  rw [advantage_eq_zero_of_queriesExactly_zero D (⌈0⌉ S) (⌈0⌉ T) hQ hw]
  exact hB

/-- Theorem 4.17 after the generic finite-query normalization bridge has been supplied. This is the
proved, assumption-explicit form of the headline: normalization supplies the `Δ` supremum step, while
global totality is only used to supply the tight `TotalUpTo` hypotheses required by the per-distinguisher
step. -/
theorem maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization
    (S T : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.isProbDist) (hT : T.isProbDist)
    (hStot : CondEquiv.TotalOnNonempty S) (hTtot : CondEquiv.TotalOnNonempty T)
    (hNorm : DeltaFiniteQueryNormalization S T) :
    (gameOf S cond |≡ T) → (Δ(S, T) : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ) := by
  intro hCE
  refine maxAdvantage_le_of_deltaFiniteQueryNormalization S T
    (blindMaxWinProb_nonneg (hS.nonNeg.fTransform _)) hNorm ?_
  intro i D hD hQ
  exact advantage_le_blindMaxWinProb_gameOf D S T cond i hcond hS hT hCE hStot hTtot hQ hD

/-- Filtered Theorem 4.17 after the filtered finite-query normalization bridge has been supplied.
This is the direct CR18 §4.10.1-to-§4.11.2 route for protocol proofs: the filtered systems provide
`TotalUpTo` at the exact query length, so the proof does not pass through a global-totality theorem for
`⌈q+1⌉S` or `⌈q+1⌉T`. -/
theorem maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization
    (q : ℕ) (S T : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.isProbDist) (hT : T.isProbDist)
    (hStot : CondEquiv.TotalOnNonempty S) (hTtot : CondEquiv.TotalOnNonempty T)
    (hNorm : DeltaFilteredFiniteQueryNormalization (q + 1) S T) :
    (gameOf (⌈q + 1⌉ S) cond |≡ ⌈q + 1⌉ T) →
      (Δ(⌈q + 1⌉ S, ⌈q + 1⌉ T) : ℝ) ≤
        (Γᵇ (gameOf (⌈q + 1⌉ S) cond) : ℝ) := by
  intro hCE
  refine maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization q S T
    (blindMaxWinProb_nonneg ((hS.nonNeg.fTransform _).fTransform _)) hNorm ?_
  intro D hD hQ
  exact advantage_le_blindMaxWinProb_gameOf_of_totalUpTo D (⌈q + 1⌉ S) (⌈q + 1⌉ T) cond q
    hcond
    (PFunPDS.isProbDist_filterQueries (q + 1) hS)
    (PFunPDS.isProbDist_filterQueries (q + 1) hT)
    hCE
    (totalUpTo_filterQueries (q + 1) hStot)
    (totalUpTo_filterQueries (q + 1) hTtot)
    hQ hD

/-- Filtered Theorem 4.17 for all query bounds. The zero-query branch is the generic fact that an
exact-zero distinguisher cannot observe the system; the successor branch is the fixed-query
Theorem-4.17 transcript proof. -/
theorem maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization_all
    (q : ℕ) (S T : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.isProbDist) (hT : T.isProbDist)
    (hStot : CondEquiv.TotalOnNonempty S) (hTtot : CondEquiv.TotalOnNonempty T)
    (hNorm : DeltaFilteredFiniteQueryNormalization q S T) :
    (gameOf (⌈q⌉ S) cond |≡ ⌈q⌉ T) →
      (Δ(⌈q⌉ S, ⌈q⌉ T) : ℝ) ≤ (Γᵇ (gameOf (⌈q⌉ S) cond) : ℝ) := by
  cases q with
  | zero =>
      intro _hCE
      exact maxAdvantage_filterQueries_zero_le_of_deltaFilteredFiniteQueryNormalization S T
        (blindMaxWinProb_nonneg ((hS.nonNeg.fTransform _).fTransform _))
        (Dist.weight_eq_weight_of_isProbDist (PFunPDS.isProbDist_filterQueries 0 hS)
          (PFunPDS.isProbDist_filterQueries 0 hT))
        hNorm
  | succ q =>
      exact maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization q S T cond hcond
        hS hT hStot hTtot hNorm

/-- Stripping the MBO preserves support-totality (`dom (stripMBO s) = dom s` realization-wise). -/
theorem totalOnNonempty_ignoreMBO {Shat : PFunPDS X (Y × Bool)}
    (h : CondEquiv.TotalOnNonempty Shat) :
    CondEquiv.TotalOnNonempty (PFunPDS.ignoreMBO Shat) := by
  intro s hs xs hne
  obtain ⟨s', hs', rfl⟩ := Dist.mem_support_fTransform _ _ hs
  exact h s' hs' xs hne

/-- Stripping the MBO preserves probability mass (it is a deterministic pushforward). -/
theorem isProbDist_ignoreMBO {Shat : PFunPDS X (Y × Bool)} (h : Shat.isProbDist) :
    (PFunPDS.ignoreMBO Shat).isProbDist := by
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO
  exact Dist.fTransform_isProbDist _ h

/-- **CR18 Theorem 4.17, filtered, abstract-game form** — the paper-usage endpoint for games whose
MBO is *not* a transcript condition (e.g. seed-indexed MBOs such as the CBC-MAC's `Aᵢ`): a
monotone-MBO game `Ŝ` conditionally equivalent to `T` bounds the filtered advantage of its stripped
system `S = Ŝ⁻` by its filtered blind winning probability,

`Ŝ |≡ T  →  Δ(⌈q⌉ S, ⌈q⌉ T) ≤ Γᵇ(⌈q⌉ Ŝ)`.

Every piece of `[q]` bookkeeping — filter/strip commutation, conditional-equivalence and
monotone-MBO filtering, finite-query normalization, and the trivial `q = 0` case — is discharged
here, once.  The standing assumptions — Maurer's model carries them in the *types* of "game" and
"random system" (Def 3.22 monotone MBO, Def 3.1 total probability system) — are `autoParam`s
discharged by `cr18_standing` from the protocol's registered `@[cr18_standing]` facts, so consumers
cite this exactly as the paper cites Theorem 4.17: the game and the conditional equivalence.
`maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization_all` is the transcript-condition
(`gameOf`) sibling. -/
theorem maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv [Nonempty X]
    (q : ℕ) (Shat : PFunPDS X (Y × Bool)) {S T : PFunPDS X Y} (hCE : Shat |≡ T)
    (hstrip : PFunPDS.ignoreMBO Shat = S := by cr18_standing)
    (hmono : MonotoneMBO Shat := by cr18_standing)
    (hS : Shat.isProbDist := by cr18_standing) (hT : T.isProbDist := by cr18_standing)
    (hStot : CondEquiv.TotalOnNonempty Shat := by cr18_standing)
    (hTtot : CondEquiv.TotalOnNonempty T := by cr18_standing) :
    (Δ(⌈q⌉ S, ⌈q⌉ T) : ℝ) ≤ (Γᵇ (⌈q⌉ Shat) : ℝ) := by
  subst hstrip
  refine maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact
    q (PFunPDS.ignoreMBO Shat) T (blindMaxWinProb_nonneg (hS.nonNeg.fTransform _))
    (deltaFilteredFiniteQueryNormalization_of_totalOnNonempty (Classical.arbitrary X) q _ _
      (totalOnNonempty_ignoreMBO hStot) hTtot) ?_
  intro D hD hQ
  rcases q with _ | n
  · rw [advantage, verdictProb_eq_of_queriesExactly_zero D (⌈0⌉ T)
      (⌈0⌉ PFunPDS.ignoreMBO Shat) hQ
      (Dist.weight_eq_weight_of_isProbDist (PFunPDS.isProbDist_filterQueries 0 hT)
        (PFunPDS.isProbDist_filterQueries 0 (isProbDist_ignoreMBO hS))), sub_self]
    exact blindMaxWinProb_nonneg (hS.nonNeg.fTransform _)
  · rw [show (⌈n + 1⌉ PFunPDS.ignoreMBO Shat) = PFunPDS.ignoreMBO (⌈n + 1⌉ Shat) from
      (PFunPDS.ignoreMBO_filterQueries (n + 1) Shat).symm]
    exact advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo D (⌈n + 1⌉ Shat) (⌈n + 1⌉ T) n
      (PFunPDS.isProbDist_filterQueries _ hS)
      (PFunPDS.isProbDist_filterQueries _ hT)
      (CondEquiv.condEquiv_filterQueries _ _ hCE)
      (monotoneMBO_filterQueries _ hmono)
      (totalUpTo_filterQueries _ hStot)
      (totalUpTo_filterQueries _ hTtot) hQ hD

/-- **CR18 Theorem 4.17 — the headline `Ŝ |≡ T → ∆(S,T) ≤ Γ(bŜ)`** (CR18_LN.txt:5602): the base objects
`S T : PFunPDS X Y` and the MBO `cond` (monotone, Def 3.22), and the **one implication** Maurer states,
with `|≡` written as the `→`. The Lean statement exposes the proof's real framework hypotheses:
probability mass, totality on the histories under discussion, and the §4.10.1 finite-query
normalization bridge from raw distinguishers to exact-query ones. `Δ(S,T)` is the `sup` over
distinguishers of the per-`D` reduction `advantage_le_blindMaxWinProb_gameOf`.

**Thesis reconciliation.** Lanzenberger's thesis treats random systems/games as behavior/equivalence
classes of PDS/PDG representatives (Def. 2.17, Notation 2.19, Def. 2.22). This theorem is still a
representative-level CR18 endpoint. The normalization hypothesis is the place where the thesis-style
behavior/finite-query layer should eventually discharge the CR18 WLOG step once and for all. -/
theorem maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf (S T : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.isProbDist) (hT : T.isProbDist)
    (hStot : CondEquiv.TotalOnNonempty S) (hTtot : CondEquiv.TotalOnNonempty T)
    (hNorm : DeltaFiniteQueryNormalization S T) :
    (gameOf S cond |≡ T) → (Δ(S, T) : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ) := by
  exact maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization S T cond hcond hS hT hStot hTtot hNorm

/-- **CR18 eq. (4.39) (the paper-facing endpoint, base objects in)**: *if for an `(X,Y)`-system `S` one
can define an MBO `cond` such that the resulting game `Ŝ := gameOf S cond` is conditionally equivalent to
`T` (`Ŝ |≡ T`), then `Ŝ ≡ᵍ T̂`* (CR18_LN.txt:5644-5688), where `T̂ := gameEnhance T Ŝ` is `T` enhanced by
copying `Ŝ`'s MBO (`pT̂_{Aᵢ|XⁱYⁱ} = pŜ_{Aᵢ|Xⁱ}`). Maurer proves it via the marginal factoring
`pŜ_{YⁱAᵢ=0|Xⁱ} = pŜ_{Aᵢ=0|Xⁱ} · pŜ_{Yⁱ|Xⁱ,Aᵢ=0} = pT̂_{Aᵢ=0|Xⁱ} · pT_{Yⁱ|Xⁱ} = pT̂_{YⁱAᵢ=0|Xⁱ}`,
using `Ŝ |≡ T`. The Lean content is the equality of not-won transcript masses, `massYAfalse Ŝ = massYAfalse T̂`
(`MassYAfalseEq`) — exactly what the Lemma 4.15 / Lemma 4.16 consumers use `Ŝ ≡ᵍ T̂` for.

Faithful to the cardinal rule: the inputs are the **base** systems `S T : PFunPDS X Y` and the **MBO `cond`**
("one can define an MBO"). The derived game `Ŝ := gameOf S cond` and the copied enhancement
`T̂ := gameEnhance T (gameOf S cond)` are both **constructed in the statement**. The monotonicity needed by
the abstract algebra helper is *discharged*, not assumed: `MonotoneMBO Ŝ` via `monotoneMBO_gameOf` (from
`cond` monotone, Def 3.22). The only genuine Def-4.19 hypothesis is `gameOf S cond |≡ T`; the rest are
Maurer's standing assumptions (probability distributions, totality on the histories under discussion).

This specializes the generic algebra helper `massYAfalse_gameEnhance_eq_abstract` (the free-`Ŝ` proof
ingredient from MODELING_REVIEW #6 / fix F1.3) to the constructed game `Ŝ = gameOf S cond`, discharging
its `hmono` obligation through the enhancement construction. -/
theorem massYAfalseEq_gameEnhance_of_condEquiv (S T : PFunPDS X Y) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.NonNeg)
    (hT : T.isProbDist) (hCE : gameOf S cond |≡ T)
    (hTtot : CondEquiv.TotalOnNonempty T) :
    MassYAfalseEq (gameOf S cond) (gameEnhance T (gameOf S cond)) :=
  fun i ys xs =>
    (massYAfalse_gameEnhance_eq_abstract T (gameOf S cond) (hS.fTransform _) hCE hT hTtot
      (monotoneMBO_gameOf S cond hcond) i ys xs).symm

end RandomSystems.CR18
