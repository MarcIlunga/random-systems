/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.GameOf
import RandomSystemsCC.TypedDistinguisherChecks
import AbstractCrypto.Multiparty

/-!
# Property transfer on the typed RS carrier — one worked unforgeability example

The first use of `AbstractCrypto.propSpec` / `gameSpec` from the RS side: a
genuine cryptographic *guarantee* — not merely a distance — crosses from an
ideal resource to every resource close to it in the strict-observation
distinguisher class of `RandomSystemsCC.TypedDistinguisher`.

## The bridge that makes it possible

The load-bearing content is the identity between an admitted AC test value
and a CR18 game-winning probability (`accept_mass_eq_win_prob_gameOf`):

* an environment `e` halting within `n` queries, read as a bounded strict
  test through `DDD.ofDDE`/`testOfTruncDDD`, has acceptance mass on a total
  law `S` equal to CR18 Definition 4.5's winning probability of the *same*
  `e` — a winner is literally a `DDE` (Definition 3.23) — against the MBO
  game `gameOf S cond` (CR18 §4.11.1), for any monotone transcript predicate
  `cond` that is false on the empty transcript.

The per-realization step (`winsDDS_gameOfDDS_iff_cond`) aligns the winner's
run against the game with the raw interaction transcript: the game transcript
projects onto the raw transcript (`transcript_ignoreMBO` at
`ignoreMBO_gameOfDDS`), and each fired MBO bit is `cond` of the *visible*
transcript so far (`visible_transcript_eq_ioTranscript`).  Monotonicity
collapses CR18's unbounded winning existential to the `n`-step transcript
once the winner halts within `n`.

## The worked property

On the two-interface Boolean carrier of `TypedFiniteChecks`, interface `1` is
read as a verification interface: an answer `true` there is an accepted
forgery (`forgedAnswer`), and `forgeryCond` is the monotone MBO "some answer
was a forgery".  The ideal resource never accepts (`witnessResource false`);
the defining tests `unforgeabilityTests` demand that every budgeted
adversary fail to provoke acceptance.

* `ideal_mem_prop_spec` — the ideal satisfies the property specification;
* `unforgeability_transfer` — `1 - ε ≤ t real` for every defining test, by
  `one_tsub_le_test_of_close`, from `edistD real ideal ≤ ε`;
* `real_mem_game_spec` — the dual `gameSpec` route via
  `gameSpec_of_edistD_le`;
* `win_prob_forgery_le` — the CR18 reading: the winning probability of every
  `n`-halting winner against `gameOf (real law) forgeryCond` is at most `ε`.

Non-vacuity receipts: the degenerate always-accepting resource
(`witnessResource true`) *fails* the defining test with value `0`
(`unforgeability_test_forgeable_eq_zero`), hence is not in the property
specification, and wins the forgery game with probability `1`
(`forgery_win_test_forgeable_eq_one`); the D1 receipt
`strict_test_class_edistD_witness_eq_one` places it at class distance exactly
`1` from the ideal, so the transfer's `1 - ε` correctly degenerates only
there.
-/

namespace RandomSystemsCC.TypedPropertyTransfer

noncomputable section

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open RandomSystemsCC.TypedFiniteChecks
open RandomSystemsCC.TypedDistinguisher
open RandomSystemsCC.TypedDistinguisherChecks
open scoped ENNReal NNReal PFunDDS

universe u v

variable {X : Type u} {Y : Type v}

/-! ## The visible transcript

CR18's MBO predicates read the *visible* interaction data — the query/answer
pairs actually produced — while the raw CR18 transcript carries `Option`
answers (a stalled completion never appears against a total system, but the
type does not know that).  `visibleTranscript` is the mediating projection.

The lemmas of this section are generic `(X, Y)`-system facts.
UPSTREAM-CANDIDATE: `RandomSystems.GameOf`, next to `ioTranscript`. -/

/-- The visible query/answer pairs of a raw transcript prefix: drop the
stalled entries, unwrap the answered ones. -/
def visibleTranscript (t : List (X × Option Y)) : List (X × Y) :=
  t.filterMap fun step => step.2.map fun answer => (step.1, answer)

@[simp]
theorem visible_transcript_nil :
    visibleTranscript ([] : List (X × Option Y)) = [] :=
  rfl

theorem visible_transcript_append_some (t : List (X × Option Y))
    (x : X) (y : Y) :
    visibleTranscript (t ++ [(x, some y)]) =
      visibleTranscript t ++ [(x, y)] := by
  simp [visibleTranscript]

/-- The visible transcript is monotone along transcript prefixes. -/
theorem visible_transcript_prefix {t t' : List (X × Option Y)}
    (h : t <+: t') : visibleTranscript t <+: visibleTranscript t' := by
  obtain ⟨rest, rfl⟩ := h
  unfold visibleTranscript
  rw [List.filterMap_append]
  exact List.prefix_append _ _

/-- A monotone transcript predicate that has fired stays fired on every
extension (`MonotoneCond`, read at `= true`). -/
theorem monotoneCond_eq_true_of_prefix {cond : List (X × Y) → Bool}
    (hmono : PFunDDS.MonotoneCond cond) {t₁ t₂ : List (X × Y)}
    (hpre : t₁ <+: t₂) (hfired : cond t₁ = true) : cond t₂ = true := by
  have hle := hmono hpre
  rw [hfired] at hle
  cases hfinal : cond t₂
  · rw [hfinal] at hle
    exact absurd hle (by decide)
  · rfl

/-- A winner budget: the environment issues no query once `n` answers have
been seen.  This is the second component of `QueriesExactly` (CR18's
normalized `q`-query winner) — exactness of the schedule is not needed for
any statement here. -/
def HaltsWithin (e : PFunDDS.DDE X Y) (n : ℕ) : Prop :=
  ∀ h : List (Option Y), n ≤ h.length → e h = none

theorem haltsWithin_of_queriesExactly {e : PFunDDS.Winner X Y} {n : ℕ}
    (h : QueriesExactly e n) : HaltsWithin e n :=
  h.2

/-- Once a budgeted environment has run for its budget, the transcript is
frozen: either it has already stalled, or the budget stops it. -/
theorem transcript_eq_of_haltsWithin {s : PFunDDS.DDS X Y}
    {e : PFunDDS.DDE X Y} {n : ℕ} (halts : HaltsWithin e n)
    {k : ℕ} (hk : n ≤ k) :
    PFunDDS.transcript s e k = PFunDDS.transcript s e n := by
  refine transcript_freeze ?_ hk
  rcases lt_or_ge (PFunDDS.transcript s e n).length n with shorter | atBudget
  · exact PFunDDS.transcript_stall_of_length_lt shorter
  · exact halts _ (by rwa [transcriptOutputs_length])

/-! ## The visible transcript of a total run is the MBO's `ioTranscript` -/

/-- Two `ioTranscript`s on propositionally equal query histories agree — the
domain proofs are irrelevant to the value. -/
theorem ioTranscript_congr' (s : PFunDDS.DDS X Y) {l l' : List X}
    (h : l = l') (hl : l ∈ PFunDDS.dom s) (hl' : l' ∈ PFunDDS.dom s) :
    PFunDDS.ioTranscript s l hl = PFunDDS.ioTranscript s l' hl' := by
  subst h
  rfl

/-- `ioTranscript` of one more query is the old transcript plus the new
query/answer pair. -/
theorem ioTranscript_concat (s : PFunDDS.DDS X Y) {l : List X} {x : X}
    (hl : l ∈ PFunDDS.dom s) (hnext : l ++ [x] ∈ PFunDDS.dom s) :
    PFunDDS.ioTranscript s (l ++ [x]) hnext =
      PFunDDS.ioTranscript s l hl ++
        [(x, PFunDDS.output s (l ++ [x]) hnext)] := by
  apply List.ext_getElem
  · simp
  intro k hk hk'
  have hkl : k < l.length + 1 := by
    simpa using hk
  rcases Nat.lt_or_ge k l.length with hsmall | hlarge
  · rw [List.getElem_append_left (by simpa using hsmall)]
    simp only [PFunDDS.ioTranscript, List.getElem_ofFn]
    have htake : (l ++ [x]).take (k + 1) = l.take (k + 1) :=
      List.take_append_of_le_length (by omega)
    refine Prod.ext ?_ ?_
    · simp [List.getElem_append_left hsmall]
    · exact PFunDDS.output_congr s htake _ _
  · obtain rfl : k = l.length := by omega
    rw [List.getElem_append_right (by simp)]
    simp only [PFunDDS.ioTranscript, List.getElem_ofFn,
      List.length_ofFn, Nat.sub_self, List.getElem_singleton]
    have htake : (l ++ [x]).take (l.length + 1) = l ++ [x] :=
      List.take_of_length_le (by simp)
    refine Prod.ext ?_ ?_
    · simp
    · exact PFunDDS.output_congr s htake _ _

/-- `ioTranscript` of a single query is the single query/answer pair. -/
theorem ioTranscript_singleton (s : PFunDDS.DDS X Y) (x : X)
    (h : [x] ∈ PFunDDS.dom s) :
    PFunDDS.ioTranscript s [x] h = [(x, PFunDDS.output s [x] h)] :=
  rfl

/-- **The visible run is the MBO's transcript**: against a total system, the
visible query/answer pairs of the raw interaction transcript are exactly the
`ioTranscript` on the queried inputs — the data a CR18 transcript predicate
is defined on. -/
theorem visible_transcript_eq_ioTranscript (s : PFunDDS.DDS X Y)
    (total : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s) (e : PFunDDS.DDE X Y) :
    ∀ (k : ℕ) (hne : (PFunDDS.transcript s e k)↓ₓ ≠ []),
      visibleTranscript (PFunDDS.transcript s e k) =
        PFunDDS.ioTranscript s ((PFunDDS.transcript s e k)↓ₓ)
          (total _ hne) := by
  intro k
  induction k with
  | zero => intro hne; exact absurd rfl hne
  | succ k ih =>
      intro hne
      rcases hfire : e ((PFunDDS.transcript s e k)↓ᵧ) with _ | x
      · have hstall : PFunDDS.transcript s e (k + 1) =
            PFunDDS.transcript s e k := transcript_succ_stall hfire
        have hne' : (PFunDDS.transcript s e k)↓ₓ ≠ [] := by
          rw [← hstall]
          exact hne
        calc visibleTranscript (PFunDDS.transcript s e (k + 1)) =
              visibleTranscript (PFunDDS.transcript s e k) := by rw [hstall]
          _ = PFunDDS.ioTranscript s ((PFunDDS.transcript s e k)↓ₓ)
                (total _ hne') := ih hne'
          _ = PFunDDS.ioTranscript s ((PFunDDS.transcript s e (k + 1))↓ₓ)
                (total _ hne) :=
              ioTranscript_congr' s (by rw [hstall]) _ _
      · have step := transcript_succ_fire (s := s) hfire
        have hnextdom : (PFunDDS.transcript s e k)↓ₓ ++ [x] ∈ PFunDDS.dom s :=
          total _ (by simp)
        have hprev : (PFunDDS.transcript s e k)↓ₓ ∈ PFunDDS.dom s ∨
            (PFunDDS.transcript s e k)↓ₓ = [] := by
          by_cases hprevne : (PFunDDS.transcript s e k)↓ₓ = []
          · exact Or.inr hprevne
          · exact Or.inl (total _ hprevne)
        have houtput :
            PFunDDS.output s⊥ ((PFunDDS.transcript s e k)↓ₓ ++ [x])
                (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
              some (PFunDDS.output s ((PFunDDS.transcript s e k)↓ₓ ++ [x])
                hnextdom) :=
          PFunDDS.output_fullyDefined_append_of_mem s _ x hprev hnextdom
        have hinputs : (PFunDDS.transcript s e (k + 1))↓ₓ =
            (PFunDDS.transcript s e k)↓ₓ ++ [x] := by
          rw [step, transcriptInputs_append]
        have hmid : visibleTranscript (PFunDDS.transcript s e (k + 1)) =
            PFunDDS.ioTranscript s ((PFunDDS.transcript s e k)↓ₓ ++ [x])
              hnextdom := by
          rw [step, houtput, visible_transcript_append_some]
          rcases hprev with hprevdom | hprevnil
          · have hprevne : (PFunDDS.transcript s e k)↓ₓ ≠ [] := by
              intro hnil
              rw [hnil] at hprevdom
              exact PFunDDS.empty_not_mem s hprevdom
            rw [ih hprevne]
            exact (ioTranscript_concat s (total _ hprevne) _).symm
          · have htrnil : PFunDDS.transcript s e k = [] :=
              List.map_eq_nil_iff.mp hprevnil
            have hvis : visibleTranscript (PFunDDS.transcript s e k) = [] := by
              rw [htrnil, visible_transcript_nil]
            have hsingle : (PFunDDS.transcript s e k)↓ₓ ++ [x] = [x] := by
              rw [hprevnil]
              rfl
            have hxdom : [x] ∈ PFunDDS.dom s := hsingle ▸ hnextdom
            rw [hvis, List.nil_append,
              PFunDDS.output_congr s hsingle hnextdom hxdom]
            calc [(x, PFunDDS.output s [x] hxdom)] =
                  PFunDDS.ioTranscript s [x] hxdom :=
                (ioTranscript_singleton s x hxdom).symm
              _ = PFunDDS.ioTranscript s
                    ((PFunDDS.transcript s e k)↓ₓ ++ [x]) hnextdom :=
                ioTranscript_congr' s hsingle.symm _ _
        rw [hmid]
        exact ioTranscript_congr' s hinputs.symm _ _

/-- Every visible answer of a total run is a genuine output of the system on
some queried prefix; hence any per-output invariant holds along the whole
visible transcript. -/
theorem forall_visible_answer_of_forall_output {P : Y → Prop}
    (s : PFunDDS.DDS X Y)
    (total : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
    (hout : ∀ (l : List X) (h : l ∈ PFunDDS.dom s), P (PFunDDS.output s l h))
    (e : PFunDDS.DDE X Y) (k : ℕ) :
    ∀ p ∈ visibleTranscript (PFunDDS.transcript s e k), P p.2 := by
  intro p hp
  by_cases hne : (PFunDDS.transcript s e k)↓ₓ = []
  · rw [List.map_eq_nil_iff.mp hne] at hp
    exact absurd hp (List.not_mem_nil)
  · rw [visible_transcript_eq_ioTranscript s total e k hne] at hp
    simp only [PFunDDS.ioTranscript] at hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    exact hout _ _

/-! ## CR18 game winning is a bounded strict-test acceptance

Per realization: the winner `e` — a winner *is* a `DDE` (CR18 Def 3.23) —
wins the MBO game `gameOfDDS cond s` exactly when `cond` fires on the visible
transcript of its budgeted run against the *base* system `s`. -/

/-- The winner's environment view of the game transcript is the raw
environment on the raw transcript. -/
private theorem winnerView_gameTranscript_eq (cond : List (X × Y) → Bool)
    (s : PFunDDS.DDS X Y) (e : PFunDDS.DDE X Y) (k : ℕ) :
    PFunDDS.winnerView e
        ((PFunDDS.transcript (PFunDDS.gameOfDDS cond s)
          (PFunDDS.winnerView e) k)↓ᵧ) =
      e ((PFunDDS.transcript s e k)↓ᵧ) := by
  have hproj : PFunDDS.transcript s e k =
      PFunDDS.projT (PFunDDS.transcript (PFunDDS.gameOfDDS cond s)
        (PFunDDS.winnerView e) k) := by
    rw [← PFunDDS.ignoreMBO_gameOfDDS cond s]
    exact PFunDDS.transcript_ignoreMBO (PFunDDS.gameOfDDS cond s) e k
  rw [hproj, PFunDDS.projT_outputs]
  rfl

/-- **The per-round winning bridge**: some MBO bit has fired in the winner's
`k`-round run against `gameOfDDS cond s` exactly when the monotone `cond`
holds of the visible `k`-round transcript against the base `s`. -/
theorem exists_win_entry_gameOfDDS_iff (cond : List (X × Y) → Bool)
    (hmono : PFunDDS.MonotoneCond cond) (hnil : cond [] = false)
    (s : PFunDDS.DDS X Y)
    (total : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
    (e : PFunDDS.DDE X Y) :
    ∀ k : ℕ,
      (∃ y : Y, (some (y, true) : Option (Y × Bool)) ∈
          (PFunDDS.transcript (PFunDDS.gameOfDDS cond s)
            (PFunDDS.winnerView e) k)↓ᵧ) ↔
        cond (visibleTranscript (PFunDDS.transcript s e k)) = true := by
  intro k
  induction k with
  | zero =>
      constructor
      · rintro ⟨y, hy⟩
        simp [transcript_zero, PFunDDS.transcriptOutputs] at hy
      · intro hcond
        rw [transcript_zero, visible_transcript_nil, hnil] at hcond
        exact absurd hcond (by simp)
  | succ k ih =>
      have hsync := winnerView_gameTranscript_eq cond s e k
      rcases hfire : e ((PFunDDS.transcript s e k)↓ᵧ) with _ | x
      · rw [transcript_succ_stall (by rw [hsync]; exact hfire),
          transcript_succ_stall hfire]
        exact ih
      · -- the raw run and the game run fire together on the same query
        have hgstep := transcript_succ_fire
          (s := PFunDDS.gameOfDDS cond s) (e := PFunDDS.winnerView e)
          (by rw [hsync]; exact hfire)
        have hrstep := transcript_succ_fire (s := s) (e := e) hfire
        -- the game inputs are the raw inputs
        have hginputs : (PFunDDS.transcript (PFunDDS.gameOfDDS cond s)
            (PFunDDS.winnerView e) k)↓ₓ = (PFunDDS.transcript s e k)↓ₓ := by
          have hproj : PFunDDS.transcript s e k =
              PFunDDS.projT (PFunDDS.transcript (PFunDDS.gameOfDDS cond s)
                (PFunDDS.winnerView e) k) := by
            rw [← PFunDDS.ignoreMBO_gameOfDDS cond s]
            exact PFunDDS.transcript_ignoreMBO (PFunDDS.gameOfDDS cond s) e k
          rw [hproj, PFunDDS.projT_inputs]
        set l := (PFunDDS.transcript s e k)↓ₓ with hl
        have hnextdom : l ++ [x] ∈ PFunDDS.dom s := total _ (by simp)
        have hprev : l ∈ PFunDDS.dom s ∨ l = [] := by
          by_cases hprevne : l = []
          · exact Or.inr hprevne
          · exact Or.inl (total _ hprevne)
        -- the appended game output is the answered pair with the `cond` bit
        have hgout :
            PFunDDS.output (PFunDDS.gameOfDDS cond s)⊥ (l ++ [x])
                (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
              some (PFunDDS.output s (l ++ [x]) hnextdom,
                cond (PFunDDS.ioTranscript s (l ++ [x]) hnextdom)) := by
          have hgamedom : l ++ [x] ∈ PFunDDS.dom (PFunDDS.gameOfDDS cond s) :=
            hnextdom
          have hgameprev :
              l ∈ PFunDDS.dom (PFunDDS.gameOfDDS cond s) ∨ l = [] := hprev
          rw [PFunDDS.output_fullyDefined_append_of_mem
            (PFunDDS.gameOfDDS cond s) l x hgameprev hgamedom]
          rw [PFunDDS.output_gameOfDDS cond s (l ++ [x]) hgamedom hnextdom]
        -- the new bit is `cond` of the new visible transcript
        have hraw_ne : (PFunDDS.transcript s e (k + 1))↓ₓ ≠ [] := by
          rw [hrstep, transcriptInputs_append]
          simp
        have hinputs : (PFunDDS.transcript s e (k + 1))↓ₓ = l ++ [x] := by
          rw [hrstep, transcriptInputs_append]
        have hbit :
            cond (visibleTranscript (PFunDDS.transcript s e (k + 1))) =
              cond (PFunDDS.ioTranscript s (l ++ [x]) hnextdom) := by
          rw [visible_transcript_eq_ioTranscript s total e (k + 1) hraw_ne]
          exact congrArg cond (ioTranscript_congr' s hinputs _ _)
        rw [hgstep, hginputs, hgout, transcriptOutputs_append]
        constructor
        · rintro ⟨y, hy⟩
          rcases List.mem_append.mp hy with hold | hnew
          · -- an earlier bit: monotonicity pushes it to the longer transcript
            have hcondk := ih.mp ⟨y, hold⟩
            refine monotoneCond_eq_true_of_prefix hmono ?_ hcondk
            exact visible_transcript_prefix (by
              rw [hrstep]; exact List.prefix_append _ _)
          · -- the new bit itself
            have hpair := List.mem_singleton.mp hnew
            simp only [Option.some.injEq, Prod.mk.injEq] at hpair
            rw [hbit]
            exact hpair.2.symm
        · intro hcond
          refine ⟨PFunDDS.output s (l ++ [x]) hnextdom, List.mem_append.mpr
            (Or.inr ?_)⟩
          rw [← hbit, hcond]
          exact List.mem_singleton.mpr rfl

/-- **CR18 winning = budgeted transcript predicate** (per realization): a
winner halting within `n` queries wins the game `gameOfDDS cond s` — CR18
Definition 3.23's `Wins`, read at the `DDS` level — exactly when the monotone
`cond` holds of the visible `n`-round transcript against the base system. -/
theorem winsDDS_gameOfDDS_iff_cond (cond : List (X × Y) → Bool)
    (hmono : PFunDDS.MonotoneCond cond) (hnil : cond [] = false)
    (s : PFunDDS.DDS X Y)
    (total : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s)
    (e : PFunDDS.DDE X Y) {n : ℕ} (halts : HaltsWithin e n) :
    winsDDS e (PFunDDS.gameOfDDS cond s) ↔
      cond (visibleTranscript (PFunDDS.transcript s e n)) = true := by
  constructor
  · rintro ⟨k, y, hy⟩
    have hk := (exists_win_entry_gameOfDDS_iff cond hmono hnil s total e k).mp
      ⟨y, hy⟩
    rcases le_total k n with hkn | hnk
    · exact monotoneCond_eq_true_of_prefix hmono
        (visible_transcript_prefix (transcript_prefix_of_le s e hkn)) hk
    · rwa [transcript_eq_of_haltsWithin halts hnk] at hk
  · intro hcond
    obtain ⟨y, hy⟩ :=
      (exists_win_entry_gameOfDDS_iff cond hmono hnil s total e n).mpr hcond
    exact ⟨n, y, hy⟩

/-! ## The AC test value is the CR18 winning probability -/

/-- Event mass is insensitive to changing the event off the support. -/
private theorem mass_congr_on_support {A : Type*}
    (distribution : RandomSystems.Dist A)
    {P Q : A → Prop}
    (same : ∀ a ∈ distribution.support, P a ↔ Q a) :
    distribution.mass P = distribution.mass Q := by
  classical
  unfold Dist.mass Finsupp.sum
  refine Finset.sum_congr rfl fun a member => ?_
  have equivalent := same a (by simpa using member)
  dsimp only
  by_cases holds : P a
  · rw [if_pos holds, if_pos (equivalent.mp holds)]
  · rw [if_neg holds, if_neg (mt equivalent.mpr holds)]

/-- The generic point-mass winning probability: CR18 Definition 4.5 at a
deterministic winner is the game-law mass of its winning set.  Generic in the
winning predicate, so it serves `winProb` and `notWonProb` alike.
UPSTREAM-CANDIDATE: `RandomSystems.MaxWinProb`, next to `winProb_le_weight`. -/
theorem gamePerf_winProb_single {Winner Game : Type*}
    (win : Winner → Game → Prop) (w : Winner)
    (G : RandomSystems.Dist Game) :
    GamePerf.winProb win (Finsupp.single w 1) G = G.mass (win w) := by
  classical
  unfold GamePerf.winProb Dist.mass
  rw [Finsupp.sum_single_index (by simp)]
  refine Finsupp.sum_congr fun g _ => ?_
  by_cases hwin : win w g
  · rw [if_pos hwin, if_pos hwin]; ring
  · rw [if_neg hwin, if_neg hwin]; ring

/-- The mixture bound for CR18 Definition 4.5: if every deterministic winner
on the support has winning mass at most `c`, so does the probabilistic
winner.  The supremum-free core of `blindMaxWinProb_fTransform_le`, over an
arbitrary support condition.
UPSTREAM-CANDIDATE: `RandomSystems.MaxWinProb`, next to `winProb_le_weight`. -/
theorem gamePerf_winProb_le_of_forall_mass_le {Winner Game : Type*}
    (win : Winner → Game → Prop) (G : RandomSystems.Dist Game) (c : NNReal)
    (W : RandomSystems.Dist Winner) (hW : W.isProbDist)
    (h : ∀ w ∈ W.support, G.mass (win w) ≤ c) :
    GamePerf.winProb win W G ≤ c := by
  classical
  unfold GamePerf.winProb
  calc W.sum (fun w wp => G.sum fun g gp => wp * gp * if win w g then 1 else 0)
      ≤ W.sum (fun w wp => wp * c) := by
        refine Finsupp.sum_le_sum fun w hw => ?_
        have hinner : (G.sum fun g gp => W w * gp * if win w g then 1 else 0)
            = W w * G.mass (win w) := by
          rw [Dist.mass, Finsupp.mul_sum]
          refine Finsupp.sum_congr fun g _ => ?_
          by_cases hwin : win w g <;> simp [hwin, mul_comm]
        rw [hinner]
        exact mul_le_mul_of_nonneg_left (h w (by simpa using hw)) (zero_le _)
    _ = (W.sum fun _ wp => wp) * c := by rw [← Finsupp.sum_mul]
    _ = c := by
        have hWsum : (W.sum fun _ wp => wp) = 1 := by
          rw [← Dist.weight_eq_finsupp_sum]
          exact hW
        rw [hWsum, one_mul]

/-- **The bridge: an admitted AC test value is a CR18 game-winning
probability.**  For a total law `S`, a monotone MBO `cond`, and a winner `e`
halting within `n` queries, the acceptance mass of the bounded strict test
"run `e`, accept iff `cond` fired on the visible transcript" is CR18
Definition 4.5's winning probability of `e` against the game `gameOf S cond`
(CR18 §4.11.1). -/
theorem accept_mass_eq_win_prob_gameOf (cond : List (X × Y) → Bool)
    (hmono : PFunDDS.MonotoneCond cond) (hnil : cond [] = false)
    (S : PFunPDS X Y) (total : CondEquiv.TotalOnNonempty S)
    (e : PFunDDS.DDE X Y) {n : ℕ} (halts : HaltsWithin e n) :
    StrictContext.acceptMass
        (StrictContextTotal.testOfTruncDDD (n + 1)
          (PFunDDS.DDD.ofDDE e n
            fun t => cond (visibleTranscript t))) S =
      winProb (Finsupp.single e 1) (gameOf S cond) := by
  rw [show winProb (Finsupp.single e 1) (gameOf S cond) =
      GamePerf.winProb winsDDS (Finsupp.single e 1) (gameOf S cond) from rfl,
    gamePerf_winProb_single, gameOf, Dist.mass_fTransform]
  unfold StrictContext.acceptMass
  refine mass_congr_on_support S fun s hs => ?_
  have stotal := total s hs
  calc true ∈ StrictContext.observe
        (StrictContextTotal.testOfTruncDDD (n + 1)
          (PFunDDS.DDD.ofDDE e n fun t => cond (visibleTranscript t))) s ↔
      PFunDDS.verdict (PFunDDS.truncDDD (n + 1)
        (PFunDDS.DDD.ofDDE e n fun t => cond (visibleTranscript t))) s :=
        StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
          (n + 1) _ s stotal
    _ ↔ PFunDDS.verdict
        (PFunDDS.DDD.ofDDE e n fun t => cond (visibleTranscript t)) s :=
        StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff e n _ s
    _ ↔ cond (visibleTranscript (PFunDDS.transcript s e n)) = true :=
        verdict_ofDDE_iff e n _ s
    _ ↔ winsDDS e (PFunDDS.gameOfDDS cond s) :=
        (winsDDS_gameOfDDS_iff_cond cond hmono hnil s stotal e halts).symm

/-- The complementary reading: the "no win" strict test has acceptance mass
CR18's not-won probability. -/
theorem accept_mass_not_eq_not_won_prob_gameOf (cond : List (X × Y) → Bool)
    (hmono : PFunDDS.MonotoneCond cond) (hnil : cond [] = false)
    (S : PFunPDS X Y) (total : CondEquiv.TotalOnNonempty S)
    (e : PFunDDS.DDE X Y) {n : ℕ} (halts : HaltsWithin e n) :
    StrictContext.acceptMass
        (StrictContextTotal.testOfTruncDDD (n + 1)
          (PFunDDS.DDD.ofDDE e n
            fun t => ! cond (visibleTranscript t))) S =
      notWonProb (Finsupp.single e 1) (gameOf S cond) := by
  rw [show notWonProb (Finsupp.single e 1) (gameOf S cond) =
      GamePerf.winProb (fun w g => ¬ winsDDS w g)
        (Finsupp.single e 1) (gameOf S cond) from rfl,
    gamePerf_winProb_single, gameOf, Dist.mass_fTransform]
  unfold StrictContext.acceptMass
  refine mass_congr_on_support S fun s hs => ?_
  have stotal := total s hs
  calc true ∈ StrictContext.observe
        (StrictContextTotal.testOfTruncDDD (n + 1)
          (PFunDDS.DDD.ofDDE e n fun t => ! cond (visibleTranscript t))) s ↔
      PFunDDS.verdict (PFunDDS.truncDDD (n + 1)
        (PFunDDS.DDD.ofDDE e n fun t => ! cond (visibleTranscript t))) s :=
        StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
          (n + 1) _ s stotal
    _ ↔ PFunDDS.verdict
        (PFunDDS.DDD.ofDDE e n fun t => ! cond (visibleTranscript t)) s :=
        StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff e n _ s
    _ ↔ (! cond (visibleTranscript (PFunDDS.transcript s e n))) = true :=
        verdict_ofDDE_iff e n _ s
    _ ↔ ¬ cond (visibleTranscript (PFunDDS.transcript s e n)) = true := by
        simp
    _ ↔ ¬ winsDDS e (PFunDDS.gameOfDDS cond s) :=
        not_congr
          (winsDDS_gameOfDDS_iff_cond cond hmono hnil s stotal e halts).symm

/-! ## The worked property: unforgeability on the two-interface carrier

Interface `1` of the `TypedFiniteChecks` Boolean carrier is read as a
verification interface; an answer `true` there is an accepted forgery. -/

/-- An answer is a forgery when the verification interface `1` accepted. -/
def forgedAnswer (answer : FlatAnswer testUniverse bitBoundary) : Bool :=
  decide (answer.1 = 1) && answer.2

/-- The forgery MBO: some visible answer was an accepted forgery. -/
def forgeryCond :
    List (Query testUniverse bitBoundary × FlatAnswer testUniverse bitBoundary)
      → Bool :=
  fun t => t.any fun step => forgedAnswer step.2

theorem forgery_cond_nil : forgeryCond [] = false := rfl

/-- The forgery MBO is monotone: an accepted forgery never un-happens
(CR18 Definition 3.22's monotonicity, via `MonotoneCond`). -/
theorem monotoneCond_forgeryCond : PFunDDS.MonotoneCond forgeryCond := by
  intro t₁ t₂ hpre
  obtain ⟨rest, rfl⟩ := hpre
  unfold forgeryCond
  rw [List.any_append]
  cases t₁.any fun step => forgedAnswer step.2 <;> simp

/-- The forgery-winning test of one budgeted adversary: run the environment
`e` for at most `n` queries and accept exactly when a forgery was accepted.
Admitted by the D1 distinguisher class at the `bitBoundary` fibre. -/
def forgeryWinTest (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) (n : ℕ) :
    Phi Interface testUniverse → ℝ≥0∞ :=
  boundaryTest bitBoundary
    (StrictContextTotal.testOfTruncDDD (n + 1)
      (PFunDDS.DDD.ofDDE e n fun t => forgeryCond (visibleTranscript t)))

/-- The defining unforgeability test of one budgeted adversary: accept
exactly when **no** forgery was accepted.  The property-side complement of
`forgeryWinTest`. -/
def unforgeabilityTest (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) (n : ℕ) :
    Phi Interface testUniverse → ℝ≥0∞ :=
  boundaryTest bitBoundary
    (StrictContextTotal.testOfTruncDDD (n + 1)
      (PFunDDS.DDD.ofDDE e n fun t => ! forgeryCond (visibleTranscript t)))

/-- The winning-test family: one forgery game per budgeted adversary. -/
def forgeryWinTests : Set (Phi Interface testUniverse → ℝ≥0∞) :=
  {t | ∃ e n, HaltsWithin e n ∧ t = forgeryWinTest e n}

/-- The defining-test family of the unforgeability property: every budgeted
adversary must fail to provoke acceptance. -/
def unforgeabilityTests : Set (Phi Interface testUniverse → ℝ≥0∞) :=
  {t | ∃ e n, HaltsWithin e n ∧ t = unforgeabilityTest e n}

theorem forgery_win_tests_subset_strict :
    forgeryWinTests ⊆ strictTests Interface testUniverse := by
  rintro t ⟨e, n, -, rfl⟩
  exact boundary_test_mem_strict_tests bitBoundary _

theorem unforgeability_tests_subset_strict :
    unforgeabilityTests ⊆ strictTests Interface testUniverse := by
  rintro t ⟨e, n, -, rfl⟩
  exact boundary_test_mem_strict_tests bitBoundary _

/-- Every admitted forgery test is even budget-admitted: the family lives in
the `q`-bounded subclass at its own budget. -/
theorem forgery_win_test_mem_bounded (e : PFunDDS.DDE
      (Query testUniverse bitBoundary) (FlatAnswer testUniverse bitBoundary))
    (n : ℕ) :
    forgeryWinTest e n ∈ boundedTests Interface testUniverse (n + 1) :=
  boundary_test_mem_bounded_tests bitBoundary (n + 1) _

/-! ## The ideal resource satisfies the property -/

/-- The ideal resource: the never-accepting system — `false` at every
interface, in particular at the verification interface.  This is the D1
witness resource `witnessResource false`. -/
def idealResource : Phi Interface testUniverse := witnessResource false

/-- Every output of the constant system carries its constant bit. -/
theorem output_flatten_constant_snd (b : Bool)
    (l : List (Query testUniverse bitBoundary))
    (h : l ∈ PFunDDS.dom (DependentDDS.flatten (constantSystem b))) :
    (PFunDDS.output (DependentDDS.flatten (constantSystem b)) l h).2 = b :=
  rfl

/-- The forgery MBO never fires against the never-accepting system. -/
theorem forgery_cond_visible_constant_false (e : PFunDDS.DDE
      (Query testUniverse bitBoundary) (FlatAnswer testUniverse bitBoundary))
    (k : ℕ) :
    forgeryCond (visibleTranscript
        (PFunDDS.transcript (DependentDDS.flatten (constantSystem false))
          e k)) = false := by
  rw [forgeryCond, List.any_eq_false]
  intro p hp
  have hanswer : p.2.2 = false :=
    forall_visible_answer_of_forall_output
      (P := fun answer => answer.2 = false)
      (DependentDDS.flatten (constantSystem false))
      (constant_system_total false)
      (fun l h => output_flatten_constant_snd false l h) e k p hp
  unfold forgedAnswer
  rw [hanswer]
  simp

/-- The ideal resource passes every defining unforgeability test with
certainty. -/
theorem unforgeability_test_ideal_eq_one (e : PFunDDS.DDE
      (Query testUniverse bitBoundary) (FlatAnswer testUniverse bitBoundary))
    (n : ℕ) :
    unforgeabilityTest e n idealResource = 1 := by
  show boundaryTest bitBoundary _
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw false)⟩ = 1
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_one
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  refine mass_single_one_of_mem ?_
  refine (StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
    (n + 1) _ _ (constant_system_total false)).mpr ?_
  refine (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff e n _ _).mpr ?_
  refine (verdict_ofDDE_iff e n _ _).mpr ?_
  rw [forgery_cond_visible_constant_false e n]
  rfl

/-- **The ideal resource satisfies the unforgeability property
specification** — `propSpec` membership, proved test by test. -/
theorem ideal_mem_prop_spec :
    idealResource ∈ propSpec unforgeabilityTests := by
  rintro t ⟨e, n, -, rfl⟩
  exact unforgeability_test_ideal_eq_one e n

/-- No budgeted adversary wins the forgery game against the ideal resource:
`gameSpec` membership at bound `0`. -/
theorem forgery_win_test_ideal_eq_zero (e : PFunDDS.DDE
      (Query testUniverse bitBoundary) (FlatAnswer testUniverse bitBoundary))
    (n : ℕ) :
    forgeryWinTest e n idealResource = 0 := by
  show boundaryTest bitBoundary _
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw false)⟩ = 0
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_zero
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  refine mass_single_one_of_not_mem ?_
  intro haccept
  have hverdict := (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
      e n _ _).mp
    ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
      (n + 1) _ _ (constant_system_total false)).mp haccept)
  have hcond := (verdict_ofDDE_iff e n _ _).mp hverdict
  rw [forgery_cond_visible_constant_false e n] at hcond
  exact absurd hcond (by simp)

theorem ideal_mem_game_spec_zero :
    idealResource ∈ gameSpec forgeryWinTests 0 := by
  rintro t ⟨e, n, -, rfl⟩
  rw [forgery_win_test_ideal_eq_zero e n]

/-! ## Non-vacuity: a degenerate resource genuinely fails the property -/

/-- The one-query break-in adversary: submit `true` at the verification
interface, then stop. -/
def breakInEnvironment :
    PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)
  | [] => some ⟨1, true⟩
  | _ :: _ => none

theorem break_in_halts : HaltsWithin breakInEnvironment 1 := by
  intro h hlen
  cases h with
  | nil => simp at hlen
  | cons _ _ => rfl

theorem unforgeability_test_break_in_mem :
    unforgeabilityTest breakInEnvironment 1 ∈ unforgeabilityTests :=
  ⟨breakInEnvironment, 1, break_in_halts, rfl⟩

/-- The one-round break-in transcript against a constant system. -/
theorem transcript_flatten_constant_break_in (b : Bool) :
    PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
        breakInEnvironment 1 =
      [(⟨1, true⟩, some ⟨1, b⟩)] := by
  have fires : breakInEnvironment
      ((PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
        breakInEnvironment 0)↓ᵧ) = some ⟨1, true⟩ := rfl
  rw [transcript_succ_fire fires]
  have output_break : PFunDDS.output
      ((DependentDDS.flatten (constantSystem b))⊥)
      (((PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
          breakInEnvironment 0)↓ₓ) ++ [⟨1, true⟩])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
      some ⟨1, b⟩ :=
    PFunDDS.output_fullyDefined_append_of_mem
      (DependentDDS.flatten (constantSystem b)) [] ⟨1, true⟩
      (Or.inr rfl)
      (constant_system_total b [⟨1, true⟩] (by simp))
  rw [output_break]
  rfl

/-- **The degenerate always-accepting resource fails the defining test with
value `0`** — the property is a real predicate, not a tautology. -/
theorem unforgeability_test_forgeable_eq_zero :
    unforgeabilityTest breakInEnvironment 1 (witnessResource true) = 0 := by
  show boundaryTest bitBoundary _
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw true)⟩ = 0
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_zero
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  refine mass_single_one_of_not_mem ?_
  intro haccept
  have hverdict := (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
      breakInEnvironment 1 _ _).mp
    ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
      2 _ _ (constant_system_total true)).mp haccept)
  have hcond := (verdict_ofDDE_iff breakInEnvironment 1 _ _).mp hverdict
  rw [transcript_flatten_constant_break_in true] at hcond
  exact absurd hcond (by decide)

/-- The degenerate resource is **outside** the property specification. -/
theorem forgeable_not_mem_prop_spec :
    witnessResource true ∉ propSpec unforgeabilityTests := by
  intro hmem
  have := hmem _ unforgeability_test_break_in_mem
  rw [unforgeability_test_forgeable_eq_zero] at this
  exact absurd this (by simp)

/-- The break-in adversary wins the forgery game against the degenerate
resource with certainty: the game itself is winnable. -/
theorem forgery_win_test_forgeable_eq_one :
    forgeryWinTest breakInEnvironment 1 (witnessResource true) = 1 := by
  show boundaryTest bitBoundary _
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw true)⟩ = 1
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_one
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  refine mass_single_one_of_mem ?_
  refine (StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
    2 _ _ (constant_system_total true)).mpr ?_
  refine (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
    breakInEnvironment 1 _ _).mpr ?_
  refine (verdict_ofDDE_iff breakInEnvironment 1 _ _).mpr ?_
  rw [transcript_flatten_constant_break_in true]
  decide

/-- The degenerate resource sits at class distance exactly `1` from the
ideal (the D1 receipt), so the `1 - ε` transfer correctly degenerates only
at total insecurity. -/
example :
    (strictTestClass Interface testUniverse).edistD
      (witnessResource true) idealResource = 1 :=
  strict_test_class_edistD_witness_eq_one

/-! ## The property transfer, end to end -/

/-- **Property transfer (LiuMau20 idiom, `1 - ε` form)**: every resource
within class distance `ε` of the ideal passes every defining unforgeability
test with probability at least `1 - ε` — the ideal's *guarantee*, not merely
its distance, reaches the real world. -/
theorem unforgeability_transfer {real : Phi Interface testUniverse}
    {ε : ℝ≥0∞}
    (close : (strictTestClass Interface testUniverse).edistD
      real idealResource ≤ ε) :
    ∀ t ∈ unforgeabilityTests, 1 - ε ≤ t real :=
  fun _t ht =>
    one_tsub_le_test_of_close (strictTestClass Interface testUniverse)
      unforgeability_tests_subset_strict ideal_mem_prop_spec close ht

/-- Property transfer from the installed contextual metric, via the sound
direction `edistD ≤ edist` of D1. -/
theorem unforgeability_transfer_of_edist {real : Phi Interface testUniverse}
    {ε : ℝ≥0∞} (close : edist real idealResource ≤ ε) :
    ∀ t ∈ unforgeabilityTests, 1 - ε ≤ t real :=
  unforgeability_transfer
    ((strict_test_class_edistD_le_edist real idealResource).trans close)

/-- **Game transfer (`gameSpec` route)**: every resource within class
distance `ε` of the ideal is in the forgery game specification at bound `ε` —
`gameSpec_of_edistD_le` at the ideal's perfect bound. -/
theorem real_mem_game_spec {real : Phi Interface testUniverse} {ε : ℝ≥0∞}
    (close : (strictTestClass Interface testUniverse).edistD
      real idealResource ≤ ε) :
    real ∈ gameSpec forgeryWinTests ε := by
  have transferred := gameSpec_of_edistD_le
    (strictTestClass Interface testUniverse)
    forgery_win_tests_subset_strict ideal_mem_game_spec_zero close
  rwa [zero_add] at transferred

/-! ## The CR18 reading of the transferred guarantee -/

/-- The admitted forgery test *is* the CR18 winning probability, on the
typed carrier: evaluating `forgeryWinTest e n` on a total law at the
`bitBoundary` fibre is CR18 Definition 4.5's `winProb` of the winner `e`
against the forgery game `gameOf (flattened law) forgeryCond`. -/
theorem forgery_win_test_eq_win_prob
    (P : DependentPDS.Prob testUniverse bitBoundary)
    (total : CondEquiv.TotalOnNonempty (DependentPDS.flatten P.val))
    (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) {n : ℕ}
    (halts : HaltsWithin e n) :
    forgeryWinTest e n ⟨bitBoundary, DependentRandomSystem.ofProb P⟩ =
      (winProb (Finsupp.single e 1)
        (gameOf (DependentPDS.flatten P.val) forgeryCond) : ℝ≥0∞) := by
  show boundaryTest bitBoundary _ _ = _
  rw [boundary_test_same, strict_mass_of_prob]
  exact_mod_cast
    accept_mass_eq_win_prob_gameOf forgeryCond monotoneCond_forgeryCond
      forgery_cond_nil (DependentPDS.flatten P.val) total e halts

/-- The defining unforgeability test *is* the CR18 not-won probability. -/
theorem unforgeability_test_eq_not_won_prob
    (P : DependentPDS.Prob testUniverse bitBoundary)
    (total : CondEquiv.TotalOnNonempty (DependentPDS.flatten P.val))
    (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) {n : ℕ}
    (halts : HaltsWithin e n) :
    unforgeabilityTest e n ⟨bitBoundary, DependentRandomSystem.ofProb P⟩ =
      (notWonProb (Finsupp.single e 1)
        (gameOf (DependentPDS.flatten P.val) forgeryCond) : ℝ≥0∞) := by
  show boundaryTest bitBoundary _ _ = _
  rw [boundary_test_same, strict_mass_of_prob]
  exact_mod_cast
    accept_mass_not_eq_not_won_prob_gameOf forgeryCond
      monotoneCond_forgeryCond forgery_cond_nil
      (DependentPDS.flatten P.val) total e halts

/-- **The transferred guarantee in CR18 terms**: for a real resource within
class distance `ε` of the ideal, every winner halting within `n` queries
wins the forgery game of the real flattened law with probability at most
`ε` — CR18 Definition 4.5 `winProb` against CR18 §4.11.1 `gameOf`, obtained
through the AC `gameSpec` transfer rather than any RS-side argument. -/
theorem win_prob_forgery_le
    (P : DependentPDS.Prob testUniverse bitBoundary)
    (total : CondEquiv.TotalOnNonempty (DependentPDS.flatten P.val))
    {ε : ℝ≥0∞}
    (close : (strictTestClass Interface testUniverse).edistD
      ⟨bitBoundary, DependentRandomSystem.ofProb P⟩ idealResource ≤ ε)
    (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) {n : ℕ}
    (halts : HaltsWithin e n) :
    (winProb (Finsupp.single e 1)
      (gameOf (DependentPDS.flatten P.val) forgeryCond) : ℝ≥0∞) ≤ ε := by
  have hmem : forgeryWinTest e n ∈ forgeryWinTests := ⟨e, n, halts, rfl⟩
  have hbound := real_mem_game_spec close _ hmem
  rwa [forgery_win_test_eq_win_prob P total e halts] at hbound

/-- The complementary `1 - ε` form in CR18 terms: the not-won probability of
every budgeted winner is at least `1 - ε`. -/
theorem not_won_prob_forgery_ge
    (P : DependentPDS.Prob testUniverse bitBoundary)
    (total : CondEquiv.TotalOnNonempty (DependentPDS.flatten P.val))
    {ε : ℝ≥0∞}
    (close : (strictTestClass Interface testUniverse).edistD
      ⟨bitBoundary, DependentRandomSystem.ofProb P⟩ idealResource ≤ ε)
    (e : PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)) {n : ℕ}
    (halts : HaltsWithin e n) :
    1 - ε ≤ (notWonProb (Finsupp.single e 1)
      (gameOf (DependentPDS.flatten P.val) forgeryCond) : ℝ≥0∞) := by
  have hmem : unforgeabilityTest e n ∈ unforgeabilityTests :=
    ⟨e, n, halts, rfl⟩
  have hbound := unforgeability_transfer close _ hmem
  rwa [unforgeability_test_eq_not_won_prob P total e halts] at hbound

/-- The probabilistic-winner form: every *winner distribution* supported on
`n`-halting winners — the CR18 Definition 4.17 quantification, restricted to
the budget — wins the forgery game of the real law with probability at most
`ε`.  The mixture bound over `win_prob_forgery_le`. -/
theorem win_prob_dist_forgery_le
    (P : DependentPDS.Prob testUniverse bitBoundary)
    (total : CondEquiv.TotalOnNonempty (DependentPDS.flatten P.val))
    {ε : ℝ≥0}
    (close : (strictTestClass Interface testUniverse).edistD
      ⟨bitBoundary, DependentRandomSystem.ofProb P⟩ idealResource ≤
        (ε : ℝ≥0∞))
    {n : ℕ} (W : RandomSystems.Dist (PFunDDS.Winner
      (Query testUniverse bitBoundary) (FlatAnswer testUniverse bitBoundary)))
    (hW : W.isProbDist) (hsupp : ∀ w ∈ W.support, HaltsWithin w n) :
    winProb W (gameOf (DependentPDS.flatten P.val) forgeryCond) ≤ ε := by
  refine gamePerf_winProb_le_of_forall_mass_le winsDDS _ ε W hW
    fun w hw => ?_
  have hone := win_prob_forgery_le P total close w (hsupp w hw)
  have hmass : (gameOf (DependentPDS.flatten P.val) forgeryCond).mass
      (winsDDS w) =
      winProb (Finsupp.single w 1)
        (gameOf (DependentPDS.flatten P.val) forgeryCond) :=
    (gamePerf_winProb_single winsDDS w _).symm
  rw [hmass]
  exact_mod_cast hone

/-! ## Budget gates

The forgery tests are graded by adversary budget; reading the grading as an
`AbstractCrypto.GateHierarchy` makes the budget ordering an instance of the
generic gate-transfer principle. -/

/-- The forgery tests of budget at most `k`. -/
def forgeryGate (k : ℕ) : Set (Phi Interface testUniverse → ℝ≥0∞) :=
  {t | ∃ e n, n ≤ k ∧ HaltsWithin e n ∧ t = forgeryWinTest e n}

theorem forgery_gate_subset_win_tests (k : ℕ) :
    forgeryGate k ⊆ forgeryWinTests := by
  rintro t ⟨e, n, -, hh, ht⟩
  exact ⟨e, n, hh, ht⟩

/-- The budget-graded forgery gate hierarchy: a larger budget admits more
forgery tests. -/
def forgeryGateHierarchy : GateHierarchy (Phi Interface testUniverse) where
  gate := forgeryGate
  mono := fun _i _j hij _t ht =>
    ht.imp fun _e h => h.imp fun _n h => ⟨h.1.trans hij, h.2⟩

/-- Every budgeted gate inherits the transferred game bound, and the generic
`GateHierarchy.transfer` moves it down the budget order. -/
theorem real_mem_game_spec_gate {real : Phi Interface testUniverse}
    {ε : ℝ≥0∞}
    (close : (strictTestClass Interface testUniverse).edistD
      real idealResource ≤ ε) (k : ℕ) :
    real ∈ gameSpec (forgeryGateHierarchy.gate k) ε :=
  gameSpec_antitone (forgery_gate_subset_win_tests k)
    (real_mem_game_spec close)

example {real : Phi Interface testUniverse} {ε : ℝ≥0∞}
    (h : real ∈ gameSpec (forgeryGateHierarchy.gate 7) ε) :
    real ∈ gameSpec (forgeryGateHierarchy.gate 3) ε :=
  forgeryGateHierarchy.transfer (by omega) h

end

end RandomSystemsCC.TypedPropertyTransfer
