/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedDistinguisherChecks
import RandomSystems.Complexity.Asymptotic
import AbstractCrypto.Relaxations

/-!
# Feasible test subcarriers and cost budgets on the typed RS carrier

AC integration receipt 8 (`../abstract-crypto/LIBRARY_GUIDE.md` §9):
"feasible resource/converter/test subcarriers and cost closure if a
computational claim is made."  This module connects the RS complexity layer
(`RandomSystems.Complexity`) to the strict-observation distinguisher class of
`RandomSystemsCC.TypedDistinguisher`, producing the first cost-graded
feasible test subcarrier on the typed carrier and the first statement in the
estate whose error is a `reductionRelaxation` budget with
`Negligible`/`PolyBoundedCost` at the asymptotic boundary.

## The cost semantics of a strict test

The RS complexity layer is machine-model-free: a `CostModel Solver Label` is
a *supplied* semantic function `Solver → Cost Label`, and AC deliberately
provides no machine or asymptotic cost model of its own
(`LIBRARY_GUIDE.md` §4).  The only cost coordinates of a strict test that
are definable without inventing a machine model are query-based, and they
fill both coordinates of `Cost I` (`RandomSystems/Complexity/Cost.lean`)
exactly:

* `Cost.intrinsic` — the *round budget*: the truncation depth `q` of the
  CR18 reader (`PFunDDS.truncDDD`, CR18 §4.10.1), i.e. the number of
  interaction rounds the test may drive.  This is the scalar budget already
  used by D1's `boundedTests`.
* `Cost.calls i` — the *per-interface call budget*: `callsTo` counts, along
  any answer history, the prefixes at which the reader's next move is a
  query owned by interface `i`; `CallsWithin` is the certificate that every
  count stays within the budget.

`costBoundedTests I U c` refines `boundedTests I U (Cost.intrinsic c)` by
the calls certificate; budgets filter upward in the `Cost` partial order
(`cost_bounded_tests_mono`, a genuine use of `Cost.le_iff`'s coordinatewise
order), and the induced class metric is dominated by the D1 budgeted metric,
the full class metric, and the installed contextual metric, in that chain.

## Non-vacuity — the restriction restricts

Two directions, both on the concrete two-interface Boolean carrier of
`TypedFiniteChecks`:

* the D1 witness test is admitted at the explicit budget
  `probeCost = ⟨2 rounds, 1 call to interface 0, 0 to interface 1⟩` and
  separates the witness resource pair at class distance exactly `1`
  (`cost_bounded_class_edistD_witness_eq_one`);
* a **starved interface is invisible**
  (`transcript_eq_of_calls_to_eq_zero`): a reader whose certified call
  count at interface `j` is zero generates identical transcripts against
  any two total systems that agree away from `j`.  Consequently the
  interface-`1` probe `sideTest` is in the full strict class but in **no**
  cost class with `Cost.calls c 1 = 0`
  (`side_test_not_mem_cost_bounded_tests`), and on a resource pair
  differing only at interface `1` the starved class metric is `0` while the
  full class metric is `1` (`cost_bounded_edistD_side_eq_zero` versus
  `strict_test_class_edistD_side_eq_one`).

## Cost closure — what holds and what is genuinely missing

MauRen11 §6.3 Definition 17 (p. 14) calls a feasibility notion
`(Φf, Σf, Df)` *closed* when the algebra restricted to `Φf`, `Σf` is still a
cryptographic algebra and `Df` is compatible with it — in particular
`DfΣfi ⊆ Df`, closure of the feasible tests under emulation of feasible
converters.  On this carrier:

* the abstract budget-transport closure holds and is consumed below:
  JM20 Theorem 3's `attachBudget`/`smul_reductionRelaxation_subset` applies
  verbatim to `strictTestClass` (D1 proved `DΣ ⊆ D` for the full class);
* at a **fixed** cost the class closes under the neutral converter only, so
  `costBoundedStrictTestClass` is honest about its converter set — the
  trivial submonoid — exactly as D1's `boundedStrictTestClass`;
* the graded closure "absorbing a converter of cost `c'` maps
  `costBoundedTests c` into `costBoundedTests (costMap c' c)`" is **not
  provable with the current estate**.  The missing piece is a *counting*
  version of context absorption: re-presenting the absorbed test
  `StrictContext.absorb (testOfTruncDDD q d) γ` as a truncated reader whose
  per-interface counts are the composition of `d`'s counts with `γ`'s
  per-call counts.  The estate has absorption without counting at three
  layers (`StrictContext.absorb` at the protocol level, `absorb` in
  `RandomSystems/AbsorbDPI.lean` for step converters, `composeOneCallDDD`
  in `RandomSystems/Complexity/ConverterBridge.lean` for one-call
  converters) and a *streak* bound through serial composition
  (`serial_composition_has_finite_query_bound` in
  `RandomSystems/ComposeRealization.lean`, whose proof internally
  establishes the explicit bound `B₁·B₂ + 1`),
  but no absorption theorem tracks per-interface counts.  Until that
  theorem exists, Definition 17's `DfΣfi ⊆ Df` on this carrier is available
  only for the neutral converter, and this module says so rather than
  packaging a vacuous closure.

## The worked computational statement

`noisyResource p` answers `true` with probability `p` and `false` otherwise
at every interface; the ideal resource never answers `true`.  Every strict
test — a fortiori every cost-budgeted test — has advantage at most `p`
between the two (`adv_le_noise`), so the noisy resource lies in the
`reductionRelaxation` of the ideal at the constant per-test budget `p`
(`noisy_mem_reductionRelaxation`) — a JM20 Definition 3 statement on the
concrete carrier, not a scalar `eball`.  The bound is *tight*: the class
distance is exactly `p` (`strict_test_class_edistD_noisy_eq`), so the budget
is the true distinguishing power, not an over-approximation.
`FeasiblyClose` packages the asymptotic boundary — a polynomially bounded
cost family (`PolyBoundedCost`) and a negligible error family
(`Negligible`), both from `RandomSystems.Complexity.Asymptotic` — and
`noisy_family_feasibly_close` discharges it for the noise rate
`(n + 1)⁻ⁿ`.
-/

namespace RandomSystemsCC.TypedFeasibility

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open RandomSystemsCC.TypedDistinguisher
open scoped ENNReal NNReal PFunDDS

noncomputable section

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code]

/-! ## Per-interface call counting on a CR18 reader -/

/-- The per-interface call count of a CR18 reader along one answer history:
the number of history prefixes (including the full history) at which the
reader's next move is a query owned by interface `i`.  This is the
machine-model-free call coordinate of `Cost I` for an interactive test —
the reader performs no work observable at the carrier other than its
queries. -/
def callsTo {boundary : Boundary U I}
    (reader : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary))
    (i : I) (history : List (Option (FlatAnswer U boundary))) : ℕ :=
  (List.range (history.length + 1)).countP fun k =>
    match reader.val (history.take k) with
    | Sum.inl query => decide (query.1 = i)
    | Sum.inr _ => false

omit [DecidableEq U.Code] in
/-- A pending query is counted: firing `query` on `history` certifies at
least one call to the query's interface. -/
theorem one_le_calls_to_of_val_eq_inl {boundary : Boundary U I}
    {reader : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary)}
    {history : List (Option (FlatAnswer U boundary))}
    {query : Query U boundary}
    (fires : reader.val history = Sum.inl query) :
    1 ≤ callsTo reader query.1 history := by
  unfold callsTo
  rw [Nat.one_le_iff_ne_zero, Ne, List.countP_eq_zero]
  intro all
  have := all history.length (List.mem_range.mpr (Nat.lt_succ_self _))
  rw [List.take_length, fires] at this
  simp at this

/-- The call-budget certificate: every per-interface count of the reader
stays within the call coordinates of `c`. -/
def CallsWithin {boundary : Boundary U I} (c : Cost I)
    (reader : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary)) :
    Prop :=
  ∀ (history : List (Option (FlatAnswer U boundary))) (i : I),
    callsTo reader i history ≤ Cost.calls c i

/-! ## The cost-bounded test subcarrier -/

/-- The `Cost`-budgeted test set: every observed fibre reads through a CR18
reader truncated at the intrinsic (round) budget — exactly D1's
`boundedTests` presentation — that additionally certifies the per-interface
call budgets.  This is the feasible test subcarrier of AC integration
receipt 8, graded by `RandomSystems.Cost`. -/
def costBoundedTests (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] (c : Cost I) :
    Set (Phi I U → ℝ≥0∞) :=
  {t | ∀ boundary : Boundary U I,
    (∀ system : DependentRandomSystem U boundary,
      t ⟨boundary, system⟩ = 0) ∨
    ∃ d : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary),
      CallsWithin c (PFunDDS.truncDDD (Cost.intrinsic c) d) ∧
      ∀ system : DependentRandomSystem U boundary,
        t ⟨boundary, system⟩ =
          (strictMass
              (StrictContextTotal.testOfTruncDDD (Cost.intrinsic c) d)
              system : ℝ≥0∞)}

/-- Dropping the call budgets recovers D1's query-budgeted class at the
round budget. -/
theorem cost_bounded_tests_subset_bounded_tests (c : Cost I) :
    costBoundedTests I U c ⊆ boundedTests I U (Cost.intrinsic c) := by
  intro t admitted boundary
  rcases admitted boundary with blind | ⟨d, -, observed⟩
  · exact Or.inl blind
  · exact Or.inr ⟨d, observed⟩

/-- Every cost-budgeted test is an admitted strict test. -/
theorem cost_bounded_tests_subset_strict_tests (c : Cost I) :
    costBoundedTests I U c ⊆ strictTests I U :=
  (cost_bounded_tests_subset_bounded_tests c).trans
    (bounded_tests_subset_strict_tests (Cost.intrinsic c))

/-- One certified boundary observation, admitted into the cost class. -/
theorem boundary_test_mem_cost_bounded_tests (boundary : Boundary U I)
    (c : Cost I)
    (d : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary))
    (certified : CallsWithin c (PFunDDS.truncDDD (Cost.intrinsic c) d)) :
    boundaryTest boundary
        (StrictContextTotal.testOfTruncDDD (Cost.intrinsic c) d) ∈
      costBoundedTests I U c := by
  intro fibre
  by_cases same : fibre = boundary
  · subst same
    exact Or.inr ⟨d, certified, fun system => boundary_test_same _ system⟩
  · exact Or.inl fun system => boundary_test_ne _ same

/-- Cost budgets filter upward in the coordinatewise `Cost` order: a test
certified at `small` is certified at every `large ≥ small`.  The round
coordinate shifts by re-truncation (`truncDDD_truncDDD_of_le`); the call
coordinates shift by `Cost.calls_le_of_le`. -/
theorem cost_bounded_tests_mono {small large : Cost I}
    (smaller : small ≤ large) :
    costBoundedTests I U small ⊆ costBoundedTests I U large := by
  intro t admitted boundary
  rcases admitted boundary with blind | ⟨d, certified, observed⟩
  · exact Or.inl blind
  · have intrinsicLe : Cost.intrinsic small ≤ Cost.intrinsic large :=
      Cost.intrinsic_le_of_le smaller
    refine Or.inr ⟨PFunDDS.truncDDD (Cost.intrinsic small) d, ?_, ?_⟩
    · intro history i
      rw [truncDDD_truncDDD_of_le intrinsicLe d]
      exact (certified history i).trans (Cost.calls_le_of_le smaller i)
    · intro system
      rw [observed system, test_of_truncDDD_truncDDD_of_le intrinsicLe d]

/-- **The cost-budgeted distinguisher class.**  As with D1's
`boundedStrictTestClass`, for a fixed budget MauRen11 Definition 16's
emulation closure holds only for the neutral converter — a nontrivial
converter changes both the round and the call budgets, and re-presenting
the absorbed test with composed counts is exactly the missing counting
absorption theorem described in the module header — so the class is honest
about its converter set: the trivial submonoid. -/
def costBoundedStrictTestClass (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] [DecidableEq U.Code] [Fintype I] (c : Cost I) :
    DistinguisherClass (⊥ : Submonoid (Protocol I U)) (Phi I U) where
  tests := costBoundedTests I U c
  test_le_one := by
    intro t admitted resource
    obtain ⟨boundary, system⟩ := resource
    rcases admitted boundary with blind | ⟨d, -, observed⟩
    · rw [blind system]
      exact zero_le_one
    · rw [observed system]
      exact_mod_cast strict_mass_le_one _ system
  test_attach := by
    intro neutral t admitted
    have isOne : (neutral : Protocol I U) = 1 :=
      Submonoid.mem_bot.mp neutral.property
    have unchanged :
        (fun resource : Phi I U => t (neutral • resource)) = t := by
      funext resource
      have : neutral • resource = resource := by
        show (neutral : Protocol I U) • resource = resource
        rw [isOne, one_smul]
      rw [this]
    rw [unchanged]
    exact admitted

@[simp]
theorem cost_bounded_strict_test_class_tests [Fintype I] (c : Cost I) :
    (costBoundedStrictTestClass I U c).tests = costBoundedTests I U c :=
  rfl

/-- The cost-class metric is dominated by D1's query-budgeted class metric
at the round budget. -/
theorem cost_bounded_edistD_le_bounded_edistD [Fintype I] (c : Cost I)
    (left right : Phi I U) :
    (costBoundedStrictTestClass I U c).edistD left right ≤
      (boundedStrictTestClass I U (Cost.intrinsic c)).edistD left right := by
  refine iSup₂_le fun t admitted => ?_
  exact (boundedStrictTestClass I U (Cost.intrinsic c)).adv_le_edistD
    (cost_bounded_tests_subset_bounded_tests c admitted) left right

/-- The cost-class metric is dominated by the full class metric and hence,
by D1's `strict_test_class_edistD_le_edist`, by the installed contextual
metric. -/
theorem cost_bounded_edistD_le_edist [Fintype I] (c : Cost I)
    (left right : Phi I U) :
    (costBoundedStrictTestClass I U c).edistD left right ≤
      edist left right :=
  ((cost_bounded_edistD_le_bounded_edistD c left right).trans
    (bounded_edistD_le_edistD (Cost.intrinsic c) left right)).trans
    (strict_test_class_edistD_le_edist left right)

/-! ## A starved interface is invisible

The lower-bound engine for the non-vacuity gate: a reader whose certified
call count at interface `j` is zero can never route a query to `j`, so its
interaction transcripts against two total systems that agree away from `j`
coincide — the class genuinely cannot see behind a call budget of zero. -/

omit [DecidableEq U.Code] in
/-- Transcript coupling across a starved interface: if every per-history
call count of `reader` at `j` is zero, and the two total systems agree on
every history avoiding `j`, then the interaction transcripts agree at every
round and never touch `j`. -/
theorem transcript_eq_of_calls_to_eq_zero {boundary : Boundary U I} {j : I}
    {reader : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary)}
    (starved : ∀ history, callsTo reader j history = 0)
    {left right : DependentDDS U boundary}
    (totalLeft : ∀ l : List (Query U boundary), l ≠ [] →
      l ∈ PFunDDS.dom (DependentDDS.flatten left))
    (totalRight : ∀ l : List (Query U boundary), l ≠ [] →
      l ∈ PFunDDS.dom (DependentDDS.flatten right))
    (agree : ∀ (l : List (Query U boundary))
      (memLeft : l ∈ PFunDDS.dom (DependentDDS.flatten left))
      (memRight : l ∈ PFunDDS.dom (DependentDDS.flatten right)),
      (∀ q ∈ l, q.1 ≠ j) →
      PFunDDS.output (DependentDDS.flatten left) l memLeft =
        PFunDDS.output (DependentDDS.flatten right) l memRight) :
    ∀ n : ℕ,
      PFunDDS.transcript (DependentDDS.flatten left)
          (PFunDDS.ddToDDE reader) n =
        PFunDDS.transcript (DependentDDS.flatten right)
          (PFunDDS.ddToDDE reader) n ∧
      ∀ q ∈ (PFunDDS.transcript (DependentDDS.flatten left)
          (PFunDDS.ddToDDE reader) n)↓ₓ, q.1 ≠ j := by
  intro n
  induction n with
  | zero =>
      refine ⟨rfl, ?_⟩
      intro q hq
      simp [PFunDDS.transcriptInputs] at hq
  | succ n ih =>
      obtain ⟨same, avoids⟩ := ih
      rcases hfire : PFunDDS.ddToDDE reader
          ((PFunDDS.transcript (DependentDDS.flatten left)
            (PFunDDS.ddToDDE reader) n)↓ᵧ) with _ | query
      · have hfireRight : PFunDDS.ddToDDE reader
            ((PFunDDS.transcript (DependentDDS.flatten right)
              (PFunDDS.ddToDDE reader) n)↓ᵧ) = none := by
          rw [← same]
          exact hfire
        rw [transcript_succ_stall hfire, transcript_succ_stall hfireRight]
        exact ⟨same, avoids⟩
      · -- the fired query cannot be owned by the starved interface
        have queryAvoids : query.1 ≠ j := by
          intro hj
          have counted := one_le_calls_to_of_val_eq_inl
            (PFunDDS.ddToDDE_eq_some_iff.mp hfire)
          rw [hj, starved] at counted
          exact absurd counted (by norm_num)
        have hfireRight : PFunDDS.ddToDDE reader
            ((PFunDDS.transcript (DependentDDS.flatten right)
              (PFunDDS.ddToDDE reader) n)↓ᵧ) = some query := by
          rw [← same]
          exact hfire
        have stepLeft := transcript_succ_fire
          (s := DependentDDS.flatten left) hfire
        have stepRight := transcript_succ_fire
          (s := DependentDDS.flatten right) hfireRight
        set inputs := (PFunDDS.transcript (DependentDDS.flatten left)
          (PFunDDS.ddToDDE reader) n)↓ₓ with hinputs
        have inputsRight : (PFunDDS.transcript (DependentDDS.flatten right)
            (PFunDDS.ddToDDE reader) n)↓ₓ = inputs := by
          rw [← same]
        have nextLeft : inputs ++ [query] ∈
            PFunDDS.dom (DependentDDS.flatten left) :=
          totalLeft _ (by simp)
        have nextRight : inputs ++ [query] ∈
            PFunDDS.dom (DependentDDS.flatten right) :=
          totalRight _ (by simp)
        have prevLeft : inputs ∈ PFunDDS.dom (DependentDDS.flatten left) ∨
            inputs = [] := by
          by_cases hne : inputs = []
          · exact Or.inr hne
          · exact Or.inl (totalLeft _ hne)
        have prevRight : inputs ∈ PFunDDS.dom (DependentDDS.flatten right) ∨
            inputs = [] := by
          by_cases hne : inputs = []
          · exact Or.inr hne
          · exact Or.inl (totalRight _ hne)
        have nextAvoids : ∀ q ∈ inputs ++ [query], q.1 ≠ j := by
          intro q hq
          rcases List.mem_append.mp hq with hold | hnew
          · exact avoids q hold
          · rw [List.mem_singleton.mp hnew]
            exact queryAvoids
        have outLeft := PFunDDS.output_fullyDefined_append_of_mem
          (DependentDDS.flatten left) inputs query prevLeft nextLeft
        have outRight := PFunDDS.output_fullyDefined_append_of_mem
          (DependentDDS.flatten right) inputs query prevRight nextRight
        have outAgree := agree (inputs ++ [query]) nextLeft nextRight
          nextAvoids
        constructor
        · rw [stepLeft, stepRight, same, inputsRight, outLeft, outRight,
            outAgree]
        · rw [stepLeft, transcriptInputs_append]
          intro q hq
          rcases List.mem_append.mp hq with hold | hnew
          · exact avoids q hold
          · rw [List.mem_singleton.mp hnew]
            exact queryAvoids

omit [DecidableEq U.Code] in
/-- Verdict coupling across a starved interface: the reader's verdict is
the same on both systems. -/
theorem verdict_iff_of_calls_to_eq_zero {boundary : Boundary U I} {j : I}
    {reader : PFunDDS.DDD (Query U boundary) (FlatAnswer U boundary)}
    (starved : ∀ history, callsTo reader j history = 0)
    {left right : DependentDDS U boundary}
    (totalLeft : ∀ l : List (Query U boundary), l ≠ [] →
      l ∈ PFunDDS.dom (DependentDDS.flatten left))
    (totalRight : ∀ l : List (Query U boundary), l ≠ [] →
      l ∈ PFunDDS.dom (DependentDDS.flatten right))
    (agree : ∀ (l : List (Query U boundary))
      (memLeft : l ∈ PFunDDS.dom (DependentDDS.flatten left))
      (memRight : l ∈ PFunDDS.dom (DependentDDS.flatten right)),
      (∀ q ∈ l, q.1 ≠ j) →
      PFunDDS.output (DependentDDS.flatten left) l memLeft =
        PFunDDS.output (DependentDDS.flatten right) l memRight) :
    (PFunDDS.verdict reader (DependentDDS.flatten left) ↔
      PFunDDS.verdict reader (DependentDDS.flatten right)) := by
  unfold PFunDDS.verdict
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← (transcript_eq_of_calls_to_eq_zero starved totalLeft totalRight
      agree n).1]
    exact hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [(transcript_eq_of_calls_to_eq_zero starved totalLeft totalRight
      agree n).1]
    exact hn

/-! ## The asymptotic boundary -/

/-- The end-to-end computational shape of receipt 8: a parameter-indexed
resource family stays within a **per-test relaxation budget**
(JM20 Definition 3, `DistinguisherClass.reductionRelaxation`) of an ideal
family, against the cost-budgeted feasible test class at a
**polynomially bounded** cost family, with a **negligible** error family —
`PolyBoundedCost` and `Negligible` from
`RandomSystems.Complexity.Asymptotic` at the asymptotic boundary. -/
def FeasiblyClose [Fintype I]
    (budget : Complexity.SecurityParameter → Cost I)
    (eps : Complexity.SecurityParameter → ℝ≥0)
    (real ideal : Complexity.SecurityParameter → Phi I U) : Prop :=
  Complexity.PolyBoundedCost budget ∧
  Complexity.Negligible (fun n => (eps n : ℝ)) ∧
  ∀ n, real n ∈
    (costBoundedStrictTestClass I U (budget n)).reductionRelaxation
      (fun _ => (eps n : ℝ≥0∞)) {ideal n}

/-! ## Non-vacuity receipts on the concrete two-interface carrier

House rule (§11.2 gate 6): every new class must come with a witness that it
is not degenerate.  Here the cost restriction is shown to *restrict*: the
D1 witness test is admitted at an explicit small budget and separates a
concrete pair at class distance `1`, while the interface-`1` probe is a
member of the full class that no `calls 1 = 0` cost class admits. -/

section Receipts

open RandomSystemsCC.TypedFiniteChecks
open RandomSystemsCC.TypedDistinguisherChecks

/-- The closed-form move of a `DDD.ofDDE` reader once the query budget is
exhausted. -/
theorem ofDDE_val_of_ge {X Y : Type*} (e : PFunDDS.DDE X Y) (n : ℕ)
    (A : List (X × Option Y) → Bool) {ys : List (Option Y)}
    (hge : n ≤ ys.length) :
    (PFunDDS.DDD.ofDDE e n A).val ys =
      Sum.inr (A (replay e (ys.take n))) := by
  show (if ys.length < n then _ else Sum.inr (A (replay e (ys.take n)))) = _
  rw [if_neg (not_lt.mpr hge)]

/-! ### The positive receipt: the D1 witness at an explicit cost -/

/-- The explicit budget of the D1 witness test: two rounds, one call to
interface `0`, no calls to interface `1`. -/
def probeCost : Cost Interface :=
  Cost.of 2 fun i => if i = 0 then 1 else 0

/-- The truncated probe reader fires exactly once, on the empty history,
with the interface-`0` probe query. -/
theorem trunc_probe_val_nil :
    (PFunDDS.truncDDD 2 probeDistinguisher).val [] = Sum.inl probeQuery :=
  rfl

/-- On any nonempty history the truncated probe reader has stopped. -/
theorem trunc_probe_val_ne_nil {history :
    List (Option (FlatAnswer testUniverse bitBoundary))}
    (nonempty : history ≠ []) :
    ∃ b, (PFunDDS.truncDDD 2 probeDistinguisher).val history = Sum.inr b := by
  have hlen : 1 ≤ history.length := by
    cases history with
    | nil => exact absurd rfl nonempty
    | cons _ _ => simp
  by_cases hlt : history.length < 2
  · rw [PFunDDS.truncDDD_val_of_lt hlt]
    show ∃ b, (PFunDDS.DDD.ofDDE probeEnvironment 1 probeAccept).val history =
      Sum.inr b
    rw [ofDDE_val_of_ge probeEnvironment 1 probeAccept hlen]
    exact ⟨_, rfl⟩
  · rw [PFunDDS.truncDDD_val_of_ge (not_lt.mp hlt)]
    rcases probeDistinguisher.val (history.take 2) with query | b
    · exact ⟨false, rfl⟩
    · exact ⟨b, rfl⟩

/-- The D1 witness reader is certified at `probeCost`. -/
theorem probe_calls_within :
    CallsWithin probeCost
      (PFunDDS.truncDDD (Cost.intrinsic probeCost) probeDistinguisher) := by
  intro history i
  show callsTo (PFunDDS.truncDDD 2 probeDistinguisher) i history ≤
    Cost.calls probeCost i
  by_cases hi : i = 0
  · subst hi
    have hone : ((List.range (history.length + 1)).countP fun k =>
        k == 0) = 1 := by
      have := List.count_eq_one_of_mem
        (List.nodup_range (n := history.length + 1))
        (List.mem_range.mpr (Nat.succ_pos history.length))
      simpa [List.count] using this
    have hmono : callsTo (PFunDDS.truncDDD 2 probeDistinguisher) 0 history ≤
        (List.range (history.length + 1)).countP fun k => k == 0 := by
      unfold callsTo
      refine List.countP_mono_left fun k hk hpk => ?_
      by_cases hnil : history.take k = []
      · -- an empty prefix with a fired query: only `k = 0` survives, since
        -- `take k = []` for `k ≠ 0` forces `history = []` and hence `k = 0`
        -- from range membership anyway
        have hzero : k = 0 := by
          cases hh : history with
          | nil =>
              rw [hh] at hk
              simpa using List.mem_range.mp hk
          | cons head tail =>
              cases k with
              | zero => rfl
              | succ k => rw [hh] at hnil; simp at hnil
        simp [hzero]
      · obtain ⟨b, hb⟩ := trunc_probe_val_ne_nil hnil
        rw [hb] at hpk
        exact Bool.noConfusion hpk
    refine hmono.trans (hone.le.trans ?_)
    show (1 : ℕ) ≤ Cost.calls probeCost 0
    simp [probeCost]
  · have hzero : callsTo (PFunDDS.truncDDD 2 probeDistinguisher) i history
        = 0 := by
      unfold callsTo
      rw [List.countP_eq_zero]
      intro k _ hpk
      by_cases hnil : history.take k = []
      · rw [hnil, trunc_probe_val_nil] at hpk
        exact hi (of_decide_eq_true hpk).symm
      · obtain ⟨b, hb⟩ := trunc_probe_val_ne_nil hnil
        rw [hb] at hpk
        exact Bool.noConfusion hpk
    rw [hzero]
    exact Nat.zero_le _

/-- **The positive receipt**: the D1 witness test is admitted at the
explicit cost `probeCost`. -/
theorem witness_test_mem_cost_bounded_tests :
    witnessTest ∈ costBoundedTests Interface testUniverse probeCost :=
  boundary_test_mem_cost_bounded_tests bitBoundary probeCost
    probeDistinguisher probe_calls_within

/-- **Non-vacuity of the cost class**: at budget `probeCost` the class
distance of the D1 witness pair is exactly `1`. -/
theorem cost_bounded_class_edistD_witness_eq_one :
    (costBoundedStrictTestClass Interface testUniverse probeCost).edistD
      (witnessResource true) (witnessResource false) = 1 := by
  refine le_antisymm
    ((costBoundedStrictTestClass Interface testUniverse
      probeCost).edistD_le_one _ _) ?_
  calc
    (1 : ℝ≥0∞) = DistinguisherClass.adv witnessTest
        (witnessResource true) (witnessResource false) :=
      witness_adv_eq_one.symm
    _ ≤ (costBoundedStrictTestClass Interface testUniverse
          probeCost).edistD (witnessResource true) (witnessResource false) :=
      (costBoundedStrictTestClass Interface testUniverse
        probeCost).adv_le_edistD witness_test_mem_cost_bounded_tests _ _

/-! ### The negative receipt: a starved interface genuinely restricts

`sideSystem` answers `true` exactly at interface `1`; the ideal constant
system never answers `true`.  The one-query interface-`1` probe separates
them within the full strict class, but no cost class with `calls 1 = 0`
admits it — by the transcript coupling, a certified reader that cannot call
interface `1` computes the same acceptance mass on both resources. -/

/-- The total resource answering `true` exactly at interface `1`. -/
def sideSystem : DependentDDS testUniverse bitBoundary where
  domain := {history | history ≠ []}
  empty_not_mem := fun absurd => absurd rfl
  prefix_closed := fun _ nonempty _ => nonempty
  output := fun history nonempty _ =>
    decide ((history.getLast nonempty).1 = 1)

theorem side_system_total :
    ∀ inputs : List (Query testUniverse bitBoundary), inputs ≠ [] →
      inputs ∈ PFunDDS.dom (DependentDDS.flatten sideSystem) :=
  fun _ nonempty => nonempty

/-- Away from interface `1`, `sideSystem` and the never-accepting constant
system are indistinguishable output for output. -/
theorem side_agrees_off_one (l : List (Query testUniverse bitBoundary))
    (memLeft : l ∈ PFunDDS.dom (DependentDDS.flatten sideSystem))
    (memRight : l ∈ PFunDDS.dom (DependentDDS.flatten (constantSystem false)))
    (avoids : ∀ q ∈ l, q.1 ≠ 1) :
    PFunDDS.output (DependentDDS.flatten sideSystem) l memLeft =
      PFunDDS.output (DependentDDS.flatten (constantSystem false)) l
        memRight := by
  have nonempty : l ≠ [] := DependentDDS.history_ne_nil sideSystem memLeft
  have hlast : decide ((l.getLast nonempty).1 = 1) = false :=
    decide_eq_false (avoids _ (List.getLast_mem nonempty))
  show (⟨(l.getLast nonempty).1, decide ((l.getLast nonempty).1 = 1)⟩ :
      FlatAnswer testUniverse bitBoundary) = ⟨(l.getLast nonempty).1, false⟩
  rw [hlast]

/-- The interface-`1` probe query. -/
def sideQuery : Query testUniverse bitBoundary := ⟨1, true⟩

/-- One-query environment for interface `1`: probe, then stop. -/
def sideEnvironment :
    PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)
  | [] => some sideQuery
  | _ :: _ => none

/-- The one-query interface-`1` bit reader. -/
def sideDistinguisher :
    PFunDDS.DDD (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary) :=
  PFunDDS.DDD.ofDDE sideEnvironment 1 probeAccept

/-- The interface-`1` reader as a strict test at the D1 witness budget. -/
def sideProbeTest :
    StrictContext.Test (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary) :=
  StrictContextTotal.testOfTruncDDD 2 sideDistinguisher

/-- The interface-`1` probe on the heterogeneous carrier. -/
def sideTest : Phi Interface testUniverse → ℝ≥0∞ :=
  boundaryTest bitBoundary sideProbeTest

/-- The point-mass law on the side system. -/
def sideLaw : DependentPDS.Prob testUniverse bitBoundary :=
  ⟨Finsupp.single sideSystem 1, by
    show Dist.weight (Finsupp.single sideSystem (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]⟩

/-- The side resource, as an element of the AC carrier. -/
def sideResource : Phi Interface testUniverse :=
  ⟨bitBoundary, DependentRandomSystem.ofProb sideLaw⟩

theorem transcript_flatten_side_one :
    PFunDDS.transcript (DependentDDS.flatten sideSystem) sideEnvironment 1 =
      [(sideQuery, some ⟨1, true⟩)] := by
  have fires : sideEnvironment
      ((PFunDDS.transcript (DependentDDS.flatten sideSystem)
        sideEnvironment 0)↓ᵧ) = some sideQuery := rfl
  rw [transcript_succ_fire fires]
  have output_side : PFunDDS.output
      ((DependentDDS.flatten sideSystem)⊥)
      (((PFunDDS.transcript (DependentDDS.flatten sideSystem)
          sideEnvironment 0)↓ₓ) ++ [sideQuery])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
      some ⟨1, true⟩ :=
    PFunDDS.output_fullyDefined_append_of_mem
      (DependentDDS.flatten sideSystem) [] sideQuery
      (Or.inr rfl)
      (side_system_total [sideQuery] (by simp))
  rw [output_side]
  rfl

theorem transcript_flatten_constant_side (b : Bool) :
    PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
        sideEnvironment 1 =
      [(sideQuery, some ⟨1, b⟩)] := by
  have fires : sideEnvironment
      ((PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
        sideEnvironment 0)↓ᵧ) = some sideQuery := rfl
  rw [transcript_succ_fire fires]
  have output_side : PFunDDS.output
      ((DependentDDS.flatten (constantSystem b))⊥)
      (((PFunDDS.transcript (DependentDDS.flatten (constantSystem b))
          sideEnvironment 0)↓ₓ) ++ [sideQuery])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
      some ⟨1, b⟩ :=
    PFunDDS.output_fullyDefined_append_of_mem
      (DependentDDS.flatten (constantSystem b)) [] sideQuery
      (Or.inr rfl)
      (constant_system_total b [sideQuery] (by simp))
  rw [output_side]
  rfl

/-- The probe accepts the side system with certainty. -/
theorem side_accepts_side :
    true ∈ StrictContext.observe sideProbeTest
      (DependentDDS.flatten sideSystem) := by
  refine (StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
    2 sideDistinguisher _ side_system_total).mpr ?_
  refine (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
    sideEnvironment 1 probeAccept _).mpr ?_
  refine (verdict_ofDDE_iff sideEnvironment 1 probeAccept _).mpr ?_
  rw [transcript_flatten_side_one]
  rfl

/-- The probe rejects the never-accepting constant system. -/
theorem side_rejects_constant_false :
    true ∉ StrictContext.observe sideProbeTest
      (DependentDDS.flatten (constantSystem false)) := by
  intro haccept
  have hverdict := (StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
      sideEnvironment 1 probeAccept _).mp
    ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
      2 sideDistinguisher _ (constant_system_total false)).mp haccept)
  have hcond := (verdict_ofDDE_iff sideEnvironment 1 probeAccept _).mp
    hverdict
  rw [transcript_flatten_constant_side false] at hcond
  exact Bool.noConfusion hcond

theorem side_test_value_side : sideTest sideResource = 1 := by
  show boundaryTest bitBoundary sideProbeTest
      ⟨bitBoundary, DependentRandomSystem.ofProb sideLaw⟩ = 1
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_one
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  exact mass_single_one_of_mem side_accepts_side

theorem side_test_value_ideal : sideTest (witnessResource false) = 0 := by
  show boundaryTest bitBoundary sideProbeTest
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw false)⟩ = 0
  rw [boundary_test_same, strict_mass_of_prob]
  refine Eq.trans (congrArg _ ?_) ENNReal.coe_zero
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  exact mass_single_one_of_not_mem side_rejects_constant_false

theorem side_test_mem_strict_tests :
    sideTest ∈ strictTests Interface testUniverse :=
  boundary_test_mem_strict_tests bitBoundary sideProbeTest

/-- The coupling at the acceptance-mass level: any reader whose truncation
is certified with zero interface-`1` calls computes the same strict mass on
the side resource and the never-accepting resource. -/
theorem strict_mass_trunc_eq_of_starved {q : ℕ}
    {d : PFunDDS.DDD (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)}
    (starvedCalls : ∀ history,
      callsTo (PFunDDS.truncDDD q d) 1 history = 0) :
    strictMass (StrictContextTotal.testOfTruncDDD q d)
        (DependentRandomSystem.ofProb sideLaw) =
      strictMass (StrictContextTotal.testOfTruncDDD q d)
        (DependentRandomSystem.ofProb (constantLaw false)) := by
  have coupled :=
    verdict_iff_of_calls_to_eq_zero starvedCalls side_system_total
      (constant_system_total false) side_agrees_off_one
  rw [strict_mass_of_prob, strict_mass_of_prob]
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  show Dist.mass (Finsupp.single sideSystem (1 : NNReal)) _ =
    Dist.mass (Finsupp.single (constantSystem false) (1 : NNReal)) _
  by_cases hv : true ∈ StrictContext.observe
      (StrictContextTotal.testOfTruncDDD q d)
      (DependentDDS.flatten sideSystem)
  · have hv' : true ∈ StrictContext.observe
        (StrictContextTotal.testOfTruncDDD q d)
        (DependentDDS.flatten (constantSystem false)) := by
      refine (StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
        q d _ (constant_system_total false)).mpr ?_
      exact coupled.mp
        ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
          q d _ side_system_total).mp hv)
    -- `exact`, not `rw`: `rw` elaborates its argument first and would fix
    -- `point := true` instead of reading the point off the goal's
    -- `Finsupp.single` (DESIGN §4 item 1, as in `TypedDistinguisherChecks`).
    refine Eq.trans (mass_single_one_of_mem hv) (Eq.symm ?_)
    exact mass_single_one_of_mem hv'
  · have hv' : true ∉ StrictContext.observe
        (StrictContextTotal.testOfTruncDDD q d)
        (DependentDDS.flatten (constantSystem false)) := by
      intro mem
      exact hv
        ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
          q d _ side_system_total).mpr
          (coupled.mpr
            ((StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
              q d _ (constant_system_total false)).mp mem)))
    refine Eq.trans (mass_single_one_of_not_mem hv) (Eq.symm ?_)
    exact mass_single_one_of_not_mem hv'

/-- **The negative receipt**: the interface-`1` probe is a member of the
full strict class that no cost class with `calls 1 = 0` admits — the
feasible subcarrier is a genuinely proper restriction. -/
theorem side_test_not_mem_cost_bounded_tests {c : Cost Interface}
    (starved : Cost.calls c 1 = 0) :
    sideTest ∉ costBoundedTests Interface testUniverse c := by
  intro admitted
  rcases admitted bitBoundary with blind | ⟨d, certified, observed⟩
  · have collapse : (1 : ℝ≥0∞) = 0 := by
      rw [← side_test_value_side]
      exact blind (DependentRandomSystem.ofProb sideLaw)
    exact one_ne_zero collapse
  · have starvedCalls : ∀ history,
        callsTo (PFunDDS.truncDDD (Cost.intrinsic c) d) 1 history = 0 :=
      fun history => Nat.le_zero.mp (starved ▸ certified history 1)
    have collapse : (1 : ℝ≥0∞) = 0 := by
      calc (1 : ℝ≥0∞) = sideTest sideResource := side_test_value_side.symm
        _ = (strictMass
              (StrictContextTotal.testOfTruncDDD (Cost.intrinsic c) d)
              (DependentRandomSystem.ofProb sideLaw) : ℝ≥0∞) :=
            observed (DependentRandomSystem.ofProb sideLaw)
        _ = (strictMass
              (StrictContextTotal.testOfTruncDDD (Cost.intrinsic c) d)
              (DependentRandomSystem.ofProb (constantLaw false)) : ℝ≥0∞) := by
            rw [strict_mass_trunc_eq_of_starved starvedCalls]
        _ = sideTest (witnessResource false) :=
            (observed (DependentRandomSystem.ofProb (constantLaw false))).symm
        _ = 0 := side_test_value_ideal
    exact one_ne_zero collapse

/-- The starved class metric is blind across interface `1` … -/
theorem cost_bounded_edistD_side_eq_zero {c : Cost Interface}
    (starved : Cost.calls c 1 = 0) :
    (costBoundedStrictTestClass Interface testUniverse c).edistD
      sideResource (witnessResource false) = 0 := by
  refine le_antisymm ?_ (zero_le _)
  refine iSup₂_le fun t admitted => ?_
  rcases admitted bitBoundary with blind | ⟨d, certified, observed⟩
  · have hL : t sideResource = 0 :=
      blind (DependentRandomSystem.ofProb sideLaw)
    have hR : t (witnessResource false) = 0 :=
      blind (DependentRandomSystem.ofProb (constantLaw false))
    unfold DistinguisherClass.adv
    rw [hL, hR]
    simp
  · have starvedCalls : ∀ history,
        callsTo (PFunDDS.truncDDD (Cost.intrinsic c) d) 1 history = 0 :=
      fun history => Nat.le_zero.mp (starved ▸ certified history 1)
    have hsame : t sideResource = t (witnessResource false) := by
      calc t sideResource = _ :=
          observed (DependentRandomSystem.ofProb sideLaw)
        _ = (strictMass
              (StrictContextTotal.testOfTruncDDD (Cost.intrinsic c) d)
              (DependentRandomSystem.ofProb (constantLaw false)) : ℝ≥0∞) := by
            rw [strict_mass_trunc_eq_of_starved starvedCalls]
        _ = t (witnessResource false) :=
            (observed (DependentRandomSystem.ofProb (constantLaw false))).symm
    unfold DistinguisherClass.adv
    rw [hsame]
    simp

/-- … while the full class separates the same pair at distance `1`. -/
theorem strict_test_class_edistD_side_eq_one :
    (strictTestClass Interface testUniverse).edistD
      sideResource (witnessResource false) = 1 := by
  refine le_antisymm
    ((strictTestClass Interface testUniverse).edistD_le_one _ _) ?_
  have hadv : DistinguisherClass.adv sideTest
      sideResource (witnessResource false) = 1 := by
    unfold DistinguisherClass.adv
    rw [side_test_value_side, side_test_value_ideal]
    simp
  calc
    (1 : ℝ≥0∞) = DistinguisherClass.adv sideTest
        sideResource (witnessResource false) := hadv.symm
    _ ≤ (strictTestClass Interface testUniverse).edistD
        sideResource (witnessResource false) :=
      (strictTestClass Interface testUniverse).adv_le_edistD
        side_test_mem_strict_tests _ _

/-! ### The worked computational statement

A resource that accepts with probability `p` sits within per-test relaxation
budget `p` of the never-accepting ideal, for every cost-budgeted class; the
budget is tight, and the parameterized family with `p n = (n + 1)⁻ⁿ` closes
the asymptotic boundary with `PolyBoundedCost` and `Negligible`. -/

/-- Event mass is additive in the distribution.
UPSTREAM-CANDIDATE: `RandomSystems.Dist`, next to `mass_restrict`. -/
theorem mass_add {A : Type*} (F G : RandomSystems.Dist A) (P : A → Prop) :
    Dist.mass (F + G) P = Dist.mass F P + Dist.mass G P := by
  classical
  unfold Dist.mass
  refine Finsupp.sum_add_index' (fun a => ite_self 0) fun a w₁ w₂ => ?_
  by_cases h : P a
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-- Event mass of a weighted point mass, on the member branch.  The
weight-`w` generalization of `TypedDistinguisherChecks.mass_single_one_of_mem`
(same two-branch discipline: an `if` in the statement would demand a
`DecidablePred` the caller cannot supply).
UPSTREAM-CANDIDATE: `RandomSystems.Dist`. -/
theorem mass_single_of_mem {A : Type*} {point : A} {event : A → Prop}
    (member : event point) (w : NNReal) :
    Dist.mass (Finsupp.single point w) event = w := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index
      (h := fun a weight => if event a then weight else 0) (ite_self 0),
    if_pos member]

/-- Event mass of a weighted point mass, on the non-member branch. -/
theorem mass_single_of_not_mem {A : Type*} {point : A} {event : A → Prop}
    (nonMember : ¬ event point) (w : NNReal) :
    Dist.mass (Finsupp.single point w) event = 0 := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index
      (h := fun a weight => if event a then weight else 0) (ite_self 0),
    if_neg nonMember]

/-- Class advantage is symmetric in its two resources.
UPSTREAM-CANDIDATE: `AbstractCrypto.Distinguisher`, next to `adv_le_edistD`. -/
theorem adv_comm {Φ : Type*} (t : Φ → ℝ≥0∞) (x y : Φ) :
    DistinguisherClass.adv t x y = DistinguisherClass.adv t y x := by
  unfold DistinguisherClass.adv
  exact sup_comm _ _

/-- The acceptance event of a strict test, as a named predicate on
deterministic systems: naming it keeps the `Dist.mass` event unification
first-order (the anonymous lambda re-triggers DESIGN §4 item 1 at every
use). -/
def accepts (test : StrictContext.Test (Query testUniverse bitBoundary)
    (FlatAnswer testUniverse bitBoundary))
    (s : DependentDDS testUniverse bitBoundary) : Prop :=
  true ∈ StrictContext.observe test (DependentDDS.flatten s)

/-- The noisy law: answer `true` everywhere with probability `p`, `false`
everywhere otherwise. -/
def noisyLaw (p : ℝ≥0) (hp : p ≤ 1) :
    DependentPDS.Prob testUniverse bitBoundary :=
  ⟨Finsupp.single (constantSystem true) p +
      Finsupp.single (constantSystem false) (1 - p), by
    show Dist.weight (Finsupp.single (constantSystem true) p +
      Finsupp.single (constantSystem false) (1 - p)) = 1
    rw [Dist.weight_eq_finsupp_sum,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    exact add_tsub_cancel_of_le hp⟩

/-- The noisy resource on the AC carrier. -/
def noisyResource (p : ℝ≥0) (hp : p ≤ 1) : Phi Interface testUniverse :=
  ⟨bitBoundary, DependentRandomSystem.ofProb (noisyLaw p hp)⟩

/-- **Every strict test has advantage at most `p`** between the ideal and
the noisy resource: the per-test budget of the reduction relaxation below,
proved for the full class so it serves every cost-budgeted subclass. -/
theorem adv_le_noise {t : Phi Interface testUniverse → ℝ≥0∞}
    (admitted : t ∈ strictTests Interface testUniverse)
    (p : ℝ≥0) (hp : p ≤ 1) :
    DistinguisherClass.adv t (witnessResource false) (noisyResource p hp) ≤
      (p : ℝ≥0∞) := by
  rcases admitted bitBoundary with blind | ⟨test, observed⟩
  · have hL : t (witnessResource false) = 0 :=
      blind (DependentRandomSystem.ofProb (constantLaw false))
    have hR : t (noisyResource p hp) = 0 :=
      blind (DependentRandomSystem.ofProb (noisyLaw p hp))
    unfold DistinguisherClass.adv
    rw [hL, hR]
    simp
  · have hL : t (witnessResource false) =
        (strictMass test
          (DependentRandomSystem.ofProb (constantLaw false)) : ℝ≥0∞) :=
      observed (DependentRandomSystem.ofProb (constantLaw false))
    have hR : t (noisyResource p hp) =
        (strictMass test
          (DependentRandomSystem.ofProb (noisyLaw p hp)) : ℝ≥0∞) :=
      observed (DependentRandomSystem.ofProb (noisyLaw p hp))
    have hIdeal : strictMass test
        (DependentRandomSystem.ofProb (constantLaw false)) =
        Dist.mass (Finsupp.single (constantSystem false) (1 : NNReal))
          (accepts test) := by
      rw [strict_mass_of_prob]
      unfold StrictContext.acceptMass DependentPDS.flatten
      rw [Dist.mass_fTransform]
      rfl
    have hNoisy : strictMass test
        (DependentRandomSystem.ofProb (noisyLaw p hp)) =
        Dist.mass (Finsupp.single (constantSystem true) p) (accepts test) +
        Dist.mass (Finsupp.single (constantSystem false) (1 - p))
          (accepts test) := by
      rw [strict_mass_of_prob]
      unfold StrictContext.acceptMass DependentPDS.flatten
      rw [Dist.mass_fTransform]
      exact mass_add (Finsupp.single (constantSystem true) p)
        (Finsupp.single (constantSystem false) (1 - p)) _
    unfold DistinguisherClass.adv
    rw [hL, hR, hIdeal, hNoisy]
    by_cases hct : accepts test (constantSystem true) <;>
      by_cases hcf : accepts test (constantSystem false)
    · rw [mass_single_of_mem hct p, mass_single_of_mem hcf (1 - p),
        mass_single_of_mem hcf 1, add_tsub_cancel_of_le hp]
      simp
    · rw [mass_single_of_mem hct p, mass_single_of_not_mem hcf (1 - p),
        mass_single_of_not_mem hcf 1, add_zero]
      simp
    · rw [mass_single_of_not_mem hct p, mass_single_of_mem hcf (1 - p),
        mass_single_of_mem hcf 1, zero_add]
      have hleft : ((1 : NNReal) : ℝ≥0∞) - ((1 - p : NNReal) : ℝ≥0∞) =
          ((p : NNReal) : ℝ≥0∞) := by
        rw [← ENNReal.coe_sub, tsub_tsub_cancel_of_le hp]
      have hright : ((1 - p : NNReal) : ℝ≥0∞) - ((1 : NNReal) : ℝ≥0∞) = 0 :=
        tsub_eq_zero_of_le (ENNReal.coe_le_coe.mpr tsub_le_self)
      rw [hleft, hright]
      simp
    · rw [mass_single_of_not_mem hct p, mass_single_of_not_mem hcf (1 - p),
        mass_single_of_not_mem hcf 1, add_zero]
      simp

/-- **The reduction-relaxation membership** (JM20 Definition 3 on the
concrete carrier): the noisy resource is admitted around the ideal at the
constant per-test budget `p`, against the cost-budgeted feasible class at
*every* budget `c`. -/
theorem noisy_mem_reductionRelaxation (c : Cost Interface) (p : ℝ≥0)
    (hp : p ≤ 1) :
    noisyResource p hp ∈
      (costBoundedStrictTestClass Interface testUniverse c).reductionRelaxation
        (fun _ => (p : ℝ≥0∞)) {witnessResource false} :=
  DistinguisherClass.mem_reductionRelaxation_iff.mpr
    ⟨witnessResource false, Set.mem_singleton _, fun t =>
      adv_le_noise (cost_bounded_tests_subset_strict_tests c t.2) p hp⟩

/-- The witness test attains the budget: its value on the noisy resource is
exactly `p`. -/
theorem witness_test_noisy_value (p : ℝ≥0) (hp : p ≤ 1) :
    witnessTest (noisyResource p hp) = (p : ℝ≥0∞) := by
  show boundaryTest bitBoundary probeTest
      ⟨bitBoundary, DependentRandomSystem.ofProb (noisyLaw p hp)⟩ = _
  rw [boundary_test_same, strict_mass_of_prob]
  refine congrArg (fun mass : NNReal => (mass : ℝ≥0∞)) ?_
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  refine Eq.trans (mass_add (Finsupp.single (constantSystem true) p)
      (Finsupp.single (constantSystem false) (1 - p))
      (accepts probeTest)) ?_
  have hct : accepts probeTest (constantSystem true) :=
    (true_mem_observe_probe_iff true).mpr rfl
  have hcf : ¬ accepts probeTest (constantSystem false) := fun mem => by
    simpa using (true_mem_observe_probe_iff false).mp mem
  rw [mass_single_of_mem hct p, mass_single_of_not_mem hcf (1 - p), add_zero]

/-- **The budget is tight**: the class distance between the noisy resource
and the ideal is exactly `p` — the relaxation budget above is the true
distinguishing power, not an over-approximation. -/
theorem strict_test_class_edistD_noisy_eq (p : ℝ≥0) (hp : p ≤ 1) :
    (strictTestClass Interface testUniverse).edistD
      (noisyResource p hp) (witnessResource false) = (p : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun t admitted => ?_
    rw [adv_comm]
    exact adv_le_noise admitted p hp
  · have hadv : DistinguisherClass.adv witnessTest
        (noisyResource p hp) (witnessResource false) = (p : ℝ≥0∞) := by
      unfold DistinguisherClass.adv
      have hzero : witnessTest (witnessResource false) = 0 := by
        rw [witness_test_value false]
        rfl
      rw [witness_test_noisy_value p hp, hzero]
      simp
    calc
      ((p : ℝ≥0∞)) = DistinguisherClass.adv witnessTest
          (noisyResource p hp) (witnessResource false) := hadv.symm
      _ ≤ (strictTestClass Interface testUniverse).edistD
          (noisyResource p hp) (witnessResource false) :=
        (strictTestClass Interface testUniverse).adv_le_edistD
          witness_test_mem_strict_tests _ _

/-! ### Closing the asymptotic boundary -/

/-- The negligible noise rate `(n + 1)⁻ⁿ`. -/
def noiseRate (n : Complexity.SecurityParameter) : ℝ≥0 :=
  ((n : ℝ≥0) + 1)⁻¹ ^ n

theorem noise_rate_le_one (n : Complexity.SecurityParameter) :
    noiseRate n ≤ 1 := by
  refine pow_le_one₀ (zero_le _) ?_
  rw [inv_le_one_iff₀]
  right
  exact le_add_self

/-- The noisy resource family at the negligible noise rate. -/
def noisyFamily (n : Complexity.SecurityParameter) :
    Phi Interface testUniverse :=
  noisyResource (noiseRate n) (noise_rate_le_one n)

/-- The linear cost family: `n` rounds and `n` calls at every interface. -/
def feasibleBudget (n : Complexity.SecurityParameter) : Cost Interface :=
  Cost.of n fun _ => n

theorem feasible_budget_poly :
    Complexity.PolyBoundedCost feasibleBudget := by
  refine ⟨fun n => n, ⟨1, 1, fun n => ?_⟩, fun n coord => ?_⟩
  · calc n ≤ n + 1 := Nat.le_succ n
      _ = 1 * (n + 1) ^ 1 := by ring
  · cases coord <;> exact le_rfl

theorem noise_rate_negligible :
    Complexity.Negligible fun n => ((noiseRate n : ℝ≥0) : ℝ) := by
  intro degree
  refine ⟨degree, fun n hn => ?_⟩
  show |((noiseRate n : ℝ≥0) : ℝ)| ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ degree
  rw [abs_of_nonneg (noiseRate n).coe_nonneg]
  have hcast : ((noiseRate n : ℝ≥0) : ℝ) = (((n : ℝ) + 1)⁻¹) ^ n := by
    push_cast [noiseRate]
    rfl
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hpow : ((n : ℝ) + 1) ^ degree ≤ ((n : ℝ) + 1) ^ n :=
    pow_le_pow_right₀ hbase hn
  have hcastNat : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, hcastNat, inv_pow, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- **The end-to-end computational statement of receipt 8**: the noisy
family is feasibly close to the ideal — a per-test `reductionRelaxation`
budget against the cost-budgeted feasible test class at a polynomially
bounded cost family, with a negligible error family. -/
theorem noisy_family_feasibly_close :
    FeasiblyClose feasibleBudget noiseRate noisyFamily
      fun _ => witnessResource false :=
  ⟨feasible_budget_poly, noise_rate_negligible, fun n =>
    noisy_mem_reductionRelaxation (feasibleBudget n) (noiseRate n)
      (noise_rate_le_one n)⟩

end Receipts

end

end RandomSystemsCC.TypedFeasibility
