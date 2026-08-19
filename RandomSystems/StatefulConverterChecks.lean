/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization

/-!
# Acceptance test: a converter that counts its own outer invocations

The `ofHistoryStep` constructor of `RandomSystems.StepRealization` claims to
make **stateful** converters expressible.  This module cashes that claim on
the smallest converter that genuinely needs memory, and separates it from the
outer-memoryless class `ofStep` had confined the estate to.

`counterFn` is a one-query-per-round converter over the *silent* outer
alphabet `U = Unit`: the caller says nothing at all, so every distinction the
converter draws between its invocations comes from its own history.  On its
`n`-th outer invocation it asks the inner resource for item `n` — a pad index,
a sequence number, a key: exactly the "Alice counts her own sends" step that
the authenticated-channel design (STATUS §11.20, §11.21) had to route through
the outer message because no constructor could express it.

What this establishes, in order:

* `isDDC_counterFn` — the converter is a CR18 Def 3.8 converter.  Memory is
  *inside* the class, not an extension of it: Def 3.8 constrains the `⊥`
  discipline and the length of query streaks, and says nothing about state.
* `counterFn_first`, `counterFn_second` — by `rfl`: at the same outer message
  `()` and the same (empty) open-round answer segment, the first invocation
  queries `1` and the second queries `2`.  The move is a function of the
  history, not of the current message.
* `not_traceEquiv_ofStep_counterFn` — **no** `ofStep` converter behaves that
  way, and not merely "no syntactically equal one": the separation is up to
  `PFunConverter.TraceEquiv`, the project's working converter identity, and
  both witnessing pairs are exhibited *inside* `counterFn`'s trace tree, so
  the difference is one a distinguisher can actually reach.
* `not_isOfStep_counterFn` — the immediate corollary at the class predicate.

The argument is the one-line reason `ofStep` cannot count: its move at
`(us, ys)` depends on `us` only through `us.getLast` and the round offset, so
at a silent outer alphabet the two invocations above collapse to the same
call `step () []`, whichever round budget is chosen.

The final section cashes the **fast path**
(`PFunConverter.ProtocolFn.apply_ofHistoryStep_eq_applyGH`) on the same
converter.  `counterFn` is applied to a concrete pad table `n ↦ 10n`, and the
resulting *system*'s answers at the first, second and third outer calls are
produced by the Lean **kernel** (`rfl`/`decide`) — `10`, `20`, `30`.  That is
what the fast path buys: `PFunConverter.apply` is a fuel-`eventual` of a
`Part`-valued transcript drive and reduces to nothing, while
`CausalApply.causalApplyAtH` against a memoryless resource is a total
`Option`-valued recursion the kernel evaluates.  `applied_ne` then reads off
the payoff at the applied system: `αS([()]) ≠ αS([(),()])` although the two
outer histories carry the same messages — the memory survives application.
-/

namespace RandomSystems.CR18

namespace StatefulConverterChecks

open PFunConverter.ProtocolFn

/-- The counting converter's step function: on an outer history of length `n`
it queries the inner resource for item `n` — the index it reads off its **own**
history, not off the outer message — and returns the answer unchanged.  One
inner query per round, so the open round's segment is empty exactly while the
query is pending. -/
def counterStep (us : List Unit) (_ : us ≠ []) : List ℕ → ℕ ⊕ ℕ
  | [] => Sum.inl us.length
  | y :: _ => Sum.inr y

/-- The counting converter's round count: one inner query per outer
invocation, in every history. -/
def counterCnt : List Unit → ℕ := fun _ => 1

/-- **The counting converter.**  Outer alphabet `Unit`: the caller supplies no
information whatsoever, so everything that distinguishes the `n`-th invocation
from the first is the converter's own memory. -/
def counterFn : PFunConverter.ProtocolFn Unit ℕ ℕ ℕ :=
  ofHistoryStep counterStep counterCnt

/-- First invocation: the converter asks the resource for item `1`. -/
theorem counterFn_first : counterFn ([()], []) = Part.some (Sum.inl 1) := rfl

/-- The first round's answer is relayed outward unchanged. -/
theorem counterFn_mid :
    counterFn ([()], [some 7]) = Part.some (Sum.inr 7) := rfl

/-- **The memory, computed.**  Second invocation, same outer message `()`,
same (empty) open-round answer segment as `counterFn_first` — and the query is
`2`, not `1`. -/
theorem counterFn_second :
    counterFn ([(), ()], [some 7]) = Part.some (Sum.inl 2) := rfl

/-- The counting converter's boundary condition: a query is pending exactly
while this round's answer segment is empty. -/
theorem counterStep_boundary (us : List Unit) (hne : us ≠ []) (ys : List ℕ) :
    (∃ x, counterStep us hne ys = Sum.inl x) ↔ ys.length < counterCnt us := by
  cases ys with
  | nil => exact ⟨fun _ => by simp [counterCnt], fun _ => ⟨us.length, rfl⟩⟩
  | cons y t =>
      constructor
      · rintro ⟨x, hx⟩
        simp [counterStep] at hx
      · intro h
        simp [counterCnt] at h

/-- The counting converter is a CR18 Def 3.8 converter: the boundary condition
is "a query is pending exactly while this round's segment is empty", and the
round counts are uniformly bounded by `1`. -/
theorem isDDC_counterFn : PFunConverter.IsDDC counterFn :=
  isDDC_ofHistoryStep counterStep counterCnt counterStep_boundary ⟨1, fun _ => le_refl 1⟩

/-- The opening pair is on the trace tree. -/
theorem reach_counterFn_first : PFunConverter.Reach counterFn ([()], []) :=
  PFunConverter.Reach.first ()

/-- The first round's answered pair is on the trace tree. -/
theorem reach_counterFn_mid : PFunConverter.Reach counterFn ([()], [some 7]) :=
  PFunConverter.Reach.answer reach_counterFn_first
    (by rw [counterFn_first]; exact Part.mem_some _) (some 7)

/-- The second invocation's pair is on the trace tree — so the memory of
`counterFn_second` is visible to an environment, not junk off the tree. -/
theorem reach_counterFn_second :
    PFunConverter.Reach counterFn ([(), ()], [some 7]) :=
  PFunConverter.Reach.next reach_counterFn_mid
    (by rw [counterFn_mid]; exact Part.mem_some _) ()

/-- **The separation.**  No outer-memoryless step converter is trace-equal to
`counterFn`.  Given such a presentation, its move at the opening pair is
`step () []`, and the boundary condition forces `0 < cnt ()` there; but then at
the second invocation the single available answer is entirely consumed by the
first round's budget, so the presentation's move is `step () []` again — while
`counterFn`'s is the strictly different `Sum.inl 2`.

The witnesses are both inside `counterFn`'s trace tree, so the separation is at
the level of the working converter identity (`PFunConverter.TraceEquiv`), not
merely of raw terms. -/
theorem not_traceEquiv_ofStep_counterFn (step : Unit → List ℕ → ℕ ⊕ ℕ)
    (cnt : Unit → ℕ)
    (hcnt : ∀ u ys, (∃ x, step u ys = Sum.inl x) ↔ ys.length < cnt u) :
    ¬ PFunConverter.TraceEquiv counterFn (ofStep step cnt) := by
  intro h
  have h1 : Sum.inl 1 ∈ ofStep step cnt ([()], []) :=
    (PFunConverter.mem_congr_of_reach h reach_counterFn_first _).mp
      (by rw [counterFn_first]; exact Part.mem_some _)
  have h2 : Sum.inl 2 ∈ ofStep step cnt ([(), ()], [some 7]) :=
    (PFunConverter.mem_congr_of_reach h reach_counterFn_second _).mp
      (by rw [counterFn_second]; exact Part.mem_some _)
  obtain ⟨ys1, hd1, hv1⟩ :=
    (mem_ofStep_iff step cnt (show ([()] : List Unit) ≠ [] by simp) [] _).mp h1
  have hys1 : ys1 = [] := by
    have hlen := congrArg List.length hd1
    simp only [List.length_drop, List.length_nil, List.length_map] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  subst hys1
  have hstep1 : step () [] = Sum.inl 1 := hv1.symm
  have hpos : 0 < cnt () := by
    have hq := (hcnt () []).mp ⟨1, hstep1⟩
    simpa using hq
  obtain ⟨ys2, hd2, hv2⟩ :=
    (mem_ofStep_iff step cnt (show ([(), ()] : List Unit) ≠ [] by simp)
      [some 7] _).mp h2
  have hoff : (([(), ()] : List Unit).dropLast.map cnt).sum = cnt () := by
    simp
  rw [hoff, List.drop_eq_nil_of_le (by simpa using hpos)] at hd2
  have hys2 : ys2 = [] := by
    have hlen := congrArg List.length hd2
    simp only [List.length_nil, List.length_map] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  subst hys2
  have hcontra : (Sum.inl 2 : ℕ ⊕ ℕ) = Sum.inl 1 := by
    rw [hv2]
    simpa using hstep1
  simp at hcontra

/-- The counting converter is genuinely outside the outer-memoryless class —
the corollary of `not_traceEquiv_ofStep_counterFn` at `IsOfStep`, whose
membership is raw equality and hence a fortiori trace equality. -/
theorem not_isOfStep_counterFn : ¬ IsOfStep counterFn := by
  rintro ⟨step, cnt, hcnt, heq⟩
  exact not_traceEquiv_ofStep_counterFn step cnt hcnt (congrArg _ heq)

/-! ### The fast path, evaluated

The three computed values below (`causalApply_counter_first`/`_second`/
`_third`) are decided by the Lean kernel from the definitions alone — `rfl`
and `decide`, no tactic reasoning and no `simp` set; their axiom footprint is
`[propext]`, without `Classical.choice`.  The bridge from the kernel-computable
`CausalApply.causalApplyAtH` to the paper-facing `PFunConverter.apply` is
`apply_ofHistoryStep_eq_applyGH` (the coherence) composed with
`CausalApply.applyRawAtH_functionEvaluator` (the memoryless-resource
collapse). -/

/-- The concrete resource: a pad table whose `n`-th item is `10 * n`. -/
def padTable : ℕ → ℕ := fun n => 10 * n

/-- The pad table as a system (every nonempty query history is answered, and
the answer is the table at the current query). -/
def padResource : PFunDDS.DDS ℕ ℕ :=
  PFunDDS.functionEvaluator padTable

/-- **The fast path computes: first outer call.**  `counterFn` queries item
`1` and relays `10`.  Kernel-decided. -/
theorem causalApply_counter_first :
    CausalApply.causalApplyAtH counterStep padTable 2 [()] = some 10 := rfl

/-- **Second outer call — same outer message, different answer.**  `counterFn`
queries item `2` and relays `20`.  Kernel-decided; the difference from
`causalApply_counter_first` is the converter's memory, since the outer
alphabet is silent. -/
theorem causalApply_counter_second :
    CausalApply.causalApplyAtH counterStep padTable 2 [(), ()] = some 20 := rfl

/-- Third outer call: `30`.  By `decide`, i.e. the kernel evaluates the whole
drive — resource queries included — to a `Bool`. -/
theorem causalApply_counter_third :
    CausalApply.causalApplyAtH counterStep padTable 2 [(), (), ()] = some 30 := by decide

/-- The applied system's raw function, at any outer history, is the
kernel-computable drive at any sufficient fuel: the coherence theorem
`apply_ofHistoryStep_eq_applyGH` transported to the memoryless resource
`padResource`. -/
theorem mem_apply_counterFn_padResource (us : List Unit) (v : ℕ) (fuel : ℕ)
    (h : CausalApply.causalApplyAtH counterStep padTable fuel us = some v) :
    v ∈ (PFunConverter.apply counterFn padResource).1 us := by
  rw [show counterFn = ofHistoryStep counterStep counterCnt from rfl,
    apply_ofHistoryStep_eq_applyGH counterStep counterCnt counterStep_boundary padResource,
    CausalApply.applyGH_toPFun, CausalApply.mem_applyRawH]
  refine ⟨fuel, ?_⟩
  rw [show padResource.1 = (PFunDDS.functionEvaluator padTable).1 from rfl,
    CausalApply.applyRawAtH_functionEvaluator, Part.mem_ofOption]
  exact h

/-- The applied system answers `10` at the first outer call. -/
theorem apply_counterFn_first : (10 : ℕ) ∈ (PFunConverter.apply counterFn padResource).1 [()] :=
  mem_apply_counterFn_padResource [()] 10 2 causalApply_counter_first

/-- The applied system answers `20` at the second outer call. -/
theorem apply_counterFn_second :
    (20 : ℕ) ∈ (PFunConverter.apply counterFn padResource).1 [(), ()] :=
  mem_apply_counterFn_padResource [(), ()] 20 2 causalApply_counter_second

/-- **The payoff.**  The *applied system* `counterFn padResource` — not merely
the converter — answers differently at the first and the second outer call,
although both outer histories carry only the silent message `()`.  The two
witnessing values were produced by the kernel; converter memory survives CR18
Def 3.9 application. -/
theorem apply_counterFn_ne :
    (PFunConverter.apply counterFn padResource).1 [()]
      ≠ (PFunConverter.apply counterFn padResource).1 [(), ()] := by
  intro heq
  have h10 : (10 : ℕ) ∈ (PFunConverter.apply counterFn padResource).1 [(), ()] :=
    heq ▸ apply_counterFn_first
  have : (10 : ℕ) = 20 := Part.mem_unique h10 apply_counterFn_second
  simp at this

end StatefulConverterChecks

end RandomSystems.CR18
