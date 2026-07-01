/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.CR18.PDS

open RandomSystems (Dist)

-- ⚠ DEPRECATED MODULE. Use the partial-function behavior `PFunPDS.Behavior` / `PFunPDS.behavior` from
-- `RandomSystems.CR18.PDS`. The `Behavior` struct below is the curried (`… → Y → NNReal`) model whose
-- `behavior`/`condSlice` compute conditionals by support-filtering, which needlessly demands
-- `DecidableEq` and leaks it into every downstream statement. The `@[deprecated]` marks below steer new
-- code to `PFunPDS`; this option keeps the legacy file itself building warning-free.
set_option linter.deprecated false

-- `DDS.dom` membership is not decidable in general; this struct-based behavior is noncomputable, so we
-- make decidability classical and ambient (low priority) rather than via a local `letI` that would
-- block `simp` from reducing `outputSeq` getElem in downstream proofs.
open scoped Classical

/-!
# CR18 Definition 3.18: Behavior of a Probabilistic System (DEPRECATED — use `PFunPDS.Behavior`)

Maurer's **behavior** `b(S)` of a probabilistic `(X, Y)`-system `S` is the
sequence of conditional probability distributions
```
  pˢ_{Yᵢ|XⁱYⁱ⁻¹} : Y × Xⁱ × Yⁱ⁻¹ →. ℝ≥0
```
for `i ≥ 1`.  The distribution at step `i` is defined by

  pˢ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹)
    := Prˢ[ S(xⁱ) = yᵢ | S(x¹)=y₁, …, S(xⁱ⁻¹)=yᵢ₋₁ ]

and is **undefined** (the conditioning event has probability 0) when
`pˢ_{Yⱼ|XʲYʲ⁻¹}(yⱼ, xʲ, yʲ⁻¹) = 0` for some `j < i`
(footnote 14/16 of CR18 source).

## Strategy

We work with `PDS X Y = Dist (DDS X Y)` from `RandomSystems.CR18.PDS`
(finite-support sub-distribution, LM20 Def 1; `NNReal`-valued).

**Step 1 — joint output distribution.**
For a fixed input history `xs : List X` of length `i`, the output
`S(xs)` induces a distribution over `Y` via the pushforward of `S` along
the response function:
```
  jointOutputDist S xs : Dist (List Y)
```
is the distribution of the output sequence `(S(x¹), …, S(xⁱ))`.

**Step 2 — conditional slice.**
`condSlice S xs ys` gives the (sub-)probability of `S(xs) = ys.last` given
`S(x¹) = y₁, …, S(xs.dropLast) = ys.dropLast`.  The result lives in
`NNReal` (matching `Dist` values) and equals the joint probability of the
full output history divided by the joint probability of the prefix history.

**Step 3 — Behavior type.**
`Behavior X Y` is the type of a sequence of conditional slices: for each
`i : ℕ`, a function
```
  step i : List X → List Y → Y → ENNReal
```
where `step i xs ys y` models `pˢ_{Yᵢ₊₁|Xⁱ⁺¹Yⁱ}(y, xs, ys)`.

The behavior `b(S)` is computed by `behavior S : Behavior X Y`.
-/

namespace RandomSystems.CR18

universe u v

variable {X : Type u} {Y : Type v}

/-!
### Joint output distribution of a PDS on a fixed input sequence

For a `PDS X Y` (= `Dist (DDS X Y)`) and a fixed input history
`xs : List X`, we compute the distribution of the output sequence
`(S.respond xs₁, S.respond (xs₁,xs₂), …, S.respond xs)`.

This is the push-forward of the DDS distribution along the function
that maps a DDS `s` to its output sequence on `xs`.
-/

/-- The output sequence of a DDS `s` on a fixed input list `xs`.

For each prefix `xs.take (k+1)` in the domain, the output sequence
records `some (s.respond (xs.take (k+1)) _)` at position `k`.  For
inputs not in the domain, we record `none`.

This is a total function so that we can push forward `PMF (DDS X Y)`.
We use `Option Y` to avoid requiring `Nonempty Y` for an arbitrary sentinel. -/
noncomputable def DDS.outputSeq (s : DDS X Y) (xs : List X) : List (Option Y) :=
  (List.finRange xs.length).map fun k =>
    let pfx := xs.take (k.val + 1)
    if h : pfx ∈ s.dom then some (s.respond pfx h)
    else none

/-- The joint output distribution of a PDS `S` on a fixed input list `xs`.

`jointOutputDist S xs` is the pushforward of the DDS distribution along
`DDS.outputSeq · xs`: the distribution of the output sequence
`(Y₁, …, Yₙ)` (encoded as `List (Option Y)`) when the DDS is drawn from
`S` and the inputs are `xs`. -/
noncomputable def jointOutputDist [DecidableEq (List (Option Y))]
    (S : PDS X Y) (xs : List X) : Dist (List (Option Y)) :=
  Dist.fTransform (DDS.outputSeq · xs) S

/-!
### Conditional slice: the step-`i` conditional distribution

`condSlice S xs ys y` computes the conditional probability
  Pr[ S(xs) = y | (Y₁,…,Yₙ₋₁) = ys ]
where `xs` has length `n = ys.length + 1`.

It equals `joint(ys ++ [y]) / joint(ys)` with the convention that the
result is 0 when the denominator is 0 (the conditioning event is
impossible; footnote 16 of CR18 says this case is "undefined", but for
Lean we return 0 and track well-definedness via `CondSlice.WellDefined`).
-/

/-- The total probability that a PDS `S` produces output sequence `ys`
on input sequence `xs`.  `xs` and `ys` should have the same length; the
function is unconditional (no length guard) to keep the type simple.

Evaluates `jointOutputDist S xs` at the single point `ys.map some`,
which corresponds to all outputs being defined (the conditioning events
all having nonzero probability). -/
noncomputable def jointProb [DecidableEq (List (Option Y))]
    (S : PDS X Y) (xs : List X) (ys : List Y) : NNReal :=
  jointOutputDist S xs (ys.map some)

/-- CR18 Definition 3.18 (conditional slice).

`condSlice S xs ys y` is the conditional probability
  Pr[ S(xs ++ [x_next]) = y | (Y₁,…,Y_{i-1}) = ys ]
for a PDS `S`, a prefix input history `xs` of length `i`, prefix output
history `ys` of length `i`, and a candidate next output `y`.

We encode it as the ratio `jointProb S (xs) (ys ++ [y]) / jointProb S xs ys`
(where `xs` is the full input history of length `|ys| + 1` here and
`ys` the full output history at that step).

When the denominator is 0 (the conditioning event has probability 0),
the result is defined to be 0.  Maurer's Definition 3.18 leaves this case
undefined (footnote 16); the `WellDefined` predicate below captures the
case where the denominator is nonzero. -/
noncomputable def condSlice [DecidableEq (List (Option Y))]
    (S : PDS X Y) (xs : List X) (ys : List Y) (y : Y) : NNReal :=
  let joint_full := jointProb S xs (ys ++ [y])
  let joint_prefix : NNReal := jointProb S xs.dropLast ys
  joint_full / joint_prefix

/-!
### The Behavior type and `b(S)`

CR18 Definition 3.18: the **behavior** `b(S)` is the sequence
`(pˢ_{Y₁|X¹}, pˢ_{Y₂|X²Y¹}, pˢ_{Y₃|X³Y²}, …)`.

We represent this as a function `ℕ → List X → List Y → Y → ENNReal`,
where the natural-number index `i` is 0-based (step `i` corresponds to
`i+1` in the paper's 1-based indexing).

At step `i`, `step i xs ys y` models `pˢ_{Yᵢ₊₁|Xⁱ⁺¹Yⁱ}(y, xs, ys)`,
where `xs` has length `i+1` (the full input history at step `i+1`) and
`ys` has length `i` (the output history at steps `1,…,i`).
-/

/-- CR18 Definition 3.18: the behavior type.

A **behavior** for alphabets `X` and `Y` is a sequence of conditional
probability kernels: for each round `i : ℕ`, a function
```
  step : List X → List Y → Y → ENNReal
```
mapping `(xⁱ, yⁱ⁻¹, y)` to the conditional probability of outputting `y`
at round `i+1`.

The well-definedness predicate `WellDefined` records Maurer's requirement
(footnote 14) that for each valid `(xs, ys)` the values sum to 1 over `Y`
when `[Fintype Y]` holds, and are 0 outside the support. -/
@[deprecated "use PFunPDS.Behavior (partial-function `→.`, DecidableEq-free) instead of this curried support-filtering struct" (since := "2026-06-20")]
structure Behavior (X : Type u) (Y : Type v) : Type (max u v + 1) where
  /-- The conditional probability kernel at round `i+1` (0-based index `i`). -/
  step : ℕ → List X → List Y → Y → NNReal

namespace Behavior

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 3.18 (footnote 14): well-definedness of a behavior at a
**valid** history.

For a round `i`, a history pair `(xs, ys)` is *valid* when `ys.length = i` and
`xs.length = i + 1` (i.e. `xs = xⁱ⁺¹` is the input history and `ys = yⁱ` the
output history at the previous step).  At such a valid history the kernel must
be a genuine probability distribution over the next output, i.e. its values
sum to 1 over `Y`.

`WellDefinedAt b i xs ys` is the *conditional* claim: **if** `(xs, ys)` is a
valid history for round `i`, **then** the conditional probabilities sum to 1.
The length conditions are hypotheses guarding the sum-to-1 conclusion — not
conjuncts asserted unconditionally.  (If they were conjuncts, the predicate
would be unsatisfiable: e.g. `i = 0, xs = [], ys = []` would demand
`[].length = 0 + 1`, i.e. `0 = 1`.)

We require `[Fintype Y]` for the sum. -/
def WellDefinedAt [Fintype Y] (b : Behavior X Y) (i : ℕ)
    (xs : List X) (ys : List Y) : Prop :=
  ys.length = i → xs.length = i + 1 →
  ∑ y : Y, b.step i xs ys y = 1

/-- CR18 Definition 3.18 (footnote 14): global well-definedness of a behavior.

A behavior is **well-defined** if, for every round `i` and every *valid* history
pair `(xs, ys)` (those with `ys.length = i` and `xs.length = i + 1`), the
conditional probabilities sum to 1 over `Y`.  This is exactly Maurer's
requirement that each `pˢ_{Yᵢ|XⁱYⁱ⁻¹}` is a conditional probability
distribution.  Histories of the wrong length impose no constraint. -/
def WellDefined [Fintype Y] (b : Behavior X Y) : Prop :=
  ∀ (i : ℕ) (xs : List X) (ys : List Y), WellDefinedAt b i xs ys

end Behavior

/-!
### Computing `b(S)` from a PDS

Given a PDS `S : PDS X Y`, we compute the behavior `b(S)` by reading off
the conditional slices `condSlice S xs ys y`.
-/

/-- CR18 Definition 3.18: the behavior `b(S)` of a probabilistic system `S`.

`behavior S` is the sequence of conditional distributions
`pˢ_{Yᵢ|XⁱYⁱ⁻¹}` for `i ≥ 1`, encoded as a `Behavior X Y` with
0-based step index.  At step `i`, `(behavior S).step i xs ys y` equals
the conditional probability `Pr[S(xs) = y | (Y₁,…,Yᵢ) = ys]` computed
by `condSlice`. -/
@[deprecated "use PFunPDS.behavior (DecidableEq-free, from Pr[·|·] conditioning) instead; this routes through condSlice support-filtering" (since := "2026-06-20")]
noncomputable def behavior [DecidableEq (List (Option Y))]
    (S : PDS X Y) : Behavior X Y where
  step _i xs ys y := condSlice S xs ys y

/-!
### CR18 Definition 3.19: Equivalence of Probabilistic Systems

Two probabilistic `(X, Y)`-systems `S` and `T` are **equivalent**, written
`S ≡ T`, when they have the same behavior, i.e. `b(S) = b(T)`.

We give two equivalent formulations:

1. **Propositional equality** (`BehaviorEq`): `behavior S = behavior T`
   — this is literally `b(S) = b(T)` and is the direct rendering of CR18 3.19.

2. **Pointwise** (`BehaviorEquiv`): for all rounds `i`, histories `xs`, `ys`,
   and outputs `y`, `(behavior S).step i xs ys y = (behavior T).step i xs ys y`.

These are definitionally equivalent; `BehaviorEquiv` is more convenient for
tactic proofs.  Both notations land under `≡ᵦ` (the CR18 `≡` symbol, subscript
to avoid clash with Lean's built-in `=` and the bounded-query `≡ₚ`).

## Relation to `≡ₚ`

The existing `RandomSystems.Equiv` module defines `≡ₚ` (`PDS.equiv`) on the
**bounded-query** type `PDS X Y q` (= `Dist (DDS X Y q)`, a finitely-supported
distribution with query bound `q`).  Definition 3.19 operates on the
**unbounded** CR18 `PDS X Y` (= `Dist (DDS X Y)`, the partial-function DDS;
CR18 3.14).  Both now share the same `RandomSystems.Dist` sub-distribution
model, but live in different DDS type families (fixed-`q` table vs.
partial-function), so the two equivalences are **not directly comparable**.
A future bridge module can relate them when the two PDS types are connected.
-/

/-- **CR18 Definition 3.19**: two probabilistic `(X, Y)`-systems are
**equivalent** when they have the same behavior.

`BehaviorEq S T` is the direct reading of `b(S) = b(T)` as propositional
equality of the `Behavior X Y` structures. -/
@[deprecated "use PFunPDS.BehaviorEq (≡ᵦ on the partial-function behavior) instead" (since := "2026-06-20")]
def BehaviorEq [DecidableEq (List (Option Y))]
    (S T : PDS X Y) : Prop :=
  behavior S = behavior T

/-- **CR18 Definition 3.19** (pointwise form): behavioral equivalence.

`BehaviorEquiv S T` holds when `b(S)` and `b(T)` agree on every round `i` and
every input/output history pair — the pointwise unfolding of `BehaviorEq`. -/
@[deprecated "use PFunPDS.BehaviorEq / behaviorEq_ext (partial-function behavior) instead" (since := "2026-06-20")]
def BehaviorEquiv [DecidableEq (List (Option Y))]
    (S T : PDS X Y) : Prop :=
  ∀ (i : ℕ) (xs : List X) (ys : List Y) (y : Y),
    (behavior S).step i xs ys y = (behavior T).step i xs ys y

/-- Notation for CR18 Definition 3.19 equivalence, matching `S ≡ T`. -/
scoped notation:50 S " ≡ᵦ " T => BehaviorEquiv S T

/-!
### Equivalence between the two formulations of CR18 3.19
-/

/-- CR18 3.19: `b(S) = b(T)` (propositional equality) is equivalent to the
pointwise condition `∀ i xs ys y, …`.

The forward direction unfolds equality of `Behavior` structures; the backward
direction folds it using `funext`. -/
theorem behaviorEq_iff_behaviorEquiv [DecidableEq (List (Option Y))]
    {S T : PDS X Y} : BehaviorEq S T ↔ S ≡ᵦ T := by
  constructor
  · intro h i xs ys y
    exact congrFun (congrFun (congrFun (congrFun (congrArg Behavior.step h) i) xs) ys) y
  · intro h
    show behavior S = behavior T
    have hstep : (behavior S).step = (behavior T).step :=
      funext fun i => funext fun xs => funext fun ys => funext fun y => h i xs ys y
    exact Behavior.mk.injEq _ _ ▸ hstep

/-- Equality of all cumulative transcript masses implies equality of behavior.

This is the reverse direction of the usual chain-rule use: since each
conditional slice is the ratio of a full cumulative joint mass by its prefix
mass, pointwise equality of `jointProb` immediately makes every slice equal. -/
theorem behaviorEq_of_jointProb_eq [DecidableEq (List (Option Y))]
    {S T : PDS X Y} (h : ∀ xs ys, jointProb S xs ys = jointProb T xs ys) :
    BehaviorEq S T := by
  apply behaviorEq_iff_behaviorEquiv.mpr
  intro i xs ys y
  simp [behavior, condSlice, h xs (ys ++ [y]), h xs.dropLast ys]

namespace BehaviorEquiv

variable [DecidableEq (List (Option Y))]

/-- Behavioral equivalence is reflexive. -/
theorem refl (S : PDS X Y) : S ≡ᵦ S := fun _ _ _ _ => rfl

/-- Behavioral equivalence is symmetric. -/
theorem symm {S T : PDS X Y} (h : S ≡ᵦ T) : T ≡ᵦ S :=
  fun i xs ys y => (h i xs ys y).symm

/-- Behavioral equivalence is transitive. -/
theorem trans {S T U : PDS X Y} (hST : S ≡ᵦ T) (hTU : T ≡ᵦ U) : S ≡ᵦ U :=
  fun i xs ys y => (hST i xs ys y).trans (hTU i xs ys y)

/-- Behavioral equivalence is an equivalence relation. -/
theorem equivalence : Equivalence (BehaviorEquiv (X := X) (Y := Y)) where
  refl  := refl
  symm  := symm
  trans := trans

/-- Two equal PDS are behaviorally equivalent (CR18 3.19: `S = T → S ≡ T`). -/
theorem of_eq {S T : PDS X Y} (h : S = T) : S ≡ᵦ T := by
  subst h; exact refl S

/-- `b(S) = b(T)` (the propositional form) follows from behavioral equivalence. -/
theorem behaviorEq_of {S T : PDS X Y} (h : S ≡ᵦ T) : BehaviorEq S T :=
  behaviorEq_iff_behaviorEquiv.mpr h

end BehaviorEquiv

/-!
### Example instantiations (CR18 Examples 3.7–3.8 sketches)

These are stubs: the `condSlice` formula is stated; closing the arithmetic
requires more Mathlib lemmas on PMF sums and is deferred.
-/

/-- CR18 Example 3.8 (sketch): the beacon `B` has flat conditional
distributions: every output `y` at every round is equally likely given any
history, i.e. `pᴮ_{Yᵢ|XⁱYⁱ⁻¹}(y, xⁱ, yⁱ⁻¹) = 1/|Y|` for all args.

This is stated as a predicate on an abstract `Behavior` rather than
computed from a PDS, since constructing the concrete PMF for an infinite
beacon requires additional infrastructure. -/
def IsBeacon [Fintype Y] [Nonempty Y] (b : Behavior X Y) : Prop :=
  ∀ (i : ℕ) (xs : List X) (ys : List Y) (y : Y),
    b.step i xs ys y = (1 : NNReal) / Fintype.card Y

/-- Sanity check that `Behavior.WellDefined` is **non-vacuous**: a beacon
behavior (flat `1/|Y|` conditional distributions) is well-defined, since the
values sum to `|Y| · (1/|Y|) = 1` over the output alphabet.

This also witnesses that the length conditions in `WellDefinedAt` are correctly
phrased as hypotheses (guards) rather than conjuncts: with conjuncts the
predicate would be unsatisfiable and this lemma unprovable. -/
theorem IsBeacon.wellDefined [Fintype Y] [Nonempty Y] {b : Behavior X Y}
    (hb : IsBeacon b) : Behavior.WellDefined b := by
  intro i xs ys _ _
  have hstep : ∀ y : Y, b.step i xs ys y = (1 : NNReal) / Fintype.card Y :=
    fun y => hb i xs ys y
  rw [Finset.sum_congr rfl (fun y _ => hstep y),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self]
  simp [Fintype.card_ne_zero]

/-!
### CR18 Example 3.8: the concrete beacon behavior

CR18 Example 3.8 introduces the **Y-beacon** `B`, a concrete `Behavior` (not
just a predicate) in which every conditional distribution is the flat uniform
distribution over `Y`:

  `pᴮ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹) = 1/|Y|`

for **all** choices of the arguments (all rounds `i`, all histories `xs`/`ys`,
all outputs `y`).

Maurer also writes `Bₙ` for the special case `Y = {0,1}^n = Fin (2^n)`.

## Strategy

We construct the beacon directly as a `Behavior X Y` whose `step` function
is the constant `1/|Y|`.  The input alphabet `X` is left generic (Maurer uses
the unary trigger `{⋄}`, but the flatness condition is independent of `X`).
We then prove `IsBeacon beaconBehavior` by `rfl`, and `Bₙ` is the instance
at `Y := Fin (2^n)`.
-/

/-- CR18 Example 3.8: the **Y-beacon behavior** `beaconBehavior`.

The beacon `B` is the `Behavior X Y` whose conditional kernel at every round
`i`, every input history `xs`, every output history `ys`, and every candidate
output `y` equals `1/|Y|`:

  `(beaconBehavior).step i xs ys y = (1 : ENNReal) / Fintype.card Y`

This is the direct Lean transcription of Maurer's formula
`pᴮ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹) = 1/|Y|` for all arguments (CR18 Ex 3.8).

The input alphabet `X` is left generic; the unary trigger alphabet
`Trigger` is the intended specialization but the beacon property is
alphabet-independent. -/
noncomputable def beaconBehavior [Fintype Y] [Nonempty Y] : Behavior X Y where
  step _i _xs _ys _y := (1 : NNReal) / Fintype.card Y

/-- CR18 Example 3.8: `beaconBehavior` satisfies `IsBeacon`.

The beacon behavior is a beacon: every conditional probability equals `1/|Y|`,
matching the predicate definition exactly by `rfl`. -/
theorem beaconBehavior_isBeacon [Fintype Y] [Nonempty Y] :
    IsBeacon (beaconBehavior (X := X) (Y := Y)) :=
  fun _i _xs _ys _y => rfl

/-- CR18 Example 3.8: `beaconBehavior` is well-defined (the flat uniform
distribution over `Y` sums to 1 at every valid history).

This follows directly from `IsBeacon.wellDefined` and `beaconBehavior_isBeacon`. -/
theorem beaconBehavior_wellDefined [Fintype Y] [Nonempty Y] :
    Behavior.WellDefined (beaconBehavior (X := X) (Y := Y)) :=
  IsBeacon.wellDefined beaconBehavior_isBeacon

/-!
#### `Bₙ`: the bitstring beacon

CR18 writes `Bₙ` for the beacon with output alphabet `Y = {0, 1}^n`, i.e.
`Y = Fin (2^n)`.  We define `beaconBₙ n` as the specialisation of
`beaconBehavior` at `Y := Fin (2^n)` with the unary trigger input alphabet
`Trigger`.
-/

/-- CR18 Example 3.8: the bitstring beacon `Bₙ`.

`beaconBn n` is the beacon with output alphabet `{0, 1}^n = Fin (2^n)` and
input alphabet `Trigger` (the unary alphabet `{⋄}`).  The conditional
probability at every round and every output `y : Fin (2^n)` equals
`1 / (2^n : ENNReal)`, matching Maurer's `Bₙ`. -/
noncomputable def beaconBn (n : ℕ) : Behavior Trigger (Fin (2 ^ n)) :=
  beaconBehavior

/-- CR18 Example 3.8: `beaconBn n` satisfies `IsBeacon`. -/
theorem beaconBn_isBeacon (n : ℕ) : IsBeacon (beaconBn n) :=
  beaconBehavior_isBeacon

/-!
### CR18 Definition 3.20: Cumulative Behavior

The **cumulative description** of the behavior of a probabilistic `(X, Y)`-system
`S` is the sequence `pˢ_{Yⁱ|Xⁱ}` of conditional probability distributions, for
`i ≥ 1`, where

  `pˢ_{Yⁱ|Xⁱ}(yⁱ, xⁱ) = Pr[ S(x₁) = y₁, S(x₁,x₂) = y₂, …, S(xⁱ) = yᵢ ]`

This is the joint probability that the system outputs the full history `yⁱ` on the
full input history `xⁱ` (where each `S(xʲ)` is queried adaptively for `j = 1,…,i`).

In our formalization, this is exactly `jointProb S xs ys` (Definition 3.18 file):
the pushforward probability that the PDS produces output sequence `ys` on inputs `xs`.

**Equation 3.2** (the key consistency identity):

  `pˢ_{Yⁱ|Xⁱ}(yⁱ, xⁱ) = ∏_{j=1}^{i} pˢ_{Yⱼ|XʲYʲ⁻¹}(yⱼ, xʲ, yʲ⁻¹)`

i.e. the cumulative joint distribution equals the product of the step-wise
conditional slices from the behavior `b(S)`.

The cumulative description is *redundant* (equivalent to the behavior) but often
easier to work with.  In particular, if `S` answers at most `q` queries, the
full behavior is determined by `pˢ_{Yq|Xq}`.
-/

/-- CR18 Definition 3.20: the **cumulative behavior type**.

A `CumulBehavior X Y` is a sequence of joint conditional distributions: for each
round `i : ℕ`, a function
```
  joint : List X → List Y → ENNReal
```
mapping `(xⁱ, yⁱ)` to the joint probability `pˢ_{Yⁱ|Xⁱ}(yⁱ, xⁱ)`.

Note: `joint i xs ys` should be interpreted as the probability that
`S(x₁) = y₁ ∧ … ∧ S(xs) = ys.getLast?` where `xs`, `ys` have the same length `i`. -/
structure CumulBehavior (X : Type u) (Y : Type v) : Type (max u v + 1) where
  /-- The joint probability kernel at round `i` (0-based; round `i` corresponds
      to a history of length `i+1`). -/
  joint : ℕ → List X → List Y → NNReal

namespace CumulBehavior

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 3.20: the cumulative behavior `pˢ_{Yⁱ|Xⁱ}` of a PDS `S`.

`cumulBehavior S` is the sequence where `(cumulBehavior S).joint i xs ys` equals
`jointProb S xs ys` — the probability that the PDS draws a DDS producing output
sequence `ys` on input sequence `xs` (both of length `i+1`, 0-based). -/
noncomputable def ofPDS [DecidableEq (List (Option Y))]
    (S : PDS X Y) : CumulBehavior X Y where
  joint _i xs ys := jointProb S xs ys

end CumulBehavior

/-- CR18 Definition 3.20: compute the cumulative behavior from a PDS.

This is the canonical constructor: `cumulBehavior S` is the `CumulBehavior X Y`
whose joint kernel at every round is the `jointProb` of `S`. -/
noncomputable def cumulBehavior [DecidableEq (List (Option Y))]
    (S : PDS X Y) : CumulBehavior X Y :=
  CumulBehavior.ofPDS S

/-!
### Equation 3.2: the consistency identity

The cumulative joint distribution equals the product of the step-wise conditional
slices:
  `pˢ_{Yⁱ|Xⁱ}(yⁱ, xⁱ) = ∏_{j=0}^{i-1} pˢ_{Yⱼ₊₁|Xʲ⁺¹Yʲ}(yⱼ₊₁, xʲ⁺¹, yʲ)`

In our encoding:
- The left-hand side is `jointProb S xs ys` where `xs`, `ys` have length `n`.
- The right-hand side is the chain-rule product
  `jointProb S [] [] * ∏_{k=0}^{n-1} condSlice S (xs.take (k+1)) (ys.take k) (ys[k])`.

The base factor `jointProb S [] []` is the probability of the **empty**
conditioning event — `Pr[⊤]`, the total mass of `S`.  For CR18's probabilistic
systems (random variables over DDSs, i.e. weight-1 distributions) this factor
equals `1`, and the product is verbatim CR18's RHS `∏_{j=1}^{i} pˢ_{Yⱼ|XʲYʲ⁻¹}`
(CR18 states Eq 3.2 for `i ≥ 1` over probability distributions).  Our PDS model
(`Dist (DDS X Y)`, LM20 Def 1) deliberately admits sub-distributions of
arbitrary weight, and the chain rule for sub-probability measures reads
  `Pr[A₁ ∧ … ∧ Aₙ] = Pr[⊤] · ∏ⱼ Pr[Aⱼ | A₁,…,Aⱼ₋₁]`
(each conditional being the ratio convention of `condSlice`); the `Pr[⊤]` base
factor is what makes the identity hold at every weight — and at `n = 0`, where
both sides are the mass of the trivial event.
-/

/-- **Auxiliary**: the chain-rule product of conditional slices for the first
`n` rounds, given full input history `xs` and output history `ys`.

`condSliceProd S xs ys n` equals
`jointProb S [] [] * ∏_{k=0}^{n-1} condSlice S (xs.take (k+1)) (ys.take k) (ys.getD k default)`.

This is the right-hand side of Eq 3.2 restricted to the first `n` steps, with
the chain-rule base factor `jointProb S [] []` (= `Pr[⊤]`, the total mass of
`S`).  On CR18's domain — weight-1 distributions — the base factor is `1` and
this is exactly CR18's product `∏_{j=1}^{n} pˢ_{Yⱼ|XʲYʲ⁻¹}`.

EQUATIONAL RECAST 2026-06-10: added the base factor `jointProb S [] []`
(previously the empty-product base was `1`).  Without it, Eq 3.2 is false on
the LM20 sub-distribution model (`n = 0` would force `S.weight = 1`); with it,
the identity is the weight-general chain rule and specializes verbatim to
CR18's Eq 3.2 on weight-1 systems. -/
noncomputable def condSliceProd [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (xs : List X) (ys : List Y) (n : ℕ) : NNReal :=
  jointProb S [] [] *
    ((List.finRange n).map (fun k =>
      condSlice S (xs.take (k.val + 1)) (ys.take k.val)
        (ys.getD k.val default))).prod

/-- `condSliceProd` at `n = 0` is the chain-rule base factor: the mass of the
empty conditioning event (`= 1` for CR18's weight-1 systems). -/
theorem condSliceProd_zero [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (xs : List X) (ys : List Y) :
    condSliceProd S xs ys 0 = jointProb S [] [] := by
  simp [condSliceProd]

/-- Recursion for `condSliceProd`: the product over `n + 1` rounds is the
product over `n` rounds times the `n`-th conditional slice. -/
theorem condSliceProd_succ [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (xs : List X) (ys : List Y) (n : ℕ) :
    condSliceProd S xs ys (n + 1) =
      condSliceProd S xs ys n *
        condSlice S (xs.take (n + 1)) (ys.take n) (ys.getD n default) := by
  unfold condSliceProd
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Function.comp_def, Fin.val_castSucc, Fin.val_last]
  ring

/-- Fiber-sum form of `jointProb`: the mass under `S` of the event
`{s | s.outputSeq xs = ys.map some}`, summed over the support of `S`. -/
theorem jointProb_eq_sum_support [DecidableEq (List (Option Y))]
    (S : PDS X Y) (xs : List X) (ys : List Y) :
    jointProb S xs ys =
      ∑ s ∈ S.support, if s.outputSeq xs = ys.map some then S s else 0 := by
  classical
  simp only [jointProb, jointOutputDist, Dist.fTransform]
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rfl

/-- The empty transcript event is sure: its joint probability is the total mass
of the PDS. -/
theorem jointProb_nil_nil_eq_mass [DecidableEq (List (Option Y))]
    (S : PDS X Y) :
    jointProb S [] [] = S.sum fun _ p => p := by
  rw [jointProb_eq_sum_support]
  simp [DDS.outputSeq]
  rfl

/-- `DDS.outputSeq` commutes with `List.take`: the output sequence on a
truncated input history is the truncation of the output sequence. -/
theorem DDS.outputSeq_take (s : DDS X Y) (xs : List X) (n : ℕ) :
    s.outputSeq (xs.take n) = (s.outputSeq xs).take n := by
  apply List.ext_getElem
  · simp [DDS.outputSeq]
  · intro i h₁ h₂
    have hi : i + 1 ≤ n := by
      simp only [DDS.outputSeq, List.length_map, List.length_finRange,
        List.length_take] at h₁
      omega
    have hpfx : (xs.take n).take (i + 1) = xs.take (i + 1) := by
      rw [List.take_take, Nat.min_eq_left hi]
    simp only [DDS.outputSeq, List.getElem_take, List.getElem_map,
      List.getElem_finRange, Fin.val_cast, hpfx]

/-- Monotonicity of the joint probability in the history length: extending the
history by one query can only shrink the event `{s | s.outputSeq · = ·}`. -/
theorem jointProb_take_succ_le [DecidableEq (List (Option Y))]
    (S : PDS X Y) (xs : List X) (ys : List Y) (n : ℕ) :
    jointProb S (xs.take (n + 1)) (ys.take (n + 1)) ≤
      jointProb S (xs.take n) (ys.take n) := by
  classical
  rw [jointProb_eq_sum_support, jointProb_eq_sum_support]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases h : s.outputSeq (xs.take (n + 1)) = (ys.take (n + 1)).map some
  · have h1 : (xs.take (n + 1)).take n = xs.take n := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ n)]
    have h2 : (ys.take (n + 1)).take n = ys.take n := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ n)]
    have hev : s.outputSeq (xs.take n) = (ys.take n).map some := by
      calc s.outputSeq (xs.take n)
          = s.outputSeq ((xs.take (n + 1)).take n) := by rw [h1]
        _ = (s.outputSeq (xs.take (n + 1))).take n := DDS.outputSeq_take ..
        _ = ((ys.take (n + 1)).map some).take n := by rw [h]
        _ = ((ys.take (n + 1)).take n).map some := List.map_take.symm
        _ = (ys.take n).map some := by rw [h2]
    rw [if_pos h, if_pos hev]
  · rw [if_neg h]
    exact zero_le _

/-- The one-step chain rule: the joint probability of an `(n+1)`-round history
factors as the joint probability of its `n`-round prefix times the `n`-th
conditional slice.  The 0-denominator corner of the `condSlice` ratio is
covered by monotonicity (`jointProb_take_succ_le`). -/
theorem jointProb_take_succ [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (xs : List X) (ys : List Y) {n : ℕ}
    (hx : n < xs.length) (hy : n < ys.length) :
    jointProb S (xs.take (n + 1)) (ys.take (n + 1)) =
      jointProb S (xs.take n) (ys.take n) *
        condSlice S (xs.take (n + 1)) (ys.take n) (ys.getD n default) := by
  have hconcat : ys.take n ++ [ys.getD n default] = ys.take (n + 1) := by
    rw [List.getD_eq_getElem ys default hy, List.take_add_one,
      List.getElem?_eq_getElem hy]
    rfl
  have hdrop : (xs.take (n + 1)).dropLast = xs.take n := by
    rw [List.dropLast_eq_take, List.length_take, List.take_take]
    congr 1
    omega
  unfold condSlice
  rw [hconcat, hdrop]
  rcases eq_or_ne (jointProb S (xs.take n) (ys.take n)) 0 with h0 | h0
  · have hle := jointProb_take_succ_le S xs ys n
    rw [h0] at hle ⊢
    rw [zero_mul]
    exact le_antisymm hle (zero_le _)
  · rw [mul_comm]
    exact (div_mul_cancel₀ _ h0).symm

/-- **CR18 Eq 3.2**: the consistency identity for the cumulative behavior.

The joint distribution `pˢ_{Yⁿ|Xⁿ}(yⁿ, xⁿ)` equals the product of the
step-wise conditional distributions `∏_{j=1}^{n} pˢ_{Yⱼ|XʲYʲ⁻¹}(yⱼ, xʲ, yʲ⁻¹)`.

In Lean terms: `jointProb S xs ys = condSliceProd S xs ys xs.length`
(when `ys.length = xs.length`).

**Proof**: telescoping induction on the history length `n`.  Each step is the
one-step chain rule `jointProb_take_succ` (the `condSlice` ratio cancels by
`div_mul_cancel₀`; the 0-denominator corner is covered by the monotonicity
lemma `jointProb_take_succ_le`), and the base `n = 0` is the chain-rule base
factor `jointProb S [] []` of `condSliceProd` (see the EQUATIONAL RECAST note
there: on CR18's weight-1 domain the base factor is `1` and the statement is
verbatim CR18 Eq 3.2; on the LM20 sub-distribution model it is the
weight-general chain rule). -/
theorem cumulBehavior_eq_condSliceProd
    [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (xs : List X) (ys : List Y)
    (hlen : ys.length = xs.length) :
    jointProb S xs ys = condSliceProd S xs ys xs.length := by
  have key : ∀ n, n ≤ xs.length →
      jointProb S (xs.take n) (ys.take n) = condSliceProd S xs ys n := by
    intro n
    induction n with
    | zero => intro _; simp [condSliceProd_zero]
    | succ n ih =>
      intro hn
      have hx : n < xs.length := Nat.lt_of_succ_le hn
      have hy : n < ys.length := by omega
      rw [jointProb_take_succ S xs ys hx hy, ih (Nat.le_of_lt hx),
        condSliceProd_succ]
  have h := key xs.length le_rfl
  have hxs : xs.take xs.length = xs := List.take_length
  have hys : ys.take xs.length = ys := by
    rw [← hlen]; exact List.take_length
  rwa [hxs, hys] at h

/-- **CR18 3.20** (abstract form): the cumulative behavior can alternatively be
described by the step-wise behavior `b(S)` via Eq 3.2.

Concretely: `(cumulBehavior S).joint i xs ys = condSliceProd S xs ys xs.length`
when `ys.length = xs.length`. -/
theorem cumulBehavior_joint_eq
    [DecidableEq (List (Option Y))] [Inhabited Y]
    (S : PDS X Y) (i : ℕ) (xs : List X) (ys : List Y)
    (hlen : ys.length = xs.length) :
    (cumulBehavior S).joint i xs ys = condSliceProd S xs ys xs.length :=
  cumulBehavior_eq_condSliceProd S xs ys hlen

/-!
### CR18 Example 3.6: the URF behavior formula (Equation 3.1)

For an `(X, Y)`-URF `R` (see CR18 Example 3.5), the behavior formula is:

```
            ⎧  1     if xᵢ = xⱼ for some j < i and yᵢ = yⱼ   (consistent repeat)
            ⎪
pᴿ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹) = ⎨  0     if xᵢ = xⱼ for some j < i and yᵢ ≠ yⱼ  (inconsistent repeat)
            ⎪
            ⎩ 1/|Y| if xᵢ ≠ xⱼ for all j < i                  (fresh input)
```

and the formula is **undefined** if `xⱼ = xₖ` and `yⱼ ≠ yₖ` for some `j < k < i`
(the history itself is inconsistent — the conditioning event has probability 0
for a function that must answer equal inputs identically).

We model the "undefined" case as 0 (following the `condSlice` convention).

## Key predicates

* `IsConsistentHistory xs ys` — the transcript `(xs, ys)` is self-consistent:
  every repeated input in `xs` has the same output in `ys`.
* `URFKernel` — the explicit three-case formula for the conditional probability.
* `URFBehavior` — the `Behavior X Y` built from `URFKernel`.

## Theorem

`urfBehavior_spec` states the three-case characterization of `URFKernel`
directly from the CR18 source.
-/

section Ex36

variable {X : Type u} {Y : Type v}

/-!
#### History consistency (for the URF "undefined" guard)

A pair of lists `(xs, ys)` (same length `n`) is **consistent** when
the map `xs[j] ↦ ys[j]` is well-defined as a function, i.e. whenever
`xs[j] = xs[k]` we have `ys[j] = ys[k]`.  This corresponds to Maurer's
condition "xⱼ = xₖ → yⱼ = yₖ for all j,k".
-/

/-- CR18 Ex 3.6: a transcript `(xs, ys)` is **consistent** if, whenever two
input positions carry the same value, their corresponding outputs also agree.

Formally: for all `j k : Fin xs.length`, `xs[j] = xs[k] → ys[j] = ys[k]`
(assuming `ys.length = xs.length`).

This is the condition under which the URF behavior formula is defined.  If a
history is inconsistent, the conditioning event `S(x₁) = y₁ ∧ … ∧ S(xᵢ₋₁) = yᵢ₋₁`
has probability 0 for a random function (which must answer equal inputs identically),
so the conditional distribution is undefined / set to 0. -/
def IsConsistentHistory [DecidableEq X] [DecidableEq Y]
    (xs : List X) (ys : List Y) (hlen : xs.length = ys.length) : Prop :=
  ∀ (j k : Fin xs.length),
    xs[j] = xs[k] →
    ys[j.cast hlen] = ys[k.cast hlen]

/-!
#### The three-case formula (Eq 3.1)

`urfBehaviorKernel xs_prev ys_prev x_curr y_curr` computes
`pᴿ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹)` given:

* `xs_prev : List X` — the previous `i-1` inputs `x₁, …, xᵢ₋₁`
* `ys_prev : List Y` — the previous `i-1` outputs `y₁, …, yᵢ₋₁`
* `x_curr  : X`     — the current input `xᵢ`
* `y_curr  : Y`     — the candidate output `yᵢ`

The formula returns:
* `1`      if `∃ j, xs_prev[j] = x_curr ∧ ys_prev[j] = y_curr`
* `0`      if `∃ j, xs_prev[j] = x_curr ∧ ys_prev[j] ≠ y_curr`
* `1/|Y|`  otherwise (fresh input)

The `Fintype Y` instance is needed only for the `1/|Y|` case.
-/

/-- CR18 Example 3.6 / Equation 3.1: the conditional-probability kernel of a
uniform random function at round `i`.

Given the previous input/output history `(xs_prev, ys_prev)` and the current
input `x_curr`, the probability of producing output `y_curr` is:

* `1`     — if some previous input matches `x_curr` with matching output
             (the URF is deterministic for repeated inputs)
* `0`     — if some previous input matches `x_curr` with a *different* output
             (impossible for a function)
* `1/|Y|` — if `x_curr` is fresh (not seen before); each output is equally likely

The histories `xs_prev` and `ys_prev` are assumed to have the same length
(the guard `hlen` below), but the definition is total: mismatched lengths simply
result in the formula treating all entries accessible to both lists.

`DecidableEq X` and `DecidableEq Y` are needed for the equality tests.
`Fintype Y` is needed for `1/|Y|`. -/
noncomputable def urfBehaviorKernel [DecidableEq X] [DecidableEq Y] [Fintype Y]
    (xs_prev : List X) (ys_prev : List Y)
    (x_curr : X) (y_curr : Y) : NNReal :=
  -- zip the previous history into (input, output) pairs
  let history := xs_prev.zip ys_prev
  -- Look for a previous (x, y) pair matching x_curr
  let matched := history.filter (fun p => p.1 = x_curr)
  if matched = [] then
    -- x_curr is fresh: each output is equally likely
    (1 : NNReal) / (Fintype.card Y : NNReal)
  else if matched.any (fun p => p.2 = y_curr) then
    -- some previous entry has (x_curr, y_curr): probability 1
    1
  else
    -- some previous entry has (x_curr, ·) but none has y_curr: probability 0
    0

/-!
#### The URF behavior
-/

/-- CR18 Example 3.6: the explicit **URF behavior**.

`urfBehavior` is the `Behavior X Y` whose step-`i` kernel is `urfBehaviorKernel`,
i.e. for each round `i`, history pair `(xs, ys)`, and candidate output `y`,

  `(urfBehavior).step i xs ys y = urfBehaviorKernel xs.dropLast ys xs.getLast! y`

where `xs` carries the full input history at round `i` (length `i+1`) and
`ys` carries the previous output history (length `i`).

(We pass `xs.dropLast` and `xs.getLast!` rather than splitting the `step` signature
because `Behavior.step` takes the *full* input history `xs` of length `i+1`.) -/
noncomputable def urfBehavior [DecidableEq X] [DecidableEq Y] [Fintype Y]
    [Inhabited X] : Behavior X Y where
  step _i xs ys y :=
    match xs.getLast? with
    | none   => 0  -- empty input history: ill-formed at this step; set to 0
    | some x_curr => urfBehaviorKernel xs.dropLast ys x_curr y

/-!
#### Specification theorem (Eq 3.1)

`urfBehavior_spec` states the three cases of Eq 3.1 as a disjunction.
-/

/-- CR18 Example 3.6 (Equation 3.1): the three-case specification of the URF
behavior kernel.

For non-empty input history `xs` (so `xs.getLast?` is `some x_curr`) and
output history `ys` of the same length as `xs.dropLast`:

1. **Consistent repeat**: if some `j < xs.dropLast.length` has
   `xs.dropLast[j] = x_curr` and `ys[j] = y_curr`, the kernel equals `1`.

2. **Inconsistent repeat**: if some `j < xs.dropLast.length` has
   `xs.dropLast[j] = x_curr` and `ys[j] ≠ y_curr` (and no position `j`
   gives the consistent case), the kernel equals `0`.

3. **Fresh**: if no `j` has `xs.dropLast[j] = x_curr`, the kernel equals
   `1/|Y|`.

This is a direct Lean transcription of CR18 Eq 3.1. -/
theorem urfBehavior_spec [DecidableEq X] [DecidableEq Y] [Fintype Y]
    (xs : List X) (ys : List Y) (x_curr : X) (y_curr : Y) :
    let matched := (xs.zip ys).filter (fun p => decide (p.1 = x_curr) = true)
    (matched = [] →
      urfBehaviorKernel xs ys x_curr y_curr = (1 : NNReal) / Fintype.card Y) ∧
    (matched ≠ [] → (matched.any (fun p => decide (p.2 = y_curr) = true)) →
      urfBehaviorKernel xs ys x_curr y_curr = 1) ∧
    (matched ≠ [] → ¬(matched.any (fun p => decide (p.2 = y_curr) = true)) →
      urfBehaviorKernel xs ys x_curr y_curr = 0) := by
  -- The three cases follow by unfolding the `urfBehaviorKernel` if-branches
  -- (`if_pos` / `if_neg` matching the decide guards).
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp only [urfBehaviorKernel]
    rw [if_pos (by simpa using h)]
  · simp only [urfBehaviorKernel]
    rw [if_neg (by simpa using h1), if_pos (by simpa using h2)]
  · simp only [urfBehaviorKernel]
    rw [if_neg (by simpa using h1), if_neg (by simpa using h2)]

end Ex36

/-!
### CR18 Example 3.7: the VIL-URF behavior

CR18 Example 3.7 (source ~line 3401):

> Equation (3.1) applies equally well if `X` is infinite, but this behavior
> does not correspond to a PDS as defined here since the sample space would
> be uncountable. However, we can consider the **behavior** without an
> underlying probabilistic system. The behavior of a URF with `X = {0,1}*` is
> called a **variable input-length URF (VIL-URF)** and is sometimes denoted
> as `Vₙ` if `Y = {0,1}ⁿ`.

The key point is that the behavior formula (Eq 3.1 = `urfBehaviorKernel`) is
still perfectly well-typed when `X = List Bool` (bitstrings of any length),
even though there is **no underlying finite PDS**: the input alphabet is
infinite, so no `Fintype X` instance exists, and the usual `PDS X Y` would
require sampling over an uncountable function space.

## Lean strategy

We represent the VIL-URF directly as a `Behavior (List Bool) (Fin (2^n))`
built from the already-defined `urfBehaviorKernel`.  Because `List Bool` has
a `DecidableEq` instance (inherited from `Bool`) and `Fin (2^n)` is a
`Fintype`, we can reuse `urfBehaviorKernel` verbatim.

The claim that there is **no underlying finite PDS** is witnessed by
`List.infinite_of_injective_forAll` — `List Bool` has no `Fintype` instance.
We record this as an axiom-free proof that `Infinite (List Bool)`.
-/

section Ex37

/-!
#### VIL-URF behavior kernel (infinite `X`)

`vilURFKernel` is `urfBehaviorKernel` specialised to `X := List Bool`.
It has type:
```
  vilURFKernel : List (List Bool) → List Y → List Bool → Y → NNReal
```
and is defined by the same three-case formula as Eq 3.1.
-/

/-- CR18 Example 3.7: the VIL-URF conditional-probability kernel.

This is `urfBehaviorKernel` at `X := List Bool`, which is a countably infinite
type with `DecidableEq`.  The three-case formula (Eq 3.1) applies:

* **Fresh** (`x_curr` has not appeared in `xs_prev`): probability `1/|Y|`.
* **Consistent repeat** (`x_curr` appeared before with output `y_curr`): probability `1`.
* **Inconsistent repeat** (`x_curr` appeared before with a different output): probability `0`.

The formula is well-typed without any `Fintype (List Bool)` requirement. -/
noncomputable def vilURFKernel [DecidableEq Y] [Fintype Y]
    (xs_prev : List (List Bool)) (ys_prev : List Y)
    (x_curr : List Bool) (y_curr : Y) : NNReal :=
  urfBehaviorKernel xs_prev ys_prev x_curr y_curr

/-!
#### VIL-URF behavior `Vₙ`

`vilURFBehavior n` is the `Behavior (List Bool) (Fin (2^n))` that Maurer calls
`Vₙ`.  It is constructed directly from `vilURFKernel` (= `urfBehaviorKernel`)
and **does not require** a `Fintype (List Bool)` instance, witnessing Maurer's
remark that the behavior can be considered "without an underlying probabilistic
system" when `X` is infinite.
-/

/-- CR18 Example 3.7: the VIL-URF behavior `Vₙ`.

`vilURFBehavior n` is the `Behavior (List Bool) (Fin (2^n))` built from the
three-case kernel `vilURFKernel`.  At each round `i`, input history `xs` (a
list of bitstrings), output history `ys`, and candidate output `y : Fin (2^n)`,
the conditional probability is:

* `1/2ⁿ`  if `xs.getLast!` is fresh (not seen in `xs.dropLast`)
* `1`      if `xs.getLast!` was seen before with the same output
* `0`      if `xs.getLast!` was seen before with a different output

This is the Lean transcription of Maurer's `Vₙ` (CR18 Example 3.7). -/
noncomputable def vilURFBehavior (n : ℕ) : Behavior (List Bool) (Fin (2 ^ n)) where
  step _i xs ys y :=
    match xs.getLast? with
    | none       => 0
    | some x_curr => vilURFKernel xs.dropLast ys x_curr y

/-!
#### VIL-URF has no underlying finite PDS (`X` infinite)

CR18 notes that `Vₙ` does **not** correspond to a PDS because `X = {0,1}*` is
infinite.  In Lean, `List Bool` is an `Infinite` type, so no `Fintype (List Bool)`
instance exists.  We record this fact.
-/

/-- `List Bool` (= `{0,1}*`) is an infinite type — there is no `Fintype`
instance.  This witnesses CR18 Example 3.7's remark that the VIL-URF behavior
has no underlying finite PDS. -/
theorem listBool_infinite : Infinite (List Bool) :=
  inferInstance

/-!
#### Predicate: a behavior is a VIL-URF

`IsVILURF b` states that the behavior `b : Behavior (List Bool) (Fin (2^n))`
satisfies the VIL-URF conditional-distribution formula (Eq 3.1 with
`X = List Bool`).  The definition mirrors `IsBeacon` for Ex 3.8.
-/

/-- CR18 Example 3.7: predicate for the VIL-URF conditional-distribution formula.

A behavior `b : Behavior (List Bool) Y` is a **VIL-URF behavior** if, at every
round, the conditional probability of output `y` given history `(xs, ys)` is:

* `1/|Y|` when `xs.getLast?` is fresh (not in `xs.dropLast`)
* `1`      when `xs.getLast?` was already answered with `y`
* `0`      when `xs.getLast?` was already answered with `y' ≠ y`

for any non-empty `xs` (for empty `xs` the kernel is 0 by convention).

This captures Maurer's remark that Eq 3.1 "applies equally well if `X` is
infinite" (Example 3.7). -/
def IsVILURF [DecidableEq Y] [Fintype Y] (b : Behavior (List Bool) Y) : Prop :=
  ∀ (i : ℕ) (xs : List (List Bool)) (ys : List Y) (y : Y),
    match xs.getLast? with
    | none       => b.step i xs ys y = 0
    | some x_curr =>
        b.step i xs ys y = vilURFKernel xs.dropLast ys x_curr y

/-- CR18 Example 3.7: `vilURFBehavior n` satisfies `IsVILURF`.

The definition of `vilURFBehavior.step` is exactly the pattern match in
`IsVILURF`, so the proof is by `rfl` (or `intro`/`rfl`). -/
theorem vilURFBehavior_isVILURF (n : ℕ) :
    IsVILURF (vilURFBehavior n) := by
  intro i xs _ys y
  simp only [vilURFBehavior]
  split <;> rfl

end Ex37

/-!
### CR18 Definition 3.21: Behavior of an Environment

CR18 Definition 3.21 (source, ~line 3572):

> The behavior of a `(Y, X)`-environment `E`, denoted `b(E)`, is the
> sequence `pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}` (for `i ≥ 1`) of conditional probability
> distributions.

This is the **environment-side dual** of Definition 3.18.  Where `b(S)`
records the conditional probability of the *output* `Yᵢ` given the full
input history `Xⁱ` and previous output history `Yⁱ⁻¹`, `b(E)` records the
conditional probability of the *next input* `Xᵢ` given the previous input
history `Xⁱ⁻¹` and the previous output history `Yⁱ⁻¹` (i.e. the
environment's own view of the conversation).

Concretely, a `(Y,X)`-PDE is `PDE X Y = Dist (DDE X Y)` where
`DDE X Y = List (Option Y) → Option X` (a DDE maps output histories to
the next input, or `none` = stop).  The conditional probability at step `i`
is:

  `pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(xᵢ, xⁱ⁻¹, yⁱ⁻¹)
    := Pr[ E(yⁱ⁻¹) = xᵢ | E(y¹) = x₁, …, E(yⁱ⁻²) = xᵢ₋₁ ]`

We follow the *exact same construction* as `b(S)`:

1. `DDE.inputSeq e ys` — the sequence of inputs the DDE emits on a fixed
   output history `ys` (prefix by prefix), analogous to `DDS.outputSeq`.
2. `envJointProb E ys xs` — the probability that the PDE emits the input
   sequence `xs` in response to output history `ys`, analogous to
   `jointProb`.
3. `envCondSlice E ys_prev xs_prev x` — the conditional probability of
   emitting `xᵢ` given the history `(xⁱ⁻¹, yⁱ⁻¹)`, analogous to
   `condSlice`.
4. `EnvBehavior X Y` — the type of an environment behavior sequence,
   analogous to `Behavior X Y` but with the roles of `X` and `Y` swapped:
   at step `i`, `step i xs ys x` models
   `pᴱ_{Xᵢ₊₁|Xⁱ⁺¹Yⁱ}(x, xs, ys)`.
   Wait — checking against the paper: `pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(xᵢ, xⁱ⁻¹, yⁱ⁻¹)`.
   So at step `i` (1-based), the conditioning is on `xⁱ⁻¹` (previous `i-1`
   inputs) and `yⁱ⁻¹` (previous `i-1` outputs).  This is the DDE's history:
   - it has already emitted `x₁,…,xᵢ₋₁` (conditioned on)
   - it has already received `y₁,…,yᵢ₋₁` (the output history it sees)
   Note: unlike `b(S)` where the system sees the FULL current input `xⁱ`,
   the environment at step `i` has only seen the PREVIOUS `yⁱ⁻¹` when it
   chooses `xᵢ`.  So the environment's "conditional" lives over a function
   whose argument is `List (Option Y)` of length `i-1`.
5. `envBehavior E : EnvBehavior X Y` — the behavior of a PDE, analogous to
   `behavior S`.
-/

/-!
#### Step 1: input sequence of a DDE on a fixed output history
-/

/-- The input sequence a DDE `e` emits when it sees output history `ys`
(presented prefix by prefix).

For each prefix `ys.take k` of the output history, the environment emits
`e (ys.take k |>.map some)` (wrapping each `y` in `some` as required by the
DDE's `List (Option Y)` domain).  We record `some x` when the environment
emits `x`, and `none` when it emits `⊣` (stop).

This mirrors `DDS.outputSeq` exactly: it is a total function on
`List (Option Y)` inputs so that we can push forward `PMF (DDE X Y)`. -/
noncomputable def DDE.inputSeq (e : DDE X Y) (ys : List Y) : List (Option X) :=
  (List.finRange ys.length).map fun k =>
    e (ys.take k.val |>.map some)

/-!
#### Step 2: joint probability that a PDE emits a given input sequence
-/

/-- The joint input distribution of a PDE `E` on a fixed output history `ys`.

`envJointInputDist E ys` is the pushforward of the DDE distribution along
`DDE.inputSeq · ys`: the distribution of the input sequence `(X₁, …, Xₙ)`
emitted by `E` when it receives outputs `ys`. -/
noncomputable def envJointInputDist [DecidableEq (List (Option X))]
    (E : PDE X Y) (ys : List Y) : Dist (List (Option X)) :=
  Dist.fTransform (DDE.inputSeq · ys) E

/-- The probability that a PDE `E` emits input sequence `xs` in response to
output history `ys`.

`envJointProb E ys xs = Pr[ E emits xs | outputs are ys ]` -/
noncomputable def envJointProb [DecidableEq (List (Option X))]
    (E : PDE X Y) (ys : List Y) (xs : List X) : NNReal :=
  envJointInputDist E ys (xs.map some)

/-!
#### Step 3: environment conditional slice (step-`i` distribution)
-/

/-- CR18 Definition 3.21: conditional probability of the next environment input.

`envCondSlice E ys_prev xs_prev x` models
  `pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(x, xs_prev, ys_prev)`
where:
- `ys_prev : List Y` is the output history `y₁,…,yᵢ₋₁` (length `i-1`)
- `xs_prev : List X` is the previous input history `x₁,…,xᵢ₋₁` (length `i-1`)
- `x : X` is the candidate next input `xᵢ`

It equals `envJointProb E (ys_prev ++ [default]) (xs_prev ++ [x]) / envJointProb E ys_prev xs_prev`,
following the same ratio convention as `condSlice`: when the denominator is 0
(the conditioning event has probability 0), the result is 0.

**Length bookkeeping (the environment leads).**  By Definition 3.7 the DDE
emits `xᵢ = e(y₁,…,yᵢ₋₁)`, so the input history *leads* the output history by one
(`x₁ = e(ε)` is emitted before any output is seen).  Concretely
`DDE.inputSeq e ys` has length `ys.length` and returns `[x₁,…,x_{|ys|}]`, where the
last input `x_{|ys|} = e(y₁…y_{|ys|−1})` does **not** consult the last output.

At round `i` (`xs_prev = xⁱ⁻¹` and `ys_prev = yⁱ⁻¹`, both length `i−1`):

* numerator = `Pr[ E emits xs_prev ++ [x] ]`.  This is an input sequence of
  length `i`, which `envJointProb` can only express with an output history of
  length `i`.  We supply `ys_prev ++ [default]`; because the `i`-th input
  ignores the `i`-th output, the value is **independent of the padding element**
  `default : Y` — it equals `Pr[X₁=x₁,…,Xᵢ₋₁=xᵢ₋₁, Xᵢ=x]` conditioned on
  outputs `yⁱ⁻¹`, exactly as Maurer requires.
* denominator = `Pr[ E emits xs_prev ]` = `envJointProb E ys_prev xs_prev`, an
  input sequence of length `i−1` against the matching output history `yⁱ⁻¹`.
  For the base case `i = 1` both lists are empty: `DDE.inputSeq e [] = []`, so the
  denominator is `Pr[empty prefix] = 1`, giving `envCondSlice E [] [] x = Pr[X₁=x]`.

⚠ The earlier formulation `envJointProb E ys_prev (xs_prev ++ [x]) /
envJointProb E ys_prev.dropLast xs_prev` was **wrong**: it paired a length-`i`
input history with a length-`(i−1)` output history, which `DDE.inputSeq` (whose
output length always equals the output-history length) can never produce, so the
numerator was identically `0` and `envCondSlice` collapsed to `0` everywhere
(e.g. it returned `0` for `Pr[X₁=true]` of the constant-`true` environment, which
is `1`).  See the contrarian-review counterexample. -/
noncomputable def envCondSlice [DecidableEq (List (Option X))] [Inhabited Y]
    (E : PDE X Y) (ys_prev : List Y) (xs_prev : List X) (x : X) : NNReal :=
  let joint_full  := envJointProb E (ys_prev ++ [default]) (xs_prev ++ [x])
  let joint_prefix : NNReal := envJointProb E ys_prev xs_prev
  joint_full / joint_prefix

/-!
#### Step 4: the EnvBehavior type
-/

/-- CR18 Definition 3.21: the environment behavior type.

An **environment behavior** for alphabets `X` and `Y` is a sequence of
conditional probability kernels: for each round `i : ℕ`, a function
```
  step : List X → List Y → X → ENNReal
```
mapping `(xⁱ⁻¹, yⁱ⁻¹, x)` to the conditional probability
`pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(x, xⁱ⁻¹, yⁱ⁻¹)` at round `i+1` (0-based index `i`).

This is the exact dual of `Behavior X Y` (which records `pˢ_{Yᵢ|XⁱYⁱ⁻¹}`),
with the roles of inputs and outputs swapped: the environment chooses the
next *input* to the system based on *output* history it has received. -/
structure EnvBehavior (X : Type u) (Y : Type v) : Type (max u v + 1) where
  /-- The conditional probability kernel at round `i+1` (0-based index `i`). -/
  step : ℕ → List X → List Y → X → NNReal

namespace EnvBehavior

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 3.21 (footnote 14 analogue): well-definedness of an
environment behavior at a **valid** history.

For a round `i`, a history pair `(xs, ys)` is *valid* when
`xs.length = i` and `ys.length = i` (i.e. `xs = xⁱ` and `ys = yⁱ` are the
input and output histories after `i` interaction rounds).  At such a valid
history the kernel must be a genuine probability distribution over the next
input, i.e. its values sum to 1 over `X`.

`WellDefinedAt b i xs ys` guards the sum-to-1 condition with length
hypotheses, exactly as in `Behavior.WellDefinedAt`. -/
def WellDefinedAt [Fintype X] (b : EnvBehavior X Y) (i : ℕ)
    (xs : List X) (ys : List Y) : Prop :=
  xs.length = i → ys.length = i →
  ∑ x : X, b.step i xs ys x = 1

/-- CR18 Definition 3.21: global well-definedness of an environment behavior. -/
def WellDefined [Fintype X] (b : EnvBehavior X Y) : Prop :=
  ∀ (i : ℕ) (xs : List X) (ys : List Y), WellDefinedAt b i xs ys

end EnvBehavior

/-!
#### Step 5: `b(E)` — the behavior of a PDE
-/

/-- CR18 Definition 3.21: the **behavior `b(E)`** of a probabilistic discrete
environment `E`.

`envBehavior E` is the sequence of conditional distributions
`pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}` for `i ≥ 1`, encoded as an `EnvBehavior X Y` with
0-based step index.  At step `i`, `(envBehavior E).step i xs ys x` equals
the conditional probability `Pr[E(ys) = x | (X₁,…,Xᵢ) = xs]` (0-based:
`xs` has length `i`, `ys` has length `i`) computed by `envCondSlice`. -/
noncomputable def envBehavior [DecidableEq (List (Option X))] [Inhabited Y]
    (E : PDE X Y) : EnvBehavior X Y where
  step _i xs ys x := envCondSlice E ys xs x

/-!
#### Equivalence of environments via behavior
-/

/-- Two PDEs are **behaviorally equivalent** when their behaviors agree
pointwise: `∀ i xs ys x, (envBehavior E).step i xs ys x = (envBehavior F).step i xs ys x`.

This is the environment-side analogue of `BehaviorEquiv` (CR18 3.19 for
systems). -/
def EnvBehaviorEquiv [DecidableEq (List (Option X))] [Inhabited Y]
    (E F : PDE X Y) : Prop :=
  ∀ (i : ℕ) (xs : List X) (ys : List Y) (x : X),
    (envBehavior E).step i xs ys x = (envBehavior F).step i xs ys x

/-- Notation for environment behavioral equivalence. -/
scoped notation:50 E " ≡ᴱ " F => EnvBehaviorEquiv E F

namespace EnvBehaviorEquiv

variable [DecidableEq (List (Option X))] [Inhabited Y]

/-- Environment behavioral equivalence is reflexive. -/
theorem refl (E : PDE X Y) : E ≡ᴱ E := fun _ _ _ _ => rfl

/-- Environment behavioral equivalence is symmetric. -/
theorem symm {E F : PDE X Y} (h : E ≡ᴱ F) : F ≡ᴱ E :=
  fun i xs ys x => (h i xs ys x).symm

/-- Environment behavioral equivalence is transitive. -/
theorem trans {E F G : PDE X Y} (hEF : E ≡ᴱ F) (hFG : F ≡ᴱ G) : E ≡ᴱ G :=
  fun i xs ys x => (hEF i xs ys x).trans (hFG i xs ys x)

end EnvBehaviorEquiv

/-!
### The environment chain rule (Eq 3.2, environment side)

The environment-side analogue of CR18 Eq 3.2: the joint input probability
`pᴱ_{Xᵏ|Yᵏ⁻¹}` factors as the product of the step-wise conditional slices
`∏_{i=1}^{k} pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}`, with the same chain-rule base factor
`envJointProb E [] []` (= `Pr[⊤]`, the total mass of `E`; `= 1` on CR18's
weight-1 domain) as the system-side `condSliceProd`.

This is the second telescoping identity needed for Lemma 3.2 (the first is
the system-side `cumulBehavior_eq_condSliceProd`); CR18 uses it implicitly
("We omit the proof of the following lemma").  Every lemma below is the
exact mirror of its system-side counterpart.
-/

/-- **Auxiliary (env side of Eq 3.2)**: the environment chain-rule product of
conditional slices for the first `n` rounds, given output history `ys` and
input history `xs`.

`envCondSliceProd E ys xs n` equals
`envJointProb E [] [] * ∏_{k=0}^{n-1} envCondSlice E (ys.take k) (xs.take k) (xs.getD k default)`.

This is the environment dual of `condSliceProd`, with the same chain-rule
base factor `envJointProb E [] []` (= `Pr[⊤]`, the total mass of `E`; `= 1`
on CR18's weight-1 domain — see the EQUATIONAL RECAST note on
`condSliceProd`). -/
noncomputable def envCondSliceProd [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (E : PDE X Y) (ys : List Y) (xs : List X) (n : ℕ) : NNReal :=
  envJointProb E [] [] *
    ((List.finRange n).map (fun k =>
      envCondSlice E (ys.take k.val) (xs.take k.val)
        (xs.getD k.val default))).prod

/-- `envCondSliceProd` at `n = 0` is the chain-rule base factor: the mass of
the empty conditioning event (`= 1` for CR18's weight-1 environments). -/
theorem envCondSliceProd_zero [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (E : PDE X Y) (ys : List Y) (xs : List X) :
    envCondSliceProd E ys xs 0 = envJointProb E [] [] := by
  simp [envCondSliceProd]

/-- Recursion for `envCondSliceProd`: the product over `n + 1` rounds is the
product over `n` rounds times the `n`-th environment conditional slice. -/
theorem envCondSliceProd_succ [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (E : PDE X Y) (ys : List Y) (xs : List X) (n : ℕ) :
    envCondSliceProd E ys xs (n + 1) =
      envCondSliceProd E ys xs n *
        envCondSlice E (ys.take n) (xs.take n) (xs.getD n default) := by
  unfold envCondSliceProd
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Function.comp_def, Fin.val_castSucc, Fin.val_last]
  ring

/-- Fiber-sum form of `envJointProb`: the mass under `E` of the event
`{e | e.inputSeq ys = xs.map some}`, summed over the support of `E`. -/
theorem envJointProb_eq_sum_support [DecidableEq (List (Option X))]
    (E : PDE X Y) (ys : List Y) (xs : List X) :
    envJointProb E ys xs =
      ∑ e ∈ E.support, if DDE.inputSeq e ys = xs.map some then E e else 0 := by
  classical
  simp only [envJointProb, envJointInputDist, Dist.fTransform]
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rfl

/-- `DDE.inputSeq` commutes with `List.take`: the input sequence on a
truncated output history is the truncation of the input sequence. -/
theorem DDE.inputSeq_take (e : DDE X Y) (ys : List Y) (n : ℕ) :
    DDE.inputSeq e (ys.take n) = (DDE.inputSeq e ys).take n := by
  apply List.ext_getElem
  · simp [DDE.inputSeq]
  · intro i h₁ h₂
    have hi : i ≤ n := by
      simp only [DDE.inputSeq, List.length_map, List.length_finRange,
        List.length_take] at h₁
      omega
    have hpfx : (ys.take n).take i = ys.take i := by
      rw [List.take_take, Nat.min_eq_left hi]
    simp only [DDE.inputSeq, List.getElem_take, List.getElem_map,
      List.getElem_finRange, Fin.val_cast, hpfx]

/-- The last output is never consulted: the input sequence on
`ys.take n ++ [z]` does not depend on the padding element `z`.  This is the
"environment leads" bookkeeping fact (CR18 Def 3.7: `xᵢ = e(y¹,…,yⁱ⁻¹)`), the
formal content of the padding convention in `envCondSlice`. -/
theorem DDE.inputSeq_take_concat (e : DDE X Y) (ys : List Y) {n : ℕ}
    (hn : n < ys.length) (z : Y) :
    DDE.inputSeq e (ys.take n ++ [z]) = DDE.inputSeq e (ys.take (n + 1)) := by
  have hlen_take : (ys.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
  apply List.ext_getElem
  · simp only [DDE.inputSeq, List.length_map, List.length_finRange,
      List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  · intro i h₁ h₂
    have hi : i ≤ n := by
      simp only [DDE.inputSeq, List.length_map, List.length_finRange,
        List.length_append, List.length_take, List.length_cons,
        List.length_nil] at h₁
      omega
    have hleft : (ys.take n ++ [z]).take i = ys.take i := by
      rw [List.take_append_of_le_length (by rw [hlen_take]; exact hi),
        List.take_take, Nat.min_eq_left hi]
    have hright : (ys.take (n + 1)).take i = ys.take i := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ_of_le hi)]
    simp only [DDE.inputSeq, List.getElem_map, List.getElem_finRange,
      Fin.val_cast, hleft, hright]

/-- Monotonicity of the environment joint probability in the history length:
extending the history by one round can only shrink the event
`{e | e.inputSeq · = ·}`. -/
theorem envJointProb_take_succ_le [DecidableEq (List (Option X))]
    (E : PDE X Y) (ys : List Y) (xs : List X) (n : ℕ) :
    envJointProb E (ys.take (n + 1)) (xs.take (n + 1)) ≤
      envJointProb E (ys.take n) (xs.take n) := by
  classical
  rw [envJointProb_eq_sum_support, envJointProb_eq_sum_support]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases h : DDE.inputSeq e (ys.take (n + 1)) = (xs.take (n + 1)).map some
  · have h1 : (ys.take (n + 1)).take n = ys.take n := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ n)]
    have h2 : (xs.take (n + 1)).take n = xs.take n := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ n)]
    have hev : DDE.inputSeq e (ys.take n) = (xs.take n).map some := by
      calc DDE.inputSeq e (ys.take n)
          = DDE.inputSeq e ((ys.take (n + 1)).take n) := by rw [h1]
        _ = (DDE.inputSeq e (ys.take (n + 1))).take n := DDE.inputSeq_take ..
        _ = ((xs.take (n + 1)).map some).take n := by rw [h]
        _ = ((xs.take (n + 1)).take n).map some := List.map_take.symm
        _ = (xs.take n).map some := by rw [h2]
    rw [if_pos h, if_pos hev]
  · rw [if_neg h]
    exact zero_le _

/-- The one-step environment chain rule: the joint input probability of an
`(n+1)`-round history factors as the joint probability of its `n`-round
prefix times the `n`-th environment conditional slice.  The 0-denominator
corner of the `envCondSlice` ratio is covered by monotonicity
(`envJointProb_take_succ_le`); the padding element of the numerator is
discharged by `DDE.inputSeq_take_concat`. -/
theorem envJointProb_take_succ [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (E : PDE X Y) (ys : List Y) (xs : List X) {n : ℕ}
    (hy : n < ys.length) (hx : n < xs.length) :
    envJointProb E (ys.take (n + 1)) (xs.take (n + 1)) =
      envJointProb E (ys.take n) (xs.take n) *
        envCondSlice E (ys.take n) (xs.take n) (xs.getD n default) := by
  have hconcat : xs.take n ++ [xs.getD n default] = xs.take (n + 1) := by
    rw [List.getD_eq_getElem xs default hx, List.take_add_one,
      List.getElem?_eq_getElem hx]
    rfl
  have hdist : envJointInputDist E (ys.take n ++ [(default : Y)]) =
      envJointInputDist E (ys.take (n + 1)) := by
    unfold envJointInputDist
    congr 1
    funext e
    exact DDE.inputSeq_take_concat e ys hy default
  have hpad : envJointProb E (ys.take n ++ [(default : Y)]) (xs.take (n + 1)) =
      envJointProb E (ys.take (n + 1)) (xs.take (n + 1)) := by
    simp only [envJointProb, hdist]
  unfold envCondSlice
  rw [hconcat, hpad]
  rcases eq_or_ne (envJointProb E (ys.take n) (xs.take n)) 0 with h0 | h0
  · have hle := envJointProb_take_succ_le E ys xs n
    rw [h0] at hle ⊢
    rw [zero_mul]
    exact le_antisymm hle (zero_le _)
  · rw [mul_comm]
    exact (div_mul_cancel₀ _ h0).symm

/-- **Eq 3.2, environment side**: the joint input probability factors as the
chain-rule product of the step-wise environment conditional slices.

`envJointProb E ys xs = envCondSliceProd E ys xs ys.length`
(when `xs.length = ys.length`).

**Proof**: telescoping induction on the history length, exactly mirroring
`cumulBehavior_eq_condSliceProd`. -/
theorem envJointProb_eq_envCondSliceProd
    [DecidableEq (List (Option X))] [Inhabited X] [Inhabited Y]
    (E : PDE X Y) (ys : List Y) (xs : List X)
    (hlen : xs.length = ys.length) :
    envJointProb E ys xs = envCondSliceProd E ys xs ys.length := by
  have key : ∀ n, n ≤ ys.length →
      envJointProb E (ys.take n) (xs.take n) = envCondSliceProd E ys xs n := by
    intro n
    induction n with
    | zero => intro _; simp [envCondSliceProd_zero]
    | succ n ih =>
      intro hn
      have hy : n < ys.length := Nat.lt_of_succ_le hn
      have hx : n < xs.length := by omega
      rw [envJointProb_take_succ E ys xs hy hx, ih (Nat.le_of_lt hy),
        envCondSliceProd_succ]
  have h := key ys.length le_rfl
  have hys : ys.take ys.length = ys := List.take_length
  have hxs : xs.take ys.length = xs := by
    rw [← hlen]; exact List.take_length
  rwa [hys, hxs] at h

/-!
### CR18 Lemma 3.2: Transcript Distribution from Behaviors

CR18 Section 3.6.5 (source ~line 3576–3608):

> We denote the random variable corresponding to the initial segment of the
> transcript (up to the `k`th step) by `XᵏYᵏ`.  Its probability distribution
> can be described in terms of the behavior of `S` and the behavior of `E`.
> We omit the proof of the following lemma.

**Lemma 3.2.** For a PDS `S` and a PDE `E`,

  `P^{ES}_{XᵏYᵏ}(xᵏ, yᵏ)  =  ∏_{i=1}^{k} pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(xᵢ, xⁱ⁻¹, yⁱ⁻¹)
                                              · pˢ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹)`

where:
- The left-hand side is the joint probability of the interleaved transcript
  `(x₁, y₁, x₂, y₂, …, xₖ, yₖ)` in the random experiment defined by `S` and `E`.
- Each factor in the product interleaves:
  (a) `pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(xᵢ, xⁱ⁻¹, yⁱ⁻¹)`: the environment behavior at step `i`,
      conditioning on the previous `i-1` inputs and `i-1` outputs;
  (b) `pˢ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹)`: the system behavior at step `i`,
      conditioning on the full `i` inputs and previous `i-1` outputs.

The key consequence (CR18, remark after Lemma 3.2) is that the transcript
distribution `P^{ES}_{XᵏYᵏ}` depends **only** on the behaviors `b(S)` and
`b(E)`, not on the specific PDS and PDE.

## Lean formalization strategy

We encode the transcript as a pair of lists `xs : List X` and `ys : List Y`
of the same length `k`.  The product over `i = 1,…,k` becomes a `List.finRange`
fold.

The **transcript distribution** `transcriptDist bS bE xs ys` is the
right-hand side of the Lemma 3.2 formula: the product over all rounds
`i = 0,…,k-1` (0-based) of

  `bE.step i (xs.take i) (ys.take i) xs[i]  ·  bS.step i (xs.take (i+1)) (ys.take i) ys[i]`

(Here `xs.take i` = `xⁱ⁻¹`, `xs.take (i+1)` = `xⁱ`, `ys.take i` = `yⁱ⁻¹`,
`xs[i]` = `xᵢ`, `ys[i]` = `yᵢ`, all in 0-based indexing.)

The **statement** asserts that the joint probability of observing transcript
`(xs, ys)` in the random experiment defined by a PDS `S` and PDE `E` equals
`transcriptDist base (behavior S) (envBehavior E) xs ys`, where `base` is the
chain-rule base factor `jointProb S [] [] * envJointProb E [] []` (= 1 on
CR18's weight-1 domain — see the EQUATIONAL RECAST note on `transcriptDist`).

**Proof omitted in source** ("We omit the proof."), but supplied here: the
system-side chain rule `cumulBehavior_eq_condSliceProd` (Eq 3.2) and its
environment dual `envJointProb_eq_envCondSliceProd`, reassembled into the
interleaved product.
-/

section Lem32

variable {X : Type u} {Y : Type v}

/-- **Auxiliary (Lem 3.2)**: the right-hand side of the Lemma 3.2 formula.

`transcriptDist base bS bE xs ys` is the product
  `base · ∏_{i=0}^{k-1} bE.step i (xs.take i) (ys.take i) (xs.getD i dfX)`
               `· bS.step i (xs.take (i+1)) (ys.take i) (ys.getD i dfY)`
(where `k = xs.length = ys.length`, and default values `dfX`, `dfY` are used
for safety when indices are out of range — they never fire when `i < k`).

This is the faithful Lean encoding of the Lemma 3.2 product formula:
each round `i` contributes the environment's probability of choosing `xᵢ`
given the previous history `(xⁱ⁻¹, yⁱ⁻¹)`, times the system's probability
of producing `yᵢ` given the full input history `(xⁱ, yⁱ⁻¹)`.

EQUATIONAL RECAST 2026-06-10: added the chain-rule base factor `base`
(previously the def was the bare product).  `base` is the mass `Pr[⊤]` of
the empty conditioning event of the random experiment; for the `S‖E`
experiment it is instantiated as
`jointProb S [] [] * envJointProb E [] []` (the product of the total masses
of `S` and `E`).  On CR18's weight-1 domain `base = 1` and the def is
verbatim CR18's product `∏_{i=1}^{k} pᴱ·pˢ`.  Without the base factor,
Lemma 3.2 is FALSE on the LM20 sub-distribution model: at `xs = ys = []`
the bare product is `1` while the genuine transcript probability is
`S.weight · E.weight` (e.g. `S = E = 0` would assert `0 = 1` — verified
counterexample).  This is the same recast, for the same reason, as the
base factor of `condSliceProd` (see the EQUATIONAL RECAST note there). -/
noncomputable def transcriptDist [Inhabited X] [Inhabited Y]
    (base : NNReal) (bS : Behavior X Y) (bE : EnvBehavior X Y)
    (xs : List X) (ys : List Y) : NNReal :=
  base *
    ((List.finRange xs.length).map (fun i =>
      let xᵢ  := xs.getD i.val default
      let yᵢ  := ys.getD i.val default
      let xprev := xs.take i.val          -- xⁱ⁻¹ : length i
      let yprev := ys.take i.val          -- yⁱ⁻¹ : length i
      let xfull := xs.take (i.val + 1)    -- xⁱ   : length i+1
      -- environment chooses xᵢ given (xⁱ⁻¹, yⁱ⁻¹)
      let pe := bE.step i.val xprev yprev xᵢ
      -- system answers yᵢ given (xⁱ, yⁱ⁻¹)
      let ps := bS.step i.val xfull yprev yᵢ
      pe * ps)
    |>.prod)

-- CONTRARIAN-REVIEW FIX (Lemma 3.2): Maurer's Lemma 3.2 is correct, but the
-- original commit formalised it in two defective ways and is fixed here (no
-- deviation from the note):
--   (1) a vacuous theorem `transcriptDist_eq : RHS = RHS` proved by `rfl` — it
--       formalised *nothing* (Maurer's left-hand side `P^{ES}_{XᵏYᵏ}` was absent
--       and both sides were the identical product term).  DELETED.
--   (2) a `lem_3_2` whose left-hand side `transcriptJointProb` ignored the
--       environment `E` entirely, making the equality FALSE (the right-hand side
--       depends on `E` through the `pᴱ` factors — see the counterexample on
--       `transcriptJointProb`).  RESTATED with the genuine S‖E joint transcript
--       probability `jointProb S xs ys * envJointProb E ys xs` (independent
--       product, CR18 §3.5) as its left-hand side.
-- The restated `lem_3_2` is faithful to Maurer's Lemma 3.2 (the chain-rule
-- factorisation of CR18 Eq 3.2 on both sides, reassembled into the interleaved
-- product) and is now PROVED (2026-06-10), with `transcriptDist` carrying the
-- chain-rule base factor on the LM20 sub-distribution model (see the
-- EQUATIONAL RECAST note on `transcriptDist`).

/-- **CR18 Lem 3.2 (substantive form)**: the intended non-trivial
equality connecting the transcript probability in the S‖E experiment to the
behavior product formula.

This is the faithful statement of Lemma 3.2: the left-hand side is
`transcriptJointProb S E xs ys` — the probability of seeing the transcript
`(xs, ys)` when `S` and `E` interact — and the right-hand side is the
behavior product `transcriptDist base (behavior S) (envBehavior E) xs ys`
(with `base` the chain-rule base factor of the experiment).

The S‖E joint transcript probability at transcript `(xs, ys)` (length `k`) is:
  `Pr[ X₁=x₁, Y₁=y₁, …, Xₖ=xₖ, Yₖ=yₖ ]`
in the experiment where `S` and `E` are drawn independently (as PMFs over
DDSs and DDEs respectively) and then interact.

Because `S` and `E` are drawn **independently** (CR18 Section 3.5: "S and E
are, as always, independent"), the probability that the interaction produces the
transcript `(xs, ys)` is the product of two independent events:

* `jointProb S xs ys` — the probability that the system `S` produces output
  history `ys` when fed input history `xs` (`pˢ_{Yᵏ|Xᵏ}`, Definition 3.20); and
* `envJointProb E ys xs` — the probability that the environment `E` emits input
  history `xs` in response to output history `ys` (`pᴱ_{Xᵏ|Yᵏ}`, Definition 3.21).

The joint transcript probability is their product, which is the genuine
`P^{ES}_{XᵏYᵏ}(xᵏ, yᵏ)` of the `S‖E` experiment (the two sequences of coin
flips are independent, so the joint factorises).  This is a **faithful**
definition of Maurer's left-hand side and it genuinely depends on **both** `S`
and `E`.

⚠ The earlier stub `jointProb S xs ys` (ignoring `E` entirely) made `lem_3_2`
a **false** statement: its right-hand side `transcriptDist (behavior S)
(envBehavior E)` depends on `E` through the `pᴱ` factors, but the left-hand
side did not.  Concretely (contrarian-review counterexample, `k = 1`): take a
deterministic `S` outputting `y₀` on `x₀` (so `jointProb S [x₀] [y₀] = 1`) and
two environments — `E₁` emitting `x₀` first and `E₂` emitting some `x' ≠ x₀`
first.  The right-hand side is `1` for `E₁` and `0` for `E₂`, while the old
left-hand side was `1` for both; the `E₂` instance asserted `1 = 0`.  With the
independent-product definition, `envJointProb E₂ [y₀] [x₀] = 0` kills the
left-hand side too, restoring the equality. -/
noncomputable def transcriptJointProb
    [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (S : PDS X Y) (E : PDE X Y)
    (xs : List X) (ys : List Y) : NNReal :=
  -- The joint probability Pr[X¹Y¹…XᵏYᵏ = (xs,ys)] in the S‖E experiment.
  -- S and E are independent (CR18 §3.5), so this is the product of:
  --   * Pr[S outputs ys on inputs xs]      = jointProb S xs ys
  --   * Pr[E emits xs on outputs ys]       = envJointProb E ys xs
  jointProb S xs ys * envJointProb E ys xs

/-- **CR18 Lemma 3.2** (faithful statement, proof omitted in source — proved
here).

The joint probability of the initial `k`-step transcript `(x₁,y₁,…,xₖ,yₖ)`
in the S‖E random experiment equals the interleaved product of the environment
and system behavior kernels:

  `P^{ES}_{XᵏYᵏ}(xᵏ,yᵏ) = ∏_{i=1}^{k}  pᴱ_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}(xᵢ,xⁱ⁻¹,yⁱ⁻¹) · pˢ_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ,xⁱ,yⁱ⁻¹)`

The proof is omitted in the CR18 source (Section 3.6.5, Lemma 3.2).
In the formalization, the left-hand side `transcriptJointProb S E xs ys` is the
genuine S‖E joint transcript probability — the independent product
`jointProb S xs ys * envJointProb E ys xs` (S and E independent, CR18 §3.5) —
which depends on **both** `S` and `E`.

The base argument of `transcriptDist` is instantiated with the chain-rule base
factor `jointProb S [] [] * envJointProb E [] []` (= `Pr[⊤]` of the `S‖E`
experiment, the product of the total masses; `= 1` on CR18's weight-1 domain,
where the statement is verbatim Maurer's — see the EQUATIONAL RECAST notes on
`transcriptDist` and `condSliceProd`; the unbased form is FALSE on the LM20
sub-distribution model, e.g. `S = E = 0`, `xs = ys = []` would assert `0 = 1`).

**Proof**: the two chain-rule factorisations of CR18 Eq 3.2 —
`cumulBehavior_eq_condSliceProd` (system side) and
`envJointProb_eq_envCondSliceProd` (environment side) — reassembled into the
interleaved product via `List.prod_map_mul`. -/
theorem lem_3_2
    [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
    [Inhabited X] [Inhabited Y]
    (S : PDS X Y) (E : PDE X Y)
    (xs : List X) (ys : List Y)
    (hlen : xs.length = ys.length) :
    transcriptJointProb S E xs ys =
    transcriptDist (jointProb S [] [] * envJointProb E [] [])
      (behavior S) (envBehavior E) xs ys := by
  have hbS : ∀ i a b c, (behavior S).step i a b c = condSlice S a b c :=
    fun _ _ _ _ => rfl
  have hbE : ∀ i a b c, (envBehavior E).step i a b c = envCondSlice E b a c :=
    fun _ _ _ _ => rfl
  simp only [transcriptJointProb, transcriptDist, hbS, hbE]
  rw [cumulBehavior_eq_condSliceProd S xs ys hlen.symm,
    envJointProb_eq_envCondSliceProd E ys xs hlen, ← hlen]
  simp only [condSliceProd, envCondSliceProd]
  rw [List.prod_map_mul]
  ring

/-- **CR18 Lem 3.2, Corollary**: the transcript distribution depends only on
the behaviors `b(S)` and `b(E)`, not on the specific PDS and PDE.

If `S ≡ᵦ T` (same behavior) then `transcriptJointProb S E = transcriptJointProb T E`
for any PDE `E`, since the right-hand side of Lemma 3.2 only involves `b(S)`.

This is the "We point out that P^{ES}_{XᵏYᵏ} depends only on the behavior of S
and E" remark from CR18 immediately after Lemma 3.2.

Stated here in the `transcriptDist` form (which, for a fixed base mass, is
purely a function of behaviors, so the claim is immediate by congruence;
on CR18's weight-1 domain `base = 1` is system-independent). -/
theorem transcriptDist_congr_bS [Inhabited X] [Inhabited Y]
    (base : NNReal) (bE : EnvBehavior X Y) (bS bT : Behavior X Y)
    (h : ∀ i xs ys y, bS.step i xs ys y = bT.step i xs ys y)
    (xs : List X) (ys : List Y) :
    transcriptDist base bS bE xs ys = transcriptDist base bT bE xs ys := by
  simp only [transcriptDist]
  simp [h]

/-- **CR18 Lem 3.2, Corollary**: the transcript distribution depends only on
`b(E)`, symmetrically to the system case.

If two environments `E` and `F` have the same behavior (`E ≡ᴱ F`), then
`transcriptDist base bS (envBehavior E) = transcriptDist base bS (envBehavior F)`. -/
theorem transcriptDist_congr_bE [Inhabited X] [Inhabited Y]
    (base : NNReal) (bS : Behavior X Y) (bE bF : EnvBehavior X Y)
    (h : ∀ i xs ys x, bE.step i xs ys x = bF.step i xs ys x)
    (xs : List X) (ys : List Y) :
    transcriptDist base bS bE xs ys = transcriptDist base bS bF xs ys := by
  simp only [transcriptDist]
  simp [h]

end Lem32

/-!
### CR18 Definition 6.1: VIL-URF (Variable Input-Length URF)

CR18 Definition 6.1 (source ~line 6328):

> The term **variable input-length URF** (a **VIL-URF**) refers to the behavior
> of a `({0,1}*, {0,1}ⁿ)`-system which for each new input in `{0,1}*` outputs a
> fresh uniformly random value in `{0,1}ⁿ`, and which replies consistently if
> inputs are repeated.  This system (behavior) is denoted as `Vₙ`.

This is the **canonical named** definition of the object introduced informally
in Example 3.7.  The difference between Ex 3.7 and Def 6.1 is presentational:
Example 3.7 observes that the URF behavior formula (Eq 3.1) applies equally
well when `X = {0,1}*` is infinite and that no finite PDS underlies it;
Definition 6.1 gives the object its official name `Vₙ` and uses it as the
target for the CBC-MAC domain-extension theorem (Thm 6.1).

## Lean strategy

`vilURFBehavior n` (defined in `section Ex37` above) is already the correct
mathematical object.  This section:

1. **Aliases** `vilURF n := vilURFBehavior n` to provide the officially-named
   definition under a name matching the paper notation.
2. **Proves `IsVILURF (vilURF n)`** — a direct consequence of
   `vilURFBehavior_isVILURF`.
3. **Proves `vilURF_wellDefined_consistent n`** — the VIL-URF behavior sums to
   1 over `Fin (2^n)` at every valid **consistent** history.  Maurer's footnote
   14/16 (and Ex 3.6) restrict the conditional distribution to *consistent*
   histories: at an inconsistent history (same input answered with two distinct
   outputs) the conditioning event has probability 0 and `pˢ_{Yᵢ|XⁱYⁱ⁻¹}` is
   *undefined*.  The **global** `Behavior.WellDefined (vilURF n)` is therefore
   FALSE — see `vilURF_not_globally_wellDefined` for the explicit
   counterexample (an inconsistent history where the kernel sums to 2, not 1).
4. **Records** `vilURF_infinite_domain` — `List Bool` is infinite, so `Vₙ` has
   no underlying finite PDS (the key point of CR18 Ex 3.7 / Def 6.1).

All theorems in this section are proved.  The consistency-guarded
well-definedness theorem below is the canonical replacement for the false
global `Behavior.WellDefined` claim: the proof splits the URF kernel into the
fresh and consistent-repeat cases, and the consistency hypothesis rules out the
double-count that breaks the global claim.
-/

section Def61

/-!
#### The canonical `Vₙ` (CR18 Definition 6.1)
-/

/-- **CR18 Definition 6.1**: the VIL-URF behavior `Vₙ`.

`vilURF n` is the `Behavior (List Bool) (Fin (2^n))` that CR18 calls `Vₙ`:
the behavior of a `({0,1}*, {0,1}ⁿ)`-system that, for each new bitstring input,
outputs a fresh uniform element of `{0,1}ⁿ`, and replies consistently on
repeated inputs.

This is the canonical named version of the object introduced in Example 3.7
(see `vilURFBehavior`).  The two definitions are definitionally equal by `rfl`. -/
noncomputable def vilURF (n : ℕ) : Behavior (List Bool) (Fin (2 ^ n)) :=
  vilURFBehavior n

/-- **CR18 Definition 6.1**: `vilURF n` equals `vilURFBehavior n` by definition. -/
theorem vilURF_eq_vilURFBehavior (n : ℕ) :
    vilURF n = vilURFBehavior n :=
  rfl

/-- **CR18 Definition 6.1**: `vilURF n` satisfies the VIL-URF predicate.

The three-case conditional distribution (fresh → `1/2ⁿ`, consistent repeat → `1`,
inconsistent repeat → `0`) holds at every round and every history. -/
theorem vilURF_isVILURF (n : ℕ) : IsVILURF (vilURF n) :=
  vilURFBehavior_isVILURF n

/-- **CR18 Definition 6.1**: `List Bool` (= `{0,1}*`) is infinite.

This witnesses Maurer's remark (Ex 3.7 / Def 6.1) that `Vₙ` has **no**
underlying finite PDS: the sample space `{0,1}* → {0,1}ⁿ` is uncountable
(it would require a PDS over an infinite product). -/
theorem vilURF_infinite_domain : Infinite (List Bool) :=
  listBool_infinite

/-- **CR18 Definition 6.1 — the global well-definedness claim is FALSE.**

The *global* `Behavior.WellDefined (vilURF n)` does NOT hold: it would assert
`∑ y, kernel = 1` at *every length-valid history*, including **inconsistent**
ones (a repeated input answered with two distinct outputs).  At an inconsistent
history the `urfBehaviorKernel` returns `1` for *each* previously-seen output,
so the sum exceeds `1`.

Concrete counterexample (proven, no sorry), at `n` with `2^n = 2` (`n = 1`),
round `i = 2`, input history `xs = [[], [], []]` (length `3 = i+1`), output
history `ys = [0, 1]` (length `2 = i`): the previous part `(xs.dropLast, ys) =
([[],[]], [0,1])` answers the **same** input `[]` first with `0`, then with `1`
— an inconsistent history — and the kernel sums to **2**, not `1`.

This faithfully tracks Maurer's footnote 14/16: `pˢ_{Yᵢ|XⁱYⁱ⁻¹}` is *undefined*
at histories whose conditioning event has probability 0 (i.e. inconsistent
ones).  Well-definedness for `Vₙ` therefore holds only on **consistent**
histories (see `vilURF_wellDefined_consistent`). -/
theorem vilURF_not_globally_wellDefined :
    ¬ Behavior.WellDefined (vilURF 1) := by
  intro hwd
  -- Instantiate at the inconsistent (but length-valid) history.
  have h := hwd 2 [[], [], []] [0, 1] rfl rfl
  -- `h : ∑ y, (vilURF 1).step 2 [[],[],[]] [0,1] y = 1`, but the LHS is 2:
  -- the step reduces definitionally to `vilURFKernel [[],[]] [0,1] [] y`, and the
  -- inconsistent history (input `[]` answered first with `0`, then with `1`)
  -- yields kernel `1` at BOTH outputs `0` and `1`, so the sum is `2`.
  simp only [vilURF, vilURFBehavior, List.getLast?, List.dropLast, List.getLast,
    vilURFKernel, urfBehaviorKernel, pow_one] at h
  norm_num [List.zip, List.zipWith, List.filter, List.any, reduceCtorEq,
    List.cons_ne_nil] at h
  -- residual: a card equation over `Fin 2` that is `2 = 1` — a decidable falsehood.
  revert h
  decide

/-- **CR18 Definition 6.1**: `vilURF n` is well-defined **on consistent
histories**.

The conditional-probability kernel of `Vₙ` sums to 1 over `Fin (2^n)` at every
length-valid history `(xs, ys)` (`ys.length = i`, `xs.length = i + 1`) whose
previous part `(xs.dropLast, ys)` is **consistent** (`IsConsistentHistory`).
Maurer's footnote 14/16 restricts the conditional distribution to exactly these
histories; on inconsistent histories `pˢ_{Yᵢ|XⁱYⁱ⁻¹}` is undefined (see
`vilURF_not_globally_wellDefined`), so consistency is the correct guard.

**Proof sketch**: for a non-empty input history `xs` with `x_curr := xs.getLast`:
- **Fresh** (`x_curr` not in `xs.dropLast`): the kernel equals `1/(2^n)` for
  each output, and `∑ y : Fin (2^n), 1/(2^n) = (2^n)·(1/(2^n)) = 1`.
- **Consistent repeat** (`x_curr` seen before with output `y₀`): by the
  consistency hypothesis there is a *unique* matched output `y₀`, so the kernel
  is `1` at `y₀` and `0` elsewhere, summing to `1`.

**Proof status**: fully proved.  The fresh case is a constant finite sum
`∑ y, 1/(2^n) = 1`; the repeat case collapses the finite sum to the unique
consistent previous output. -/
theorem vilURF_wellDefined_consistent (n : ℕ) :
    ∀ (i : ℕ) (xs : List (List Bool)) (ys : List (Fin (2 ^ n))),
      ys.length = i → xs.length = i + 1 →
      (hlen : xs.dropLast.length = ys.length) →
      IsConsistentHistory xs.dropLast ys hlen →
      ∑ y : Fin (2 ^ n), (vilURF n).step i xs ys y = 1 := by
  intro i xs ys hys hxs hlen _hcons
  simp only [vilURF, vilURFBehavior]
  -- Goal: ∑ y : Fin (2^n), (match xs.getLast? with | none => 0
  --         | some x_curr => vilURFKernel xs.dropLast ys x_curr y) = 1
  cases hxs_last : xs.getLast? with
  | none =>
    -- xs is empty, but hxs says xs.length = i + 1 ≥ 1: contradiction
    have : xs = [] := List.getLast?_eq_none_iff.mp hxs_last
    simp [this] at hxs
  | some x_curr =>
    -- xs is nonempty; goal: ∑ y, vilURFKernel xs.dropLast ys x_curr y = 1
    simp only [vilURFKernel, urfBehaviorKernel]
    -- The sum splits by whether x_curr is fresh or repeated.  The consistency
    -- hypothesis `_hcons` guarantees that in the repeat case there is exactly
    -- one matched output, so the sum is 1 (no double-count).
    set f := List.filter (fun p => decide (p.1 = x_curr)) (xs.dropLast.zip ys) with hf
    by_cases hfe : f = []
    · -- Fresh case: x_curr unseen, so the kernel is `1/(2^n)` at every output.
      --   ∑ y : Fin (2^n), 1/(2^n) = (2^n) · (1/(2^n)) = 1.
      simp only [hfe, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one_div]
      rw [div_self]
      positivity
    · -- Consistent-repeat case: the kernel is `1` exactly at the matched output
      --   `y₀`, and `0` elsewhere; by consistency every matched pair carries the
      --   same `y₀`, so the sum is a single `1`.
      simp only [if_neg hfe]
      -- (1) Every matched pair has the same second component (from `_hcons`).
      have hpair : ∀ p ∈ f, ∀ q ∈ f, p.2 = q.2 := by
        intro p hp q hq
        rw [hf, List.mem_filter] at hp hq
        obtain ⟨hpz, hp1⟩ := hp
        obtain ⟨hqz, hq1⟩ := hq
        simp only [decide_eq_true_eq] at hp1 hq1
        rw [List.mem_iff_getElem] at hpz hqz
        obtain ⟨jp, hjp, hjpe⟩ := hpz
        obtain ⟨jq, hjq, hjqe⟩ := hqz
        rw [List.getElem_zip] at hjpe hjqe
        have hzl : (xs.dropLast.zip ys).length = xs.dropLast.length := by
          rw [List.length_zip, hlen, Nat.min_self]
        rw [hzl] at hjp hjq
        have hp1' : xs.dropLast[jp] = x_curr := by rw [← hjpe] at hp1; exact hp1
        have hq1' : xs.dropLast[jq] = x_curr := by rw [← hjqe] at hq1; exact hq1
        have hxeq : xs.dropLast[jp] = xs.dropLast[jq] := by rw [hp1', hq1']
        have hys := _hcons ⟨jp, hjp⟩ ⟨jq, hjq⟩ hxeq
        rw [← hjpe, ← hjqe]
        exact hys
      -- (2) Collapse the sum to a single `1` at `y₀ := (head f).2`.
      obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil f hfe
      set y₀ := p0.2 with hy0
      have hany : ∀ x : Fin (2 ^ n),
          (f.any fun p => decide (p.2 = x)) = true ↔ x = y₀ := by
        intro x
        constructor
        · intro hx
          rw [List.any_eq_true] at hx
          obtain ⟨q, hq, hqx⟩ := hx
          simp only [decide_eq_true_eq] at hqx
          have : q.2 = y₀ := hpair q hq p0 hp0
          rw [← hqx, this]
        · intro hx
          rw [List.any_eq_true]
          refine ⟨p0, hp0, ?_⟩
          simp only [decide_eq_true_eq]
          rw [hx]
      have hrw : (∑ x : Fin (2 ^ n),
            if (f.any fun p => decide (p.2 = x)) = true then (1 : NNReal) else 0)
          = ∑ x : Fin (2 ^ n), if x = y₀ then (1 : NNReal) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [hany x]
      rw [hrw, Finset.sum_ite_eq' Finset.univ y₀ (fun _ => (1 : NNReal))]
      simp

end Def61

end RandomSystems.CR18
