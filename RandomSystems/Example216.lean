/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.LanzenbergerChain

/-!
# Thesis Example 2.16, and Definition 2.28's two printed displays

(Lanzenberger, *Theory of Random Systems and Games*, printed pp. 14–16 and 18;
scanned original `papers/thesis (1).pdf`, PDF leaves 24–26 and 28.)

Example 2.16 introduces the four single-query `({0,1},{0,1})`-DDS of Figure 2.1

```
zero(x) := 0,   one(x) := 1,   id(x) := x,   flip(x) := 1 − x
```

and the one-parameter family of probabilistic discrete systems

```
V_α := {(zero, α), (one, α), (id, 1/2 − α), (flip, 1/2 − α)},   α ∈ [0, 1/2],
```

all of which "have the same behavior": they answer a *single* query with a
uniform random bit.  The point of the example is that the PDS carrier
(a distribution over deterministic systems) is strictly finer than behavior —
`V₀` samples the answers to `0` and to `1` as two independent bits, and
`V_{1/2}` samples one bit and returns it to whichever query is asked — and that
the two are indistinguishable only because "a system can only be executed
once" (printed p. 15, below Def 2.15).

The single-query restriction is **load-bearing, not decoration**, which is why
`singleQuery` below carves the domain down to `X¹` (`mem_dom_singleQuery`)
rather than reusing the stateless total `PFunDDS.functionEvaluator`.  The
design reason (argument only — *not* formalized in this file): a total
evaluator answers every history, so asking `0` and then `1` reads both
coordinates of the same sample and the `{id, flip}` mixture becomes visibly
correlated where the `{zero, one}` mixture is not.  What *is* kernel-checked
here is the positive side — that on the single-query carrier no environment
separates them (`equivalent_V`), and that every query after the first is
rejected (`raw_fullyDefined_singleQuery_of_two_le`).

## What is proved here

* `equivalent_V` — `V_α ≡ V_β` for all `α, β ∈ [0, 1/2]` (thesis Def 2.17), via
  the closed form `observableBehavior_V` of the class's CR18 Def 3.20 behavior
  on the resource view `s⊥`;
* `delta_V0_Vhalf` — `δ(V₀, V_{1/2}) = 1`: the two extremes of the family have
  disjoint supports, so the thesis's remark below Def 2.28 is exact;
* `definition_2_28_printed_displays_disagree` — **the erratum, kernel-checked**.

## The erratum

Definition 2.28 prints, verbatim,

```
Δ(S,T) := inf_{S∈𝐒, T∈𝐓} δ(S,T) = 1 − inf_{(S,T)∈𝐒×𝐓} sup_ℰ Pr^ℰ(S = T),
```

asserting that its two displays are the same number.  By the classical
coupling lemma `sup_ℰ Pr^ℰ(S = T) = 1 − δ(S,T)` at each representative pair
(`supAgreement_pair_eq_weight_sub_delta`), so the second display equals
`sup_{reps} δ`, while the first is `inf_{reps} δ`.  They agree exactly when `δ`
is constant across representatives — which is what Example 2.16 denies, and the
thesis's own remark below Def 2.28 cites `V₀`/`V_{1/2}` to deny it.

Taking `𝐒 = 𝐓 = [V]` makes this quantitative and closes the loop: the first
display is `0` (take the same representative twice) and the second is `1` (take
`V₀` against `V_{1/2}`).  This was previously recorded as source-verified hand
algebra; it is now a theorem.  The corrected reading — `Lanzenberger`'s
`multiSystemDistance`, with the inner quantifier turned into a `sup` — agrees
with the first display at the same class pair
(`corrected_display_agrees_at_V`).
-/

namespace RandomSystems.Dist

open RandomSystems (Dist)

open Classical in
/-- The mass of an event under a point law: the weight, gated by the event.
Completes the `mass_add` / `weight_add` pair of `MultiSystemCoupling.lean`
(`Dist.lean` is not free to rebuild). -/
theorem mass_single {A : Type*} (a : A) (c : ℝ) (P : A → Prop) :
    Dist.mass (Finsupp.single a c) P = if P a then c else 0 := by
  unfold Dist.mass
  rw [Finsupp.sum_single_index (by by_cases h : P a <;> simp [h])]

/-- The weight of a point law is its single value. -/
theorem weight_single {A : Type*} (a : A) (c : ℝ) :
    Dist.weight (Finsupp.single a c : Dist A) = c := by
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_single_index rfl

/-- A point law at a non-negative value is a non-negative law — structural on
the `NNReal` carrier, a two-line split on the signed one.  Stated at the
weakest layer the atoms need: nothing here is normalized. -/
theorem nonNeg_single {A : Type*} (a : A) {c : ℝ} (hc : 0 ≤ c) :
    Dist.NonNeg (Finsupp.single a c : Dist A) := fun b => by
  classical
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_rfl

end RandomSystems.Dist

namespace RandomSystems.CR18.Example216

open RandomSystems (Dist)
open PFunDDS

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Thesis Def 2.9 at `dom(s) = X¹`: the single-query deterministic systems -/

/-- Thesis Figure 2.1: the **single-query** DDS realizing `f : X → Y` — domain
exactly the length-one histories `X¹` (`mem_dom_singleQuery`), answering `f x`
to the first query `x` and nothing afterwards.

Assembled from the existing constructors: `glue` dispatches on the first query,
`prepend x (some (f x))` answers it, and the `empty` continuation makes the
system self-destruct.  This is *not* `PFunDDS.functionEvaluator f`, which
accepts every nonempty history (see the module header for why the restriction
is load-bearing). -/
def singleQuery (f : X → Y) : PFunDDS.DDS X Y :=
  PFunDDS.DDS.glue fun x => PFunDDS.DDS.prepend x (some (f x)) PFunDDS.DDS.empty

/-- The single-query system's domain is exactly `X¹`. -/
theorem mem_dom_singleQuery (f : X → Y) (l : List X) :
    l ∈ PFunDDS.dom (singleQuery f) ↔ ∃ x, l = [x] := by
  rcases l with _ | ⟨x, m⟩
  · exact iff_of_false (PFunDDS.empty_not_mem _) (by rintro ⟨x, h⟩; simp at h)
  · rw [singleQuery, cons_mem_dom_glue, dom_prepend_some]
    constructor
    · rintro (h | ⟨m', hm', -⟩)
      · exact ⟨x, h⟩
      · exact absurd hm' (not_mem_dom_empty m')
    · rintro ⟨x', h⟩
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp h
      exact Or.inl rfl

/-- Every accepted history of a single-query system has length one. -/
theorem length_eq_one_of_mem_dom_singleQuery {f : X → Y} {l : List X}
    (h : l ∈ PFunDDS.dom (singleQuery f)) : l.length = 1 := by
  obtain ⟨x, rfl⟩ := (mem_dom_singleQuery f l).mp h
  rfl

/-- A `⊥`-completed system evaluates to a `Part.some` on every nonempty history
(`dom s⊥ = {l | l ≠ []}`), which is the shape `observableBehavior` reads. -/
theorem raw_fullyDefined_eq_some (s : PFunDDS.DDS X Y) {l : List X}
    (hl : l ∈ PFunDDS.dom (PFunDDS.fullyDefined s)) :
    (PFunDDS.fullyDefined s).1 l
      = Part.some (PFunDDS.output (PFunDDS.fullyDefined s) l hl) :=
  (Part.some_get hl).symm

/-- Every nonempty history is in the domain of a `⊥`-completed system. -/
theorem mem_dom_fullyDefined_of_ne_nil (s : PFunDDS.DDS X Y) {l : List X}
    (hl : l ≠ []) : l ∈ PFunDDS.dom (PFunDDS.fullyDefined s) := by
  rw [PFunDDS.dom_fullyDefined]; exact hl

/-- The first `s⊥`-answer of a single-query system is `f x`. -/
theorem raw_fullyDefined_singleQuery_singleton (f : X → Y) (x : X) :
    (PFunDDS.fullyDefined (singleQuery f)).1 [x] = Part.some (some (f x)) := by
  rw [raw_fullyDefined_eq_some _ (mem_dom_fullyDefined_of_ne_nil _ (by simp))]
  exact congrArg Part.some
    (output_fullyDefined_glue_prepend (fun x' => some (f x'))
      (fun _ => PFunDDS.DDS.empty) x)

/-- Every later `s⊥`-answer of a single-query system is `⊥`: the system is
executed once.  This is the formal content of the thesis's remark below
Def 2.15 ("a system can only be executed once"). -/
theorem raw_fullyDefined_singleQuery_of_two_le (f : X → Y) {l : List X}
    (hlen : 2 ≤ l.length) :
    (PFunDDS.fullyDefined (singleQuery f)).1 l = Part.some none := by
  classical
  have hne : l ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  rw [raw_fullyDefined_eq_some _ (mem_dom_fullyDefined_of_ne_nil _ hne)]
  refine congrArg Part.some ?_
  -- the scanned context is nonempty, because the very first query is accepted
  have hdrop : l.dropLast ≠ [] := by
    intro h
    have hlen0 : l.dropLast.length = 0 := by rw [h]; rfl
    rw [List.length_dropLast] at hlen0
    omega
  obtain ⟨x, m, hxm⟩ : ∃ x m, l.dropLast = x :: m := by
    cases hd : l.dropLast with
    | nil => exact absurd hd hdrop
    | cons x m => exact ⟨x, m, rfl⟩
  have hpre : PFunDDS.keptPrefix (singleQuery f) [x]
      <+: PFunDDS.keptPrefix (singleQuery f) l.dropLast :=
    PFunDDS.keptPrefix_mono _ (by rw [hxm]; exact ⟨m, rfl⟩)
  rw [PFunDDS.keptPrefix_eq_self_of_mem _
    ((mem_dom_singleQuery f [x]).mpr ⟨x, rfl⟩)] at hpre
  have hkept : 1 ≤ (PFunDDS.keptPrefix (singleQuery f) l.dropLast).length :=
    hpre.length_le
  rw [PFunDDS.output_fullyDefined]
  refine dif_neg fun hmem => ?_
  have hlen1 := length_eq_one_of_mem_dom_singleQuery hmem
  rw [List.length_append, List.length_singleton] at hlen1
  omega

/-- Single-query systems remember their function: the constructor is
injective. -/
theorem singleQuery_injective :
    Function.Injective (singleQuery (X := X) (Y := Y)) := by
  intro f g h
  funext x
  have hx : (PFunDDS.fullyDefined (singleQuery f)).1 [x]
      = (PFunDDS.fullyDefined (singleQuery g)).1 [x] := by rw [h]
  rw [raw_fullyDefined_singleQuery_singleton,
    raw_fullyDefined_singleQuery_singleton] at hx
  exact Option.some_inj.mp (Part.some_inj.mp hx)

/-! ## The `s⊥`-consistency event that Def 3.20 behavior measures -/

/-- The environment-independent event whose mass is `observableBehavior S t`:
the deterministic system `s` produces, on the input projection of `t`, exactly
`t`'s answers (rejections included, as `⊥`).  Spelled out so the single-query
characterization below can be stated. -/
def Consistent (t : List (X × Option Y)) (s : PFunDDS.DDS X Y) : Prop :=
  ∀ k (hk : k < t.length),
    (PFunDDS.fullyDefined s).1 (PFunDDS.transcriptInputs (t.take (k + 1)))
      = Part.some (t[k].2)

theorem observableBehavior_eq_mass_consistent (S : PFunPDS X Y)
    (t : List (X × Option Y)) : observableBehavior S t = S.mass (Consistent t) :=
  rfl

theorem consistent_nil (s : PFunDDS.DDS X Y) :
    Consistent ([] : List (X × Option Y)) s :=
  fun _ hk => absurd hk (by simp)

private theorem length_transcriptInputs_take (t : List (X × Option Y)) (m : ℕ) :
    (PFunDDS.transcriptInputs (t.take m)).length = min m t.length := by
  simp [PFunDDS.transcriptInputs]

/-- **The single-query consistency event, computed.**  A single-query system is
consistent with a nonempty transcript exactly when it answers the first query as
recorded and every later query was rejected — the formal content of "a system
can only be executed once".  Note the right-hand side splits into a part
depending on `f` (the first answer) and a part that does not (the tail), which
is why the whole family `V_α` has one behavior. -/
theorem consistent_singleQuery_cons (f : X → Y) (x : X) (y : Option Y)
    (rest : List (X × Option Y)) :
    Consistent ((x, y) :: rest) (singleQuery f)
      ↔ y = some (f x) ∧ ∀ p ∈ rest, p.2 = none := by
  have hfirst : PFunDDS.transcriptInputs (((x, y) :: rest).take (0 + 1)) = [x] := by
    simp [PFunDDS.transcriptInputs]
  have hlater : ∀ j, j < rest.length →
      2 ≤ (PFunDDS.transcriptInputs (((x, y) :: rest).take (j + 1 + 1))).length := by
    intro j hj
    rw [length_transcriptInputs_take]
    simp only [List.length_cons]
    omega
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      rw [hfirst, raw_fullyDefined_singleQuery_singleton] at h0
      simpa using (Part.some_inj.mp h0).symm
    · rw [List.forall_mem_iff_forall_getElem]
      intro j hj
      have hj' := h (j + 1) (by simp only [List.length_cons]; omega)
      rw [raw_fullyDefined_singleQuery_of_two_le f (hlater j hj)] at hj'
      simpa using (Part.some_inj.mp hj').symm
  · rintro ⟨hy, hrest⟩ k hk
    rw [List.forall_mem_iff_forall_getElem] at hrest
    by_cases hk0 : k = 0
    · subst hk0
      rw [hfirst, raw_fullyDefined_singleQuery_singleton]
      simp [hy]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < rest.length := by
        simp only [List.length_cons] at hk; omega
      rw [raw_fullyDefined_singleQuery_of_two_le f (hlater j hj)]
      simpa using (hrest j hj).symm

/-! ## Example 2.16's family `V_α` -/

/-- Thesis Example 2.10 / Figure 2.1: `zero(x) := 0`. -/
def zeroFn : Bool → Bool := fun _ => false

/-- Thesis Example 2.10 / Figure 2.1: `one(x) := 1`. -/
def oneFn : Bool → Bool := fun _ => true

/-- Thesis Example 2.10 / Figure 2.1: `id(x) := x`. -/
def idFn : Bool → Bool := fun x => x

/-- Thesis Example 2.10 / Figure 2.1: `flip(x) := 1 − x`. -/
def flipFn : Bool → Bool := fun x => !x

/-- **Thesis Example 2.16**:
`V_α := {(zero, α), (one, α), (id, 1/2 − α), (flip, 1/2 − α)}`.
The thesis's `V` is `V_{1/4}` and its `V'` is `V_{1/2}`; the two extremes
`V₀` and `V_{1/2}` are the pair its Def 2.28 remark cites.

The family's *index* is unchanged by the signed-carrier migration: Example
2.16 ranges `α` over `[0, 1/2]`, which is still spelled `α : ℝ≥0` together
with `α ≤ 1/2`.  Only the *masses* moved to `ℝ`, so `1/2 − α` is now honest
subtraction rather than `ℝ≥0`'s truncated one; the coercion is written out to
keep that visible.  Consequently `0 ≤ α` stays structural — no statement
below had to acquire it — and `α ≤ 1/2` is exactly what `nonNeg_V` needs. -/
noncomputable def V (α : NNReal) : PFunPDS Bool Bool :=
  Finsupp.single (singleQuery zeroFn) (α : ℝ)
    + Finsupp.single (singleQuery oneFn) (α : ℝ)
    + Finsupp.single (singleQuery idFn) (1 / 2 - (α : ℝ))
    + Finsupp.single (singleQuery flipFn) (1 / 2 - (α : ℝ))

open Classical in
/-- The mass of an event under `V_α`, atom by atom. -/
theorem mass_V (α : NNReal) (P : PFunDDS.DDS Bool Bool → Prop) :
    (V α).mass P
      = (if P (singleQuery zeroFn) then (α : ℝ) else 0)
        + (if P (singleQuery oneFn) then (α : ℝ) else 0)
        + (if P (singleQuery idFn) then 1 / 2 - (α : ℝ) else 0)
        + (if P (singleQuery flipFn) then 1 / 2 - (α : ℝ) else 0) := by
  rw [V, Dist.mass_add, Dist.mass_add, Dist.mass_add, Dist.mass_single,
    Dist.mass_single, Dist.mass_single, Dist.mass_single]

/-- Each `V_α` with `α ≤ 1/2` is a probability distribution.

`_hα` is retained for fidelity to Example 2.16's stated range: on the `ℝ≥0`
carrier the truncated `1/2 − α` made it load-bearing (without it the two
`{id, flip}` atoms vanish and the weight is `2α`), while honest subtraction
makes the weight `1` unconditionally.  It is still the hypothesis every
caller has, and `nonNeg_V` — the other half of `isProbDist` — genuinely
needs it. -/
theorem weight_V {α : NNReal} (_hα : α ≤ 1 / 2) : (V α).weight = 1 := by
  rw [V, Dist.weight_add, Dist.weight_add, Dist.weight_add, Dist.weight_single,
    Dist.weight_single, Dist.weight_single, Dist.weight_single]
  ring

/-- Each `V_α` with `α ≤ 1/2` is **pointwise non-negative** — the half of
`isProbDist` that the `ℝ≥0` carrier supplied structurally.  `Dist.NonNeg` is
the right layer and `hα` the whole cost: `0 ≤ α` is still free from the index
type, and `0 ≤ 1/2 − α` is exactly Example 2.16's upper end. -/
theorem nonNeg_V {α : NNReal} (hα : α ≤ 1 / 2) : (V α).NonNeg := by
  have hcoe : (α : ℝ) ≤ 1 / 2 := by exact_mod_cast hα
  have hrest : (0 : ℝ) ≤ 1 / 2 - (α : ℝ) := by linarith
  intro s
  simp only [V, Finsupp.add_apply]
  exact add_nonneg (add_nonneg (add_nonneg
    (Dist.nonNeg_single _ α.coe_nonneg s) (Dist.nonNeg_single _ α.coe_nonneg s))
    (Dist.nonNeg_single _ hrest s)) (Dist.nonNeg_single _ hrest s)

/-- Each `V_α` with `α ≤ 1/2` is a probability law.  Over the signed carrier
`isProbDist` is the conjunction of the two lemmas above; on `ℝ≥0` it was
`weight_V` alone. -/
theorem isProbDist_V {α : NNReal} (hα : α ≤ 1 / 2) : (V α).isProbDist :=
  ⟨nonNeg_V hα, weight_V hα⟩

/-- `V_α` as a probability law (thesis Def 2.14's normalized carrier). -/
noncomputable def VProb (α : NNReal) (hα : α ≤ 1 / 2) : PFunPDS.Prob Bool Bool :=
  ⟨V α, isProbDist_V hα⟩

/-- The single behavior of the whole class `[V]` (CR18 Def 3.20 on the resource
view `s⊥`): the empty transcript carries the full weight, an initial answered
query carries `1/2` whichever bit it records, and every later query must be
rejected. -/
noncomputable def classBehavior : ObservableBehavior Bool Bool :=
  fun t => match t with
    | [] => 1
    | (_, y) :: rest => if y ≠ none ∧ ∀ p ∈ rest, p.2 = none then 1 / 2 else 0

@[simp] theorem classBehavior_nil : classBehavior [] = 1 := rfl

@[simp] theorem classBehavior_cons (x : Bool) (y : Option Bool)
    (rest : List (Bool × Option Bool)) :
    classBehavior ((x, y) :: rest)
      = if y ≠ none ∧ ∀ p ∈ rest, p.2 = none then 1 / 2 else 0 := rfl

/-- **Example 2.16's claim, computed**: every `V_α` with `α ∈ [0, 1/2]` has the
same Def 3.20 behavior on `s⊥`, namely `classBehavior` — a uniform random bit
for the one query that gets answered.  The parameter cancels because each of
the two pairs `{zero, one}` and `{id, flip}` contains exactly one system
answering a prescribed bit to a prescribed query — each answered query
therefore weighs `α + (1/2 − α)`.  As in `weight_V`, `_hα` is retained for
fidelity to Example 2.16's range: the cancellation was `ℝ≥0`'s
`add_tsub_cancel_of_le`, and over `ℝ` it is `ring`. -/
theorem observableBehavior_V {α : NNReal} (_hα : α ≤ 1 / 2) :
    observableBehavior (V α) = classBehavior := by
  classical
  funext t
  rw [observableBehavior_eq_mass_consistent, mass_V]
  match t with
  | [] =>
      rw [if_pos (consistent_nil _), if_pos (consistent_nil _),
        if_pos (consistent_nil _), if_pos (consistent_nil _), classBehavior_nil]
      ring
  | (x, y) :: rest =>
      rw [classBehavior_cons]
      by_cases hrest : ∀ p ∈ rest, p.2 = none
      · cases y with
        | none =>
            have hfalse : ∀ g : Bool → Bool,
                ¬ Consistent ((x, none) :: rest) (singleQuery g) := by
              intro g hg
              exact absurd ((consistent_singleQuery_cons g x none rest).mp hg).1
                (by simp)
            rw [if_neg (hfalse _), if_neg (hfalse _), if_neg (hfalse _),
              if_neg (hfalse _), if_neg (by simp)]
            simp
        | some b =>
            have hcond : ∀ g : Bool → Bool,
                Consistent ((x, some b) :: rest) (singleQuery g) ↔ g x = b := by
              intro g
              rw [consistent_singleQuery_cons]
              constructor
              · rintro ⟨h1, -⟩
                exact (Option.some_inj.mp h1).symm
              · intro h1
                exact ⟨by rw [h1], hrest⟩
            rw [if_pos (⟨by simp, hrest⟩ :
              (some b : Option Bool) ≠ none ∧ ∀ p ∈ rest, p.2 = none)]
            simp only [hcond]
            cases b <;> cases x <;>
              simp only [zeroFn, oneFn, idFn, flipFn, Bool.not_false,
                Bool.not_true, reduceIte, reduceCtorEq] <;>
              ring
      · have hfalse : ∀ g : Bool → Bool,
            ¬ Consistent ((x, y) :: rest) (singleQuery g) := by
          intro g hg
          exact hrest ((consistent_singleQuery_cons g x y rest).mp hg).2
        rw [if_neg (hfalse _), if_neg (hfalse _), if_neg (hfalse _),
          if_neg (hfalse _), if_neg (fun h => hrest h.2)]
        simp

/-- **Thesis Example 2.16, deliverable 1**: `V_α ≡ V_β` for all
`α, β ∈ [0, 1/2]` — the thesis's "it is easy to verify that for any
`α ∈ [0, 1/2]`, the PDS `V_α` has the same behavior as `V`".  In particular
`V₀ ≡ V_{1/2}` (`equivalent_V0_Vhalf`). -/
theorem equivalent_V {α β : NNReal} (hα : α ≤ 1 / 2) (hβ : β ≤ 1 / 2) :
    Equivalent (V α) (V β) :=
  (behavior_equivalent_iff_transcript_equivalent (VProb α hα) (VProb β hβ)).mp
    (by
      show observableBehavior (V α) = observableBehavior (V β)
      rw [observableBehavior_V hα, observableBehavior_V hβ])

/-- **Thesis Example 2.16, deliverable 2**: `V₀ ≡ V_{1/2}`. -/
theorem equivalent_V0_Vhalf : Equivalent (V 0) (V (1 / 2)) :=
  equivalent_V (by norm_num) le_rfl

/-! ## `δ(V₀, V_{1/2}) = 1` -/

/-- If the second law vanishes on the first law's support, the one-sided
distance is the whole first weight (thesis Def 2.4 at disjoint supports).

`hμ` is the signed carrier's cost: `δ`'s summand is `max (μ a − ν a) 0`, which
collapses to `μ a` only where `μ a ≥ 0`, and `ℝ≥0`'s `tsub_zero` used to
supply that for free.  `Dist.NonNeg` is the weakest layer available, not a
convenience: the proof only reads `μ` on its support, and off the support
`μ a = 0`, so `∀ a ∈ μ.support, 0 ≤ μ a` *is* `Dist.NonNeg μ`.  Nothing is
normalized here, so `isProbDist` would be strictly more. -/
theorem delta_eq_weight_of_apply_eq_zero {A : Type*} (μ ν : Dist A)
    (hμ : μ.NonNeg) (h : ∀ a ∈ μ.support, ν a = 0) : δ μ ν = μ.weight := by
  unfold δ
  rw [Dist.weight_eq_finsupp_sum]
  exact Finsupp.sum_congr fun a ha => by
    rw [h a ha, sub_zero, max_eq_left (hμ a)]

private theorem singleQuery_ne {f g : Bool → Bool} (h : f ≠ g) :
    singleQuery f ≠ singleQuery g := fun heq => h (singleQuery_injective heq)

/-- `V₀ = {(id, 1/2), (flip, 1/2)}`: the `zero`/`one` atoms carry no mass. -/
theorem V0_eq : V 0
    = Finsupp.single (singleQuery idFn) (1 / 2)
      + Finsupp.single (singleQuery flipFn) (1 / 2) := by
  rw [V]
  simp

/-- `V_{1/2} = {(zero, 1/2), (one, 1/2)}`: the `id`/`flip` atoms carry no
mass. -/
theorem Vhalf_eq : V (1 / 2)
    = Finsupp.single (singleQuery zeroFn) (1 / 2)
      + Finsupp.single (singleQuery oneFn) (1 / 2) := by
  rw [V]
  simp

/-- **Thesis Example 2.16, deliverable 3**: `δ(V₀, V_{1/2}) = 1`.  The two
extremes of the family are supported on disjoint sets of deterministic systems
— `{id, flip}` against `{zero, one}` — so the one-sided distance exhausts the
whole weight, exactly the thesis's remark below Def 2.28. -/
theorem delta_V0_Vhalf : δ (V 0) (V (1 / 2)) = 1 := by
  classical
  have hzero : ∀ a ∈ (V 0).support, (V (1 / 2)) a = 0 := by
    intro a ha
    have hsub : a = singleQuery idFn ∨ a = singleQuery flipFn := by
      rw [V0_eq] at ha
      rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
      · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
      · exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
    rw [Vhalf_eq]
    rcases hsub with rfl | rfl <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply] <;>
      rw [if_neg (singleQuery_ne (by decide)),
        if_neg (singleQuery_ne (by decide)), add_zero]
  rw [delta_eq_weight_of_apply_eq_zero _ _ (nonNeg_V (by norm_num)) hzero,
    weight_V (by norm_num)]

/-! ## The Definition 2.28 erratum, kernel-checked -/

/-- The representative pair `(V₀, V_{1/2})` of the class `[V]`, packaged as
Def 2.27's `Fin 2` tuple. -/
noncomputable def witnessPair : Fin 2 → PFunPDS Bool Bool :=
  fun k => if k = 0 then V 0 else V (1 / 2)

theorem witnessPair_equivalent (k : Fin 2) :
    Equivalent (witnessPair k) (V 0) := by
  fin_cases k
  · exact fun _ _ => rfl
  · exact (equivalent_V le_rfl (by norm_num) : Equivalent (V (1 / 2)) (V 0))

/-- The witness pair's inner supremum vanishes: no coupling of `V₀` with
`V_{1/2}` ever puts mass on the diagonal, because their supports are
disjoint. -/
theorem supAgreement_witnessPair :
    Lanzenberger.supAgreement witnessPair = 0 := by
  have hnn : ∀ k, (witnessPair k).NonNeg := by
    intro k
    fin_cases k
    · show (V 0).NonNeg
      exact nonNeg_V (by norm_num)
    · show (V (1 / 2)).NonNeg
      exact nonNeg_V le_rfl
  rw [Lanzenberger.supAgreement_pair_eq_weight_sub_delta witnessPair hnn
    (by
      show (V (1 / 2)).weight = (V 0).weight
      rw [weight_V le_rfl, weight_V (by norm_num)])]
  show (V 0).weight - δ (V 0) (V (1 / 2)) = 0
  rw [weight_V (by norm_num), delta_V0_Vhalf]
  norm_num

private theorem printed_set_mem_zero :
    (0 : ℝ) ∈ {a : ℝ | ∃ laws : Fin 2 → PFunPDS Bool Bool,
      (∀ i, Equivalent (laws i) ((fun _ => V 0 : Fin 2 → PFunPDS Bool Bool) i))
        ∧ a = Lanzenberger.supAgreement laws} :=
  ⟨witnessPair, witnessPair_equivalent, supAgreement_witnessPair.symm⟩

/-- **Definition 2.28's second printed display, evaluated at `𝐒 = 𝐓 = [V]`:
it is `1`.** -/
theorem printedMultiSystemDistance_V0 :
    Lanzenberger.printedMultiSystemDistance (fun _ : Fin 2 => V 0) = 1 := by
  have hnonneg : ∀ a ∈ {a : ℝ | ∃ laws : Fin 2 → PFunPDS Bool Bool,
      (∀ i, Equivalent (laws i) ((fun _ => V 0 : Fin 2 → PFunPDS Bool Bool) i))
        ∧ a = Lanzenberger.supAgreement laws}, (0 : ℝ) ≤ a := by
    rintro a ⟨laws, -, rfl⟩
    exact Lanzenberger.supAgreement_nonneg laws
  have hinf : sInf {a : ℝ | ∃ laws : Fin 2 → PFunPDS Bool Bool,
      (∀ i, Equivalent (laws i) ((fun _ => V 0 : Fin 2 → PFunPDS Bool Bool) i))
        ∧ a = Lanzenberger.supAgreement laws} = 0 :=
    le_antisymm (csInf_le ⟨0, hnonneg⟩ printed_set_mem_zero)
      (le_csInf ⟨0, printed_set_mem_zero⟩ hnonneg)
  unfold Lanzenberger.printedMultiSystemDistance
  rw [hinf, sub_zero]

/-- **Definition 2.28's first printed display, evaluated at `𝐒 = 𝐓 = [V]`:
it is `0`** — take the same representative on both sides. -/
theorem class_distance_V0 : Δ (V 0) (V 0) = 0 := by
  have hnonneg : ∀ a ∈ {a : ℝ | ∃ S' T' : PFunPDS Bool Bool,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' (V 0) ∧ Equivalent T' (V 0) ∧ a = (δ S' T' : ℝ)},
      (0 : ℝ) ≤ a := by
    rintro a ⟨S', T', -, -, -, -, rfl⟩
    exact δ_nonneg S' T'
  have hmem : (0 : ℝ) ∈ {a : ℝ | ∃ S' T' : PFunPDS Bool Bool,
      S'.NonNeg ∧ T'.NonNeg ∧
      Equivalent S' (V 0) ∧ Equivalent T' (V 0) ∧ a = (δ S' T' : ℝ)} :=
    ⟨V 0, V 0, nonNeg_V (by norm_num), nonNeg_V (by norm_num),
      fun _ _ => rfl, fun _ _ => rfl, (δ_self _).symm⟩
  exact le_antisymm (csInf_le ⟨0, hnonneg⟩ hmem) (le_csInf ⟨0, hmem⟩ hnonneg)

/-- **The erratum, as a theorem.**  At the class pair `𝐒 = 𝐓 = [V]` of thesis
Example 2.16, Definition 2.28's two printed displays take *different* values:
its first display `inf_{S∈𝐒,T∈𝐓} δ(S,T)` is `0`, its second display
`1 − inf_{(S,T)∈𝐒×𝐓} sup_ℰ Pr^ℰ(S = T)` is `1`.

The printed definition therefore cannot be read verbatim.  The reason is
exactly the one the thesis itself points at in the remark below Def 2.28: the
classical coupling lemma turns the inner `sup_ℰ Pr^ℰ` into `1 − δ` per
representative pair, so an `inf` over representatives on the right computes the
`sup` of `δ`, not its `inf` — and `V₀`/`V_{1/2}` are equivalent representatives
at `δ = 1`, so the two differ maximally.  See `corrected_display_agrees_at_V`
for the repaired reading. -/
theorem definition_2_28_printed_displays_disagree :
    Lanzenberger.printedMultiSystemDistance (fun _ : Fin 2 => V 0)
      ≠ Δ (V 0) (V 0) := by
  rw [printedMultiSystemDistance_V0, class_distance_V0]
  norm_num

/-- The **corrected** reading of Def 2.28's second display —
`multiSystemDistance`, with the inner quantifier a `sup` over representatives —
does agree with the first display at the same class pair.  Together with
`definition_2_28_printed_displays_disagree` this pins the erratum to the
quantifier and nowhere else. -/
theorem corrected_display_agrees_at_V :
    Lanzenberger.multiSystemDistance (fun _ : Fin 2 => V 0) = Δ (V 0) (V 0) :=
  Lanzenberger.definition_2_28_pair_distance_eq_class_distance
    (isProbDist_V (α := 0) (by norm_num)) (isProbDist_V (α := 0) (by norm_num))
    _ rfl rfl

end RandomSystems.CR18.Example216
