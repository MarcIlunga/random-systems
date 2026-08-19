/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.StatDist
import RandomSystems.PFunDDS
import RandomSystems.PFunConverter

/-!
# CR18 Probabilistic Discrete Systems and Environments

This module formalizes CR18 Definitions 3.14–3.17. Maurer defines a
probabilistic discrete `(X, Y)`-system as a random variable over the set of
deterministic discrete `(X, Y)`-systems, characterized by its probability
distribution over DDSs. A probabilistic discrete environment (PDE) is the
symmetric notion: a random variable over deterministic discrete environments.
A probabilistic discrete converter (PDC) is a random variable over DDCs.

## Distribution model: `RandomSystems.Dist` (NOT `PMF`)

Following Lanzenberger–Maurer (LM20) Definition 1, a "distribution" here is a
**finitely-supported function with weight not necessarily 1** — i.e. a
sub-distribution of arbitrary weight.  LM20 explicitly notes this generality is
essential ("the proof of Theorem 1 relies on distributions of arbitrary
weight").  Mathlib's `PMF` is the wrong model: it forces total mass `1` and
permits infinite support, which (a) cannot represent the successor operator
`S^{↑x↓y}` (conditioning on the first query drops mass → sub-distribution),
(b) cannot carry coupling / Δ intermediates, and (c) is incompatible with the
existing `RandomSystems.Dist` / `statDist` / `Coupling` / `FundamentalTheorem`
machinery (all `Finsupp` / `NNReal`).

We therefore use `RandomSystems.Dist A := A →₀ ℝ` throughout.  Point mass is
`Finsupp.single a 1`, evaluation is `Finsupp` application `(d : Dist A) a`,
pushforward is `Dist.fTransform`, and uniform is `Dist.uniform`.
-/

open RandomSystems (Dist)
open RandomSystems.CryptoNotation

namespace RandomSystems.CR18

universe u v w z

attribute [local instance] Classical.propDecidable


/-!
## PFun-native CR18 Definitions 3.14–3.16

The compatibility-layer `PDS` above is over the original `DDS` record.  During
the migration to the partial-function presentation, the same mathematical
definition is kept in parallel: a probabilistic discrete system is a
finite-support distribution over PFun-native deterministic objects.
-/

/-- CR18 Definition 3.14, PFun-native form: a probabilistic discrete
`(X,Y)`-system is a random variable over deterministic discrete systems,
represented by its finite-support distribution over `PFunDDS.DDS X Y`.

Lanzenberger Def 2.14 is this carrier **plus** the common-domain clause:
all support atoms present one domain `dom(S)`.  The repository keeps the
clause as the separate predicate `PFunPDS.HasFixedDomain`
(`RandomSystem.lean`), imposed exactly where the thesis needs it; the
clause is substantive, not cosmetic — dropping it falsifies attainment
(`AttainmentCounterexample.lean`). -/
abbrev PFunPDS (X : Type u) (Y : Type v) : Type (max u v) :=
  Dist (PFunDDS.DDS X Y)

namespace PFunPDS

variable {X : Type u} {Y : Type v}

/-- A probability law over PFun-native deterministic systems. -/
abbrev Prob (X : Type u) (Y : Type v) :=
  {S : PFunPDS X Y // S.isProbDist}

/-- Degenerate PFun-native PDS concentrated at one deterministic system. -/
noncomputable def pure (s : PFunDDS.DDS X Y) : PFunPDS X Y :=
  Finsupp.single s 1

/-- Alias for the deterministic special case of a PFun-native PDS. -/
noncomputable abbrev ofDDS (s : PFunDDS.DDS X Y) : PFunPDS X Y :=
  pure s

/-- Probability mass assigned to one deterministic system. -/
def prob (S : PFunPDS X Y) (s : PFunDDS.DDS X Y) : ℝ :=
  S s

@[simp]
theorem prob_apply (S : PFunPDS X Y) (s : PFunDDS.DDS X Y) :
    prob S s = S s :=
  rfl

@[simp]
theorem prob_pure (s : PFunDDS.DDS X Y) :
    prob (pure s : PFunPDS X Y) s = 1 := by
  simp [prob, pure]

/-! ### CR18 §3.4.3 / Definition 3.10: query filters -/

/-- Push a DDS-level prefix-closed domain restriction through a probabilistic
system's distribution over deterministic representatives. -/
noncomputable def filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (G : PFunPDS X Y) : PFunPDS X Y :=
  Dist.fTransform (PFunDDS.filterDom P hP) G

/-- Domain filtering preserves and reflects total probability mass — for a
non-negative law.  (Over the signed carrier the unconditional `↔` is false:
the filter map merges representatives and can cancel signed masses.) -/
theorem isProbDist_filterDom_iff (P : List X → Prop) (hP : PrefixClosed P)
    {S : PFunPDS X Y} (hS : S.NonNeg) :
    (filterDom P hP S).isProbDist ↔ S.isProbDist := by
  unfold filterDom
  exact Dist.isProbDist_fTransform _ hS

/-- **The `[q]` filter on a probabilistic system** — push the DDS-level query
restriction through the distribution over deterministic representatives. This is
CR18 Def. 3.17's "composition of a probabilistic converter with a probabilistic
system", specialized to the deterministic filter `[q]`. -/
noncomputable def filterQueries (q : ℕ) (G : PFunPDS X Y) : PFunPDS X Y :=
  Dist.fTransform (PFunDDS.filterQueries q) G

/-- The query filter is definitionally the length-bounded instance of `filterDom`.
The pushforward spelling preserves the established unfold normal form. -/
theorem filterQueries_eq_filterDom (q : ℕ) (G : PFunPDS X Y) :
    filterQueries q G =
      filterDom (fun l => l.length ≤ q) (prefixClosed_length_le q) G := rfl

/-! ### Bundled domain filters (UPSTREAM-CANDIDATE)

`filterDom` takes the admission predicate and its closure proof as two separate
arguments, so every call site must name both — and there are ~160 of them.  That
also leaves the *general* restriction without notation, while its length-bounded
special case has one (`⌈q⌉`); a σ-budget or block-count restriction therefore
reads far worse than a query-count one, for no mathematical reason.

`DomFilter` bundles the pair, giving the general restriction the notation
`⌈φ⌉ᵈ G` in the shape of `⌈q⌉ G`.  `⌈q⌉` is then literally an instance
(`filterOf_queryFilter`, by `rfl`), not a parallel notion.  Additive: existing
`filterDom` call sites are untouched. -/

/-- **A domain filter** (UPSTREAM-CANDIDATE): a prefix-closed admission predicate
on query histories, bundled with its closure proof. -/
structure DomFilter (X : Type u) where
  /-- The admitted query histories. -/
  P : List X → Prop
  /-- Admission is prefix-closed, so the restriction is a CR18 filter. -/
  prefixClosed : PrefixClosed P

/-- The action of a bundled domain filter on a probabilistic system. -/
noncomputable def filterOf (φ : DomFilter X) (G : PFunPDS X Y) : PFunPDS X Y :=
  filterDom φ.P φ.prefixClosed G

/-- The query-count restriction `[q]` as a bundled domain filter. -/
def queryFilter (q : ℕ) : DomFilter X :=
  ⟨fun l => l.length ≤ q, prefixClosed_length_le q⟩

@[simp] theorem filterOf_eq_filterDom (φ : DomFilter X) (G : PFunPDS X Y) :
    filterOf φ G = filterDom φ.P φ.prefixClosed G := rfl

/-- **`⌈q⌉` is an instance of the general restriction**, definitionally. -/
@[simp] theorem filterOf_queryFilter (q : ℕ) (G : PFunPDS X Y) :
    filterOf (queryFilter q) G = filterQueries q G := rfl

/-- Domain filtering by a bundled filter preserves and reflects total mass, for a
non-negative law (`isProbDist_filterDom_iff` at the bundled surface). -/
theorem isProbDist_filterOf_iff (φ : DomFilter X) {S : PFunPDS X Y} (hS : S.NonNeg) :
    (filterOf φ S).isProbDist ↔ S.isProbDist :=
  isProbDist_filterDom_iff φ.P φ.prefixClosed hS

/-- Query filtering preserves and reflects total probability mass — for a
non-negative law (see `isProbDist_filterDom_iff`). -/
theorem isProbDist_filterQueries_iff (q : ℕ) {S : PFunPDS X Y} (hS : S.NonNeg) :
    (filterQueries q S).isProbDist ↔ S.isProbDist := by
  unfold filterQueries
  exact Dist.isProbDist_fTransform _ hS

/-- Query filtering sends probability laws to probability laws. -/
theorem isProbDist_filterQueries (q : ℕ) {S : PFunPDS X Y} (hS : S.isProbDist) :
    (filterQueries q S).isProbDist :=
  Dist.fTransform_isProbDist _ hS

/-! ### CR18 Definition 3.15: random functions and permutations -/

/-- CR18 Definition 3.15, PFun-native form: a random function is a PDS whose
support consists of stateless function-evaluator DDSs. -/
def IsRandomFunction (S : PFunPDS X Y) : Prop :=
  ∀ s : PFunDDS.DDS X Y, S s ≠ 0 →
    ∃ f : X → Y, s = PFunDDS.functionEvaluator f

/-- Push a distribution over functions forward to the corresponding PDS. -/
noncomputable def ofFunDist
    (Df : Dist (X → Y)) : PFunPDS X Y :=
  Dist.fTransform PFunDDS.functionEvaluator Df

/-- Function-distribution pushforward preserves and reflects total probability
mass.  (Unconditional: `functionEvaluator` is injective, so the pushforward
cannot merge signed masses.) -/
@[simp] theorem isProbDist_ofFunDist_iff (Df : Dist (X → Y)) :
    (ofFunDist Df).isProbDist ↔ Df.isProbDist := by
  unfold ofFunDist
  exact Dist.isProbDist_fTransform_of_injective PFunDDS.functionEvaluator_injective Df

/-- Uniform random function. -/
noncomputable def URF [Fintype (X → Y)] [Nonempty (X → Y)]
    : PFunPDS X Y :=
  ofFunDist (Dist.uniform (X → Y))

/-- The uniform random-function system has total mass one. -/
@[simp] theorem URF_isProbDist [Fintype (X → Y)] [Nonempty (X → Y)] :
    (URF (X := X) (Y := Y)).isProbDist := by
  unfold URF
  rw [isProbDist_ofFunDist_iff]
  exact Dist.uniform_isProbDist

/-- A function distribution pushed through `functionEvaluator` is a random
function in the sense of Definition 3.15. -/
theorem ofFunDist_isRandomFunction
    (Df : Dist (X → Y)) :
    IsRandomFunction (ofFunDist Df) := by
  intro s hs
  rw [ofFunDist, Dist.fTransform_apply_eq_mass] at hs
  by_contra hcon
  simp only [not_exists] at hcon
  apply hs
  unfold Dist.mass Finsupp.sum
  apply Finset.sum_eq_zero
  intro f _hf
  by_cases hf : PFunDDS.functionEvaluator f = s
  · exact False.elim (hcon f hf.symm)
  · simp [hf]

/-- CR18 Definition 3.15, PFun-native form: a random permutation is a PDS whose
support consists of function evaluators for bijections. -/
def IsRandomPermutation {X : Type u} (S : PFunPDS X X) : Prop :=
  ∀ s : PFunDDS.DDS X X, S s ≠ 0 →
    ∃ f : X → X, Function.Bijective f ∧ s = PFunDDS.functionEvaluator f

/-- Push a distribution over permutations forward to the corresponding PDS. -/
noncomputable def ofPermDist (X : Type u)
    (Dσ : Dist (Equiv.Perm X)) : PFunPDS X X :=
  Dist.fTransform (fun σ : Equiv.Perm X => PFunDDS.functionEvaluator σ.toFun) Dσ

/-- Permutation-distribution pushforward preserves and reflects total probability mass. -/
@[simp] theorem isProbDist_ofPermDist_iff {X : Type u} (Dσ : Dist (Equiv.Perm X)) :
    (ofPermDist X Dσ).isProbDist ↔ Dσ.isProbDist := by
  unfold ofPermDist
  exact Dist.isProbDist_fTransform_of_injective
    (fun σ τ h => Equiv.coe_fn_injective (PFunDDS.functionEvaluator_injective h)) Dσ

/-- Uniform random permutation. -/
noncomputable def URP (X : Type u) [Fintype X] : PFunPDS X X :=
  letI : Nonempty (Equiv.Perm X) := ⟨Equiv.refl X⟩
  ofPermDist X (Dist.uniform (Equiv.Perm X))

/-- The uniform random-permutation system has total mass one. -/
@[simp] theorem URP_isProbDist (X : Type u) [Fintype X] :
    (URP X).isProbDist := by
  unfold URP
  rw [isProbDist_ofPermDist_iff]
  convert Dist.uniform_isProbDist using 2

/-- Permutations are functions: `ofPermDist` is `ofFunDist` of the coerced distribution. -/
theorem ofPermDist_eq_ofFunDist {X : Type u} (Dσ : Dist (Equiv.Perm X)) :
    ofPermDist X Dσ = ofFunDist (Dist.fTransform (fun σ : Equiv.Perm X => σ.toFun) Dσ) := by
  unfold ofPermDist ofFunDist
  rw [Dist.fTransform_comp]
  rfl

/-- The URP is in particular a random function (Def 3.15) — every realization is a function
evaluator.  (Stated here, inside `URP`'s own instance context; see the classical-boundary note
on `URP_isProbDist`.) -/
theorem URP_isRandomFunction (X : Type u) [Fintype X] : IsRandomFunction (URP X) := by
  unfold URP
  rw [ofPermDist_eq_ofFunDist]
  exact ofFunDist_isRandomFunction _

/-- The URF is a random function (Def 3.15). -/
theorem URF_isRandomFunction [Fintype (X → Y)] [Nonempty (X → Y)] :
    IsRandomFunction (URF (X := X) (Y := Y)) := by
  unfold URF
  exact ofFunDist_isRandomFunction _

/-- `ofPermDist` is a random permutation in the sense of Definition 3.15. -/
theorem ofPermDist_isRandomPermutation (X : Type u) [Fintype (Equiv.Perm X)]
    (Dσ : Dist (Equiv.Perm X)) :
    IsRandomPermutation (ofPermDist X Dσ) := by
  intro s hs
  rw [ofPermDist, Dist.fTransform_apply_eq_mass] at hs
  by_contra hcon
  apply hs
  unfold Dist.mass Finsupp.sum
  apply Finset.sum_eq_zero
  intro σ _hσ
  by_cases hσs : PFunDDS.functionEvaluator σ.toFun = s
  · exact False.elim (hcon ⟨σ.toFun, σ.bijective, hσs.symm⟩)
  · dsimp
    have hσs' : ¬ PFunDDS.functionEvaluator (⇑σ) = s := by
      intro h
      exact hσs (by simpa using h)
    rw [if_neg hσs']

namespace Ex35

/-- CR18 Example 3.5, PFun-native form: the `{0,1}^m,{0,1}^n` URF. -/
noncomputable def R (m n : ℕ) : PFunPDS (Fin (2 ^ m)) (Fin (2 ^ n)) :=
  URF (X := Fin (2 ^ m)) (Y := Fin (2 ^ n))

/-- CR18 Example 3.5, PFun-native form: the `{0,1}^m` URP. -/
noncomputable def P (m : ℕ) : PFunPDS (Fin (2 ^ m)) (Fin (2 ^ m)) :=
  URP (Fin (2 ^ m))

theorem R_isRandomFunction (m n : ℕ) :
    IsRandomFunction (R m n) := by
  unfold R URF
  exact ofFunDist_isRandomFunction _

theorem P_isRandomPermutation (m : ℕ) :
    IsRandomPermutation (P m) := by
  unfold P URP
  exact ofPermDist_isRandomPermutation (Fin (2 ^ m)) _

end Ex35

end PFunPDS

/-- CR18 notation for the query filter `[q]G` (Def. 3.10). Corner brackets avoid
clashing with Lean list literals (`[q]`) and `getElem` (`G[q]`); reads as Maurer's
`[q]G`. -/
scoped notation:max "⌈" q "⌉" G => PFunPDS.filterQueries q G

/-- Notation for the general domain restriction (UPSTREAM-CANDIDATE): `⌈φ⌉ᵈ G`
restricts `G` to the histories admitted by the bundled filter `φ`.  The `ᵈ`
distinguishes it from the query-count case `⌈q⌉ G`, which it subsumes
(`PFunPDS.filterOf_queryFilter`). -/
scoped notation:max "⌈" φ "⌉ᵈ" G => PFunPDS.filterOf φ G

/-- Lanzenberger Def 2.15 (= CR18 Definition 3.16), PFun-native form: a
probabilistic discrete environment for an `(X,Y)`-DDS is a random variable
over deterministic environments, represented by its finite-support
distribution over `PFunDDS.DDE X Y`.  (The two sources define the
probabilistic layer identically; they differ one level down, in the
deterministic environment carrier — see `ThesisModel.lean`.) -/
abbrev PFunPDE (X : Type u) (Y : Type v) : Type (max u v) :=
  Dist (PFunDDS.DDE X Y)

namespace PFunPDE

variable {X : Type u} {Y : Type v}

/-- A probability law over PFun-native deterministic environments. -/
abbrev Prob (X : Type u) (Y : Type v) :=
  {E : PFunPDE X Y // E.isProbDist}

/-- CR18 Definition 3.7: the deterministic transcript **function** `tr(·,·)`,
sending a deterministic system–environment pair `(s,e)` to its transcript
sequence `tr(s,e) = PFunDDS.transcript s e`.

This is a *function*, not a random variable — it carries no distribution. It is
the deterministic map through which the transcript **random variable** `tr(S,E)`
is built (see `transcriptRV`): when the system `S` and environment `E` are
themselves random variables, `tr(S,E)` is `tr(·,·)` composed with `⟨S,E⟩`. -/
noncomputable def transcriptFun :
    PFunDDS.DDS X Y × PFunDDS.DDE X Y → (ℕ → List (X × Option Y)) :=
  fun se => PFunDDS.transcript se.1 se.2

/-! #### CR18 Definition 3.16 — the random-variable form -/

/-- CR18 Definition 3.16, random-variable form (dual to `PFunPDS.RV`): a PDE is a
random variable over deterministic environments — a function from a sample space
`Ω` to `PFunDDS.DDE X Y`. The `PFunPDE X Y = Dist (DDE X Y)` above is its law. -/
abbrev RV (Ω : Type w) (X : Type u) (Y : Type v) := Dist.RV (Ω := Ω) (A := PFunDDS.DDE X Y)

/-- The **law** of a PDE random variable in experiment `p`: the pushforward of
`p` along `E` (Def 3.16, distribution form). -/
noncomputable def RV.law {Ω : Type w} (p : Dist.ProbDist Ω) (E : RV Ω X Y) : PFunPDE X Y :=
  Dist.fTransform E p.val

/-- A probabilistic environment is `k`-query-total on concrete output
histories when it supplies a next query for every concrete output history of
length `< k`. This is the exact totality condition needed for length-`k`
CR18 transcript-prefix laws over `X^k × Y^k`; arbitrary DDEs may stop, so this
is not built into `PFunPDE.RV`. -/
def RV.KQueryTotal {Ω : Type w} (E : RV Ω X Y) (k : ℕ) : Prop :=
  ∀ (ω : Ω) (ys : List Y), ys.length < k → ∃ x : X, E ω (ys.map some) = some x

/-- A deterministic environment is `k`-query-total on concrete output histories
when it supplies a next query for every concrete output history of length `< k`.
This is the deterministic specialization of `PFunPDE.RV.KQueryTotal`, stated
directly on the CR18 `DDE` rather than through an artificial one-point random
variable. -/
def DDEKQueryTotal (E : PFunDDS.DDE X Y) (k : ℕ) : Prop :=
  ∀ ys : List Y, ys.length < k → ∃ x : X, E (ys.map some) = some x

/-- Deterministic CR18 environments that issue exactly the `q` concrete queries
needed to define a length-`q` transcript-prefix law. -/
abbrev QQueryEnvironment (X : Type u) (Y : Type v) (q : Nat) :=
  {E : PFunDDS.DDE X Y // DDEKQueryTotal E q}

end PFunPDE

/-- CR18 Definition 3.17, PFun-native form: a probabilistic discrete
converter is a random variable over deterministic discrete converters,
represented by its finite-support distribution over `PFunConverter.DDC`. -/
abbrev PFunPDC (U : Type u) (V : Type v) (X : Type w) (Y : Type z) :
    Type (max (max u v) (max w z)) :=
  Dist (PFunConverter.DDC U V X Y)

/-! ### CR18 §3.6.2 / Definition 3.18: behavior of a PDS -/

namespace PFunPDS

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 3.18: `b(S)` is the sequence
`p^S_{Yᵢ|XⁱYⁱ⁻¹}`. Lean indexes it from `0`, so index `i` is paper round
`i + 1`. -/
abbrev Behavior (X : Type u) (Y : Type v) : Type (max u v) :=
  (i : ℕ) → Y × (Vector X (i + 1) × Vector Y i) →. ℝ

/-- CR18 Definition 3.18. -/
noncomputable def behavior (S : PFunPDS X Y) : Behavior X Y :=
  fun _ arg =>
    let yi := arg.1
    let xi := arg.2.1.toList
    let yprev := arg.2.2.toList
    Pr[(∃ h : xi ∈ PFunDDS.dom s, PFunDDS.output s xi h = yi) |
      s ←$ S,
      ∀ k : Fin yprev.length,
        ∃ h : xi.take (k.1 + 1) ∈ PFunDDS.dom s,
          PFunDDS.output s (xi.take (k.1 + 1)) h = yprev.get k]

/-- CR18 §3.6.2, first displayed behavior kernel `p^S_{Y₁|X₁}`.

This is just the first element of `b(S)`, specialized to an input/output pair
`(y₁, x₁)`. -/
noncomputable def pY1GivenX1 (S : PFunPDS X Y) : Y × X →. ℝ :=
  fun arg =>
    behavior S 0
      (arg.1, (Vector.singleton arg.2,
        Vector.ofFn (α := Y) (n := 0) (fun i => nomatch i)))

/-- CR18 notation for Definition 3.18. -/
scoped notation "b" "(" S ")" => behavior S

/-! ### CR18 Definition 3.19: equivalence by behavior -/

/-- CR18 Definition 3.19, PFun-native form: two probabilistic systems are
equivalent exactly when they have the same behavior.

**Resource-level warning.**  On partial systems this notion is **strictly
coarser** than the thesis's Def 2.17 transcript equivalence (`Equivalent`):
the Def 3.18 kernel conditions on successful histories only and provably
loses the correlations a rejected query reveals —
`AttainmentCounterexample.behaviorEq_not_equivalent_counterexample` exhibits
two probability laws with equal kernels and distinct transcript laws.  The
behavior notion that does match transcript laws on the `s⊥` resource view is
Definition 3.20's cumulative `Option`-behavior
(`behavior_equivalent_iff_transcript_equivalent`, `RandomSystem.lean`). -/
def BehaviorEq (S T : PFunPDS X Y) : Prop :=
  behavior S = behavior T

/-- Notation for CR18 Definition 3.19: equivalence of PDSs by behavior. -/
scoped infix:50 " ≡ᵦ " => BehaviorEq

@[simp]
theorem behaviorEq_iff_behavior (S T : PFunPDS X Y) :
    S ≡ᵦ T ↔ behavior S = behavior T :=
  Iff.rfl

/-- Pointwise form of CR18 Definition 3.19. This is just function
extensionality for `b(S) = b(T)`. -/
theorem behaviorEq_ext {S T : PFunPDS X Y} :
    S ≡ᵦ T ↔ ∀ i arg, behavior S i arg = behavior T i arg := by
  constructor
  · intro h i arg
    exact congrFun (congrFun h i) arg
  · intro h
    funext i arg
    exact h i arg

namespace BehaviorEq

theorem refl (S : PFunPDS X Y) : S ≡ᵦ S :=
  rfl

theorem symm {S T : PFunPDS X Y} (h : S ≡ᵦ T) : T ≡ᵦ S :=
  Eq.symm h

theorem trans {S T U : PFunPDS X Y} (hST : S ≡ᵦ T) (hTU : T ≡ᵦ U) :
    S ≡ᵦ U :=
  Eq.trans hST hTU

theorem equivalence : Equivalence (BehaviorEq (X := X) (Y := Y)) where
  refl := refl
  symm := symm
  trans := trans

theorem of_eq {S T : PFunPDS X Y} (h : S = T) : S ≡ᵦ T := by
  subst h
  rfl

theorem behavior_eq {S T : PFunPDS X Y} (h : S ≡ᵦ T) :
    behavior S = behavior T :=
  h

end BehaviorEq

/-! ### CR18 §3.6.4 / Definition 3.20: cumulative behavior -/

/-- CR18 Definition 3.20, PFun-native form: the cumulative description
`p^S_{Yⁱ|Xⁱ}`.

Lean indexes from `0`, so index `i` represents the paper length `i + 1`.
The argument order follows the paper formula `p^S_{Yⁱ|Xⁱ}(yⁱ, xⁱ)`. -/
abbrev CumulativeBehavior (X : Type u) (Y : Type v) : Type (max u v) :=
  (i : ℕ) → Vector Y (i + 1) × Vector X (i + 1) → ℝ

/-- CR18 Definition 3.20: `p^S_{Yⁱ|Xⁱ}(yⁱ,xⁱ)` is the probability, over the
choice of deterministic `s ← S`, that
`(s(x₁), s(x₁,x₂), …, s(xⁱ)) = yⁱ`. -/
noncomputable def cumulativeBehavior (S : PFunPDS X Y) : CumulativeBehavior X Y :=
  fun _ arg =>
    let ys := arg.1.toList
    let xs := arg.2.toList
    Dist.mass S (fun s =>
      ∀ k : Fin ys.length,
        ∃ h : xs.take (k.1 + 1) ∈ PFunDDS.dom s,
          PFunDDS.output s (xs.take (k.1 + 1)) h = ys.get k)

/-- CR18 notation for Definition 3.20. -/
scoped notation "bᶜ" "(" S ")" => cumulativeBehavior S

/-- The input prefix `xʲ` of a fixed full input sequence `xⁱ`, where
`j : Fin i`. -/
def inputPrefix {n : ℕ} (xs : Vector X n) (j : Fin n) : Vector X (j.1 + 1) :=
  Vector.ofFn fun k : Fin (j.1 + 1) =>
    xs.get ⟨k.1, by omega⟩

/-- The previous-output prefix `yʲ⁻¹` of a fixed full output sequence `yⁱ`,
where `j : Fin i`. -/
def outputPrefix {n : ℕ} (ys : Vector Y n) (j : Fin n) : Vector Y j.1 :=
  Vector.ofFn fun k : Fin j.1 =>
    ys.get ⟨k.1, by omega⟩

/-- `inputPrefix xs j` is exactly the length-`(j+1)` prefix of `xs`. -/
theorem inputPrefix_toList {n : ℕ} (xs : Vector X n) (j : Fin n) :
    (inputPrefix xs j).toList = xs.toList.take (j.1 + 1) := by
  apply List.ext_getElem
  · simp only [inputPrefix, Vector.toList_ofFn, List.length_ofFn, List.length_take,
      Vector.length_toList]
    omega
  · intro k h1 h2
    simp only [inputPrefix, Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take,
      Vector.get_eq_getElem, Vector.getElem_toList]

/-- `outputPrefix ys j` is exactly the length-`j` prefix of `ys`. -/
theorem outputPrefix_toList {n : ℕ} (ys : Vector Y n) (j : Fin n) :
    (outputPrefix ys j).toList = ys.toList.take j.1 := by
  apply List.ext_getElem
  · simp only [outputPrefix, Vector.toList_ofFn, List.length_ofFn, List.length_take,
      Vector.length_toList]
    omega
  · intro k h1 h2
    simp only [outputPrefix, Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take,
      Vector.get_eq_getElem, Vector.getElem_toList]

/-- CR18 Eq. (3.2): the cumulative behavior is the product of the stepwise
behavior kernels.

The hypothesis `hS` is the paper's probabilistic-system assumption. It is
needed because this file's `Dist` model also admits LM20 sub-distributions; for
sub-distributions the same telescoping identity has an extra leading
`S.weight` factor.

The hypothesis `hdef` says every conditional behavior factor in the product is
defined, i.e. every conditioning prefix has nonzero probability. -/
theorem cumulativeBehavior_eq_behavior_prod (S : PFunPDS X Y)
    (hS : S.isProbDist) {i : ℕ}
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1))
    (hdef : ∀ j : Fin (i + 1),
      (b(S) j.1 (ys.get j, (inputPrefix xs j, outputPrefix ys j))).Dom) :
    bᶜ(S) i (ys, xs) =
      ∏ j : Fin (i + 1),
        (b(S) j.1
          (ys.get j, (inputPrefix xs j, outputPrefix ys j))).get (hdef j) := by
  classical
  -- The output-prefix event family `Aₖ s = "s outputs yₖ on the k-th input prefix"`,
  -- made total in `k` with `getD` (in range it is the Vector-indexed event).
  let yv : ℕ → Y := fun k => ys.toList.getD k (ys.get 0)
  let A : ℕ → PFunDDS.DDS X Y → Prop := fun k s =>
    ∃ h : xs.toList.take (k + 1) ∈ PFunDDS.dom s,
      PFunDDS.output s (xs.toList.take (k + 1)) h = yv k
  have hyslen : ys.toList.length = i + 1 := by simp
  -- In range, the total `yv k` is the Vector-indexed output value.
  have hyv : ∀ k (hk : k < i + 1), yv k = ys.toList[k]'(by omega) :=
    fun k hk => List.getD_eq_getElem ys.toList (ys.get 0) (by omega)
  -- (1) the cumulative behavior is the mass of the full conjunction `⋀_{k<i+1} Aₖ`.
  have hcum : bᶜ(S) i (ys, xs) = S.mass (fun s => ∀ k, k < i + 1 → A k s) := by
    unfold cumulativeBehavior
    apply Dist.mass_congr
    intro s
    dsimp only
    rw [Fin.forall_iff]
    refine forall_congr' fun k => ?_
    constructor
    · intro h hk
      obtain ⟨hh, hv⟩ := h (by omega)
      exact ⟨hh, by rw [hv, List.get_eq_getElem, ← hyv k hk]⟩
    · intro h hk
      obtain ⟨hh, hv⟩ := h (by omega)
      exact ⟨hh, by rw [hv, hyv k (by omega), List.get_eq_getElem]⟩
  -- range split for the `A`-conjunction.
  have hsplit : ∀ (B : ℕ → Prop) m, (∀ k, k < m + 1 → B k) ↔ (∀ k, k < m → B k) ∧ B m := by
    intro B m
    constructor
    · intro h; exact ⟨fun k hk => h k (by omega), h m (by omega)⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact h1 k hk'
      · exact h2
  -- the k-th entry of an output prefix is the (total) value `yv k`.
  have hoval : ∀ (j : Fin (i + 1)) (m : ℕ) (hm : m < (outputPrefix ys j).toList.length),
      (outputPrefix ys j).toList.get ⟨m, hm⟩ = yv m := by
    intro j m hm
    have hlen : (outputPrefix ys j).toList.length = j.1 := by
      rw [outputPrefix_toList, List.length_take, hyslen]; omega
    have hmi : m < i + 1 := by have := j.2; omega
    rw [hyv m hmi, List.get_eq_getElem]
    simp only [outputPrefix, Vector.getElem_toList, Vector.getElem_ofFn, Vector.get_eq_getElem]
  -- the behavior conditioning event ⟺ the `A`-prefix `⋀_{k<j} Aₖ`.
  have hQiff : ∀ (j : Fin (i + 1)) (s : PFunDDS.DDS X Y),
      (∀ k : Fin (outputPrefix ys j).toList.length,
          ∃ h : (inputPrefix xs j).toList.take (↑k + 1) ∈ PFunDDS.dom s,
            PFunDDS.output s ((inputPrefix xs j).toList.take (↑k + 1)) h
              = (outputPrefix ys j).toList.get k) ↔ (∀ k, k < j.1 → A k s) := by
    intro j s
    have hlen : (outputPrefix ys j).toList.length = j.1 := by
      rw [outputPrefix_toList, List.length_take, hyslen]; omega
    rw [Fin.forall_iff]
    refine forall_congr' fun k => ?_
    constructor
    · intro hall hk
      have hk' : k < (outputPrefix ys j).toList.length := by rw [hlen]; exact hk
      have htake : (inputPrefix xs j).toList.take (k + 1) = xs.toList.take (k + 1) := by
        rw [inputPrefix_toList, List.take_take]; congr 1; omega
      obtain ⟨hh, hv⟩ := hall hk'
      refine ⟨htake ▸ hh, ?_⟩
      rw [PFunDDS.output_congr s htake.symm (htake ▸ hh) hh, hv]
      exact hoval j k hk'
    · intro hA hk'
      have hk : k < j.1 := by rw [← hlen]; exact hk'
      have htake : (inputPrefix xs j).toList.take (k + 1) = xs.toList.take (k + 1) := by
        rw [inputPrefix_toList, List.take_take]; congr 1; omega
      obtain ⟨hh, hv⟩ := hA hk
      refine ⟨htake.symm ▸ hh, ?_⟩
      rw [PFunDDS.output_congr s htake (htake.symm ▸ hh) hh, hv]
      exact (hoval j k hk').symm
  -- the behavior current-output event ⟺ `A_{j}`.
  have hPiff : ∀ (j : Fin (i + 1)) (s : PFunDDS.DDS X Y),
      (∃ h : (inputPrefix xs j).toList ∈ PFunDDS.dom s,
          PFunDDS.output s (inputPrefix xs j).toList h = ys.get j) ↔ A j.1 s := by
    intro j s
    have htake : (inputPrefix xs j).toList = xs.toList.take (j.1 + 1) := inputPrefix_toList xs j
    have hyj : ys.get j = yv j.1 := by
      rw [hyv j.1 j.2, Vector.get_eq_getElem, Vector.getElem_toList]
    constructor
    · rintro ⟨hh, hv⟩
      exact ⟨htake ▸ hh, by rw [PFunDDS.output_congr s htake.symm (htake ▸ hh) hh, hv, hyj]⟩
    · rintro ⟨hh, hv⟩
      exact ⟨htake.symm ▸ hh, by rw [PFunDDS.output_congr s htake (htake.symm ▸ hh) hh, hv, ← hyj]⟩
  -- (2) each behavior factor is the one-step conditional mass.
  have hfac : ∀ j : Fin (i + 1),
      (b(S) j.1 (ys.get j, (inputPrefix xs j, outputPrefix ys j))).get (hdef j) =
        S.mass (fun s => ∀ k, k < j.1 + 1 → A k s) / S.mass (fun s => ∀ k, k < j.1 → A k s) := by
    intro j
    simp only [behavior]
    rw [Dist.cond_get]
    congr 1
    · apply Dist.mass_congr
      intro s
      rw [hPiff j s, hQiff j s, hsplit (fun k => A k s) j.1]
      exact and_comm
    · exact Dist.mass_congr S (fun s => hQiff j s)
  -- (3) every conditioning prefix has nonzero mass (from `hdef`).
  have hpos : ∀ j, j ≤ i → S.mass (fun s => ∀ k, k < j → A k s) ≠ 0 := by
    intro j hj hzero
    exact hdef ⟨j, by omega⟩
      ((Dist.mass_congr S (fun s => hQiff ⟨j, by omega⟩ s)).trans hzero)
  rw [hcum, Finset.prod_congr rfl (fun j _ => hfac j),
    Fin.prod_univ_eq_prod_range
      (fun m => S.mass (fun s => ∀ k, k < m + 1 → A k s) / S.mass (fun s => ∀ k, k < m → A k s))
      (i + 1)]
  exact Dist.mass_biForall_lt_eq_prod ⟨S, hS⟩ A i hpos

/-! ### CR18 Definition 3.14 — the random-variable form

Definition 3.14 *literally* says a PDS is a random variable over DDS. The
`PFunPDS X Y = Dist (DDS X Y)` above is its **law**; here is the random variable
itself (a function `Ω → DDS`, via the existing `Dist.RV`), together with the
forgetful map to its law and the fact that every observable factors through it. -/

/-- CR18 Definition 3.14, random-variable form: a PDS is a random variable over
deterministic systems — a function from a sample space `Ω` to `PFunDDS.DDS X Y`.
The distribution `p : ProbDist Ω` on the sample space is ambient. -/
abbrev RV (Ω : Type w) (X : Type u) (Y : Type v) := Dist.RV (Ω := Ω) (A := PFunDDS.DDS X Y)

/-- The **law** of a PDS random variable in experiment `p`: the pushforward of `p`
along `S` (Def 3.14, distribution form). Equals `(ℙ⟦S⟧ : ProbDist _).val`. -/
noncomputable def RV.law {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y) : PFunPDS X Y :=
  Dist.fTransform S p.val

/-- A probabilistic system is `k`-step-total on concrete input histories when
it produces a concrete output on every nonempty input history of length at most
`k`. This is the system-side totality condition needed for length-`k` CR18
transcript-prefix laws over `X^k × Y^k`. -/
def RV.KStepTotal {Ω : Type w} (S : RV Ω X Y) (k : ℕ) : Prop :=
  ∀ (ω : Ω) (xs : List X), xs ≠ [] → xs.length ≤ k →
    ∃ y : Y, (S ω).1 xs = Part.some y

/-! ### CR18 §3.6.1–3.6.2 — behavior via the output random variables

Maurer's behavior, RV-native and built on the generic function-valued-RV infra
(`Dist.RV.eval`). A PDS is a *function-valued* random variable (`funView`); its
outputs `S(α)` are the evaluations of that function-valued RV (Maurer fn15: "S is
a function-valued random variable, hence S(α) is a Y-valued random variable"); and
`b(S)` is the family of *conditional laws* of those output random variables. No
bespoke output evaluator — every output is `Dist.RV.eval` of `funView`. -/

/-- A PDS as a **function-valued random variable** (Maurer fn15): its value at
`ω` is the underlying partial function `List X →. Y` of the chosen DDS. The
outputs `S(α)` are `Dist.RV.eval` of this view. -/
def funView {Ω : Type w} (S : RV Ω X Y) : Dist.RV (Ω := Ω) (A := PFunDDS.Raw X Y) :=
  fun ω => (S ω).1

/-- The previous-outputs random variable along an input history `α = x₁…xᵢ`: the
tuple `(S(x¹), …, S(xⁱ⁻¹))` of outputs on the proper nonempty prefixes (lengths
`1 … i-1`), each an evaluation of `funView S`. -/
def prevOut {Ω : Type w} (S : RV Ω X Y) (α : List X) :
    Dist.RV (Ω := Ω) (A := List (Part Y)) :=
  fun ω => (List.range (α.length - 1)).map (fun j => Dist.RV.eval (funView S) (α.take (j + 1)) ω)

/-- CR18 Definition 3.18, RV-native form. The behavior `b(S)` at input history
`α = x₁…xᵢ` is the conditional law of the output random variable `S(xⁱ)` given the
previous output random variables `(S(x¹),…,S(xⁱ⁻¹))`:

`p^S_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, α, yⁱ⁻¹) = ℙ⟦ S(xⁱ) | S(x¹),…,S(xⁱ⁻¹) ⟧[yᵢ, yⁱ⁻¹]`,

a partial function of `(yᵢ, yⁱ⁻¹)`. Normalization (fn14: the slice sums to 1 over
`yᵢ`) and partiality (fn14: undefined when the conditioning history has
probability 0) are inherited from `Dist.condPMFOf`. For `|α| = 1` the conditioning
tuple is empty and this collapses to the channel law `ℙ⟦S(x)⟧` (§3.6.1,
`channelLaw`). -/
noncomputable def behaviorB {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y)
    (α : List X) : Part Y → List (Part Y) → Part ℝ :=
  Dist.condPMFOf p (Dist.RV.eval (funView S) α) (prevOut S α)

/-- CR18 §3.6.1, channel behavior: for a single input `x`, the behavior is just
the **law of the output random variable** `S(x)` — `p^C_{Y|X}(·,x) = ℙ⟦C(x)⟧`,
the pushforward of `S`'s law-over-functions along "evaluate at `[x]`"
(`Dist.mass_eval`). It is `behaviorB` with empty conditioning. -/
noncomputable def channelLaw {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y)
    (x : X) : Dist.ProbDist (Part Y) :=
  Dist.PMF p (Dist.RV.eval (funView S) [x])

/-- The conditioning tuple is empty on a single input: `prevOut S [x] = []`. -/
@[simp]
theorem prevOut_singleton {Ω : Type w} (S : RV Ω X Y) (x : X) :
    prevOut S [x] = fun _ => [] := by
  funext ω
  simp [prevOut]

/-! #### Confirmation that `behaviorB` is exactly CR18 Definition 3.18

Three theorems pin `behaviorB` to Maurer's definition: the **defining equation**
(the conditional probability of the i-th output given the previous outputs),
footnote 14's **normalization** (each slice is a probability distribution over the
i-th output), and footnote 14's **partiality** (undefined exactly when the
conditioning history has probability 0). Together they are Definition 3.18. -/

/-- **CR18 Def 3.18, the defining equation.** When the conditioning history has
positive probability, `behaviorB` is the conditional probability of the output
random variable `S(xⁱ)` given the previous outputs:
`p^S_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ, xⁱ, yⁱ⁻¹) = Pr[ S(xⁱ)=yᵢ ∧ S(x¹..xⁱ⁻¹)=yⁱ⁻¹ ] / Pr[ S(x¹..xⁱ⁻¹)=yⁱ⁻¹ ]`,
where `S(α) = (S ω).1 α` is the output random variable (Maurer fn15). -/
theorem behaviorB_get {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y)
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y))
    (h : p.val.mass (fun ω => prevOut S α ω = yprev) ≠ 0) :
    (behaviorB p S α yᵢ yprev).get h
      = p.val.mass (fun ω => Dist.RV.eval (funView S) α ω = yᵢ ∧ prevOut S α ω = yprev)
        / p.val.mass (fun ω => prevOut S α ω = yprev) :=
  Dist.condPMFOf_apply p (Dist.RV.eval (funView S) α) (prevOut S α) yprev h yᵢ

/-- **CR18 Def 3.18, footnote 14 — each `b(S)ᵢ` is a conditional probability
distribution.** For a fixed input history `α` and previous outputs `yⁱ⁻¹` with
positive probability, the slice `yᵢ ↦ behaviorB p S α yᵢ yⁱ⁻¹` is a genuine
probability distribution over the i-th output (sums to 1) — not just a kernel.
The slice's value at `yᵢ` is exactly `(behaviorB p S α yᵢ yⁱ⁻¹).get h`. -/
theorem behaviorB_slice_isProbDist {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y)
    (α : List X) (yprev : List (Part Y))
    (h : p.val.mass (fun ω => prevOut S α ω = yprev) ≠ 0) :
    (Dist.condPMFOfDist p (Dist.RV.eval (funView S) α) (prevOut S α) yprev h).val.isProbDist
      ∧ ∀ yᵢ, Dist.condPMFOfDist p (Dist.RV.eval (funView S) α) (prevOut S α) yprev h yᵢ
          = (behaviorB p S α yᵢ yprev).get h :=
  ⟨Dist.condPMFOf_isProbDist p (Dist.RV.eval (funView S) α) (prevOut S α) yprev h,
   fun yᵢ => Dist.condPMFOfDist_apply p (Dist.RV.eval (funView S) α) (prevOut S α) yprev h yᵢ⟩

/-- **CR18 Def 3.18, footnote 14 — partiality.** `behaviorB` is defined at
`(yᵢ, α, yⁱ⁻¹)` exactly when the conditioning history `yⁱ⁻¹` has nonzero
probability under the input history `α`. -/
theorem behaviorB_dom {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y)
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y)) :
    (behaviorB p S α yᵢ yprev).Dom
      ↔ p.val.mass (fun ω => prevOut S α ω = yprev) ≠ 0 :=
  Iff.rfl

/-! #### The output-sequence random variable (CR18 §3.6.4 cumulative form)

For a fixed input history `xs = (x₁,…,xᵢ)`, the outputs `(Y₁,…,Yᵢ) =
(S(x¹),…,S(xⁱ))` form a random variable over output sequences. Its law (Def 3.20)
is the *cumulative behavior*; the key structural fact is that dropping the last
output of an extended history recovers the shorter history's sequence — the
seed of the consistency (causality) condition. -/

/-- The output-sequence random variable: `xs ↦ (S(x¹),…,S(x^{|xs|}))`, the
outputs of `S` on every nonempty prefix of `xs`. -/
noncomputable def outSeq {Ω : Type w} (S : RV Ω X Y) (xs : List X) :
    Dist.RV (Ω := Ω) (A := List (Part Y)) :=
  fun ω => (List.range xs.length).map (fun j => Dist.RV.eval (funView S) (xs.take (j + 1)) ω)

/-- Dropping the last output of an extended history recovers the shorter history's
output sequence: `(S(x¹),…,S(xⁱ),S(xⁱ⁺¹)).dropLast = (S(x¹),…,S(xⁱ))`. This is the
causal core of the consistency condition (`Yⱼ` does not depend on future inputs). -/
theorem dropLast_outSeq {Ω : Type w} (S : RV Ω X Y) (xs : List X) (x : X) (ω : Ω) :
    (outSeq S (xs ++ [x]) ω).dropLast = outSeq S xs ω := by
  unfold outSeq
  rw [List.length_append, List.length_singleton, List.range_succ,
    List.map_append, List.map_cons, List.map_nil, List.dropLast_concat]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [List.take_append_of_le_length (by omega)]

/-- The conditioning in `behaviorB` (the previous outputs `S(x¹),…,S(xⁱ⁻¹)`) is
exactly the **prefix** of the joint output sequence: `prevOut S xs = (outSeq S
xs).dropLast`. So the Def 3.18 conditional kernel `behaviorB S` conditions the last
output of the first-class joint behavior on the earlier ones. -/
theorem prevOut_eq_dropLast_outSeq {Ω : Type w} (S : RV Ω X Y) (xs : List X) (ω : Ω) :
    prevOut S xs ω = (outSeq S xs ω).dropLast := by
  have key : ∀ (g : ℕ → Part Y) (n : ℕ),
      (List.map g (List.range n)).dropLast = List.map g (List.range (n - 1)) := by
    intro g n; cases n with
    | zero => rfl
    | succ k => rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.dropLast_concat, Nat.succ_sub_one]
  unfold prevOut outSeq
  exact (key (fun j => Dist.RV.eval (funView S) (xs.take (j + 1)) ω) xs.length).symm

/-- The output sequence has exactly one entry per input: `|Yⁱ| = |xⁱ| = i`. -/
theorem outSeq_length {Ω : Type w} (S : RV Ω X Y) (xs : List X) (ω : Ω) :
    (outSeq S xs ω).length = xs.length := by
  simp [outSeq]

/-- **CR18 §3.6.4 (pre-Def-3.20)**: the `j`-th entry of the output sequence is the
output of `S` on the length-`(j+1)` prefix — `Yⱼ₊₁ = S(x¹…x^{j+1})`. This is exactly
the paper's `Y₁ = S(x₁)`, `Y₂ = S(x₁,x₂)`, `Y₃ = S(x₁,x₂,x₃)`, … (`j` is 0-based). -/
theorem getElem_outSeq {Ω : Type w} (S : RV Ω X Y) (xs : List X) (ω : Ω)
    (j : ℕ) (hj : j < (outSeq S xs ω).length) :
    (outSeq S xs ω)[j] = Dist.RV.eval (funView S) (xs.take (j + 1)) ω := by
  simp only [outSeq, List.getElem_map, List.getElem_range]

/-! #### List ⇄ conjunction view (the single bridge behind Eq 3.2)

The joint behavior is a **list-valued** random variable (`outSeq`), but the
probability chain rule (`mass_biForall_lt_eq_prod`) speaks of a **family of
per-index events** `⋀ₖ Aₖ`. These two lemmas convert once between the two: the
list-equality event of `outSeq`/`prevOut` against a `range`-indexed target is the
conjunction of the per-prefix output events. Everything downstream (Def 3.20 ↔ Def
3.18, the consistency condition) reuses them instead of re-deriving the bridge. -/

/-- `outSeq S xs ω = (range |xs|).map g` iff every prefix output matches `g`. -/
theorem outSeq_eq_map_iff {Ω : Type w} (S : RV Ω X Y) (xs : List X)
    (g : ℕ → Part Y) (ω : Ω) :
    outSeq S xs ω = (List.range xs.length).map g
      ↔ ∀ k, k < xs.length → Dist.RV.eval (funView S) (xs.take (k + 1)) ω = g k := by
  refine ⟨fun h k hk => ?_, fun h => ?_⟩
  · have := congrArg (fun l => l[k]?) h
    simpa [outSeq, List.getElem?_map, List.getElem?_range, hk] using this
  · simp only [outSeq]
    exact List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

/-- The conditioning conversion: `prevOut` on a length-`(j+1)` prefix equals
`(range j).map g` iff the first `j` prefix outputs match `g`. -/
theorem prevOut_take_eq_map_iff {Ω : Type w} (S : RV Ω X Y) (xs : List X) {j : ℕ}
    (hj : j < xs.length) (g : ℕ → Part Y) (ω : Ω) :
    prevOut S (xs.take (j + 1)) ω = (List.range j).map g
      ↔ ∀ k, k < j → Dist.RV.eval (funView S) (xs.take (k + 1)) ω = g k := by
  have hlen : (xs.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hpv : prevOut S (xs.take (j + 1)) ω
      = (List.range j).map (fun k => Dist.RV.eval (funView S) (xs.take (k + 1)) ω) := by
    simp only [prevOut, hlen, Nat.add_sub_cancel]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    have hkt : (xs.take (j + 1)).take (k + 1) = xs.take (k + 1) := by
      rw [List.take_take]; congr 1; omega
    rw [hkt]
  rw [hpv]
  refine ⟨fun h k hk => ?_, fun h => ?_⟩
  · have := congrArg (fun l => l[k]?) h
    simpa [List.getElem?_map, List.getElem?_range, hk] using this
  · exact List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

/-! #### `outSeq`/`prevOut` structural API (one snoc, one dropLast)

Two reusable structural facts about the list-valued behavior RVs: the output sequence
is built one output at a time (`outSeq_snoc`), and the previous-outputs RV is the
output sequence on the history with its last input dropped (`prevOut_eq_outSeq_dropLast`).
These are the bridges every recursion/telescoping over the behavior uses (Eq 3.2's
inverse, the consistency condition, transcripts). -/

/-- The output sequence on an extended history is the **snoc** of the shorter one with
the last output `S(x¹…xⁱ⁺¹)`. -/
theorem outSeq_snoc {Ω : Type w} (S : RV Ω X Y) (xs : List X) (x : X) (ω : Ω) :
    outSeq S (xs ++ [x]) ω
      = outSeq S xs ω ++ [Dist.RV.eval (funView S) (xs ++ [x]) ω] := by
  have hne : outSeq S (xs ++ [x]) ω ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, outSeq_length, List.length_append,
      List.length_singleton]; omega
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [dropLast_outSeq]
  congr 1
  rw [List.getLast_eq_getElem, getElem_outSeq, outSeq_length, List.length_append,
    List.length_singleton, Nat.add_sub_cancel,
    show xs.length + 1 = (xs ++ [x]).length by simp, List.take_length]

/-- The **previous-outputs** RV on a history equals the **output-sequence** RV on the
history with its last input dropped: `prevOut S xs = outSeq S xs.dropLast`. -/
theorem prevOut_eq_outSeq_dropLast {Ω : Type w} (S : RV Ω X Y) (xs : List X) (ω : Ω) :
    prevOut S xs ω = outSeq S xs.dropLast ω := by
  simp only [prevOut, outSeq, List.length_dropLast]
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  congr 1
  rw [List.dropLast_eq_take, List.take_take]
  congr 1
  omega

/-- **CR18 §3.6.4, the consistency condition** (causality / non-anticipation): *for
`j < i`, `Yⱼ` does not depend on `X_{j+1},…,X_i`*. The first `j` outputs of `S` on the
history `xⁱ` are exactly its outputs on the first `j` inputs — later inputs cannot
influence earlier outputs. (`getElem_outSeq` is the per-output form `Yⱼ = S(x¹…xʲ)`;
`dropLast_outSeq` is the single-input-step special case.) -/
theorem outSeq_take {Ω : Type w} (S : RV Ω X Y) (xs : List X) (j : ℕ) (ω : Ω) :
    (outSeq S xs ω).take j = outSeq S (xs.take j) ω := by
  apply List.ext_getElem
  · simp only [List.length_take, outSeq_length]
  · intro k h1 _
    have hk : k < j := by simp only [List.length_take, outSeq_length] at h1; omega
    have ht : xs.take (k + 1) = (xs.take j).take (k + 1) := by
      rw [List.take_take]; congr 1; omega
    rw [List.getElem_take, getElem_outSeq, getElem_outSeq, ht]

/-! #### Behavior is computed from the law (Maurer's "distribution over DDS")

The behavior `b(S)` only depends on the **law** of `S` — its distribution over
deterministic systems. This is Maurer's "these conditional distributions can be
computed from the probability distribution (of S) over deterministic systems",
and the reason behavioral equivalence (Def 3.19) is well-defined: distinct random
variables (even on different sample spaces) with the same law have the same
behavior. The engine is `Dist.condPMFOf_comp`: every output `S(α)` is a
deterministic image of `S`, so the conditional law factors through `ℙ⟦S⟧`. -/

/-- CR18 Def 3.18, **law form**: the behavior computed directly from a
distribution `L` over deterministic systems — the experiment that samples `s ← L`
and uses it (sample space `DDS X Y`, identity random variable). This is Maurer's
"computed from the distribution over deterministic systems". -/
noncomputable def behaviorOfLaw (L : Dist.ProbDist (PFunDDS.DDS X Y)) :
    List X → Part Y → List (Part Y) → Part ℝ :=
  behaviorB L (fun s => s)

/-- The bridge: `b(S)` is computed from the law `ℙ⟦S⟧`. The RV-form behavior in
any experiment equals the law-form behavior of its distribution over DDS. -/
theorem behaviorB_eq_behaviorOfLaw {Ω : Type w} (p : Dist.ProbDist Ω) (S : RV Ω X Y) :
    behaviorB p S = behaviorOfLaw (Dist.PMF p S) := by
  funext α
  exact Dist.condPMFOf_comp p S
    (fun s => (s : PFunDDS.DDS X Y).1 α)
    (fun s => (List.range (α.length - 1)).map (fun j => (s : PFunDDS.DDS X Y).1 (α.take (j + 1))))

/-- CR18 §3.6.2, the coarsening (the surprising line 3232): behavior depends only
on the law, so two random variables — over possibly different sample spaces —
with the **same distribution over DDS** have the **same behavior**. This is the
collapse the whole indistinguishability theory rests on. -/
theorem behaviorB_eq_of_law_eq {Ω : Type w} {Ω' : Type z}
    (p : Dist.ProbDist Ω) (q : Dist.ProbDist Ω') (S : RV Ω X Y) (T : RV Ω' X Y)
    (hlaw : Dist.PMF p S = Dist.PMF q T) :
    behaviorB p S = behaviorB q T := by
  rw [behaviorB_eq_behaviorOfLaw, behaviorB_eq_behaviorOfLaw, hlaw]

/-! #### CR18 Definition 3.19: equivalence by behavior (RV form) -/

/-- CR18 Definition 3.19, RV-native: two probabilistic systems `S` (in experiment
`p`) and `T` (in experiment `q`) are **behaviorally equivalent** when they have the
same behavior. By `behaviorB_eq_of_law_eq`, equal law implies equivalence. -/
def BehaviorEqRV {Ω : Type w} {Ω' : Type z}
    (p : Dist.ProbDist Ω) (S : RV Ω X Y) (q : Dist.ProbDist Ω') (T : RV Ω' X Y) : Prop :=
  behaviorB p S = behaviorB q T

/-- Equal law ⇒ behaviorally equivalent (Def 3.19 from the coarsening). -/
theorem behaviorEqRV_of_law_eq {Ω : Type w} {Ω' : Type z}
    (p : Dist.ProbDist Ω) (q : Dist.ProbDist Ω') (S : RV Ω X Y) (T : RV Ω' X Y)
    (hlaw : Dist.PMF p S = Dist.PMF q T) :
    BehaviorEqRV p S q T :=
  behaviorB_eq_of_law_eq p q S T hlaw

/-! ### CR18 Example 3.6: behavior of a URF -/

theorem take_succ_ne_nil {xs : List X} {k : ℕ} (hk : k < xs.length) :
    xs.take (k + 1) ≠ [] := by
  intro hnil
  rw [List.take_eq_nil_iff] at hnil
  rcases hnil with hzero | hxs
  · exact Nat.succ_ne_zero k hzero
  · simp [hxs] at hk

theorem vector_getLast_toList {i : ℕ} (xs : Vector X (i + 1)) :
    xs.toList.getLast (by simp) =
      xs.get ⟨i, Nat.lt_succ_self i⟩ := by
  rw [List.getLast_eq_getElem]
  simp [Vector.getElem_toList]
  rfl

/-- CR18 Example 3.6: the behavior of a uniform random function.

This is the paper's conditional-probability kernel:
`Pr[f(xᵢ) = yᵢ | f(x₁)=y₁, ..., f(xᵢ₋₁)=yᵢ₋₁]`, where `f` is sampled
uniformly from `X → Y`. -/
noncomputable def urfBehavior [Fintype (X → Y)]
    [Nonempty (X → Y)] :
    Behavior X Y :=
  fun i arg =>
    let yi := arg.1
    let yprev := arg.2.2.toList
    let xs := arg.2.1.toList
    let xi := arg.2.1.get ⟨i, Nat.lt_succ_self i⟩
    Pr[f xi = yi |
      f ←$ Dist.uniform (X → Y),
      ∀ k : Fin yprev.length,
        f ((xs.take (k.1 + 1)).getLast (by
          have hk : k.1 < i := by simpa [yprev] using k.2
          exact take_succ_ne_nil (xs := xs) (by simp [xs]; omega))) = yprev.get k]

/-- The behavior obtained by going through the PFun DDS function evaluator. -/
noncomputable def urfDDSSamplingBehavior [Fintype (X → Y)] [Nonempty (X → Y)] :
    Behavior X Y :=
  fun _ arg =>
    let yi := arg.1
    let xs := arg.2.1.toList
    let ys := arg.2.2.toList
    Pr[(∃ h : xs ∈ PFunDDS.dom (PFunDDS.functionEvaluator f),
          PFunDDS.output (PFunDDS.functionEvaluator f) xs h = yi) |
      f ←$ Dist.uniform (X → Y),
      ∀ k : Fin ys.length,
        ∃ h : xs.take (k.1 + 1) ∈ PFunDDS.dom (PFunDDS.functionEvaluator f),
          PFunDDS.output (PFunDDS.functionEvaluator f) (xs.take (k.1 + 1)) h = ys.get k]

/-- CR18 Example 3.6: the PDS that samples functions uniformly has the URF
sampling behavior. -/
theorem behavior_URF_sampling [Fintype (X → Y)] [Nonempty (X → Y)]
    :
    behavior (URF (X := X) (Y := Y)) =
      urfDDSSamplingBehavior (X := X) (Y := Y) := by
  funext i arg
  apply Part.ext
  intro a
  unfold behavior urfDDSSamplingBehavior URF ofFunDist Dist.cond
  simp [Dist.mass_fTransform]

/-- Function-evaluator form of the URF behavior is the paper conditional kernel. -/
theorem urfDDSSamplingBehavior_eq_urfBehavior
    [Fintype (X → Y)] [Nonempty (X → Y)] :
    urfDDSSamplingBehavior (X := X) (Y := Y) =
      urfBehavior (X := X) (Y := Y) := by
  funext i arg
  apply Part.ext
  intro a
  unfold urfDDSSamplingBehavior urfBehavior
  simp [Dist.cond, PFunDDS.output, PFunDDS.functionEvaluator, vector_getLast_toList]

/-- CR18 Example 3.6: the PDS that samples functions uniformly has the URF
behavior. -/
theorem behavior_URF [Fintype (X → Y)] [Nonempty (X → Y)]
    :
    behavior (URF (X := X) (Y := Y)) =
      urfBehavior (X := X) (Y := Y) := by
  rw [behavior_URF_sampling, urfDDSSamplingBehavior_eq_urfBehavior]

/-! #### CR18 Example 3.6, RV-native: the URF as a function-valued random variable

The uniform random function is a *function-valued random variable* `R`: uniformly
sample `f : X → Y` and view it as a DDS. Its output is **memoryless** — `R(α)` is
`f` of the *current* input only — so `behaviorB` reduces to the conditional law of
the uniform function values. -/

section URF
variable [Fintype (X → Y)] [Nonempty (X → Y)]

/-- The uniform distribution over `X → Y` as a probability distribution. -/
noncomputable def uniformP : Dist.ProbDist (X → Y) :=
  ⟨Dist.uniform (X → Y), Dist.uniform_isProbDist⟩

/-- The underlying distribution of the canonical uniform function probability
law is the ordinary uniform distribution on functions. -/
@[simp]
theorem uniformP_val : (uniformP (X := X) (Y := Y)).val = Dist.uniform (X → Y) :=
  rfl

/-- CR18 Example 3.5/3.6: the **uniform random function** `R` as a random
variable. Sample space `X → Y`, ambient experiment `uniformP`; each `f` is viewed
as a DDS via `functionEvaluator`. Its law over DDS is exactly the URF PDS. -/
noncomputable def urfRV : RV (X → Y) X Y := fun f => PFunDDS.functionEvaluator f

/-- The URF as a random variable has the URF PDS as its law (Def 3.15). -/
theorem urfRV_law : (Dist.PMF uniformP (urfRV : RV (X → Y) X Y)).val = URF :=
  rfl

omit [Fintype (X → Y)] [Nonempty (X → Y)] in
/-- The URF output random variable is **memoryless**: on the singleton history
`[x]`, `R([x]) = f x`. -/
theorem urfRV_eval_single (x : X) (f : X → Y) :
    Dist.RV.eval (funView urfRV) [x] f = Part.some (f x) := by
  show (PFunDDS.functionEvaluator f).1 [x] = Part.some (f x)
  apply Part.ext'
  · simp [PFunDDS.functionEvaluator]
  · intro _ _; simp [PFunDDS.functionEvaluator]

/-- CR18 Example 3.6, first output (channel base case): the first output of the
URF `R` is distributed as `Pr_f[f(x) = y]` — the probability that a uniform random
function maps `x` to `y`. This is `p^R_{Y₁|X₁}(y, x)`. -/
theorem behaviorB_urfRV_first (x : X) (y : Y) :
    behaviorB (uniformP : Dist.ProbDist (X → Y)) (urfRV : RV (X → Y) X Y) [x] (Part.some y) []
      = Part.some ((Dist.uniform (X → Y)).mass (fun f => f x = y)) := by
  have hprev : (fun f : X → Y => prevOut urfRV [x] f = []) = fun _ => True := by
    funext f; simp [prevOut_singleton]
  have h1 : (uniformP : Dist.ProbDist (X → Y)).val.mass (fun f => prevOut urfRV [x] f = []) = 1 := by
    rw [hprev]; simpa [Dist.mass, Dist.weight] using uniformP.property.weight_eq
  have hdom : (behaviorB uniformP urfRV [x] (Part.some y) []).Dom := by
    rw [behaviorB_dom, h1]; exact one_ne_zero
  rw [← Part.some_get hdom]
  congr 1
  rw [behaviorB_get _ _ _ _ _ (by rwa [behaviorB_dom] at hdom), h1, div_one]
  apply Dist.mass_congr
  intro f
  rw [urfRV_eval_single, prevOut_singleton]
  simp [Part.some_inj]

omit [Fintype (X → Y)] [Nonempty (X → Y)] in
/-- The URF output random variable is **memoryless** on any nonempty input
history: `R(α) = f(xᵢ)` where `xᵢ = α.getLast` is the current input (the output
depends only on the most recent input). -/
theorem urfRV_eval (α : List X) (hα : α ≠ []) (f : X → Y) :
    Dist.RV.eval (funView urfRV) α f = Part.some (f (α.getLast hα)) := by
  show (PFunDDS.functionEvaluator f).1 α = Part.some (f (α.getLast hα))
  apply Part.ext'
  · simp [PFunDDS.functionEvaluator, hα]
  · intro _ _; simp [PFunDDS.functionEvaluator]

omit [Fintype (X → Y)] [Nonempty (X → Y)] in
/-- **Cornerstone characterization of the URF previous-outputs RV.** Because the URF
is memoryless (`urfRV_eval`), the previous-outputs random variable along `α` is just
`f` evaluated at each proper-prefix input — i.e. `f` mapped over `α.dropLast`:
`prevOut urfRV α f = [some (f x₁), …, some (f xᵢ₋₁)]`. Everything about the URF's
conditioning history reduces to this clean form. -/
theorem prevOut_urfRV_eq (α : List X) (f : X → Y) :
    prevOut (urfRV : RV (X → Y) X Y) α f = α.dropLast.map (fun x => Part.some (f x)) := by
  unfold prevOut
  apply List.ext_getElem
  · simp [List.length_dropLast]
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hjlt : j < α.length - 1 := by
      simpa [List.length_map, List.length_range] using h1
    have hne : α.take (j + 1) ≠ [] := by
      rw [← List.length_pos_iff_ne_nil, List.length_take]; omega
    rw [urfRV_eval (α.take (j + 1)) hne f]
    congr 2
    rw [List.getLast_eq_getElem, List.getElem_take, List.getElem_dropLast]
    congr 1
    rw [List.length_take]; omega

/-- CR18 Example 3.6, general round: the URF behavior is the conditional law of
the **current uniform function value** `f(xᵢ)` — `b(R)` at input history `α` (with
current input `xᵢ = α.getLast`) is `Pr_f[ f(xᵢ) = yᵢ | <previous outputs> ]`. This
is the memoryless reduction of `behaviorB` to the function value at the current
input (Maurer Eq 3.1 in conditional form). -/
theorem behaviorB_urfRV_output (α : List X) (hα : α ≠ []) (yᵢ : Y)
    (yprev : List (Part Y)) :
    behaviorB uniformP (urfRV : RV (X → Y) X Y) α (Part.some yᵢ) yprev
      = Dist.condPMFOf uniformP (fun f => f (α.getLast hα)) (prevOut urfRV α) yᵢ yprev := by
  refine Part.ext' Iff.rfl ?_
  intro _ _
  show _ / _ = _ / _
  congr 1
  apply Dist.mass_congr
  intro f
  rw [urfRV_eval α hα f]
  simp [Part.some_inj]

end URF

end PFunPDS

/-! ## CR18 §3.6: behavior as a first-class object

Per **Definition 3.18**, the behavior is the **sequence of conditional
probabilities** `p_{Yᵢ|XⁱYⁱ⁻¹}`, derived over a **PDS** — *a random variable over
DDS*, `S : Ω → DDS`. The probabilities are taken in the "random experiment of
choosing `S` at random"; that experiment `p` is **ambient and suppressed** in the
notation `b⟦S⟧`, exactly as Maurer suppresses it and as the existing `ℙ⟦·⟧` does. -/

/-- A **conditional probability distribution** `p_{A|B}` of an `A`-valued random
variable given a `B`-valued one — CR18 Def A.5/A.6 and Def 3.18 **footnote 14**: the
*partial* stochastic matrix `A × B → ℝ⁺`, a `PFun` (`→.`; partial: undefined where the
conditioning has probability 0). The two value spaces are **arbitrary** — they may
coincide (`A = B`), and either may itself be a product or a list/tuple. This is the
generic conditional-distribution type; the behaviour below instantiates it with the
current output as `A` and the history `Xⁱ × Yⁱ⁻¹` as `B`. -/
def CondDist (A B : Type*) : Type _ := (A × B) →. ℝ

/-- CR18 **Definition 3.18**: the behavior of a probabilistic `(X,Y)`-system is the
**sequence** `(p^S_{Yᵢ|XⁱYⁱ⁻¹})_{i≥1}` of conditional probability distributions,
indexed by `n = i-1 : ℕ` (so `n = 0` is the first output). The `n`-th element is a
`CondDist Y (Xⁱ × Yⁱ⁻¹)` — the conditional distribution of the current output `Y`
given the input history `Xⁱ` (length `n+1`) and previous outputs `Yⁱ⁻¹` (length `n`),
in the paper's cartesian-product argument order `Y × Xⁱ × Yⁱ⁻¹`. -/
def BehaviorSeq (X Y : Type*) : Type _ :=
  (n : ℕ) → CondDist Y (List.Vector X (n + 1) × List.Vector Y n)

/-- The fn14 **kernel** form of one conditional distribution: `(yᵢ, xⁱ, yⁱ⁻¹) ↦ ℝ⁺`
with histories as plain lists. This is the *engine* — `behaviorOf` reads the masses
of its `CondDist`s from here, and the URF results are proved at this level. -/
abbrev BehaviorKernel (X : Type u) (Y : Type v) : Type (max u v) :=
  List X → Part Y → List (Part Y) → Part ℝ

/-- The kernel behavior of a PDS `S`: `behaviorKernel p S α yᵢ yⁱ⁻¹ =
`Pr[ S(xⁱ)=yᵢ | S(x¹)=y₁, … ]`. Write `b⟦S⟧` to suppress the ambient experiment `p`. -/
noncomputable def behaviorKernel {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) : BehaviorKernel X Y :=
  PFunPDS.behaviorB p S

/-- CR18 **Definition 3.18**, the behavior of a PDS `S` as the first-class object: the
sequence of conditional probability distributions. The `n`-th element, applied to
`(yᵢ, xⁱ, yⁱ⁻¹)` (input history of length `n+1`, previous outputs of length `n`), is
`Pr[ S(xⁱ)=yᵢ | S(x¹)=y₁, … ]`, read off the kernel `behaviorKernel`. -/
noncomputable def behaviorOf {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) : BehaviorSeq X Y :=
  fun _n c => PFunPDS.behaviorB p S c.2.1.toList (Part.some c.1) (c.2.2.toList.map Part.some)

/-- **CR18 Def 3.18 / footnote 14 — partiality** for the first-class behavior: the
`n`-th conditional distribution `p_{Yᵢ|XⁱYⁱ⁻¹}` is *defined* at `(yᵢ, xⁱ, yⁱ⁻¹)`
exactly when the conditioning history `yⁱ⁻¹` has nonzero probability. -/
theorem behaviorOf_dom {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) (n : ℕ)
    (yᵢ : Y) (xs : List.Vector X (n + 1)) (ys : List.Vector Y n) :
    (behaviorOf p S n (yᵢ, xs, ys)).Dom
      ↔ p.val.mass (fun ω => PFunPDS.prevOut S xs.toList ω = ys.toList.map Part.some) ≠ 0 :=
  PFunPDS.behaviorB_dom p S xs.toList (Part.some yᵢ) (ys.toList.map Part.some)

/-- **CR18 Definition 3.19 — coarsening / equivalence by behavior** for the
first-class behavior: two PDS (random variables over DDS), possibly on different
sample spaces, with the **same distribution over DDS** have the **same behavior**.
The behavior forgets everything about `S` except its law — the collapse the whole
indistinguishability theory rests on. -/
theorem behaviorOf_eq_of_law_eq {Ω : Type w} {Ω' : Type z} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (q : Dist.ProbDist Ω')
    (S : PFunPDS.RV Ω X Y) (T : PFunPDS.RV Ω' X Y)
    (hlaw : Dist.PMF p S = Dist.PMF q T) :
    behaviorOf p S = behaviorOf q T := by
  funext n c
  exact congrFun (congrFun (congrFun
    (PFunPDS.behaviorB_eq_of_law_eq p q S T hlaw) c.2.1.toList) (Part.some c.1))
    (c.2.2.toList.map Part.some)

/-- **CR18 Definition 3.19**: two probabilistic `(X,Y)`-systems — PDS, i.e. random
variables over DDS, on possibly different sample spaces — are **equivalent** (Maurer:
`S ≡ T`) iff they have the **same behavior** `b(·)`. The behavior is the complete
observable, so this is the right notion of "indistinguishable as systems". -/
def BehaviorSeqEquiv {Ω : Type w} {Ω' : Type z} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y)
    (q : Dist.ProbDist Ω') (T : PFunPDS.RV Ω' X Y) : Prop :=
  behaviorOf p S = behaviorOf q T

/-- `≡` (Def 3.19) is reflexive. -/
theorem BehaviorSeqEquiv.rfl' {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) : BehaviorSeqEquiv p S p S := Eq.refl _

/-- `≡` (Def 3.19) is symmetric. -/
theorem BehaviorSeqEquiv.symm {Ω : Type w} {Ω' : Type z} {X : Type u} {Y : Type v}
    {p : Dist.ProbDist Ω} {S : PFunPDS.RV Ω X Y}
    {q : Dist.ProbDist Ω'} {T : PFunPDS.RV Ω' X Y}
    (h : BehaviorSeqEquiv p S q T) : BehaviorSeqEquiv q T p S := Eq.symm h

/-- `≡` (Def 3.19) is transitive. -/
theorem BehaviorSeqEquiv.trans {Ω Ω' Ω'' : Type*} {X : Type u} {Y : Type v}
    {p : Dist.ProbDist Ω} {S : PFunPDS.RV Ω X Y}
    {q : Dist.ProbDist Ω'} {T : PFunPDS.RV Ω' X Y}
    {r : Dist.ProbDist Ω''} {U : PFunPDS.RV Ω'' X Y}
    (h₁ : BehaviorSeqEquiv p S q T) (h₂ : BehaviorSeqEquiv q T r U) :
    BehaviorSeqEquiv p S r U := Eq.trans h₁ h₂

/-- **CR18 Def 3.19 ⇐ same law** (the coarsening): two PDS with the same distribution
over DDS are equivalent. The behavior forgets all but the law. -/
theorem BehaviorSeqEquiv.of_law_eq {Ω : Type w} {Ω' : Type z} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (q : Dist.ProbDist Ω')
    (S : PFunPDS.RV Ω X Y) (T : PFunPDS.RV Ω' X Y)
    (hlaw : Dist.PMF p S = Dist.PMF q T) : BehaviorSeqEquiv p S q T :=
  behaviorOf_eq_of_law_eq p q S T hlaw

/-- **CR18 Definition 3.19**: behavioral equivalence is a genuine **equivalence
relation** on the PDS over a fixed sample space / experiment `p` (it is the kernel of
`behaviorOf p`). -/
theorem behaviorSeqEquiv_equivalence {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) :
    Equivalence (fun S T : PFunPDS.RV Ω X Y => BehaviorSeqEquiv p S p T) :=
  ⟨fun _ => Eq.refl _, fun h => Eq.symm h, fun h₁ h₂ => Eq.trans h₁ h₂⟩

/-- The **`Setoid`** of PDS (over a fixed experiment `p`) under behavioral
equivalence. CR18: "a behavior can be understood as the equivalence class of all
probabilistic systems with that behavior" — those classes are `Quotient` of this. -/
def behaviorSetoid {Ω : Type w} {X : Type u} {Y : Type v} (p : Dist.ProbDist Ω) :
    Setoid (PFunPDS.RV Ω X Y) where
  r S T := BehaviorSeqEquiv p S p T
  iseqv := behaviorSeqEquiv_equivalence p

/-- Maurer's `S ≡ T` (CR18 Definition 3.19): behavioral equivalence in the ambient
experiment `p` (suppressed, exactly as `b⟦·⟧` and `ℙ⟦·⟧` suppress it). -/
macro:50 S:term:51 " ≡ᵇ " T:term:51 : term => do
  let p := Lean.mkIdent `p
  `(BehaviorSeqEquiv $p $S $p $T)

/-! ### CR18 §3.6.4 / Definition 3.20 — the cumulative description -/

/-- CR18 **Definition 3.20**: the **cumulative description** of the behavior of a
probabilistic `(X,Y)`-system is the sequence of **joint** distributions of the output
sequence given the input sequence. The `n`-th element is `p^S_{Yⁱ|Xⁱ}` (round
`i = n+1`): a conditional distribution of the *whole output tuple* `yⁱ : Yⁱ` (length
`i`) given the input tuple `xⁱ : Xⁱ` (length `i`) — `CondDist (Yⁱ) (Xⁱ)`. CR18 calls
this "redundant but often easier to work with"; the conditional Def 3.18 behavior is
recovered from it (Eq 3.2). -/
def CumulativeBehaviorSeq (X Y : Type*) : Type _ :=
  (n : ℕ) → CondDist (List.Vector Y (n + 1)) (List.Vector X (n + 1))

/-- CR18 Definition 3.20: the cumulative description of a PDS `S` in experiment `p`.
On `(yⁱ, xⁱ)` it is the joint probability `Pr[(S(x¹),…,S(xⁱ)) = yⁱ]` — the law of the
output-sequence random variable `outSeq S xⁱ` at `yⁱ`. It is **total** (always
defined): unlike Def 3.18, conditioning is on the *deterministic* input sequence
`xⁱ`, not on a random event, so no `⊥`/partiality arises. -/
noncomputable def cumulativeBehaviorOf {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) : CumulativeBehaviorSeq X Y :=
  fun _n c => Part.some (p.val.mass
    (fun ω => PFunPDS.outSeq S c.2.toList ω = c.1.toList.map Part.some))

/-- **Def 3.20 defining equation**: `p^S_{Yⁱ|Xⁱ}(yⁱ, xⁱ) = Pr[(S(x¹),…,S(xⁱ)) = yⁱ]`,
the joint mass of the output-sequence random variable at `yⁱ`. -/
@[simp] theorem cumulativeBehaviorOf_apply {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) (n : ℕ)
    (yi : List.Vector Y (n + 1)) (xi : List.Vector X (n + 1)) :
    cumulativeBehaviorOf p S n (yi, xi)
      = Part.some (p.val.mass
          (fun ω => PFunPDS.outSeq S xi.toList ω = yi.toList.map Part.some)) :=
  rfl

/-- **Def 3.20 is total**: the cumulative description is defined at *every* `(yⁱ, xⁱ)`
— there is no partiality (contrast Def 3.18's `behaviorOf_dom`). -/
theorem cumulativeBehaviorOf_dom {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) (n : ℕ)
    (c : List.Vector Y (n + 1) × List.Vector X (n + 1)) :
    (cumulativeBehaviorOf p S n c).Dom := trivial

/-- Length-`(j+1)` input prefix `xʲ⁺¹` of a fixed input sequence, as a `List.Vector`
matching the behavior layer — so `.toList` is `take` definitionally (unlike the
core-`Vector` `PFunPDS.inputPrefix`). -/
def inputPrefixV {X : Type u} {n : ℕ} (xs : List.Vector X n) (j : Fin n) :
    List.Vector X (j.1 + 1) :=
  ⟨xs.toList.take (j.1 + 1), by
    rw [List.length_take, List.Vector.toList_length]; have := j.2; omega⟩

/-- Length-`j` previous-output prefix `yʲ` of a fixed output sequence, as a `List.Vector`. -/
def outputPrefixV {Y : Type v} {n : ℕ} (ys : List.Vector Y n) (j : Fin n) :
    List.Vector Y j.1 :=
  ⟨ys.toList.take j.1, by
    rw [List.length_take, List.Vector.toList_length]; have := j.2; omega⟩

@[simp] theorem inputPrefixV_toList {X : Type u} {n : ℕ} (xs : List.Vector X n) (j : Fin n) :
    (inputPrefixV xs j).toList = xs.toList.take (j.1 + 1) := rfl

@[simp] theorem outputPrefixV_toList {Y : Type v} {n : ℕ} (ys : List.Vector Y n) (j : Fin n) :
    (outputPrefixV ys j).toList = ys.toList.take j.1 := rfl

/-- **CR18 Equation 3.2 (the chain rule)**: the cumulative description (Def 3.20) is
the **product** of the Def-3.18 conditionals — `p^S_{Yⁱ|Xⁱ} = ∏ⱼ p^S_{Yⱼ|XʲYʲ⁻¹}`. The
joint probability of the output sequence factors as the product of the per-step
conditional probabilities (`hdef`: every factor is defined, i.e. every conditioning
prefix has nonzero probability). This is exactly the probability chain rule
(`mass_biForall_lt_eq_prod`), telescoping the prefix masses. -/
theorem cumulativeBehaviorOf_eq_behaviorOf_prod {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) {i : ℕ}
    (ys : List.Vector Y (i + 1)) (xs : List.Vector X (i + 1))
    (hdef : ∀ j : Fin (i + 1),
      (behaviorOf p S j.1 (ys.get j, inputPrefixV xs j, outputPrefixV ys j)).Dom) :
    (cumulativeBehaviorOf p S i (ys, xs)).get (cumulativeBehaviorOf_dom p S i (ys, xs))
      = ∏ j : Fin (i + 1),
          (behaviorOf p S j.1
            (ys.get j, inputPrefixV xs j, outputPrefixV ys j)).get (hdef j) := by
  classical
  have hxlen : xs.toList.length = i + 1 := by simp
  have hylen : ys.toList.length = i + 1 := by simp
  -- `yv k` is the k-th target output; `A k ω` says "the (k+1)-st output of S is yₖ"
  set yv : ℕ → Y := fun k => ys.toList.getD k (ys.get 0) with hyv0
  have hyv : ∀ (k : ℕ) (hk : k < ys.toList.length), yv k = ys.toList[k] :=
    fun k hk => List.getD_eq_getElem _ _ hk
  set A : ℕ → Ω → Prop := fun k ω =>
    Dist.RV.eval (PFunPDS.funView S) (xs.toList.take (k + 1)) ω = Part.some (yv k) with hAdef
  -- a some-mapped output prefix is the range-map of `yv`
  have hysmap : ∀ m, m ≤ i + 1 →
      (ys.toList.take m).map Part.some = (List.range m).map (fun k => Part.some (yv k)) := by
    intro m hm
    have hlen : ((ys.toList.take m).map Part.some).length
        = ((List.range m).map (fun k => Part.some (yv k))).length := by
      simp only [List.length_map, List.length_take, List.length_range, hylen]; omega
    refine List.ext_getElem hlen fun k h1 _ => ?_
    have hk : k < m := by simp only [List.length_map, List.length_take, hylen] at h1; omega
    rw [List.getElem_map, List.getElem_take, List.getElem_map, List.getElem_range, hyv k (by omega)]
  -- split a `< (m+1)` conjunction into `< m` and the top index
  have hsplit : ∀ (B : ℕ → Prop) m, (∀ k, k < m + 1 → B k) ↔ (∀ k, k < m → B k) ∧ B m := by
    intro B m
    refine ⟨fun h => ⟨fun k hk => h k (by omega), h m (by omega)⟩, fun ⟨h1, h2⟩ k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact h1 k hk'
    · exact h2
  -- (1) the cumulative description is the mass of the full prefix-event conjunction
  have hcum : (cumulativeBehaviorOf p S i (ys, xs)).get (cumulativeBehaviorOf_dom p S i (ys, xs))
      = p.val.mass (fun ω => ∀ k, k < i + 1 → A k ω) := by
    show p.val.mass (fun ω => PFunPDS.outSeq S xs.toList ω = ys.toList.map Part.some) = _
    have htgt : ys.toList.map Part.some
        = (List.range xs.toList.length).map (fun k => Part.some (yv k)) := by
      rw [hxlen]; have h := hysmap (i + 1) le_rfl
      rwa [List.take_of_length_le (le_of_eq hylen)] at h
    refine Dist.mass_congr _ fun ω => ?_
    rw [htgt, PFunPDS.outSeq_eq_map_iff, hxlen]
  -- the conditioning event is the proper prefix conjunction `⋀_{k<j} Aₖ`
  have hQ : ∀ (j : Fin (i + 1)) (ω : Ω),
      (PFunPDS.prevOut S (inputPrefixV xs j).toList ω = (outputPrefixV ys j).toList.map Part.some)
        ↔ (∀ k, k < j.1 → A k ω) := by
    intro j ω
    rw [inputPrefixV_toList, outputPrefixV_toList, hysmap j.1 (by have := j.2; omega),
      PFunPDS.prevOut_take_eq_map_iff S xs.toList
        (show j.1 < xs.toList.length by rw [hxlen]; exact j.2) (fun k => Part.some (yv k)) ω]
  -- the current-output event is exactly `A_{j}`
  have hP : ∀ (j : Fin (i + 1)) (ω : Ω),
      (Dist.RV.eval (PFunPDS.funView S) (inputPrefixV xs j).toList ω = Part.some (ys.get j))
        ↔ A j.1 ω := by
    intro j ω
    have hgj : ys.get j = yv j.1 := by
      have h0 : ys.get j = ys.toList[j.1]'(by omega) := rfl
      rw [h0, hyv j.1 (by omega)]
    rw [inputPrefixV_toList, hgj]
  -- (2) each Def-3.18 factor is the one-step conditional mass `cum_{j+1}/cum_j`
  have hfac : ∀ j : Fin (i + 1),
      (behaviorOf p S j.1 (ys.get j, inputPrefixV xs j, outputPrefixV ys j)).get (hdef j)
        = p.val.mass (fun ω => ∀ k, k < j.1 + 1 → A k ω)
          / p.val.mass (fun ω => ∀ k, k < j.1 → A k ω) := by
    intro j
    show (PFunPDS.behaviorB p S (inputPrefixV xs j).toList (Part.some (ys.get j))
        ((outputPrefixV ys j).toList.map Part.some)).get (hdef j) = _
    rw [PFunPDS.behaviorB_get _ _ _ _ _ (hdef j)]
    congr 1
    · refine Dist.mass_congr _ fun ω => ?_
      rw [hP j ω, hQ j ω, hsplit (fun k => A k ω) j.1]; exact and_comm
    · exact Dist.mass_congr _ fun ω => hQ j ω
  -- (3) every conditioning prefix has nonzero mass (from `hdef`)
  have hpos : ∀ j, j ≤ i → p.val.mass (fun ω => ∀ k, k < j → A k ω) ≠ 0 := fun j hj hz =>
    hdef ⟨j, by omega⟩ ((Dist.mass_congr _ fun ω => hQ ⟨j, by omega⟩ ω).trans hz)
  -- assemble via the NNReal probability chain rule (the telescoping identity)
  rw [hcum, Finset.prod_congr rfl (fun j _ => hfac j),
    Fin.prod_univ_eq_prod_range (fun m => p.val.mass (fun ω => ∀ k, k < m + 1 → A k ω)
      / p.val.mass (fun ω => ∀ k, k < m → A k ω)) (i + 1)]
  exact Dist.mass_biForall_lt_eq_prod p A i hpos

/-- **CR18, the conversion equation just after Eq 3.2** (the *inverse* of Eq 3.2): the
Def-3.18 conditional is recovered from the cumulative description (Def 3.20) as the
ratio of consecutive cumulatives,
`p^S_{Yᵢ|XⁱYⁱ⁻¹}(yᵢ,xⁱ,yⁱ⁻¹) = p^S_{Yⁱ|Xⁱ}(yⁱ,xⁱ) / p^S_{Yⁱ⁻¹|Xⁱ⁻¹}(yⁱ⁻¹,xⁱ⁻¹)`,
whenever the denominator is nonzero (which is exactly the conditional being defined,
`hdef`). Here `yⁱ = yⁱ⁻¹ ⌢ yᵢ` and `xⁱ⁻¹` is `xⁱ` without its last input. This is
why the cumulative description, though redundant, completely determines the
behavior. -/
theorem behaviorOf_eq_cumulative_div {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) {n : ℕ}
    (yi : Y) (xs : List.Vector X (n + 2)) (ys : List.Vector Y (n + 1))
    (hdef : (behaviorOf p S (n + 1) (yi, xs, ys)).Dom) :
    (behaviorOf p S (n + 1) (yi, xs, ys)).get hdef
      = (cumulativeBehaviorOf p S (n + 1) (⟨ys.toList ++ [yi], by simp⟩, xs)).get
            (cumulativeBehaviorOf_dom _ _ _ _)
        / (cumulativeBehaviorOf p S n (ys, ⟨xs.toList.dropLast, by simp⟩)).get
            (cumulativeBehaviorOf_dom _ _ _ _) := by
  have hxl : xs.toList.length = n + 2 := by simp
  have hyl : ys.toList.length = n + 1 := by simp
  have hne : xs.toList ≠ [] := by rw [← List.length_pos_iff_ne_nil]; omega
  have hxsnoc : xs.toList = xs.toList.dropLast ++ [xs.toList.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  -- `outSeq` on the full input is `prevOut` snoc the last output value
  have hsnoc : ∀ ω, PFunPDS.outSeq S xs.toList ω
      = PFunPDS.prevOut S xs.toList ω ++ [Dist.RV.eval (PFunPDS.funView S) xs.toList ω] := by
    intro ω
    rw [PFunPDS.prevOut_eq_outSeq_dropLast]
    conv_lhs => rw [hxsnoc]
    rw [PFunPDS.outSeq_snoc, ← hxsnoc]
  -- `prevOut` on the full input is `outSeq` on the dropped-last input `xⁱ⁻¹`
  have hpe : ∀ ω, PFunPDS.prevOut S xs.toList ω = PFunPDS.outSeq S (xs.toList.dropLast) ω :=
    fun ω => PFunPDS.prevOut_eq_outSeq_dropLast S xs.toList ω
  show (PFunPDS.behaviorB p S xs.toList (Part.some yi) (ys.toList.map Part.some)).get hdef = _
  rw [PFunPDS.behaviorB_get _ _ _ _ _ hdef]
  congr 1
  · -- numerator = mass of the full output sequence = the (n+1)-cumulative
    show p.val.mass _
      = p.val.mass (fun ω => PFunPDS.outSeq S xs.toList ω = (ys.toList ++ [yi]).map Part.some)
    refine Dist.mass_congr _ fun ω => ?_
    rw [hsnoc ω, List.map_append, List.map_cons, List.map_nil]
    have hpl : (PFunPDS.prevOut S xs.toList ω).length = (ys.toList.map Part.some).length := by
      simp only [PFunPDS.prevOut, List.length_map, List.length_range, hxl, hyl]; omega
    constructor
    · rintro ⟨h1, h2⟩; rw [h2, h1]
    · intro h
      obtain ⟨ha, hb⟩ := List.append_inj h hpl
      exact ⟨by simpa using hb, ha⟩
  · -- denominator = mass on the prefix input = the `n`-cumulative
    show p.val.mass _
      = p.val.mass (fun ω => PFunPDS.outSeq S (xs.toList.dropLast) ω = ys.toList.map Part.some)
    exact Dist.mass_congr _ fun ω => by rw [hpe ω]

/-- Maurer-style behavior notation: `b⟦S⟧` is the behavior of the PDS `S` in the
ambient experiment `p` (suppressed, as in `ℙ⟦·⟧`). -/
macro "b⟦" S:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(behaviorKernel $p $S)

/-! ### `b⟦S⟧` realizes CR18 Definition 3.18 (no visible `p`) -/

section Faithfulness
variable {Ω : Type w} {X : Type u} {Y : Type v}

/-- **Def 3.18 defining equation** for `b⟦S⟧`: the conditional probability of the
current output given the previous outputs, in the experiment of choosing `S`. -/
theorem behaviorKernel_get (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y)
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y))
    (h : p.val.mass (fun ω => PFunPDS.prevOut S α ω = yprev) ≠ 0) :
    (b⟦S⟧ α yᵢ yprev).get h
      = p.val.mass (fun ω =>
          Dist.RV.eval (PFunPDS.funView S) α ω = yᵢ ∧ PFunPDS.prevOut S α ω = yprev)
        / p.val.mass (fun ω => PFunPDS.prevOut S α ω = yprev) :=
  PFunPDS.behaviorB_get p S α yᵢ yprev h

/-- **Def 3.18 partiality (fn14)** for `b⟦S⟧`: defined iff the conditioning history
has nonzero probability. -/
theorem behaviorKernel_dom (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y)
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y)) :
    (b⟦S⟧ α yᵢ yprev).Dom ↔ p.val.mass (fun ω => PFunPDS.prevOut S α ω = yprev) ≠ 0 :=
  PFunPDS.behaviorB_dom p S α yᵢ yprev

/-- **The coarsening** (the point of comparing an RV to its behavior): two PDS —
random variables over DDS, possibly on different sample spaces — with the **same
distribution over DDS** have the **same behavior** `b⟦·⟧`. The behavior forgets
everything about `S` except its law. -/
theorem behaviorKernel_eq_of_law_eq {Ω' : Type z}
    (p : Dist.ProbDist Ω) (q : Dist.ProbDist Ω')
    (S : PFunPDS.RV Ω X Y) (T : PFunPDS.RV Ω' X Y)
    (hlaw : Dist.PMF p S = Dist.PMF q T) :
    behaviorKernel p S = behaviorKernel q T :=
  PFunPDS.behaviorB_eq_of_law_eq p q S T hlaw

end Faithfulness

/-! ### CR18 Definition 3.21 — the behavior of an environment

An environment is the **dual** of a system: a `(Y,X)`-environment `E` observes the
output history and produces the next query, i.e. a random variable `RV Ω Y X`. CR18
defines its behavior "analogously to Definition 3.18" — it is the system-behavior
construction with inputs and outputs swapped. -/

/-- CR18 **Definition 3.21**: the behavior of a `(Y,X)`-environment `E` is its sequence
of conditional query distributions `p^E_{Xᵢ|Yⁱ⁻¹Xⁱ⁻¹}` — the dual of a system's behavior
(Def 3.18). Write `bₑ⟦E⟧` to suppress the ambient experiment `p`. -/
noncomputable def envBehaviorKernel {Ω : Type w} {X : Type u} {Y : Type v}
    (p : Dist.ProbDist Ω) (E : PFunPDS.RV Ω Y X) : BehaviorKernel Y X :=
  behaviorKernel p E

/-- Environment-behavior notation `bₑ⟦E⟧` (the dual of `b⟦S⟧`). -/
macro "bₑ⟦" E:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(envBehaviorKernel $p $E)

section EnvFaithfulness
variable {Ω : Type w} {X : Type u} {Y : Type v}

/-- **Def 3.21 defining equation** for `bₑ⟦E⟧`: the conditional probability of the
current query given the previous queries, in the experiment of choosing `E`. -/
theorem envBehaviorKernel_get (p : Dist.ProbDist Ω) (E : PFunPDS.RV Ω Y X)
    (α : List Y) (xᵢ : Part X) (xprev : List (Part X))
    (h : p.val.mass (fun ω => PFunPDS.prevOut E α ω = xprev) ≠ 0) :
    (bₑ⟦E⟧ α xᵢ xprev).get h
      = p.val.mass (fun ω =>
          Dist.RV.eval (PFunPDS.funView E) α ω = xᵢ ∧ PFunPDS.prevOut E α ω = xprev)
        / p.val.mass (fun ω => PFunPDS.prevOut E α ω = xprev) :=
  PFunPDS.behaviorB_get p E α xᵢ xprev h

/-- **Def 3.21 partiality** for `bₑ⟦E⟧`: defined iff the conditioning history has nonzero
probability. -/
theorem envBehaviorKernel_dom (p : Dist.ProbDist Ω) (E : PFunPDS.RV Ω Y X)
    (α : List Y) (xᵢ : Part X) (xprev : List (Part X)) :
    (bₑ⟦E⟧ α xᵢ xprev).Dom ↔ p.val.mass (fun ω => PFunPDS.prevOut E α ω = xprev) ≠ 0 :=
  PFunPDS.behaviorB_dom p E α xᵢ xprev

end EnvFaithfulness

/-! ### The behavior of the URF random variable

The URF `urfRV` is a random variable over DDS on the sample space `X → Y` (all
functions, uniform). Its **behavior** `b⟦urfRV⟧` — the observable object — is far
simpler than the RV: the first output is uniform, and the i-th output is `f(xᵢ)`. -/

/-- CR18 Example 3.6, the URF behavior, first output: `b⟦R⟧` at `[x]` is the
uniform law `Pr_f[f(x)=y]`. -/
theorem behaviorKernel_urf_first {X : Type u} {Y : Type v}
    [Fintype (X → Y)] [Nonempty (X → Y)] (x : X) (y : Y) :
    behaviorKernel PFunPDS.uniformP PFunPDS.urfRV [x] (Part.some y) []
      = Part.some ((Dist.uniform (X → Y)).mass (fun f => f x = y)) :=
  PFunPDS.behaviorB_urfRV_first x y

open Classical in
/-- CR18 **Example 3.6 / Eq 3.1**: the behavior of an `(X,Y)`-URF, as a *standalone*
`Behavior` — Maurer's explicit closed form, with the three cases stated literally.
`pairs = (xⱼ, yⱼ)_{j<i}` are the previous input/output pairs (`α.dropLast` with
`yⁱ⁻¹`), `xᵢ = α.getLast` is the current input:

* **`1`**  if `xᵢ = xⱼ` for some `j < i` **and** `yᵢ = yⱼ`;
* **`0`**  if `xᵢ = xⱼ` for some `j < i` **and** `yᵢ ≠ yⱼ`;
* **`1/|Y|`** if `xᵢ ≠ xⱼ` for all `j < i`;
* **undefined** (`none`) if `xⱼ = xₖ` but `yⱼ ≠ yₖ` for some `j < k < i`
  (inconsistent history).

The first guard disjunct (`length`/`Dom`) records that `yⁱ⁻¹` must be an actual
output history in `Yⁱ⁻¹` — Maurer types `yⁱ⁻¹ ∈ Yⁱ⁻¹` so this is automatic for him;
in the total `List (Part Y)` encoding it is the explicit "outside the domain"
condition. The last disjunct is Maurer's literal inconsistency case. -/
noncomputable def urfBehaviorK {X : Type u} {Y : Type v} [Fintype Y] : BehaviorKernel X Y :=
  fun α yᵢ yprev =>
    let pairs := α.dropLast.zip yprev
    if yprev.length ≠ α.dropLast.length ∨ (∃ y ∈ yprev, ¬ y.Dom)
        ∨ (∃ p ∈ pairs, ∃ q ∈ pairs, p.1 = q.1 ∧ p.2 ≠ q.2) then
      Part.none                                                   -- xⱼ = xₖ ∧ yⱼ ≠ yₖ (or yⁱ⁻¹ ∉ Yⁱ⁻¹) : undefined
    else match α.getLast? with
      | none => Part.none
      | some xᵢ =>
        if ∃ p ∈ pairs, p.1 = xᵢ ∧ p.2 = yᵢ then Part.some 1      -- xᵢ = xⱼ ∧ yᵢ = yⱼ
        else if ∃ p ∈ pairs, p.1 = xᵢ ∧ p.2 ≠ yᵢ then Part.some 0  -- xᵢ = xⱼ ∧ yᵢ ≠ yⱼ
        else if yᵢ.Dom then Part.some (Fintype.card Y : ℝ)⁻¹  -- xᵢ ≠ xⱼ for all j : 1/|Y|
        else Part.some 0

/-- Uniform-function counting: a uniformly random `f : X → Y` has `f x` uniform —
`Pr_f[f(x) = y] = 1/|Y|`. (Pushforward of `uniform (X → Y)` along evaluation at `x`
is `uniform Y`, via `Equiv.piSplitAt`.) -/
theorem uniform_mass_eval {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (x : X) (y : Y) :
    (Dist.uniform (X → Y)).mass (fun f => f x = y) = (Fintype.card Y : ℝ)⁻¹ := by
  have hpush : Dist.fTransform (fun f : X → Y => f x) (Dist.uniform (X → Y)) = Dist.uniform Y := by
    have hcomp : (fun f : X → Y => f x)
        = Prod.fst ∘ (Equiv.piSplitAt x (fun _ : X => Y)) := by
      funext f; simp [Equiv.piSplitAt_apply]
    rw [hcomp, ← Dist.fTransform_comp, Dist.fTransform_equiv_uniform, Dist.fTransform_fst_uniform]
  rw [← Dist.fTransform_apply_eq_mass, hpush, Dist.uniform_apply, one_div]

/-- **Evaluation independence for uniform function spaces**: for a uniformly random
`f : X → Y`, the value `f x` is independent of any function `H` of the *other*
coordinates (`f` restricted to `j ≠ x`). This is the key independence fact behind the
URF behaving memorylessly on a fresh input: conditioning on the history (outputs at
inputs `≠ x`) leaves `f x` uniform. Proof splits `X → Y ≃ Y × ({j // j ≠ x} → Y)` via
`Equiv.piSplitAt` and factors the product mass. The higher-order pushforward step is
discharged by *explicitly instantiating* the predicate metavariable in `transfer`
(`rw` cannot infer `?R` by higher-order unification, and simp cannot pattern-match it
either since `ab.1`/`ab.2` are projections, not bound variables — see web/Mathlib note
on this `rw` limitation). -/
theorem indep_eval {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (x : X) (H : ({j : X // j ≠ x} → Y) → Z) :
    Dist.IndepRV (⟨Dist.uniform (X → Y), Dist.uniform_isProbDist⟩ : Dist.ProbDist (X → Y))
      (fun f => f x) (fun f => H (fun j => f j.1)) := by
  intro a c
  have transfer : ∀ (R : (Y × ({j : X // j ≠ x} → Y)) → Prop),
      (Dist.uniform (X → Y)).mass (fun f => R (Equiv.piSplitAt x (fun _ => Y) f))
        = (Dist.prod (Dist.uniform Y) (Dist.uniform ({j : X // j ≠ x} → Y))).mass R := fun R => by
    rw [← Dist.mass_fTransform, Dist.fTransform_equiv_uniform, ← Dist.prod_uniform]
  have h1 : ∀ f : X → Y, (Equiv.piSplitAt x (fun _ => Y) f).1 = f x := fun f => by
    simp [Equiv.piSplitAt_apply]
  have h2 : ∀ f : X → Y, (Equiv.piSplitAt x (fun _ => Y) f).2 = fun j => f j.1 := fun f => by
    simp [Equiv.piSplitAt_apply]
  show (Dist.uniform (X → Y)).mass (fun f => f x = a ∧ H (fun j => f j.1) = c)
    = (Dist.uniform (X → Y)).mass (fun f => f x = a)
      * (Dist.uniform (X → Y)).mass (fun f => H (fun j => f j.1) = c)
  rw [show (fun f : X → Y => f x = a ∧ H (fun j => f j.1) = c)
        = (fun f => (fun yg : Y × _ => yg.1 = a ∧ H yg.2 = c) (Equiv.piSplitAt x (fun _ => Y) f)) from
      by funext f; simp only [h1, h2],
     show (fun f : X → Y => f x = a)
        = (fun f => (fun yg : Y × _ => yg.1 = a) (Equiv.piSplitAt x (fun _ => Y) f)) from
      by funext f; simp only [h1],
     show (fun f : X → Y => H (fun j => f j.1) = c)
        = (fun f => (fun yg : Y × _ => H yg.2 = c) (Equiv.piSplitAt x (fun _ => Y) f)) from
      by funext f; simp only [h2],
     transfer (fun yg => yg.1 = a ∧ H yg.2 = c), transfer (fun yg => yg.1 = a),
     transfer (fun yg => H yg.2 = c),
     Dist.mass_prod_and (Dist.uniform Y) (Dist.uniform _) (fun y => y = a) (fun g => H g = c),
     Dist.mass_prod_fst (Dist.uniform Y) (Dist.uniform _) (fun y => y = a),
     Dist.mass_prod_snd (Dist.uniform Y) (Dist.uniform _) (fun g => H g = c)]
  simp [Dist.weight_uniform]

/-- CR18 Example 3.6, **first output realizes Eq 3.1 (fresh case)**: the behavior of
the URF random variable at `[x]` is `1/|Y|` — exactly `urfBehaviorK [x] (some y) []`.
The rich RV (a uniform random function on `X → Y`) collapses to the trivial uniform
conditional. -/
theorem behaviorKernel_urf_eq_first {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (x : X) (y : Y) :
    behaviorKernel PFunPDS.uniformP PFunPDS.urfRV [x] (Part.some y) []
      = urfBehaviorK [x] (Part.some y) [] := by
  have hrhs : urfBehaviorK [x] (Part.some y) [] = Part.some (Fintype.card Y : ℝ)⁻¹ := by
    simp [urfBehaviorK]
  rw [behaviorKernel_urf_first, uniform_mass_eval, hrhs]

/-- CR18 **Example 3.6 / Eq 3.1, the FRESH case** (the heart of "a new input gets a
uniform output"): when the current input `xᵢ = α.getLast` does **not** occur among the
previous inputs `α.dropLast`, and the conditioning history `yprev` is *realizable*
(some function produces it), the URF behavior at `α` is exactly `1/|Y|` — independent
of `yprev`. Proof: the URF output `f(xᵢ)` is statistically independent (CR18 Def A.6)
of the previous-outputs random variable, which reads `f` only at inputs `≠ xᵢ`
(`prevOut_urfRV_eq` + `indep_eval`); conditioning therefore collapses to the marginal
`Pr_f[f(xᵢ)=y] = 1/|Y|` (`condPMFOf_get_of_indep` + `uniform_mass_eval`). -/
theorem behaviorKernel_urf_fresh {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (α : List X) (hα : α ≠ []) (y : Y) (yprev : List (Part Y))
    (hxi : α.getLast hα ∉ α.dropLast)
    (hreal : ∃ g : X → Y, α.dropLast.map (fun x => Part.some (g x)) = yprev) :
    behaviorKernel PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α (Part.some y) yprev
      = Part.some ((Fintype.card Y : ℝ)⁻¹) := by
  set xᵢ := α.getLast hα with hxidef
  -- `H` recovers the previous outputs from `f` restricted to the inputs `≠ xᵢ`.
  set H : ({j : X // j ≠ xᵢ} → Y) → List (Part Y) :=
    fun r => α.dropLast.map (fun x => if h : x ≠ xᵢ then Part.some (r ⟨x, h⟩) else Part.none)
    with hH
  have hPrev : (PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α)
      = fun f => H (fun j => f j.1) := by
    funext f
    rw [PFunPDS.prevOut_urfRV_eq]
    apply List.map_congr_left
    intro x hx
    have hne : x ≠ xᵢ := fun h => hxi (h ▸ hx)
    simp [hne]
  -- The conditioning history has nonzero probability: it is realizable.
  have hb : PFunPDS.uniformP.val.mass
      (fun f => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) ≠ 0 := by
    have he : (fun f : X → Y => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
        = fun f => α.dropLast.map (fun x => Part.some (f x)) = yprev := by
      funext f; rw [PFunPDS.prevOut_urfRV_eq]
    rw [he]; exact (Dist.uniform_mass_ne_zero_iff _).mpr hreal
  -- `f(xᵢ)` is independent of the history (CR18 Def A.6).
  have hindep : Dist.IndepRV PFunPDS.uniformP (fun f => f xᵢ)
      (PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α) := by
    rw [hPrev]; exact indep_eval xᵢ H
  -- Conditioning collapses to the marginal `1/|Y|`.
  have hval : (Dist.condPMFOf PFunPDS.uniformP (fun f => f xᵢ)
      (PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α) y yprev).get hb
      = (Fintype.card Y : ℝ)⁻¹ := by
    rw [Dist.condPMFOf_get_of_indep PFunPDS.uniformP _ _ hindep y yprev hb]
    exact uniform_mass_eval xᵢ y
  show PFunPDS.behaviorB PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)
    α (Part.some y) yprev = _
  rw [PFunPDS.behaviorB_urfRV_output α hα y yprev]
  exact Part.eq_some_iff.mpr (hval ▸ Part.get_mem hb)

/-- CR18 **Example 3.6 / Eq 3.1, the REPEAT case** (a repeated input is
deterministic): when the current input `xᵢ = α.getLast` **does** occur among the
previous inputs and the realizable history assigns it `g(xᵢ)`, the URF behavior is
`1` if `y = g(xᵢ)` and `0` otherwise — the output is forced by the history. Proof:
on the conditioning set `f` is pinned `f(xᵢ) = g(xᵢ)` (the history records `f` at
`xᵢ`), so the numerator equals the denominator when `y = g(xᵢ)` and is `0` otherwise. -/
theorem behaviorKernel_urf_repeat {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (α : List X) (hα : α ≠ []) (y : Y) (g : X → Y)
    (hxi : α.getLast hα ∈ α.dropLast) :
    behaviorKernel PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α (Part.some y)
        (α.dropLast.map (fun x => Part.some (g x)))
      = Part.some (if y = g (α.getLast hα) then 1 else 0) := by
  set xᵢ := α.getLast hα with hxidef
  set yprev := α.dropLast.map (fun x => Part.some (g x)) with hyprev
  -- on the conditioning set, `f(xᵢ)` is pinned to `g(xᵢ)`: the history records it.
  have hpin : ∀ f : X → Y,
      PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev → f xᵢ = g xᵢ := by
    intro f hf
    rw [PFunPDS.prevOut_urfRV_eq, hyprev] at hf
    rw [List.mem_iff_getElem] at hxi
    obtain ⟨k, hk, hkeq⟩ := hxi
    have hpt : (α.dropLast.map (fun x => Part.some (f x)))[k]?
        = (α.dropLast.map (fun x => Part.some (g x)))[k]? := by rw [hf]
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hk, hkeq] at hpt
    simp only [Option.map_some, Option.some_inj, Part.some_inj] at hpt
    exact hpt
  have hb : PFunPDS.uniformP.val.mass
      (fun f => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) ≠ 0 := by
    have he : (fun f : X → Y => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
        = fun f => α.dropLast.map (fun x => Part.some (f x)) = yprev := by
      funext f; rw [PFunPDS.prevOut_urfRV_eq]
    rw [he]; exact (Dist.uniform_mass_ne_zero_iff _).mpr ⟨g, rfl⟩
  have hval : (Dist.condPMFOf PFunPDS.uniformP (fun f => f xᵢ)
      (PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α) y yprev).get hb
      = (if y = g xᵢ then 1 else 0) := by
    rw [Dist.condPMFOf_apply]
    by_cases hy : y = g xᵢ
    · rw [if_pos hy]
      have hnum : PFunPDS.uniformP.val.mass
            (fun f => f xᵢ = y ∧ PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
          = PFunPDS.uniformP.val.mass
            (fun f => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) := by
        apply Dist.mass_congr; intro f
        exact ⟨fun h => h.2, fun h => ⟨(hpin f h).trans hy.symm, h⟩⟩
      rw [hnum, div_self hb]
    · rw [if_neg hy]
      have hnum : PFunPDS.uniformP.val.mass
          (fun f => f xᵢ = y ∧ PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
          = 0 := by
        have hF : (fun f : X → Y =>
            f xᵢ = y ∧ PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
            = fun _ => False := by
          funext f
          simp only [eq_iff_iff, iff_false]
          rintro ⟨hfy, hprev⟩
          exact hy (hfy ▸ hpin f hprev)
        rw [hF]; simp [Dist.mass_eq_sum]
      rw [hnum, zero_div]
  show PFunPDS.behaviorB PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)
    α (Part.some y) yprev = _
  rw [PFunPDS.behaviorB_urfRV_output α hα y yprev]
  exact Part.eq_some_iff.mpr (hval ▸ Part.get_mem hb)

/-- CR18 Def 3.18 partiality (fn14) for the URF: an **unrealizable** history (no
function `g` produces it) has probability `0`, so the behavior is undefined. -/
theorem behaviorKernel_urf_unrealizable {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (α : List X) (yᵢ : Part Y) (yprev : List (Part Y))
    (h : ¬ ∃ g : X → Y, α.dropLast.map (fun x => Part.some (g x)) = yprev) :
    behaviorKernel PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α yᵢ yprev = Part.none := by
  rw [Part.eq_none_iff']
  intro hdom
  rw [behaviorKernel_dom] at hdom
  apply h
  have he : (fun f : X → Y => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
      = fun f => α.dropLast.map (fun x => Part.some (f x)) = yprev := by
    funext f; rw [PFunPDS.prevOut_urfRV_eq]
  rw [he] at hdom
  exact (Dist.uniform_mass_ne_zero_iff _).mp hdom

/-- CR18 Eq 3.1, the **`yᵢ = ⊥` (no output) case**: on a nonempty history the URF
output random variable always has a value, so the probability that it equals "no
output" is `0`. (Realizable history.) -/
theorem behaviorKernel_urf_none_output {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (α : List X) (hα : α ≠ []) (g : X → Y) :
    behaviorKernel PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α Part.none
        (α.dropLast.map (fun x => Part.some (g x))) = Part.some 0 := by
  set yprev := α.dropLast.map (fun x => Part.some (g x)) with hyprev
  have hb : PFunPDS.uniformP.val.mass
      (fun f => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) ≠ 0 := by
    have he : (fun f : X → Y => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev)
        = fun f => α.dropLast.map (fun x => Part.some (f x)) = yprev := by
      funext f; rw [PFunPDS.prevOut_urfRV_eq]
    rw [he]; exact (Dist.uniform_mass_ne_zero_iff _).mpr ⟨g, rfl⟩
  have hnum : PFunPDS.uniformP.val.mass
      (fun f => Dist.RV.eval (PFunPDS.funView (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)) α f = Part.none
        ∧ PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) = 0 := by
    have hF : (fun f : X → Y =>
        Dist.RV.eval (PFunPDS.funView (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)) α f = Part.none
        ∧ PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α f = yprev) = fun _ => False := by
      funext f; rw [PFunPDS.urfRV_eval α hα f]; simp
    rw [hF]; simp [Dist.mass_eq_sum]
  have hval : (PFunPDS.behaviorB PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)
      α Part.none yprev).get hb = 0 := by
    show (Dist.condPMFOf PFunPDS.uniformP (Dist.RV.eval (PFunPDS.funView (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y)) α)
      (PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α) Part.none yprev).get hb = 0
    rw [Dist.condPMFOf_apply, hnum, zero_div]
  show PFunPDS.behaviorB PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α Part.none yprev = _
  exact Part.eq_some_iff.mpr (hval ▸ Part.get_mem hb)

/-- `l.zip (l.map f) = l.map (x ↦ (x, f x))` — pairing a list with its image. -/
theorem zip_map_self {A Z : Type*} (l : List A) (f : A → Z) :
    l.zip (l.map f) = l.map (fun x => (x, f x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.zip_cons_cons, ih]

/-- **Realizability from consistency** (the bridge for CR18 Def 3.18's domain): a
history `yprev` of the right length, all defined, and *consistent* (equal inputs get
equal outputs, the negation of Eq 3.1's inconsistency guard) is realized by some
function `g`. The witness reads off `yprev` at the first occurrence of each input. -/
theorem realizable_of_consistent {X : Type u} {Y : Type v} [DecidableEq X] [Nonempty Y]
    (xs : List X) (yprev : List (Part Y))
    (hlen : yprev.length = xs.length)
    (hdom : ∀ y ∈ yprev, y.Dom)
    (hcons : ∀ p ∈ xs.zip yprev, ∀ q ∈ xs.zip yprev, p.1 = q.1 → p.2 = q.2) :
    ∃ g : X → Y, xs.map (fun x => Part.some (g x)) = yprev := by
  have hmemdom : ∀ x (hx : x ∈ xs),
      (yprev[xs.idxOf x]'(by rw [hlen]; exact List.idxOf_lt_length_of_mem hx)).Dom :=
    fun x hx => hdom _ (List.getElem_mem _)
  refine ⟨fun x => if hx : x ∈ xs then
      (yprev[xs.idxOf x]'(by rw [hlen]; exact List.idxOf_lt_length_of_mem hx)).get (hmemdom x hx)
    else Classical.arbitrary Y, ?_⟩
  apply List.ext_getElem
  · rw [List.length_map, hlen]
  · intro k hk1 hk2
    rw [List.length_map] at hk1
    have hmemk : xs[k] ∈ xs := List.getElem_mem _
    rw [List.getElem_map]
    dsimp only
    rw [dif_pos hmemk]
    have hjlt : xs.idxOf xs[k] < xs.length := List.idxOf_lt_length_of_mem hmemk
    have hjk : xs[xs.idxOf xs[k]] = xs[k] := List.getElem_idxOf hjlt
    have hpmem : (xs[xs.idxOf xs[k]], yprev[xs.idxOf xs[k]]'(by rw [hlen]; exact hjlt))
        ∈ xs.zip yprev := by
      rw [List.mem_iff_getElem]
      exact ⟨xs.idxOf xs[k], by rw [List.length_zip, hlen]; omega, by simp [List.getElem_zip]⟩
    have hqmem : (xs[k], yprev[k]'(by rw [hlen]; exact hk1)) ∈ xs.zip yprev := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by rw [List.length_zip, hlen]; omega, by simp [List.getElem_zip]⟩
    have hval := hcons _ hpmem _ hqmem hjk
    rw [Part.some_get]
    exact hval

open Classical in
/-- CR18 **Example 3.6 / Eq 3.1, the full equality**: the behavior of the URF random
variable `b⟦R⟧` *is* the closed-form `urfBehaviorK`. Glues the channel/fresh/repeat/
no-output value cases on realizable histories with the partiality (`none`) on
unrealizable ones — the latter matched to `urfBehaviorK`'s guard via
`realizable_of_consistent`. This is "the URF realizes Eq 3.1", as a function. -/
theorem behaviorKernel_urf_eq {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (α : List X) (hα : α ≠ []) :
    behaviorKernel PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) α = urfBehaviorK α := by
  funext yᵢ yprev
  by_cases hreal : ∃ g : X → Y, α.dropLast.map (fun x => Part.some (g x)) = yprev
  · obtain ⟨g, rfl⟩ := hreal
    have hpairs : α.dropLast.zip (α.dropLast.map (fun x => Part.some (g x)))
        = α.dropLast.map (fun x => (x, Part.some (g x))) := zip_map_self _ _
    have hP : ∀ (z : Part Y),
        (∃ p ∈ α.dropLast.map (fun x => (x, Part.some (g x))), p.1 = α.getLast hα ∧ p.2 = z)
          ↔ (α.getLast hα ∈ α.dropLast ∧ Part.some (g (α.getLast hα)) = z) := by
      intro z; simp only [List.mem_map]
      constructor
      · rintro ⟨p, ⟨x, hx, rfl⟩, h1, h2⟩; exact ⟨h1 ▸ hx, h1 ▸ h2⟩
      · rintro ⟨hmem, h2⟩; exact ⟨_, ⟨_, hmem, rfl⟩, rfl, h2⟩
    have hPne : ∀ (z : Part Y),
        (∃ p ∈ α.dropLast.map (fun x => (x, Part.some (g x))), p.1 = α.getLast hα ∧ p.2 ≠ z)
          ↔ (α.getLast hα ∈ α.dropLast ∧ Part.some (g (α.getLast hα)) ≠ z) := by
      intro z; simp only [List.mem_map]
      constructor
      · rintro ⟨p, ⟨x, hx, rfl⟩, h1, h2⟩; exact ⟨h1 ▸ hx, h1 ▸ h2⟩
      · rintro ⟨hmem, h2⟩; exact ⟨_, ⟨_, hmem, rfl⟩, rfl, h2⟩
    have hguard : ¬ ((α.dropLast.map (fun x => Part.some (g x))).length ≠ α.dropLast.length
         ∨ (∃ y ∈ α.dropLast.map (fun x => Part.some (g x)), ¬ y.Dom)
         ∨ (∃ p ∈ α.dropLast.zip (α.dropLast.map (fun x => Part.some (g x))),
              ∃ q ∈ α.dropLast.zip (α.dropLast.map (fun x => Part.some (g x))),
                p.1 = q.1 ∧ p.2 ≠ q.2)) := by
      rw [hpairs]; push Not
      refine ⟨by simp, ?_, ?_⟩
      · intro y hy; simp only [List.mem_map] at hy; obtain ⟨x, _, rfl⟩ := hy; trivial
      · intro p hp q hq h1
        simp only [List.mem_map] at hp hq
        obtain ⟨x, _, rfl⟩ := hp; obtain ⟨x', _, rfl⟩ := hq
        simp only at h1; subst h1; rfl
    simp only [urfBehaviorK, if_neg hguard, List.getLast?_eq_some_getLast hα]
    rw [hpairs]
    simp only [hP, hPne]
    by_cases hyd : yᵢ.Dom
    · obtain ⟨y, rfl⟩ : ∃ y, yᵢ = Part.some y := ⟨yᵢ.get hyd, (Part.some_get hyd).symm⟩
      have key : (Part.some (g (α.getLast hα)) = Part.some y) ↔ y = g (α.getLast hα) := by
        rw [Part.some_inj]; exact eq_comm
      by_cases hmem : α.getLast hα ∈ α.dropLast
      · rw [behaviorKernel_urf_repeat α hα y g hmem]
        by_cases hy : y = g (α.getLast hα) <;> simp [hmem, hy, key, ne_eq]
      · rw [behaviorKernel_urf_fresh α hα y _ hmem ⟨g, rfl⟩]
        simp [hmem, Part.some_dom]
    · obtain rfl : yᵢ = Part.none := Part.eq_none_iff'.mpr hyd
      rw [behaviorKernel_urf_none_output α hα g]
      by_cases hmem : α.getLast hα ∈ α.dropLast <;>
        simp [hmem, Part.not_none_dom]
  · rw [behaviorKernel_urf_unrealizable α yᵢ yprev hreal]
    have hg : (yprev.length ≠ α.dropLast.length ∨ (∃ y ∈ yprev, ¬ y.Dom)
         ∨ (∃ p ∈ α.dropLast.zip yprev, ∃ q ∈ α.dropLast.zip yprev, p.1 = q.1 ∧ p.2 ≠ q.2)) := by
      by_contra hg
      push Not at hg
      obtain ⟨hlen, hdom, hcons⟩ := hg
      exact hreal (realizable_of_consistent α.dropLast yprev hlen hdom hcons)
    simp only [urfBehaviorK, if_pos hg]

/-- CR18 **Example 3.6 / Eq 3.1** as a first-class `Behavior` (the sequence of
conditional probability distributions): the `(X,Y)`-URF behavior. The `n`-th element,
on `(yᵢ, xⁱ, yⁱ⁻¹)`, is the literal Eq 3.1 closed form (`1` on a matching repeat, `0`
on a clashing repeat, `1/|Y|` on a fresh input, undefined on an inconsistent history)
— carried by the kernel `urfBehaviorK`. -/
noncomputable def urfBehaviorSeq {X : Type u} {Y : Type v} [Fintype Y] : BehaviorSeq X Y :=
  fun _n c => urfBehaviorK c.2.1.toList (Part.some c.1) (c.2.2.toList.map Part.some)

/-- CR18 **Example 3.6 / Eq 3.1, the full equality at the `Behavior` level**: the
behavior of the URF random variable `b(R)` — *the sequence of conditional probability
distributions* (Def 3.18) — **is** the closed-form `urfBehavior`. Reduces, at each
round `n` and argument `(yᵢ, xⁱ, yⁱ⁻¹)`, to the proven kernel equality
`behaviorKernel_urf_eq` (the input tuple `xⁱ` has length `n+1 ≠ 0`, so the history is
nonempty). -/
theorem behaviorOf_urf_eq {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    behaviorOf PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) = urfBehaviorSeq := by
  funext n c
  obtain ⟨yᵢ, xs, ys⟩ := c
  have hα : xs.toList ≠ [] := by
    have hlen : xs.toList.length = n + 1 := xs.2
    intro h; rw [h, List.length_nil] at hlen; omega
  show PFunPDS.behaviorB PFunPDS.uniformP PFunPDS.urfRV xs.toList (Part.some yᵢ)
      (ys.toList.map Part.some)
    = urfBehaviorK xs.toList (Part.some yᵢ) (ys.toList.map Part.some)
  exact congrFun (congrFun (behaviorKernel_urf_eq xs.toList hα) (Part.some yᵢ))
    (ys.toList.map Part.some)

/-- **CR18 Def 3.18 / footnote 14 — normalization** for the URF behavior: at every
round `n` and **realizable** history `(xⁱ, yⁱ⁻¹)` (one with nonzero probability), the
conditional probabilities sum to 1 over the next output `yᵢ : Y` — i.e. each slice is
a genuine probability distribution. Proof: `behaviorB_urfRV_output` rewrites the URF
conditional as the conditional of the **Y-valued** RV `f ↦ f(xᵢ)` (the URF is total,
so no `⊥` mass), whose slice is a `ProbDist` over `Y` of weight 1
(`condPMFOf_isProbDist`); the weight is exactly the sum over `yᵢ`. -/
theorem behaviorOf_urf_normalized {X : Type u} {Y : Type v}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (n : ℕ) (xs : List.Vector X (n + 1)) (ys : List.Vector Y n)
    (h : PFunPDS.uniformP.val.mass
        (fun f => PFunPDS.prevOut (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) xs.toList f
          = ys.toList.map Part.some) ≠ 0) :
    ∑ y : Y, (behaviorOf PFunPDS.uniformP (PFunPDS.urfRV : PFunPDS.RV (X → Y) X Y) n
        (y, xs, ys)).get
        ((behaviorOf_dom PFunPDS.uniformP PFunPDS.urfRV n y xs ys).mpr h) = 1 := by
  have hα : xs.toList ≠ [] := by
    have hlen : xs.toList.length = n + 1 := xs.2
    intro he; rw [he, List.length_nil] at hlen; omega
  -- The conditional of the Y-valued RV `f ↦ f(xᵢ)` given the history is a `ProbDist Y`.
  have hPD := Dist.condPMFOf_isProbDist PFunPDS.uniformP
    (fun f => f (xs.toList.getLast hα)) (PFunPDS.prevOut PFunPDS.urfRV xs.toList)
    (ys.toList.map Part.some) h
  have hPD' := hPD.weight_eq
  rw [Dist.weight_eq_sum] at hPD'
  rw [← hPD']
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show (PFunPDS.behaviorB PFunPDS.uniformP PFunPDS.urfRV xs.toList (Part.some y)
      (ys.toList.map Part.some)).get _
    = Dist.condPMFOfDist PFunPDS.uniformP (fun f => f (xs.toList.getLast hα))
        (PFunPDS.prevOut PFunPDS.urfRV xs.toList) (ys.toList.map Part.some) h y
  rw [Dist.condPMFOfDist_apply]
  simp only [PFunPDS.behaviorB_urfRV_output xs.toList hα y (ys.toList.map Part.some)]

/-- **CR18 Def 3.18 / footnote 14 — normalization, general (total) PDS**: for any PDS
`S` whose output is **total** on a realizable history `(xⁱ, yⁱ⁻¹)` — i.e. the
probability of "no output" (`⊥`) under that history is `0` (`htot`) — the conditional
probabilities sum to 1 over the next output `yᵢ : Y`. The conditional law of the
`Part Y`-valued output is a `ProbDist (Part Y)` of weight 1; splitting that weight as
`(⊥ mass) + ∑_{y} (some y mass)` (`weight_eq_none_add_sum_some`) and killing the `⊥`
term by totality leaves `∑_{y} = 1`. The URF is the special case where totality is
automatic (`behaviorOf_urf_normalized`). -/
theorem behaviorOf_normalized {Ω : Type w} {X : Type u} {Y : Type v} [Fintype Y]
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) (n : ℕ)
    (xs : List.Vector X (n + 1)) (ys : List.Vector Y n)
    (h : p.val.mass (fun ω => PFunPDS.prevOut S xs.toList ω = ys.toList.map Part.some) ≠ 0)
    (htot : p.val.mass (fun ω =>
        Dist.RV.eval (PFunPDS.funView S) xs.toList ω = Part.none
        ∧ PFunPDS.prevOut S xs.toList ω = ys.toList.map Part.some) = 0) :
    ∑ y : Y, (behaviorOf p S n (y, xs, ys)).get
        ((behaviorOf_dom p S n y xs ys).mpr h) = 1 := by
  have hPD := Dist.condPMFOf_isProbDist p (Dist.RV.eval (PFunPDS.funView S) xs.toList)
    (PFunPDS.prevOut S xs.toList) (ys.toList.map Part.some) h
  have hPD' := hPD.weight_eq
  rw [Dist.weight_eq_none_add_sum_some] at hPD'
  have hnone : (Dist.condPMFOfDist p (Dist.RV.eval (PFunPDS.funView S) xs.toList)
      (PFunPDS.prevOut S xs.toList) (ys.toList.map Part.some) h).val Part.none = 0 := by
    show Dist.condPMFOfDist p (Dist.RV.eval (PFunPDS.funView S) xs.toList)
      (PFunPDS.prevOut S xs.toList) (ys.toList.map Part.some) h Part.none = 0
    rw [Dist.condPMFOfDist_apply, Dist.condPMFOf_apply, htot, zero_div]
  rw [hnone, zero_add] at hPD'
  rw [← hPD']
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show (PFunPDS.behaviorB p S xs.toList (Part.some y) (ys.toList.map Part.some)).get _
    = Dist.condPMFOfDist p (Dist.RV.eval (PFunPDS.funView S) xs.toList)
        (PFunPDS.prevOut S xs.toList) (ys.toList.map Part.some) h (Part.some y)
  rw [Dist.condPMFOfDist_apply]
  rfl

namespace PFunPDE

variable {X : Type u} {Y : Type v}

/-- CR18 Definition 3.16: the transcript **random variable** `tr(S,E)`.

Maurer: `tr(S,E)` is "a random variable taking on as values sequences
`x₁,y₁,x₂,y₂,…`". So it is exactly that — a random variable, i.e. a function on a
sample space, via the existing `Dist.RV`. Given a PDS `S` (a random variable
`Ω₁ → DDS`) and a PDE `E` (a random variable `Ω₂ → DDE`) selected
**independently**, the joint experiment lives on the product sample space
`Ω₁ × Ω₂`, and `tr(S,E)` sends `ω` to the deterministic transcript
`tr(S ω₁, E ω₂)`. It is the deterministic map `tr(·,·)` (`transcriptFun`)
composed with the joint random variable `⟨S,E⟩`.

No law/distribution appears here: `tr(S,E)` is the random variable itself. Its
law in a given experiment `p : ProbDist (Ω₁ × Ω₂)` is the generic pushforward
`Dist.PMF p (tr(S,E))` — and, crucially, distinct random variables with equal
laws share that transcript law (the collapse that indistinguishability rests on,
the transcript analogue of `PFunPDS.RV.behavior_eq_of_law_eq`). -/
noncomputable def transcriptRV {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : RV Ω₂ X Y) :
    Dist.RV (Ω := Ω₁ × Ω₂) (A := ℕ → List (X × Option Y)) :=
  fun ω => transcriptFun (S ω.1, E ω.2)

@[simp]
theorem transcriptRV_apply {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : RV Ω₂ X Y) (ω : Ω₁ × Ω₂) :
    transcriptRV S E ω = PFunDDS.transcript (S ω.1) (E ω.2) :=
  rfl

/-- CR18 notation for the transcript **random variable** `tr(S,E)` (Def 3.16):
the random variable `ω ↦ tr(S ω₁, E ω₂)`. Capital `S, E` (random variables over
`DDS`/`DDE`) select this RV overload; lowercase `tr(s,e)` (deterministic
`DDS`/`DDE`) is the deterministic transcript function. -/
scoped notation "tr" "(" S "," E ")" => transcriptRV S E

/-! ### CR18 §3.6.5 — the transcript distribution (Maurer's "list of random variables")

Maurer: the transcript `tr(S,E) = X₁,Y₁,X₂,Y₂,…` "can essentially equivalently be understood
as the sequence of random variables". Modelling it that way — as the **list of RVs**, not via
the deterministic transcript recurrence — is what makes Lemma 3.2 immediate. The output RVs
`Yᵢ = S(X¹…Xⁱ)` depend only on the system and the query RVs `Xᵢ = E(Y¹…Yⁱ⁻¹)` only on the
environment, so for a fixed target `(xⁱ,yⁱ)` the transcript event already splits into an
`S`-part (on `ω₁`) and an `E`-part (on `ω₂`); independence then factors it in one step. The
environment is the dual system `E : RV Ω₂ Y X` (Def 3.21): it reads the output history
`yⁱ⁻¹` (length `i-1`) and produces the query `xᵢ`, one step behind the system, which sees
`xⁱ` (length `i`). -/

/-- CR18 §3.6.5: the **transcript distribution** `P^{ES}_{X^kY^k}(xⁱ,yⁱ)` as the joint law of
the transcript random variables — the mass, in the independent experiment `pS × pE`, of the
event that the system produces `yⁱ` on the input prefixes of `xⁱ` (`Yᵢ = S(x¹…xⁱ)`) and the
environment produces `xⁱ` on the output prefixes of `yⁱ` (`Xᵢ = E(y¹…yⁱ⁻¹)`). -/
noncomputable def transcriptDist {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) : ℝ :=
  (Dist.prodProbDist pS pE).val.mass (fun ω =>
    (∀ i (hi : i < k), Dist.RV.eval (PFunPDS.funView S) (xs.toList.take (i + 1)) ω.1
        = Part.some (ys.get ⟨i, hi⟩))
    ∧ (∀ i (hi : i < k), E ω.2 ((ys.toList.take i).map some)
        = some (xs.get ⟨i, hi⟩)))

/-! Candidate for upstream: first-class transcript-law names.

CR18 Lemma 3.2 is a statement about the law of the transcript prefix
`X^kY^k`, factored into a system contribution and an environment contribution.
The raw `transcriptDist` definition above already formalizes that law as a
mass. The names below expose the two rectangle events, their masses, and the
prefix-law kernel directly, so later proofs can cite the paper-level objects
instead of reopening the event body.

This is also the bridge to the thesis presentation (`papers/thesis (1).pdf`):
Def. 2.17 identifies PDS representatives by equality of transcript distributions
in all compatible deterministic environments, Notation 2.19 names those
equivalence classes as random systems, Def. 2.26 defines `Adv` as a supremum
over transcript-distribution distances, and Thm. 2.31 proves the corresponding
static distance `A` equals `Adv`. These definitions remain representative-level;
quotient/equivalence-class lifting should be a theorem on top of them, not baked
into the event definition. -/

/-- A length-`k` transcript prefix `(x^k, y^k)`. -/
abbrev TranscriptPrefix (X : Type u) (Y : Type v) (k : ℕ) : Type (max u v) :=
  List.Vector X k × List.Vector Y k

/-- A transcript-prefix law as the probability mass assigned to each prefix. -/
abbrev TranscriptLaw (X : Type u) (Y : Type v) (k : ℕ) : Type (max u v) :=
  TranscriptPrefix X Y k → ℝ

/-- CR18 Lemma 3.2, system rectangle event:
`S(x^1)=y_1, ..., S(x^k)=y_k`. -/
def transcriptSystemEvent {Ω : Type w} (S : PFunPDS.RV Ω X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) (ω : Ω) : Prop :=
  ∀ i (hi : i < k),
    Dist.RV.eval (PFunPDS.funView S) (xs.toList.take (i + 1)) ω =
      Part.some (ys.get ⟨i, hi⟩)

/-- CR18 Lemma 3.2, environment rectangle event:
`E()=x_1, E(y^1)=x_2, ..., E(y^{k-1})=x_k`. The environment is a DDE, so it
sees the previous output history as values in `Y ∪ {⊥}`. -/
def transcriptEnvironmentEvent {Ω : Type w} (E : PFunPDE.RV Ω X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) (ω : Ω) : Prop :=
  ∀ i (hi : i < k),
    E ω ((ys.toList.take i).map some) = some (xs.get ⟨i, hi⟩)

/-- Candidate for upstream: the joint rectangle event for a fixed transcript
prefix in the independent `S`/`E` experiment. This packages the exact event
whose mass is the CR18 transcript-prefix law. -/
def transcriptJointEvent {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (t : TranscriptPrefix X Y k) (ω : Ω₁ × Ω₂) : Prop :=
  transcriptSystemEvent S t.1 t.2 ω.1 ∧
    transcriptEnvironmentEvent E t.1 t.2 ω.2

/-- Candidate for upstream: one system/environment sample realizes at most one
length-`k` transcript prefix. The proof follows the CR18 transcript recurrence:
the environment fixes the next query from the previous output prefix, then the
system fixes the next output from the current input prefix. -/
theorem transcriptJointEvent_unique {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (t u : TranscriptPrefix X Y k) (ω : Ω₁ × Ω₂) :
    transcriptJointEvent S E t ω → transcriptJointEvent S E u ω → t = u := by
  intro ht hu
  rcases ht with ⟨htS, htE⟩
  rcases hu with ⟨huS, huE⟩
  have hprefix : ∀ n, n ≤ k →
      t.1.toList.take n = u.1.toList.take n ∧
        t.2.toList.take n = u.2.toList.take n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnk : n < k := Nat.lt_of_succ_le hn
        have ihn := ih (Nat.le_of_lt hnk)
        have hx_get : t.1.get ⟨n, hnk⟩ = u.1.get ⟨n, hnk⟩ := by
          have htE_n := htE n hnk
          have huE_n := huE n hnk
          have hys : (t.2.toList.take n).map some = (u.2.toList.take n).map some := by
            rw [ihn.2]
          rw [hys] at htE_n
          exact Option.some.inj (htE_n.symm.trans huE_n)
        have ht_x_succ : t.1.toList.take (n + 1) =
            t.1.toList.take n ++ [t.1.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' t.1.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        have hu_x_succ : u.1.toList.take (n + 1) =
            u.1.toList.take n ++ [u.1.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' u.1.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        have hx_prefix : t.1.toList.take (n + 1) = u.1.toList.take (n + 1) := by
          rw [ht_x_succ, hu_x_succ, ihn.1, hx_get]
        have hy_get : t.2.get ⟨n, hnk⟩ = u.2.get ⟨n, hnk⟩ := by
          have htS_n := htS n hnk
          have huS_n := huS n hnk
          rw [hx_prefix] at htS_n
          exact Part.some_inj.mp (htS_n.symm.trans huS_n)
        have ht_y_succ : t.2.toList.take (n + 1) =
            t.2.toList.take n ++ [t.2.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' t.2.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        have hu_y_succ : u.2.toList.take (n + 1) =
            u.2.toList.take n ++ [u.2.get ⟨n, hnk⟩] := by
          rw [← List.take_concat_get' u.2.toList n
            (by simpa [List.Vector.toList_length] using hnk)]
          congr 1
        constructor
        · exact hx_prefix
        · rw [ht_y_succ, hu_y_succ, ihn.2, hy_get]
  have hfull := hprefix k (le_refl k)
  apply Prod.ext
  · exact Subtype.ext (by
      rw [List.take_of_length_le (l := t.1.toList) (by simp),
        List.take_of_length_le (l := u.1.toList) (by simp)] at hfull
      exact hfull.1)
  · exact Subtype.ext (by
      rw [List.take_of_length_le (l := t.2.toList) (by simp),
        List.take_of_length_le (l := u.2.toList) (by simp)] at hfull
      exact hfull.2)

/-- Candidate for upstream: total systems and total environments realize a
length-`k` concrete transcript prefix for every system/environment sample pair.
This is the structural coverage fact behind transcript-law normalization. -/
theorem transcriptJointEvent_exists_of_total {Ω₁ : Type w} {Ω₂ : Type z}
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (hS : PFunPDS.RV.KStepTotal S k)
    (hE : PFunPDE.RV.KQueryTotal E k) :
    ∀ ω : Ω₁ × Ω₂, ∃ t : TranscriptPrefix X Y k,
      transcriptJointEvent S E t ω := by
  induction k with
  | zero =>
      intro ω
      refine ⟨(⟨[], rfl⟩, ⟨[], rfl⟩), ?_⟩
      constructor <;> intro i hi <;> omega
  | succ k ih =>
      have hSprev : PFunPDS.RV.KStepTotal S k := by
        intro ω xs hne hlen
        exact hS ω xs hne (Nat.le_trans hlen (Nat.le_succ k))
      have hEprev : PFunPDE.RV.KQueryTotal E k := by
        intro ω ys hlen
        exact hE ω ys (Nat.lt_trans hlen (Nat.lt_succ_self k))
      intro ω
      obtain ⟨t, ht⟩ := ih hSprev hEprev ω
      obtain ⟨x, hx⟩ := hE ω.2 t.2.toList (by simp [List.Vector.toList_length])
      obtain ⟨y, hy⟩ := hS ω.1 (t.1.toList ++ [x]) (by simp)
        (by simp [List.Vector.toList_length])
      let xs' : List.Vector X (k + 1) := ⟨t.1.toList ++ [x], by simp [List.Vector.toList_length]⟩
      let ys' : List.Vector Y (k + 1) := ⟨t.2.toList ++ [y], by simp [List.Vector.toList_length]⟩
      rcases ht with ⟨htS, htE⟩
      refine ⟨(xs', ys'), ?_⟩
      constructor
      · intro i hi
        rcases (Nat.lt_succ_iff_lt_or_eq.mp hi) with hlt | rfl
        · change (PFunPDS.funView S).eval
            (List.take (i + 1) (t.1.toList ++ [x])) ω.1 =
              Part.some (List.Vector.get
                (⟨t.2.toList ++ [y], by simp [List.Vector.toList_length]⟩ :
                  List.Vector Y (k + 1)) ⟨i, hi⟩)
          rw [List.take_append_of_le_length
            (by simpa [List.Vector.toList_length] using Nat.succ_le_of_lt hlt)]
          have hget :
              (List.Vector.get
                (⟨t.2.toList ++ [y], by simp [List.Vector.toList_length]⟩ :
                  List.Vector Y (k + 1)) ⟨i, hi⟩) = t.2.get ⟨i, hlt⟩ := by
            change (t.2.toList ++ [y]).get
                ⟨i, by simpa [List.Vector.toList_length] using hi⟩ =
              t.2.toList.get ⟨i, by simpa [List.Vector.toList_length] using hlt⟩
            simp [List.get_eq_getElem, hlt, List.Vector.toList_length]
          rw [hget]
          exact htS i hlt
        · change (PFunPDS.funView S).eval
              (List.take (i + 1) (t.1.toList ++ [x])) ω.1 =
            Part.some (List.Vector.get
              (⟨t.2.toList ++ [y], by simp [List.Vector.toList_length]⟩ :
                List.Vector Y (i + 1)) ⟨i, hi⟩)
          rw [List.take_of_length_le (by simp [List.Vector.toList_length])]
          have hget :
              (List.Vector.get
                (⟨t.2.toList ++ [y], by simp [List.Vector.toList_length]⟩ :
                  List.Vector Y (i + 1)) ⟨i, hi⟩) = y := by
            change (t.2.toList ++ [y]).get
                ⟨i, by simp [List.Vector.toList_length]⟩ = y
            simp [List.get_eq_getElem, List.Vector.toList_length]
          rw [hget]
          simpa [PFunPDS.funView] using hy
      · intro i hi
        rcases (Nat.lt_succ_iff_lt_or_eq.mp hi) with hlt | rfl
        · change E ω.2 (List.map some (List.take i (t.2.toList ++ [y]))) =
            some (List.Vector.get
              (⟨t.1.toList ++ [x], by simp [List.Vector.toList_length]⟩ :
                List.Vector X (k + 1)) ⟨i, hi⟩)
          rw [List.take_append_of_le_length
            (by simpa [List.Vector.toList_length] using Nat.le_of_lt hlt)]
          have hget :
              (List.Vector.get
                (⟨t.1.toList ++ [x], by simp [List.Vector.toList_length]⟩ :
                  List.Vector X (k + 1)) ⟨i, hi⟩) = t.1.get ⟨i, hlt⟩ := by
            change (t.1.toList ++ [x]).get
                ⟨i, by simpa [List.Vector.toList_length] using hi⟩ =
              t.1.toList.get ⟨i, by simpa [List.Vector.toList_length] using hlt⟩
            simp [List.get_eq_getElem, hlt, List.Vector.toList_length]
          rw [hget]
          exact htE i hlt
        · change E ω.2 (List.map some (List.take i (t.2.toList ++ [y]))) =
            some (List.Vector.get
              (⟨t.1.toList ++ [x], by simp [List.Vector.toList_length]⟩ :
                List.Vector X (i + 1)) ⟨i, hi⟩)
          rw [List.take_append_of_le_length (by simp [List.Vector.toList_length])]
          have hget :
              (List.Vector.get
                (⟨t.1.toList ++ [x], by simp [List.Vector.toList_length]⟩ :
                  List.Vector X (i + 1)) ⟨i, hi⟩) = x := by
            change (t.1.toList ++ [x]).get
                ⟨i, by simp [List.Vector.toList_length]⟩ = x
            simp [List.get_eq_getElem, List.Vector.toList_length]
          rw [hget]
          rw [List.take_of_length_le (by simp [List.Vector.toList_length])]
          exact hx

/-- The system factor in CR18 Lemma 3.2. -/
noncomputable def transcriptSystemFactor {Ω : Type w}
    (pS : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) : ℝ :=
  pS.val.mass (transcriptSystemEvent S xs ys)

/-- The environment factor in CR18 Lemma 3.2. -/
noncomputable def transcriptEnvironmentFactor {Ω : Type w}
    (pE : Dist.ProbDist Ω) (E : PFunPDE.RV Ω X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) : ℝ :=
  pE.val.mass (transcriptEnvironmentEvent E xs ys)

/-- The CR18 transcript-prefix law `P^{ES}_{X^kY^k}`. -/
noncomputable def transcriptLaw {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) (k : ℕ) :
    TranscriptLaw X Y k :=
  fun t => transcriptDist pS pE S E t.1 t.2

@[simp]
theorem transcriptLaw_apply {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (t : TranscriptPrefix X Y k) :
    transcriptLaw pS pE S E k t = transcriptDist pS pE S E t.1 t.2 :=
  rfl

/-- The named joint transcript event is exactly the event used by
`transcriptDist`. -/
theorem transcriptDist_eq_mass_jointEvent {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (t : TranscriptPrefix X Y k) :
    transcriptDist pS pE S E t.1 t.2 =
      (Dist.prodProbDist pS pE).val.mass (transcriptJointEvent S E t) := by
  rfl

/-- A transcript-prefix law as a finite distribution over transcript prefixes. -/
noncomputable def transcriptLawDist {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (law : TranscriptLaw X Y k) : Dist (TranscriptPrefix X Y k) :=
  Dist.ofFiniteMassFunction law

@[simp]
theorem transcriptLawDist_apply {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (law : TranscriptLaw X Y k) (t : TranscriptPrefix X Y k) :
    transcriptLawDist law t = law t := by
  simp [transcriptLawDist]

/-- Candidate for upstream: the mass of a transcript-prefix event under the
finite transcript-law distribution is the mass of the corresponding pulled-back
joint event on independently sampled system/environment implementations. -/
theorem transcriptLawDist_mass_eq_mass_exists_jointEvent {Ω₁ : Type w} {Ω₂ : Type z}
    {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (P : TranscriptPrefix X Y k → Prop) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).mass P =
      (Dist.prodProbDist pS pE).val.mass
        (fun ω => ∃ t : TranscriptPrefix X Y k, transcriptJointEvent S E t ω ∧ P t) := by
  classical
  let μ : Dist (Ω₁ × Ω₂) := (Dist.prodProbDist pS pE).val
  have hUnion :
      μ.mass
          (fun ω => ∃ t : TranscriptPrefix X Y k,
            transcriptJointEvent S E t ω ∧ P t) =
        ∑ t : TranscriptPrefix X Y k,
          μ.mass (fun ω => transcriptJointEvent S E t ω ∧ P t) := by
    unfold Dist.mass Finsupp.sum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only []
    by_cases hω : ∃ t : TranscriptPrefix X Y k,
        transcriptJointEvent S E t ω ∧ P t
    · have hω' := hω
      obtain ⟨t₀, ht₀⟩ := hω
      rw [if_pos hω']
      rw [Finset.sum_eq_single t₀]
      · simp [ht₀]
      · intro t _ hne
        have hnot : ¬ (transcriptJointEvent S E t ω ∧ P t) := by
          intro ht
          exact hne (transcriptJointEvent_unique S E t t₀ ω ht.1 ht₀.1)
        simp [hnot]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ t₀))
    · have hnone : ∀ t : TranscriptPrefix X Y k,
          ¬ (transcriptJointEvent S E t ω ∧ P t) := by
        intro t ht
        exact hω ⟨t, ht⟩
      simp [hnone]
  rw [hUnion]
  rw [Dist.mass_eq_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : P t
  · rw [if_pos ht]
    rw [transcriptLawDist_apply, transcriptLaw_apply, transcriptDist_eq_mass_jointEvent]
    apply Dist.mass_congr
    intro ω
    simp [ht]
  · rw [if_neg ht]
    have hzero : μ.mass (fun ω => transcriptJointEvent S E t ω ∧ P t) = 0 := by
      simp [Dist.mass, ht]
    rw [hzero]

/-- The total mass of a transcript-law distribution is the finite sum of the
transcript-prefix law over all prefixes. -/
theorem transcriptLawDist_weight {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (law : TranscriptLaw X Y k) :
    (transcriptLawDist law).weight = ∑ t : TranscriptPrefix X Y k, law t := by
  simpa [transcriptLawDist] using Dist.weight_ofFiniteMassFunction law

/-- A transcript-prefix law distribution is pointwise non-negative: each entry
is an event mass under a product probability law. -/
theorem transcriptLawDist_transcriptLaw_nonNeg {Ω₁ : Type w} {Ω₂ : Type z}
    {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).NonNeg := fun t => by
  rw [transcriptLawDist_apply, transcriptLaw_apply,
    transcriptDist_eq_mass_jointEvent]
  exact (Dist.prodProbDist pS pE).property.nonNeg.mass_nonneg _

/-- Transcript-prefix law of a probability PDS against a deterministic CR18
environment.  This is the law-level specialization of `transcriptLaw`; the
system law is sampled directly and the environment is represented by the
one-point probability space internally. -/
noncomputable def deterministicTranscriptLaw
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) (k : ℕ) :
    TranscriptLaw X Y k :=
  transcriptLaw S Dist.unitProbDist.{0}
    ((fun s : PFunDDS.DDS X Y => s) : PFunPDS.RV (PFunDDS.DDS X Y) X Y)
    ((fun _ : PUnit => E) : PFunPDE.RV PUnit X Y) k

/-- Finite distribution form of `deterministicTranscriptLaw`. -/
noncomputable def deterministicTranscriptLawDist {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) :
    Dist (TranscriptPrefix X Y k) :=
  transcriptLawDist (deterministicTranscriptLaw S E k)

@[simp]
theorem deterministicTranscriptLawDist_apply {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y)
    (t : TranscriptPrefix X Y k) :
    deterministicTranscriptLawDist S E t = deterministicTranscriptLaw S E k t := by
  simp [deterministicTranscriptLawDist]

/-- The deterministic-environment transcript-law distribution is pointwise
non-negative. -/
theorem deterministicTranscriptLawDist_nonNeg {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) :
    (deterministicTranscriptLawDist (k := k) S E).NonNeg :=
  transcriptLawDist_transcriptLaw_nonNeg S Dist.unitProbDist.{0} _ _

/-- Candidate for upstream: a transcript law has total mass at most one as
soon as every sample realizes at most one length-`k` transcript prefix. The
remaining CR18 structural proof is the uniqueness premise, not any
H-technique-specific density argument. -/
theorem transcriptLawDist_weight_le_one_of_unique_jointEvent {Ω₁ : Type w} {Ω₂ : Type z}
    {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (huniq : ∀ t u : TranscriptPrefix X Y k, ∀ ω : Ω₁ × Ω₂,
      transcriptJointEvent S E t ω → transcriptJointEvent S E u ω → t = u) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).weight ≤ 1 := by
  rw [transcriptLawDist_weight]
  calc
    ∑ t : TranscriptPrefix X Y k, transcriptLaw pS pE S E k t
        = ∑ t : TranscriptPrefix X Y k,
            (Dist.prodProbDist pS pE).val.mass (transcriptJointEvent S E t) := by
          simp_rw [transcriptLaw_apply, transcriptDist_eq_mass_jointEvent]
    _ ≤ (Dist.prodProbDist pS pE).val.weight := by
          exact Dist.sum_mass_le_weight_of_pairwise_disjoint
            (Dist.prodProbDist pS pE).property.nonNeg
            (fun t ω => transcriptJointEvent S E t ω)
            (fun t u hne ω ht hu => hne (huniq t u ω ht hu))
    _ = 1 := by
          exact (Dist.prodProbDist pS pE).property.weight_eq

/-- Candidate for upstream: every CR18 transcript-prefix law is a
subdistribution. Partial systems/environments may stop or be undefined, so the
correct generic statement is `≤ 1`; equality belongs to a separate totality
API. -/
theorem transcriptLawDist_weight_le_one {Ω₁ : Type w} {Ω₂ : Type z} {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).weight ≤ 1 := by
  exact transcriptLawDist_weight_le_one_of_unique_jointEvent pS pE S E
    (fun t u ω ht hu => transcriptJointEvent_unique S E t u ω ht hu)

/-- Candidate for upstream: a CR18 transcript-prefix law has total mass exactly
one when every system/environment sample realizes some length-`k` transcript
prefix. This is the equality companion to `transcriptLawDist_weight_le_one`;
the coverage premise is the meaningful totality condition, not an
H-technique-specific assumption. -/
theorem transcriptLawDist_weight_eq_one_of_jointEvent_cover {Ω₁ : Type w} {Ω₂ : Type z}
    {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (hcover : ∀ ω : Ω₁ × Ω₂, ∃ t : TranscriptPrefix X Y k,
      transcriptJointEvent S E t ω) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).weight = 1 := by
  rw [transcriptLawDist_weight]
  calc
    ∑ t : TranscriptPrefix X Y k, transcriptLaw pS pE S E k t
        = ∑ t : TranscriptPrefix X Y k,
            (Dist.prodProbDist pS pE).val.mass (transcriptJointEvent S E t) := by
          simp_rw [transcriptLaw_apply, transcriptDist_eq_mass_jointEvent]
    _ = (Dist.prodProbDist pS pE).val.weight := by
          exact Dist.sum_mass_eq_weight_of_pairwise_disjoint_of_cover
            (Dist.prodProbDist pS pE).val
            (fun t ω => transcriptJointEvent S E t ω)
            (fun t u hne ω ht hu =>
              hne (transcriptJointEvent_unique S E t u ω ht hu))
            hcover
    _ = 1 := by
          exact (Dist.prodProbDist pS pE).property.weight_eq

/-- Candidate for upstream: total systems/environments produce a normalized
length-`k` CR18 transcript-prefix law. -/
theorem transcriptLawDist_weight_eq_one_of_total {Ω₁ : Type w} {Ω₂ : Type z}
    {k : ℕ} [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (hS : PFunPDS.RV.KStepTotal S k)
    (hE : PFunPDE.RV.KQueryTotal E k) :
    (transcriptLawDist (transcriptLaw pS pE S E k)).weight = 1 := by
  exact transcriptLawDist_weight_eq_one_of_jointEvent_cover pS pE S E
    (transcriptJointEvent_exists_of_total S E hS hE)

@[simp]
theorem transcriptLawDist_transcriptLaw_apply {Ω₁ : Type w} {Ω₂ : Type z} {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (t : TranscriptPrefix X Y k) :
    transcriptLawDist (transcriptLaw pS pE S E k) t =
      transcriptDist pS pE S E t.1 t.2 := by
  simp

/-- **CR18 Lemma 3.2 (factored form)**: by independence of the system `S` and the environment
`E`, the transcript distribution factors into the system part (the output RVs) and the
environment part (the query RVs) — `P^{ES}_{X^kY^k} = (system)·(environment)`. With Maurer's
**list-of-RVs** model this is *immediately* `Dist.mass_prod_and`: there is no transcript
recurrence to unfold (contrast the deterministic-transcript model, where this needed a
separability induction). Each factor is a cumulative behavior — the system factor is the
`S`-cumulative `Pr[ outSeq S xⁱ = yⁱ ]` (via `outSeq_eq_map_iff`), the environment factor the
`E`-cumulative `Pr[ E's queries = xⁱ ]`. -/
theorem transcriptDist_eq_mul {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) :
    transcriptDist pS pE S E xs ys
      = pS.val.mass (fun ω₁ => ∀ i (hi : i < k),
            Dist.RV.eval (PFunPDS.funView S) (xs.toList.take (i + 1)) ω₁ = Part.some (ys.get ⟨i, hi⟩))
        * pE.val.mass (fun ω₂ => ∀ i (hi : i < k),
            E ω₂ ((ys.toList.take i).map some) = some (xs.get ⟨i, hi⟩)) := by
  rw [transcriptDist, Dist.prodProbDist_val]
  exact Dist.mass_prod_and pS.val pE.val
    (fun ω₁ => ∀ i (hi : i < k),
      Dist.RV.eval (PFunPDS.funView S) (xs.toList.take (i + 1)) ω₁ = Part.some (ys.get ⟨i, hi⟩))
    (fun ω₂ => ∀ i (hi : i < k),
      E ω₂ ((ys.toList.take i).map some) = some (xs.get ⟨i, hi⟩))

/-- CR18 Lemma 3.2 with named factors. This is definitionally the existing
`transcriptDist_eq_mul`, but avoids exposing the rectangle predicates at use
sites. -/
theorem transcriptDist_eq_systemFactor_mul_environmentFactor {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (xs : List.Vector X k) (ys : List.Vector Y k) :
    transcriptDist pS pE S E xs ys =
      transcriptSystemFactor pS S xs ys * transcriptEnvironmentFactor pE E xs ys := by
  exact transcriptDist_eq_mul pS pE S E xs ys

/-- CR18 Lemma 3.2 as a statement about the first-class transcript law. -/
theorem transcriptLaw_eq_systemFactor_mul_environmentFactor {Ω₁ : Type w} {Ω₂ : Type z}
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y) {k : ℕ}
    (t : TranscriptPrefix X Y k) :
    transcriptLaw pS pE S E k t =
      transcriptSystemFactor pS S t.1 t.2 * transcriptEnvironmentFactor pE E t.1 t.2 := by
  exact transcriptDist_eq_systemFactor_mul_environmentFactor pS pE S E t.1 t.2

/-- CR18 Lemma 3.2 as a statement about the transcript-law distribution. -/
theorem transcriptLawDist_eq_systemFactor_mul_environmentFactor {Ω₁ : Type w} {Ω₂ : Type z} {k : ℕ}
    [Fintype (TranscriptPrefix X Y k)]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) (E : PFunPDE.RV Ω₂ X Y)
    (t : TranscriptPrefix X Y k) :
    transcriptLawDist (transcriptLaw pS pE S E k) t =
      transcriptSystemFactor pS S t.1 t.2 * transcriptEnvironmentFactor pE E t.1 t.2 := by
  simpa using transcriptLaw_eq_systemFactor_mul_environmentFactor pS pE S E t

/-- A deterministic transcript law of a law-level PDS induced by a sampled
deterministic system is the same transcript law computed directly from the
original sample space. -/
theorem deterministicTranscriptLaw_pmf {Ω : Type*}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y)
    (E : PFunDDS.DDE X Y) {k : ℕ} (t : TranscriptPrefix X Y k) :
    deterministicTranscriptLaw (Dist.PMF p S) E k t =
      transcriptLaw p Dist.unitProbDist.{0}
        S ((fun _ : PUnit => E) : PFunPDE.RV PUnit X Y) k t := by
  unfold deterministicTranscriptLaw
  rw [transcriptLaw_eq_systemFactor_mul_environmentFactor,
    transcriptLaw_eq_systemFactor_mul_environmentFactor]
  congr 1
  unfold transcriptSystemFactor Dist.PMF
  rw [Dist.mass_fTransform]
  rfl

namespace Prob

/-- Embed a deterministic CR18 environment as the degenerate law-level PDE
concentrated on that environment. -/
noncomputable def ofDDE (E : PFunDDS.DDE X Y) : PFunPDE.Prob X Y :=
  Dist.PMF (A := PFunDDS.DDE X Y) (Ω := PUnit.{1})
    Dist.unitProbDist.{0} (fun _ : PUnit.{1} => E)

/-- Law-level totality for exactly `q` environment queries: every deterministic
environment in the law's support issues a concrete next query on output
histories of length `< q`. -/
def KQueryTotal (E : PFunPDE.Prob X Y) (q : Nat) : Prop :=
  ∀ e, e ∈ E.val.support → PFunPDE.DDEKQueryTotal e q

/-- If a deterministic CR18 environment is q-query-total, then its degenerate
law-level PDE is q-query-total. -/
theorem ofDDE_KQueryTotal
    (E : PFunDDS.DDE X Y) {q : Nat} (hE : PFunPDE.DDEKQueryTotal E q) :
    KQueryTotal (ofDDE E) q := by
  intro e he ys hlen
  unfold ofDDE Dist.PMF at he
  obtain ⟨ω, _hω, hω⟩ :=
    Dist.mem_support_fTransform
      (fun _ : PUnit.{1} => E) Dist.unitProbDist.{0}.val he
  subst e
  exact hE ys hlen

end Prob

end PFunPDE

namespace PFunPDS
namespace Prob

variable {X : Type u} {Y : Type v}

/-- Law-level totality up to `q` system queries: every deterministic system in
the law's support produces a concrete output on every nonempty input history of
length at most `q`. -/
def KStepTotal (S : PFunPDS.Prob X Y) (q : Nat) : Prop :=
  ∀ s, s ∈ S.val.support →
    ∀ xs : List X, xs ≠ [] → xs.length ≤ q →
      ∃ y : Y, s.1 xs = Part.some y

/-- A PMF induced by a `q`-step-total system-valued random variable is
law-level `q`-step-total. -/
theorem KStepTotal_pmf_of_rv {Ω : Type*}
    (p : Dist.ProbDist Ω) (S : PFunPDS.RV Ω X Y) {q : Nat}
    (hS : PFunPDS.RV.KStepTotal S q) :
    KStepTotal (Dist.PMF p S) q := by
  intro s hs xs hxs hlen
  unfold Dist.PMF at hs
  obtain ⟨ω, _hω, hω⟩ := Dist.mem_support_fTransform S p.val hs
  subst s
  exact hS ω xs hxs hlen

/-- The transcript-prefix law induced by law-level system and environment
objects.  The sample spaces are the deterministic systems/environments
themselves; no representative wrapper is exposed. -/
noncomputable def transcriptLaw
    (S : PFunPDS.Prob X Y) (E : PFunPDE.Prob X Y) (q : Nat) :
    PFunPDE.TranscriptLaw X Y q :=
  PFunPDE.transcriptLaw S E
    ((fun s : PFunDDS.DDS X Y => s) :
      PFunPDS.RV (PFunDDS.DDS X Y) X Y)
    ((fun e : PFunDDS.DDE X Y => e) :
      PFunPDE.RV (PFunDDS.DDE X Y) X Y)
    q

/-- The transcript-prefix distribution induced by law-level system and
environment objects. -/
noncomputable def transcriptDist {q : Nat} [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunPDE.Prob X Y) :
    Dist (PFunPDE.TranscriptPrefix X Y q) :=
  PFunPDE.transcriptLawDist (transcriptLaw S E q)

/-- A law-level CR18 transcript distribution is pointwise non-negative. -/
theorem transcriptDist_nonNeg {q : Nat} [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunPDE.Prob X Y) :
    (transcriptDist (q := q) S E).NonNeg :=
  PFunPDE.transcriptLawDist_transcriptLaw_nonNeg S E _ _

/-- A law-level CR18 transcript distribution is always a subdistribution. -/
theorem transcriptDist_weight_le_one {q : Nat} [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunPDE.Prob X Y) :
    (transcriptDist (q := q) S E).weight ≤ 1 := by
  simpa [transcriptDist, transcriptLaw] using
    PFunPDE.transcriptLawDist_weight_le_one S E
      ((fun s : PFunDDS.DDS X Y => s) :
        PFunPDS.RV (PFunDDS.DDS X Y) X Y)
      ((fun e : PFunDDS.DDE X Y => e) :
        PFunPDE.RV (PFunDDS.DDE X Y) X Y)

/-- If the law-level system and environment are total on their supports, their
CR18 transcript distribution has total mass one. -/
theorem transcriptDist_weight_eq_one_of_total {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunPDE.Prob X Y)
    (hS : KStepTotal S q) (hE : PFunPDE.Prob.KQueryTotal E q) :
    (transcriptDist (q := q) S E).weight = 1 := by
  have hdist :
      transcriptDist (q := q) S E =
        PFunPDE.transcriptLawDist
          (PFunPDE.transcriptLaw
            (Dist.supportProbDist S)
            (Dist.supportProbDist E)
            ((fun s : {s : PFunDDS.DDS X Y // s ∈ S.val.support} => s.1) :
              PFunPDS.RV {s : PFunDDS.DDS X Y // s ∈ S.val.support} X Y)
            ((fun e : {e : PFunDDS.DDE X Y // e ∈ E.val.support} => e.1) :
              PFunPDE.RV {e : PFunDDS.DDE X Y // e ∈ E.val.support} X Y)
            q) := by
    ext t
    simp [transcriptDist, transcriptLaw]
    rw [PFunPDE.transcriptDist_eq_systemFactor_mul_environmentFactor,
      PFunPDE.transcriptDist_eq_systemFactor_mul_environmentFactor]
    congr 1
    · unfold PFunPDE.transcriptSystemFactor
      symm
      simpa using
        (Dist.supportProbDist_mass_preimage S
          (PFunPDE.transcriptSystemEvent
            ((fun s : PFunDDS.DDS X Y => s) :
              PFunPDS.RV (PFunDDS.DDS X Y) X Y)
            t.1 t.2))
    · unfold PFunPDE.transcriptEnvironmentFactor
      symm
      simpa using
        (Dist.supportProbDist_mass_preimage E
          (PFunPDE.transcriptEnvironmentEvent
            ((fun e : PFunDDS.DDE X Y => e) :
              PFunPDE.RV (PFunDDS.DDE X Y) X Y)
            t.1 t.2))
  rw [hdist]
  exact PFunPDE.transcriptLawDist_weight_eq_one_of_total
    (Dist.supportProbDist S)
    (Dist.supportProbDist E)
    ((fun s : {s : PFunDDS.DDS X Y // s ∈ S.val.support} => s.1) :
      PFunPDS.RV {s : PFunDDS.DDS X Y // s ∈ S.val.support} X Y)
    ((fun e : {e : PFunDDS.DDE X Y // e ∈ E.val.support} => e.1) :
      PFunPDE.RV {e : PFunDDS.DDE X Y // e ∈ E.val.support} X Y)
    (by
      intro s xs hxs hlen
      exact hS s.1 s.2 xs hxs hlen)
    (by
      intro e ys hlen
      exact hE e.1 e.2 ys hlen)

/-- Transcript distribution for a law-level PDS against a deterministic CR18
environment. -/
noncomputable def deterministicTranscriptDist {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) :
    Dist (PFunPDE.TranscriptPrefix X Y q) :=
  PFunPDE.deterministicTranscriptLawDist (k := q) S E

/-- A degenerate law-level PDE concentrated on a deterministic environment
induces the same transcript distribution as the deterministic transcript-law
specialization. -/
@[simp]
theorem transcriptDist_ofDDE {q : Nat} [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S : PFunPDS.Prob X Y) (E : PFunDDS.DDE X Y) :
    transcriptDist (q := q) S (PFunPDE.Prob.ofDDE E) =
      deterministicTranscriptDist (q := q) S E := by
  ext t
  simp [transcriptDist, transcriptLaw, deterministicTranscriptDist,
    PFunPDE.Prob.ofDDE, PFunPDE.deterministicTranscriptLawDist,
    PFunPDE.deterministicTranscriptLaw]
  rw [PFunPDE.transcriptDist_eq_systemFactor_mul_environmentFactor,
    PFunPDE.transcriptDist_eq_systemFactor_mul_environmentFactor]
  congr 1
  unfold PFunPDE.transcriptEnvironmentFactor Dist.PMF
  rw [Dist.mass_fTransform]
  rfl

/-- The ideal uniform random function as a law-level PDS. -/
noncomputable def urf {X : Type u} {Y : Type v}
    [Fintype (X → Y)] [Nonempty (X → Y)] : PFunPDS.Prob X Y :=
  Dist.PMF
    (PFunPDS.uniformP (X := X) (Y := Y))
    (PFunPDS.urfRV (X := X) (Y := Y))

/-- The ideal uniform random permutation as a law-level PDS. -/
noncomputable def urp {X : Type u} [Fintype X] : PFunPDS.Prob X X :=
  ⟨PFunPDS.URP X, PFunPDS.URP_isProbDist X⟩

/-- Thesis-style transcript adaptive advantage between two CR18 probabilistic
systems: the supremum, over q-query-total deterministic environments, of the
statistical distance between their length-`q` deterministic transcript laws.

This is stated on law-level PDS objects; sample spaces, random variables, and
representative adapters do not appear in the statement. -/
noncomputable def adaptiveTranscriptAdvantage {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) : ℝ :=
  sSup ((fun E : PFunPDE.QQueryEnvironment X Y q =>
      (RandomSystems.statDist
        (deterministicTranscriptDist (q := q) S E.1)
        (deterministicTranscriptDist (q := q) T E.1) : ℝ)) ''
    Set.univ)

/-- **Support lemma forced by formalization; candidate for upstream.** The image
defining the law-level adaptive transcript advantage is bounded above by `1`.

This is the reusable side-condition for comparing restricted environment
suprema with the full thesis-style supremum. -/
theorem adaptiveTranscriptAdvantage_image_bddAbove {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    BddAbove ((fun E : PFunPDE.QQueryEnvironment X Y q =>
      (RandomSystems.statDist
        (deterministicTranscriptDist (q := q) S E.1)
        (deterministicTranscriptDist (q := q) T E.1) : ℝ)) ''
      Set.univ) := by
  refine ⟨1, ?_⟩
  rintro x ⟨E, _hE, rfl⟩
  have hstat : RandomSystems.statDist
      (deterministicTranscriptDist (q := q) S E.1)
      (deterministicTranscriptDist (q := q) T E.1) ≤
      (deterministicTranscriptDist (q := q) S E.1).weight :=
    RandomSystems.statDist_le_weight
      (PFunPDE.deterministicTranscriptLawDist_nonNeg S E.1)
      (PFunPDE.deterministicTranscriptLawDist_nonNeg T E.1)
  have hweight :
      (deterministicTranscriptDist (q := q) S E.1).weight ≤ 1 := by
    rw [← transcriptDist_ofDDE (q := q) S E.1]
    exact transcriptDist_weight_le_one (q := q) S (PFunPDE.Prob.ofDDE E.1)
  exact_mod_cast le_trans hstat hweight

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
Every concrete q-query-total deterministic environment contributes one point to
the law-level adaptive transcript-advantage supremum. -/
theorem deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) (E : PFunPDE.QQueryEnvironment X Y q) :
    (RandomSystems.statDist
      (deterministicTranscriptDist (q := q) S E.1)
      (deterministicTranscriptDist (q := q) T E.1) : ℝ) ≤
      adaptiveTranscriptAdvantage (q := q) S T := by
  unfold adaptiveTranscriptAdvantage
  exact le_csSup
    (adaptiveTranscriptAdvantage_image_bddAbove (q := q) S T)
    ⟨E, Set.mem_univ E, rfl⟩

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
The thesis-style adaptive transcript advantage is nonnegative, including the
degenerate case where there are no `q`-query-total deterministic environments. -/
theorem adaptiveTranscriptAdvantage_nonneg {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) :
    0 ≤ adaptiveTranscriptAdvantage (q := q) S T := by
  unfold adaptiveTranscriptAdvantage
  exact RandomSystems.sSup_image_univ_nonneg_of_forall _
    (adaptiveTranscriptAdvantage_image_bddAbove (q := q) S T) (by
      intro E
      exact_mod_cast RandomSystems.statDist_nonneg
        (deterministicTranscriptDist (q := q) S E.1)
        (deterministicTranscriptDist (q := q) T E.1))

/-- A uniform pointwise transcript-distance bound for every q-query-total
deterministic environment bounds the law-level adaptive transcript supremum. -/
theorem adaptiveTranscriptAdvantage_le_of_pointwise {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y)
    (eps : NNReal)
    (h_pointwise : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      RandomSystems.statDist
        (deterministicTranscriptDist (q := q) S E.1)
        (deterministicTranscriptDist (q := q) T E.1) ≤ eps) :
    adaptiveTranscriptAdvantage (q := q) S T ≤ (eps : ℝ) := by
  unfold adaptiveTranscriptAdvantage
  exact RandomSystems.sSup_image_univ_le_of_forall _ (by positivity) (by
    intro E
    exact_mod_cast h_pointwise E)

/-- Real-valued companion to `adaptiveTranscriptAdvantage_le_of_pointwise`.

The signed distribution carrier makes real-valued analytic bounds natural.
The explicit non-negativity premise is exactly what the old `NNReal` codomain
supplied structurally. -/
theorem adaptiveTranscriptAdvantage_le_of_pointwise_real {q : Nat}
    [Fintype (PFunPDE.TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y)
    (eps : ℝ) (heps : 0 ≤ eps)
    (h_pointwise : ∀ E : PFunPDE.QQueryEnvironment X Y q,
      RandomSystems.statDist
        (deterministicTranscriptDist (q := q) S E.1)
        (deterministicTranscriptDist (q := q) T E.1) ≤ eps) :
    adaptiveTranscriptAdvantage (q := q) S T ≤ eps := by
  unfold adaptiveTranscriptAdvantage
  exact RandomSystems.sSup_image_univ_le_of_forall _ heps h_pointwise

end Prob
end PFunPDS

namespace PFunPDE

variable {X : Type u} {Y : Type v}

/-- **CR18 Equation 3.3**: in the joint experiment, the conditional distribution of the i-th
output `Yᵢ` given the full input history `Xⁱ` and the previous outputs `Yⁱ⁻¹` equals the
system's Def-3.18 behavior `p^S_{Yᵢ|XⁱYⁱ⁻¹}` — *independently of the environment*. The
environment's contribution to the conditioning event (`Q ω₂`, the queries `Xⁱ` produced from
`Yⁱ⁻¹`) is identical in numerator and denominator, so by independence it **cancels**; what
remains is the pure system ratio `Pr[outSeq S xⁱ = yⁱ] / Pr[outSeq S xⁱ⁻¹ = yⁱ⁻¹]`, which is
exactly `behaviorOf` (the conversion `behaviorOf_eq_cumulative_div`). This is why `S`'s
behavior is recovered in the experiment — provided we condition on `Xⁱ`. -/
theorem transcriptCond_eq_behaviorOf {Ω₁ : Type w} {Ω₂ : Type z}
    [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    (pS : Dist.ProbDist Ω₁) (pE : Dist.ProbDist Ω₂)
    (S : PFunPDS.RV Ω₁ X Y) {n : ℕ}
    (yi : Y) (xs : List.Vector X (n + 2)) (ys : List.Vector Y (n + 1))
    (Q : Ω₂ → Prop) (hQ : pE.val.mass Q ≠ 0)
    (hdef : (behaviorOf pS S (n + 1) (yi, xs, ys)).Dom) :
    (Dist.prodProbDist pS pE).val.mass (fun ω =>
          PFunPDS.outSeq S xs.toList ω.1 = (ys.toList ++ [yi]).map Part.some ∧ Q ω.2)
        / (Dist.prodProbDist pS pE).val.mass (fun ω =>
          PFunPDS.outSeq S xs.toList.dropLast ω.1 = ys.toList.map Part.some ∧ Q ω.2)
      = (behaviorOf pS S (n + 1) (yi, xs, ys)).get hdef := by
  rw [Dist.prodProbDist_val,
    Dist.mass_prod_and pS.val pE.val
      (fun ω₁ => PFunPDS.outSeq S xs.toList ω₁ = (ys.toList ++ [yi]).map Part.some) Q,
    Dist.mass_prod_and pS.val pE.val
      (fun ω₁ => PFunPDS.outSeq S xs.toList.dropLast ω₁ = ys.toList.map Part.some) Q,
    mul_div_mul_right _ _ hQ, behaviorOf_eq_cumulative_div pS S yi xs ys hdef]
  rfl

end PFunPDE

/-! ## CR18 §3.7.1 / Definition 3.22 — discrete games (monotone binary output)

A **game** is an `(X, Y × Bool)`-DDS whose binary output component is *monotone*: once the
"won" bit turns `true` it stays `true` (`aᵢ = 1 ⇒ aⱼ = 1` for `j ≥ i`). This is the
PFun-native form of Definition 3.22 on `PFunDDS.DDS`, continuing the §3.6/§3.7 PFun model.
(The older record-`DDS` formalization — winner Def 3.23, multi-games, Def 4.5/4.6 — lives
in `RandomSystems/CR18/Game.lean`.) Only the game is defined here. -/

namespace PFunDDS

/-- CR18 **Definition 3.22**: the **monotone binary output (MBO)** property is *simply a
property of a `List (Y × Bool)`* — its `Bool` projection is monotone (`Monotone`, with `Bool`'s
`false ≤ true`: once `1`, stays `1`). The "games" are the `List (Y × Bool)` restricted to this
monotone-`Bool` subset; nothing about a system yet. -/
def IsMBO {Y : Type v} (outs : List (Y × Bool)) : Prop :=
  Monotone fun i : Fin outs.length => (outs.get i).2

/-- The output history of a `(X, Y × Bool)`-DDS `g` along an in-domain input history `l`: the
list of `Y × Bool` outputs on the nonempty prefixes `l.take 1, …, l.take |l|` (each in the
domain by prefix-closure). This is the `List (Y × Bool)` to which `IsMBO` applies. -/
def outputHistory {X : Type u} {Y : Type v} (g : DDS X (Y × Bool))
    (l : List X) (hl : l ∈ dom g) : List (Y × Bool) :=
  List.ofFn fun i : Fin l.length =>
    output g (l.take (i.1 + 1))
      (prefix_closed g (List.take_prefix (i.1 + 1) l)
        (by rw [← List.length_pos_iff_ne_nil, List.length_take]; have := i.2; omega) hl)

/-- CR18 **Definition 3.22**: a `(X, Y × Bool)`-DDS *is a game* (DDG) when **every** output
history it produces is an MBO — i.e. all its outputs land in the monotone-`Bool` subset. -/
def DDS.IsGame {X : Type u} {Y : Type v} (g : DDS X (Y × Bool)) : Prop :=
  ∀ (l : List X) (hl : l ∈ dom g), IsMBO (outputHistory g l hl)

/-- CR18 **Definition 3.22**: a **deterministic discrete `(X, Y)`-game (DDG)** is the subtype of
`(X, Y × Bool)`-DDS whose output histories are MBO — exactly as a `DDS` is `Raw` carved out by
`Valid`. -/
abbrev DDG (X : Type u) (Y : Type v) : Type (max u v) := { g : DDS X (Y × Bool) // g.IsGame }

/-- **Support lemma forced by formalization; candidate for upstream.** A history
evaluator with a prefix-monotone Boolean component is a deterministic game. -/
theorem historyEvaluator_pair_isGame_of_monotone {X : Type u} {Y : Type v}
    (g : (l : List X) → l ≠ [] → Y) (b : List X → Bool)
    (hb : ∀ {l₁ l₂ : List X}, l₁ <+: l₂ → b l₁ ≤ b l₂) :
    (historyEvaluator (fun l hne => (g l hne, b l))).IsGame := by
  intro l hl
  dsimp [IsMBO, outputHistory]
  intro i j hij
  simp [historyEvaluator]
  apply hb
  exact (List.take_isPrefix_take).mpr (Or.inl (Nat.succ_le_succ hij))

end PFunDDS

namespace PFunPDS

/-- CR18 **Definition 3.22** (probabilistic): a **probabilistic discrete game (PDG)** is a PDS
ranging over games — a random variable valued in `PFunDDS.DDG` (the game subtype), exactly as a
PDS is a random variable valued in `DDS`. Being a game is the *codomain*, not a side predicate:
the exclusion to monotone-output systems already happened at the `DDS → DDG` level. -/
abbrev PDG (Ω : Type w) (X : Type u) (Y : Type v) : Type _ :=
  Dist.RV (Ω := Ω) (A := PFunDDS.DDG X Y)

end PFunPDS

/-- CR18 **Definition 3.22**, support-restricted PDS form (UPSTREAM-CANDIDATE): a raw
`PFunPDS X (Y × Bool)` is supported on deterministic games.

This is the side-predicate view of `PFunPDS.PDG`, useful when theorem infrastructure works over raw
representatives rather than the game subtype. It belongs with the carrier definitions: public
paper-facing statements should either use a `PDG` representative, construct this fact, or assume this
minimal predicate exactly where monotonicity is used. -/
def MonotoneMBO {X : Type u} {Y : Type v} (Shat : PFunPDS X (Y × Bool)) : Prop :=
  ∀ s ∈ Shat.support, s.IsGame

/-- Restricting the domain preserves a game's monotone binary output. -/
theorem isGame_filterDom {X : Type u} {Y : Type v}
    (P : List X → Prop) (hP : PrefixClosed P)
    {g : PFunDDS.DDS X (Y × Bool)} (h : g.IsGame) :
    (PFunDDS.filterDom P hP g).IsGame :=
  fun l hl => h l hl.1

/-- A common domain restriction preserves the monotone-MBO property. -/
theorem monotoneMBO_filterDom {X : Type u} {Y : Type v}
    (P : List X → Prop) (hP : PrefixClosed P)
    {S : PFunPDS X (Y × Bool)} (h : MonotoneMBO S) :
    MonotoneMBO (PFunPDS.filterDom P hP S) := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := Dist.mem_support_fTransform _ _ hs
  exact isGame_filterDom P hP (h s' hs')

/-- `[q]` only restricts the domain (`… ∧ length ≤ q`) and preserves outputs,
so a game stays a game under the query filter. -/
theorem isGame_filterQueries {X : Type u} {Y : Type v} (q : ℕ)
    {g : PFunDDS.DDS X (Y × Bool)} (h : g.IsGame) :
    (PFunDDS.filterQueries q g).IsGame :=
  isGame_filterDom (fun xs => xs.length ≤ q) (prefixClosed_length_le q) h

/-- Query filtering preserves the monotone-MBO property of a probabilistic game. -/
theorem monotoneMBO_filterQueries {X : Type u} {Y : Type v} (q : ℕ)
    {S : PFunPDS X (Y × Bool)} (h : MonotoneMBO S) :
    MonotoneMBO (⌈q⌉ S) :=
  monotoneMBO_filterDom (fun xs => xs.length ≤ q) (prefixClosed_length_le q) h

namespace PFunPDS

variable {X : Type u} {Y : Type v}

/-- Raw representative law of a probabilistic discrete game (UPSTREAM-CANDIDATE): forget the
`DDG` subtype at the deterministic layer and push the ambient experiment forward to a
`PFunPDS X (Y × Bool)`.

This is the bridge between the thesis/CR18 game carrier (`PDG`, a random variable into deterministic
games) and the existing raw bit-system kernels (`winProb`, `Γ`, `prewinBehavior`, etc.). -/
noncomputable def PDG.rawLaw {Ω : Type w} (p : Dist.ProbDist Ω) (G : PDG Ω X Y) :
    PFunPDS X (Y × Bool) :=
  Dist.fTransform (fun ω => (G ω).val) p.val

/-- The raw representative law of a `PDG` is a probability distribution. -/
theorem PDG.rawLaw_isProbDist {Ω : Type w} (p : Dist.ProbDist Ω) (G : PDG Ω X Y) :
    (PDG.rawLaw p G).isProbDist := by
  exact Dist.fTransform_isProbDist (fun ω => (G ω).val) p.property

/-- The raw representative law of a `PDG` is supported on games. -/
theorem PDG.rawLaw_monotoneMBO {Ω : Type w} (p : Dist.ProbDist Ω) (G : PDG Ω X Y) :
    MonotoneMBO (PDG.rawLaw p G) := by
  intro s hs
  unfold PDG.rawLaw at hs
  have hsub :
      (Dist.fTransform (fun ω => (G ω).val) p.val).support ⊆
        p.val.support.image (fun ω => (G ω).val) :=
    Finsupp.mapDomain_support
  rcases Finset.mem_image.mp (hsub hs) with ⟨ω, _hω, rfl⟩
  exact (G ω).property

end PFunPDS

/-! ## CR18 §3.7.1 / Def 3.23 — winners; §3.7.2 / Def 3.24 — distinguishers

Same discipline: a winner and a distinguisher are just (variants of) the existing environment
**function type** — no structures, no side predicates. -/

namespace PFunDDS

/-- CR18 **Definition 3.23**: a (deterministic) **winner** for an `(X, Y)`-game is a
`(Y, X)`-environment — it reads the game's *visible* `Y`-outputs and issues `X`-queries (the MBO
bit is hidden from it). So a winner *is* a `DDE X Y`; no new type. -/
abbrev Winner (X : Type u) (Y : Type v) : Type (max u v) := DDE X Y

/-- A distinguisher's verdict is **final**: once it emits a stop symbol `⊣ᵦ` (`Sum.inr b`) on
some output history, it emits the *same* verdict on every extension. A `DDE`'s stop `⊣` carries
no output and needs no such restriction; a `DDD` stops *with* a verdict bit, so the bit must be
well-defined (the interaction is over and the answer cannot change).

Read it as a shape constraint on each **run**: along one prefix-chain of output histories the
DDD emits a (possibly infinite) sequence of queries terminating in at most one final bit —
`StopFinal` is exactly that "ends in a single bit". It only constrains a single chain, so two
runs with different responses may end in different bits (that is the adaptivity, not a leak);
an infinite run that never stops defaults to verdict `0`. -/
def StopFinal {X : Type u} {Y : Type v} (d : List (Option Y) → X ⊕ Bool) : Prop :=
  ∀ {h h' : List (Option Y)}, h <+: h' → ∀ b : Bool, d h = Sum.inr b → d h' = Sum.inr b

/-- CR18 **Definition 3.24**: a (deterministic) discrete **distinguisher (DDD)** for
`(X, Y)`-systems is an environment with *two* stop symbols `⊣₀`, `⊣₁`: reading the output
history it either issues a query (`Sum.inl x`) or stops with a verdict bit (`Sum.inr b`). A
`DDE` carries one stop (`Option X`); a `DDD` carries two — directly the sum `X ⊕ Bool`, no
payload-carrying `Step` inductive. Because the stop *carries output*, a DDD is the subtype of
such environments whose verdict is final (`StopFinal`) — the restriction a `DDE` does not need. -/
abbrev DDD (X : Type u) (Y : Type v) : Type (max u v) :=
  { d : List (Option Y) → X ⊕ Bool // StopFinal d }

/-! ### Outcomes — pure reads over the generic transcript `tr` (Def 3.7)

The winner-vs-game and distinguisher-vs-system interactions are *not* new constructions: each
is the generic transcript `transcript` (Def 3.7) instantiated, with exactly one paper-mandated
projection on the environment. Winning / the output bit are then reads off that transcript. -/

/-- The winner's **view** of a game's output: a winner reads only `Y`, never the MBO bit — Def
3.23, "the MBO `aᵢ` is not returned to `w`". So as an environment for the game system
`g : DDS X (Y × Bool)` it is `w` precomposed with the `Y`-projection of the output history. This
is the *only* adapter; it feeds the **generic** transcript — there is no bespoke game transcript. -/
def winnerView {X : Type u} {Y : Type v} (w : Winner X Y) : DDE X (Y × Bool) :=
  fun h => w (h.map (Option.map Prod.fst))

/-- CR18 **Definition 3.23** winning. The winner-vs-game interaction *is* the generic transcript
`transcript g.1 (winnerView w)` (Def 3.7) at the winner's `Y`-view; it produces exactly Maurer's
`x₁,(y₁,a₁),x₂,(y₂,a₂),…`. **`w` wins `g`** iff some MBO bit is `1` — read straight off that
transcript's output projection (`↓ᵧ`). -/
def Wins {X : Type u} {Y : Type v} (w : Winner X Y) (g : DDG X Y) : Prop :=
  ∃ n, ∃ y : Y, (some (y, true) : Option (Y × Bool)) ∈ (transcript g.val (winnerView w) n)↓ᵧ

/-- The distinguisher as a plain environment: its two stop symbols `⊣₀,⊣₁` are *both* stops for
the interaction (Def 3.24), so as a `DDE` it forgets the verdict — `inl x ↦ query x`,
`inr _ ↦ stop`. The only adapter; it feeds the **generic** transcript. -/
def ddToDDE {X : Type u} {Y : Type v} (d : DDD X Y) : DDE X Y :=
  fun h => match d.val h with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- The induced environment stops exactly where the distinguisher emits a verdict. -/
theorem ddToDDE_eq_none_iff {X : Type u} {Y : Type v} {d : DDD X Y} {h : List (Option Y)} :
    ddToDDE d h = none ↔ ∃ b, d.val h = Sum.inr b := by
  unfold ddToDDE
  rcases hd : d.val h with x | b <;> simp

/-- The induced environment queries exactly where the distinguisher queries. -/
theorem ddToDDE_eq_some_iff {X : Type u} {Y : Type v} {d : DDD X Y} {h : List (Option Y)}
    {x : X} :
    ddToDDE d h = some x ↔ d.val h = Sum.inl x := by
  unfold ddToDDE
  rcases hd : d.val h with x' | b <;> simp

/-- CR18 **Definition 3.24** output ("the output of `d` for system `s`"). The
distinguisher-vs-system interaction *is* the generic transcript `transcript s (ddToDDE d)`
(Def 3.7) at `d`'s stop-or-query view; the **verdict bit** is the index of the stopping symbol —
`1` exactly when `d` emits `⊣₁` along that run, else `0` (covering both `⊣₀` and non-termination).
`StopFinal` makes the verdict unique. A read off the transcript, no new machinery. (Named
`verdict` to avoid the existing `PFunDDS.output`, the DDS output-at-history reader.) The verdict
*bit is 1* is a proposition — an `∃` over the run, exactly mirroring `Wins` — not a `Bool` forced
through classical `decide`; "bit is 0" is its negation. -/
def verdict {X : Type u} {Y : Type v} (d : DDD X Y) (s : DDS X Y) : Prop :=
  ∃ n, d.val ((transcript s (ddToDDE d) n)↓ᵧ) = Sum.inr true

end PFunDDS


end RandomSystems.CR18
