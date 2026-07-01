/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# CR18 §4.4 — Abstract Computational Problems and Reductions

This module develops §4.4 one subsection at a time. Currently **§4.4.2 Preliminaries** and
**§4.4.3** (Definition 4.2: the abstract problem).

## §4.4.2 Preliminaries — verbatim (anti-drift anchor)

> For the composition of functions `f` and `g` we write `gf` instead of `g ∘ f`. Hence we write,
> for example, `hgf(a)` instead of `h(g(f(a)))`. Sometimes we write simply `fa` instead of `f(a)`.
>
> For functions `fᵢ : Aᵢ → Bᵢ` (for `1 ≤ i ≤ k`), `(f₁,…,fₖ)` denotes the direct product of
> `f₁,…,fₖ`, i.e., the function `A₁ × ⋯ × Aₖ → B₁ × ⋯ × Bₖ` defined by
> `(f₁,…,fₖ)(a₁,…,aₖ) = (f₁(a₁),…,fₖ(aₖ))`.
>
> For functions `fᵢ : A → Bᵢ` (for `1 ≤ i ≤ k`), `[f₁,…,fₖ]` denotes the function
> `A → B₁ × ⋯ × Bₖ` defined by `[f₁,…,fₖ](a) = (f₁(a),…,fₖ(a))`.
>
> The function assigning to a list of real numbers their sum is denoted as `sum`. For example,
> `sum(3,4,5) = 12`. Similarly, for boolean-valued lists we denote by `∧` (or `∨`) the logical
> AND (or logical OR) of the values.
>
> For functions `f : A → B` and `g : A → B`, where a partial order `≤` is defined on `B`, we
> write `f ≤ g` to mean `∀a (f(a) ≤ g(a))`.

## Modeling

§4.4.2 introduces *no new objects* — only notation for standard function operations, every one of
which Lean already provides. So the faithful model is **not** to re-implement anything: we pin each
of Maurer's notations to its existing Lean realization and confirm the defining equation it states.
(Maurer's `(·)` and `[·]` collide with Lean's tuple/list syntax, so we use the Lean spellings
`Prod.map` and the pointwise pairing `fun a => (f a, g a)` rather than reusing that syntax.)

| Maurer | Lean (existing) |
| --- | --- |
| composition `gf` | `g ∘ f` (`Function.comp`) |
| direct product `(f₁,f₂)` | `Prod.map f₁ f₂` |
| tupling `[f₁,f₂]` | `fun a => (f₁ a, f₂ a)` |
| `sum` of a real list | `List.sum` |
| `∧` / `∨` of a boolean list | `List.all · id` / `List.any · id` |
| pointwise `f ≤ g` | the `Pi` order on `A → B` (`f ≤ g ↔ ∀ a, f a ≤ g a`) |
-/

namespace RandomSystems.CR18

universe u v w

variable {A B C : Type*}

/-- Composition `gf` is `g ∘ f`: `(g ∘ f)(a) = g(f(a))`. -/
example (f : A → B) (g : B → C) (a : A) : (g ∘ f) a = g (f a) := rfl

/-- Direct product `(f₁,f₂) = Prod.map f₁ f₂`: `(f₁,f₂)(a₁,a₂) = (f₁ a₁, f₂ a₂)` (the `k = 2`
case; larger `k` is the same by nesting). -/
example {A₁ A₂ B₁ B₂ : Type*} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (a₁ : A₁) (a₂ : A₂) :
    Prod.map f₁ f₂ (a₁, a₂) = (f₁ a₁, f₂ a₂) := rfl

/-- Tupling `[f₁,f₂] = fun a => (f₁ a, f₂ a)`: `[f₁,f₂](a) = (f₁ a, f₂ a)`. -/
example {B₁ B₂ : Type*} (f₁ : A → B₁) (f₂ : A → B₂) (a : A) :
    (fun x => (f₁ x, f₂ x)) a = (f₁ a, f₂ a) := rfl

/-- `sum` of a list of reals is `List.sum`: `sum(3,4,5) = 12` (the text's example). -/
example : ([3, 4, 5] : List ℝ).sum = 12 := by norm_num

/-- `∧` of a boolean list is the logical AND of its values (`List.all · id`). -/
example : [true, true, false].all id = false := by decide

/-- `∨` of a boolean list is the logical OR of its values (`List.any · id`). -/
example : [true, true, false].any id = true := by decide

/-- Pointwise order: for `f g : A → B` with `B` (pre)ordered, `f ≤ g` means `∀ a, f a ≤ g a` —
exactly Lean's `Pi` order, definitionally. -/
example [Preorder B] (f g : A → B) : f ≤ g ↔ ∀ a, f a ≤ g a := Iff.rfl

/-! ## §4.4.3 Problems, Solvers, and Performance — verbatim (anti-drift anchor)

> In a theory of computation, at the most abstract level one considers two types of objects.
>
> * **Problems** are objects that should be computed or solved.
> * **Solvers** are objects that compute or solve a problem.
>
> **Definition 4.2.** A problem `p` is (an object) equipped with a set `Σ_p` of solvers, a
> partially ordered set `(Ω_p; ≤)` of performance values, and a performance function
> `p : Σ_p → Ω_p` assigning a performance value `p(s)` to every solver `s ∈ Σ_p`. A solver `s`
> for which `p(s) ≥ a` for `a ∈ Ω_p` is called an `a`-solver for `p`.
>
> [Performance values are often real numbers (`Ω_p ⊆ ℝ`) — e.g. a success probability or a
> distinguishing advantage — but more general sets are allowed; games use `[0,1]`, distinction
> problems `[−1,1]`. Footnote 14: here `a ≤ b` means the value `b` is (in some sense) at least as
> good as `a`.]

### Modeling

A problem is *an object equipped with* `(Σ_p, Ω_p, p̄)`, and the problem object `p` and its
**performance function** `p̄ : Σ_p → Ω_p` are *distinct*: `p̄` is what you get by running solvers
against `p` (e.g. `p` is a distinction pair `⟨S₀|S₁⟩` and `p̄(D)` is `D`'s advantage; `p` is a game
`G` and `p̄(W)` is `W`'s winning probability). We render "equipped with" as a **typeclass**
`Problem P Solver Perf` on the problem-object type `P` — the one place a bundle is unavoidable,
because it introduces *associated data* (`Solver = Σ_p`, `Perf = Ω_p`) and a function, which no
predicate/subtype/product can. `Perf` carries Lean's existing `PartialOrder`; the single field
`perf` is `p̄` (`perf p : Solver → Perf`, `perf p s = p̄(s)`).

This is exactly the compatibility mechanism: a concrete type — a search problem, a distinction
pair, a game — *becomes* a Def-4.2 problem by providing one `instance` (its `Σ`, its `Ω`, and its
performance function `p̄`), and then lives under the one abstract theory. The §4.4.4 bound
`p̄ ≤ ε` is the §4.4.2 pointwise order on `Solver → Perf` applied to `perf p`. -/

-- §4.4.3 onward is classical / measure-theoretic; rather than annotate each definition, the
-- section is `noncomputable`.
noncomputable section

/-- CR18 **Definition 4.2**: a **problem** is an object `p : P` *equipped with* a solver set
`Solver` (`= Σ_p`), a **partially ordered** performance set `Perf` (`= Ω_p`, with `[PartialOrder
Perf]` a standing condition — Def 4.2's `(Ω_p; ≤)`), and a **performance function** `perf` (`= p̄`).
For a problem object `p`, `perf p : Solver → Perf` is its performance function `p̄`, and
`perf p s = p̄(s)`. The problem object `p` and its performance function `p̄ = perf p` are
deliberately distinct. `Solver` is an `outParam` — determined by the problem type `P` (one
canonical solver set per problem type), so `Problem.perf p` needs no `Solver` hint. -/
class Problem (P : Type u) (Solver : outParam (Type v)) (Perf : Type w) [PartialOrder Perf] where
  /-- The performance function `p̄`: `perf p s` is the performance `p̄(s)` of solver `s` on the
  problem object `p`. -/
  perf : P → Solver → Perf

/-- Maurer's notation `p̄` for a problem's performance function `Problem.perf p`. -/
scoped postfix:max "̄" => Problem.perf

/-- CR18 Definition 4.2, the **`a`-solver** notion: a solver `s` is an `a`-solver for problem `p`
when its performance is at least `a`, i.e. `p̄(s) ≥ a` — written `a ≤ perf p s`, using the partial
order on the performance set. -/
def Problem.IsASolver {P : Type u} {Solver : Type v} {Perf : Type w} [PartialOrder Perf]
    [Problem P Solver Perf] (p : P) (a : Perf) (s : Solver) : Prop :=
  a ≤ p̄ s

/-! ## §4.4.4 Upper Bounds on Performance — verbatim (anti-drift anchor)

> An important goal in cryptography and complexity theory is to prove that a certain problem `p`
> is hard (e.g., the problem of breaking a cryptosystem). Ideally, one wants to prove an upper
> bound on the performance of any solver for `p`, i.e., a statement of the form `∀s p̄(s) ≤ ε` for
> some small `ε`. This can also be written simply as
>
> `p̄ ≤ ε`,
>
> where `ε` is understood as the constant function `Σ_p → Ω_p` mapping every solver to the value
> `ε`. (Note that usually `ε` is real-valued.) Such a statement is often called
> *information-theoretic* or *unconditional* since it holds for any solver. In particular, it does
> not depend on the implementation complexity.
>
> However, since for a usual computational problem `p` there always exists a (possibly inefficient)
> solver that solves the problem well (i.e., with high performance), one proves a weaker statement
> where the upper bound depends on the performance function `q̄` of another problem `q`. Such a
> statement is called a *reduction*. More generally, `p` can also be upper bounded in terms of the
> performance functions `q̄ᵢ` (`i = 1, …, k`) of several problems.

### The notation `p̄ ≤ ε`

The nice bit: a performance *value* `ε : Ω_p` is read as the *constant function* `fun _ => ε`, and
`p̄ ≤ ε` is then the §4.4.2 pointwise order on `Σ_p → Ω_p`. We write it `p̄ ≤ᶜ ε` (the `ᶜ` marks the
constant-function coercion Lean will not insert silently); it unfolds *definitionally* to
`∀ s, p̄ s ≤ ε`, the information-theoretic bound. A *reduction* bound `p̄ ≤ q̄` (function ≤ function)
needs no new notation — it is the plain pointwise order (formalised at Def 4.3, §4.4.5). -/

/-- CR18 §4.4.4 notation: `p̄ ≤ᶜ ε` is Maurer's `p̄ ≤ ε` — the performance function `p̄` bounded by
the *constant* `ε`, i.e. `p̄ ≤ (fun _ => ε)`. -/
scoped notation:50 phat:51 " ≤ᶜ " ε:51 => phat ≤ Function.const _ ε

/-- CR18 §4.4.4: the constant bound `p̄ ≤ ε` *is* the information-theoretic statement
`∀ s, p̄ s ≤ ε` — definitionally, via the §4.4.2 pointwise order. -/
theorem le_const_iff {Solver : Type*} {Perf : Type*} [Preorder Perf]
    {phat : Solver → Perf} {ε : Perf} : (phat ≤ᶜ ε) ↔ ∀ s, phat s ≤ ε :=
  Iff.rfl

/-- An information-theoretic upper bound on a problem `p`: `p̄ ≤ ε` says every solver's performance
is at most `ε` (no solver does better than `ε`). -/
example {P : Type u} {Solver : Type v} {Perf : Type w} [PartialOrder Perf]
    [Problem P Solver Perf] (p : P) (ε : Perf) :
    (p̄ ≤ᶜ ε) ↔ ∀ s, p̄ s ≤ ε :=
  le_const_iff

/-! ## §4.4.5 The Reduction Concept — verbatim (anti-drift anchor)

> An important concept in computer science is to use a solver `s` for a problem `p` with
> performance at least `a` (i.e., `p̄(s) ≥ a`) to construct a solver `s′` for a problem `q` with
> performance at least `a′` (i.e., `q̄(s′) ≥ a′`), where `s′ = ρ(s)` for a function `ρ : Σ_p → Σ_q`
> (called the **reduction function**) and where `a′ = τ(a)` for a ≤-respecting function
> `τ : Ω_p → Ω_q` (called the **performance translation function**). This can be summarized by the
> function inequality
>
> `τ p̄ ≤ q̄ ρ`     (4.1)
>
> which states that for any `a`-solver `s` for `p`, `ρ(s)` is a `(τ(a))`-solver for `q`:
> `∀ s ∈ Σ_p : τ p̄(s) ≤ q̄ ρ(s)`. In the following, performance translation functions will tacitly
> be assumed to be ≤-respecting.
>
> A special case of (4.1) is `p̄ ≤ q̄ ρ`, where `τ` is the identity function, i.e., `ρ` transforms a
> solver for `q` into an equally good solver for `p`. Another special case of (4.1) is `τ p̄ ≤ q̄`,
> where `ρ` is the identity function, i.e., every solver for `p` is also a solver for `q` with
> performance related via the function `τ`.
>
> [Footnote 15: `τ` is ≤-respecting if `a ≤ b ⇒ τ(a) ≤ τ(b)`, i.e., a better solver for `s` does
> not result in a worse solver for `s′`.]
>
> **Definition 4.3.** For functions `ρ` and `τ` satisfying (4.1), `ρ` is called a **τ-reduction of
> problem `q` to problem `p`**.

Modeling: `τ p̄` and `q̄ ρ` are the §4.4.2 composition `gf = g ∘ f`; (4.1) is the §4.4.2 pointwise
order on `Σ_p → Ω_q`; `p̄ = Problem.perf p`. Def 4.3 names an **object**, not a proposition: "ρ is
*called* a τ-reduction", so a τ-reduction *is the reduction function* `ρ` — modelled as the subtype
of functions carved out by (4.1). The ≤-respecting `τ` (`Monotone τ`, footnote 15) is the tacit
standing assumption on translations, supplied where a reduction is used. -/

section Reductions

-- Shared once: two problems `p : P`, `q : Q` with their solver/performance sets and a translation
-- `τ`. Each declaration below auto-includes only the binders it actually uses.
variable {P Sp Ωp Q Sq Ωq : Type*} [PartialOrder Ωp] [Problem P Sp Ωp]
  [PartialOrder Ωq] [Problem Q Sq Ωq] {p : P} {q : Q} {τ : Ωp → Ωq}

/-- CR18 **Definition 4.3**: a **τ-reduction of `q` to `p`** is a **reduction function**
`ρ : Σ_p → Σ_q` satisfying the function inequality (4.1) `τ ∘ p̄ ≤ q̄ ∘ ρ`. The paper says "`ρ` is
called a τ-reduction", so it *is* the function `ρ` carved out by (4.1) — the subtype below — and a
reduction **applies as that function**: `r s` is the `q`-solver built from the `p`-solver `s` (via
the `CoeFun` below; `r.2` is the (4.1) certificate). `τ : Ω_p → Ω_q` is the **performance
translation**, tacitly ≤-respecting (`Monotone τ`, footnote 15). Special cases: `τ = id` gives
`p̄ ≤ q̄ ∘ ρ`; `ρ = id` (so `Σ_p = Σ_q`) gives `τ ∘ p̄ ≤ q̄`. -/
abbrev Reduction (p : P) (q : Q) (τ : Ωp → Ωq) : Type _ :=
  { ρ : Sp → Sq // τ ∘ p̄ ≤ q̄ ∘ ρ }

/-- A τ-reduction *is* its reduction function `ρ`: `r s = ρ(s)`, the `q`-solver built from the
`p`-solver `s`. (So one writes `r s`, never `r.1 s`.) -/
instance : CoeFun (Reduction p q τ) (fun _ => Sp → Sq) := ⟨Subtype.val⟩

/-- CR18 (4.1) per solver: a τ-reduction `r` of `q` to `p` sends every solver `s` for `p` to the
solver `r s` for `q` with `τ`-translated performance — `τ (p̄ s) ≤ q̄ (r s)`. (So an `a`-solver `s`
for `p` gives a `(τ a)`-solver `r s` for `q`.) -/
theorem Reduction.spec (r : Reduction p q τ) (s : Sp) :
    τ (p̄ s) ≤ q̄ (r s) :=
  r.2 s

/-! ## §4.4.6 Interpretations of Reductions — verbatim (anti-drift anchor)

> The usefulness and strength of a reduction is determined by two factors:
> • by how much `ρ` blows up the complexity of a solver `s` (i.e., reduces the efficiency), and
> • by how much `τ` reduces the performance. (In some cases, `τ` can also increase the
>   performance.)
>
> Inequality (4.1) can be interpreted in two different ways: as implying a lower bound on `q̄` (in
> terms of `p̄`), or as implying an upper bound on `p̄` (in terms of `q̄`). For the latter
> interpretation it is convenient to write the inequality in a different form, by considering a
> ≤-respecting function `λ : Ω_q → Ω_p` satisfying
>
> `id ≤ λ τ`     (4.2)
>
> (i.e., `a ≤ λτ a` for all `a ∈ Ω_q`). If `Ω_p` and `Ω_q` are intervals of `ℝ` and if `τ` is
> strictly ≤-respecting, then one can choose `λ = τ⁻¹` (i.e., `id = λ τ`). We have
>
> `τ p̄ ≤ q̄ ρ  ⟹  λτ p̄ ≤ λ q̄ ρ  ⟹  p̄ ≤ λ q̄ ρ`     (4.3)
>
> where in the first step we have used the ≤-respecting property of `λ`. If equality holds in
> (4.2), then (4.3) and (4.1) are (logically) equivalent. Inequality (4.3) is the form of a
> reduction statement used to state an upper bound on the performance of any solver for `p`, in
> terms of the function `q̄`.

Modeling: the two factors are prose (complexity is not in this abstract model). The lower-bound
reading *is* (4.1) — `Reduction.spec`. Formalized below: (4.3) the upper-bound interpretation
(`Reduction.upperBound`); the equivalence (4.1) ⟺ (4.3) under equality in (4.2)
(`reduction_iff_upperBound`); and the `λ = τ⁻¹` case (`reduction_iff_upperBound_of_orderIso`).
`λ` is spelled `lam` (`λ` is Lean's binder); `λ τ = lam ∘ τ`, (4.2) is `id ≤ lam ∘ τ`, and `≤`/`∘`
are the §4.4.2 pointwise order / composition. -/

/-- CR18 §4.4.6 inequality **(4.3)**, the **upper-bound interpretation** of a reduction: for a
≤-respecting `lam : Ω_q → Ω_p` (`Monotone`) with `id ≤ lam ∘ τ` (4.2), a τ-reduction `r` of `q` to
`p` bounds `p`'s performance in terms of `q`'s — `p̄ ≤ lam ∘ q̄ ∘ r`. Derivation: `τ∘p̄ ≤ q̄∘r`
⟹ `lam∘τ∘p̄ ≤ lam∘q̄∘r` (`lam` ≤-respecting) ⟹ `p̄ ≤ lam∘q̄∘r` (using `id ≤ lam∘τ`). When
`lam = τ⁻¹` (so equality in (4.2)), (4.3) ⟺ (4.1). -/
theorem Reduction.upperBound (r : Reduction p q τ) {lam : Ωq → Ωp} (lam_mono : Monotone lam)
    (id_le_lam_tau : id ≤ lam ∘ τ) : p̄ ≤ lam ∘ q̄ ∘ ⇑r :=
  -- `r.spec s : τ (p̄ s) ≤ q̄ (r s)` is (4.1) at solver `s`;
  -- `id_le_lam_tau (p̄ s) : p̄ s ≤ lam (τ (p̄ s))` is (4.2) at `p̄ s`.
  fun s => le_trans (id_le_lam_tau (p̄ s)) (lam_mono (r.spec s))

/-- CR18 §4.4.6: **when equality holds in (4.2)** — `lam` a two-sided inverse of `τ`, both
≤-respecting (`λ = τ⁻¹`) — the reduction inequality (4.1) and the upper-bound inequality (4.3) are
*logically equivalent*, for any candidate reduction function `ρ`. (`→` is (4.3), using
`lam ∘ τ = id`; `←` pushes back through `τ`, using `τ ∘ lam = id`.) -/
theorem reduction_iff_upperBound {lam : Ωq → Ωp} (τ_mono : Monotone τ) (lam_mono : Monotone lam)
    (lam_comp_tau : lam ∘ τ = id) (tau_comp_lam : τ ∘ lam = id) {ρ : Sp → Sq} :
    (τ ∘ p̄ ≤ q̄ ∘ ρ) ↔ (p̄ ≤ lam ∘ q̄ ∘ ρ) := by
  simp only [Pi.le_def, Function.comp_apply]
  constructor
  · intro four_one s
    simpa [show lam (τ (p̄ s)) = p̄ s from congrFun lam_comp_tau (p̄ s)] using lam_mono (four_one s)
  · intro four_three s
    simpa [show τ (lam (q̄ (ρ s))) = q̄ (ρ s) from congrFun tau_comp_lam (q̄ (ρ s))]
      using τ_mono (four_three s)

/-- CR18 §4.4.6, the **`λ = τ⁻¹` case**: when the performance translation is an order isomorphism
`e : Ω_p ≃o Ω_q` (the paper's "`τ` strictly ≤-respecting between intervals of `ℝ`"), one takes
`λ = e⁻¹ = e.symm`, equality holds in (4.2), and (4.1) and (4.3) are equivalent. -/
theorem reduction_iff_upperBound_of_orderIso (e : Ωp ≃o Ωq) {ρ : Sp → Sq} :
    (⇑e ∘ p̄ ≤ q̄ ∘ ρ) ↔ (p̄ ≤ ⇑(e.symm) ∘ q̄ ∘ ρ) :=
  reduction_iff_upperBound (τ := ⇑e) (lam := ⇑(e.symm))
    e.monotone e.symm.monotone (by ext a; simp) (by ext a; simp)

end Reductions

/-- CR18 §4.4.6, the paper's **"`Ω_p`, `Ω_q` intervals of `ℝ`, `τ` strictly ≤-respecting"** case,
made concrete: when the performance sets are *linearly* ordered and `τ` is `StrictMono` and onto,
`τ` is an order isomorphism (`StrictMono.orderIsoOfSurjective`), so `λ = τ⁻¹` exists and (4.1) ⟺
(4.3). (This is `reduction_iff_upperBound_of_orderIso` with the iso built from strict monotonicity;
`[LinearOrder Ω_p]` supplies the `PartialOrder` the `Problem` instance needs.) -/
theorem reduction_iff_upperBound_of_strictMono {P Sp Ωp Q Sq Ωq : Type*}
    [LinearOrder Ωp] [LinearOrder Ωq] [Problem P Sp Ωp] [Problem Q Sq Ωq]
    (p : P) (q : Q) {τ : Ωp → Ωq} (τ_strictMono : StrictMono τ)
    (τ_surjective : Function.Surjective τ) {ρ : Sp → Sq} :
    (τ ∘ p̄ ≤ q̄ ∘ ρ) ↔
      (p̄ ≤ ⇑(StrictMono.orderIsoOfSurjective τ τ_strictMono τ_surjective).symm ∘ q̄ ∘ ρ) :=
  reduction_iff_upperBound_of_orderIso
    (StrictMono.orderIsoOfSurjective τ τ_strictMono τ_surjective)

/-! ## §4.4.7 Complexity-Theoretic Interpretation — verbatim (anti-drift anchor)

> This subsection is not needed for understanding the rest of the course. […] assume that all
> problems we consider have the same solver set `Σ` and that we have fixed a computational model
> with a complexity notion assigning to every solver `s ∈ Σ` a complexity value `γ(s)` in some
> domain `Γ` of complexity values, for example `Γ = ℕ`. […] We can then associate with a
> complexity value `c` the class `Σ_c` of all solvers with at most that complexity:
>
> `Σ_c = { s | γ(s) ≤ c }`.
>
> We also consider a reduction `ρ : Σ → Σ`. Now, one particular interpretation of abstract
> reductions is that, formally, the (derived) solver set `Σ'` is the set `Γ` of complexity values,
> and the (derived) performance function `p'` is a function `Γ → Ω` mapping complexities to
> performance and assigning to a complexity value `c` the best achievable performance for any
> solver with complexity at most `c`:
>
> `p'(c) = sup { p̄(s) | s ∈ Σ_c }`.
>
> Moreover, the (derived) reduction function `ρ'` is a function `Γ → Γ` mapping complexities to
> complexities. A complexity value `c` is mapped to the maximal possible complexity of a solver
> resulting from applying the reduction `ρ` to any solver with complexity at most `c`:
>
> `ρ'(c) = sup { γ(ρ(s)) | s ∈ Σ_c }`.
>
> We do not make this more formal but point out that a computational model would have to come with
> an exact description of the function `ρ'` […]. This is very tedious, and to some extent
> arbitrary, already for simple computational models. […]

Modeling (tight, exactly as written): `γ : Σ → Γ` is the complexity function; `Σ_c` the complexity
class; `p'`, `ρ'` the derived performance / reduction. `sup { f s | s ∈ Σ_c }` is `sSup (f '' Σ_c)`.
The paper itself stops here ("we do not make this more formal"), so there are no theorems — only
the derived objects. The interpretation is that `(Γ, Ω, p')` is the derived (Def 4.2) problem over
the complexity domain and `ρ'` its reduction. (`Σ` is `S` in code — `Σ` is Lean's Sigma binder.) -/

section ComplexityInterpretation

variable {S Γ : Type*} [LE Γ] (γ : S → Γ)

/-- §4.4.7: the **complexity class** `Σ_c = { s | γ(s) ≤ c }` — the solvers of complexity at most
`c`, for a complexity function `γ : Σ → Γ`. -/
def complexityClass (c : Γ) : Set S := {s | γ s ≤ c}

variable {P Ω : Type*} [PartialOrder Ω] [SupSet Ω] [Problem P S Ω]

/-- §4.4.7: the **derived performance function** `p'(c) = sup { p̄(s) | s ∈ Σ_c }` — the best
achievable performance with complexity at most `c`. A function `Γ → Ω` over the complexity domain
(the derived solver set is `Γ`). -/
def derivedPerf (p : P) : Γ → Ω :=
  fun c => sSup (p̄ '' complexityClass γ c)

variable [SupSet Γ]

/-- §4.4.7: the **derived reduction function** `ρ'(c) = sup { γ(ρ(s)) | s ∈ Σ_c }` — the maximal
complexity of a solver obtained by applying the reduction `ρ : Σ → Σ` to any solver of complexity
at most `c`. A function `Γ → Γ`. -/
def derivedReduction (ρ : S → S) : Γ → Γ :=
  fun c => sSup ((fun s => γ (ρ s)) '' complexityClass γ c)

end ComplexityInterpretation

/-! ## §4.4.8 Composition of Reductions — verbatim (anti-drift anchor)

> Reductions can be composed:
>
> **Lemma 4.5.** `τ p̄ ≤ q̄ ρ ∧ τ' q̄ ≤ r̄ ρ' ⟹ τ' τ p̄ ≤ r̄ ρ' ρ`.
>
> Proof. Composing both sides of `τ p̄ ≤ q̄ ρ` with (the ≤-respecting function) `τ'` on the left
> side results in `τ' τ p̄ ≤ τ' q̄ ρ` since `τ'` is ≤-respecting. Composing both sides of
> `τ' q̄ ≤ r̄ ρ'` with `ρ` on the right side results in `τ' q̄ ρ ≤ r̄ ρ' ρ`. Combining the two
> inequalities yields `τ' τ p̄ ≤ r̄ ρ' ρ`. ∎
>
> Reduction statements of the form (4.3) also compose:
>
> **Lemma 4.6.** `p̄ ≤ λ q̄ ρ ∧ q̄ ≤ λ' r̄ ρ' ⟹ p̄ ≤ λ λ' r̄ ρ' ρ`.

Modeling: both are **lemmas** (theorems) — the composition of two reduction *inequalities*. Lemma
4.5 (`reduction_comp`) composes two (4.1)-form reductions into the `(τ'∘τ)`-reduction with function
`ρ'∘ρ`, needing `τ'` ≤-respecting; Lemma 4.6 (`upperBound_comp`) composes two (4.3)-form bounds,
needing `λ` ≤-respecting. Each is a single `le_trans`, exactly the paper's argument (`λ` is `lam`). -/

section Composition

variable {P Sp Ωp Q Sq Ωq R Sr Ωr : Type*}
  [PartialOrder Ωp] [Problem P Sp Ωp] [PartialOrder Ωq] [Problem Q Sq Ωq]
  [PartialOrder Ωr] [Problem R Sr Ωr]
  {p : P} {q : Q} {r : R} {τ : Ωp → Ωq} {τ' : Ωq → Ωr}

/-- CR18 **Lemma 4.5** (reductions compose): from `τ ∘ p̄ ≤ q̄ ∘ ρ` (`ρ` a τ-reduction of `q` to
`p`) and `τ' ∘ q̄ ≤ r̄ ∘ ρ'` (`ρ'` a τ'-reduction of `r` to `q`), with `τ'` ≤-respecting, follows
`(τ' ∘ τ) ∘ p̄ ≤ r̄ ∘ (ρ' ∘ ρ)` — i.e. `ρ' ∘ ρ` is a `(τ'∘τ)`-reduction of `r` to `p`. -/
theorem reduction_comp {ρ : Sp → Sq} {ρ' : Sq → Sr} (τ'_mono : Monotone τ')
    (p_reduction : τ ∘ p̄ ≤ q̄ ∘ ρ) (q_reduction : τ' ∘ q̄ ≤ r̄ ∘ ρ') :
    (τ' ∘ τ) ∘ p̄ ≤ r̄ ∘ (ρ' ∘ ρ) :=
  -- `τ'_mono (p_reduction s) : τ' (τ (p̄ s)) ≤ τ' (q̄ (ρ s))`;
  -- `q_reduction (ρ s)       : τ' (q̄ (ρ s)) ≤ r̄ (ρ' (ρ s))`.
  fun s => le_trans (τ'_mono (p_reduction s)) (q_reduction (ρ s))

/-- CR18 **Lemma 4.6** (upper-bound (4.3) forms compose): from `p̄ ≤ lam ∘ q̄ ∘ ρ` and
`q̄ ≤ lam' ∘ r̄ ∘ ρ'` (with `lam` ≤-respecting) follows `p̄ ≤ lam ∘ lam' ∘ r̄ ∘ (ρ' ∘ ρ)`. -/
theorem upperBound_comp {lam : Ωq → Ωp} {lam' : Ωr → Ωq} {ρ : Sp → Sq} {ρ' : Sq → Sr}
    (lam_mono : Monotone lam) (p_bound : p̄ ≤ lam ∘ q̄ ∘ ρ) (q_bound : q̄ ≤ lam' ∘ r̄ ∘ ρ') :
    p̄ ≤ lam ∘ lam' ∘ r̄ ∘ (ρ' ∘ ρ) :=
  -- `p_bound s : p̄ s ≤ lam (q̄ (ρ s))`;  `lam_mono (q_bound (ρ s)) : lam (q̄ (ρ s)) ≤ lam (lam' (r̄ (ρ' (ρ s))))`.
  fun s => le_trans (p_bound s) (lam_mono (q_bound (ρ s)))

end Composition

/-! ## §4.4.9 Generalized Reductions — verbatim (anti-drift anchor)

> A reduction statement `τ p̄ ≤ q̄ ρ` can be generalized by letting the construction make use of a
> list `s = (s₁,…,sₙ)` of solvers, one for each problem in a list `p = (p₁,…,pₙ)` of problems.
> Letting `τ` be a ≤-respecting function `τ : Ωp₁ × ⋯ × Ωpₙ → Ωq` and `ρ : Σp₁ × ⋯ × Σpₙ → Σq`,
> inequality (4.1) generalizes to `τ(p̄₁(s₁),…,p̄ₙ(sₙ)) ≤ q̄(ρ(s₁,…,sₙ))` for all `(s₁,…,sₙ)`, or
> equivalently the function inequality `τ p̄ ≤ q̄ ρ` (4.4). [Footnote 18: `τ` is ≤-respecting iff
> `∀i (aᵢ ≤ bᵢ) ⟹ τ(a₁,…,aₙ) ≤ τ(b₁,…,bₙ)`.]
>
> A reduction `p̄ ≤ λ q̄ ρ` can also be generalized by replacing `q` by a list `q = (q₁,…,qₖ)` with
> the same solver set `Σ`, `ρ` by a list `[ρ₁,…,ρₖ]` with `ρᵢ : Σ → Σqᵢ`, and `λ` by a ≤-respecting
> `λ : Ωq₁ × ⋯ × Ωqₖ → Ωp`: `p̄(s) ≤ λ(q̄₁(ρ₁(s)),…,q̄ₖ(ρₖ(s)))` for all `s`, equivalently
> `p̄ ≤ λ q̄ρ` (4.5), where `λ q̄ρ = λ ∘ (q̄₁,…,q̄ₖ) ∘ [ρ₁,…,ρₖ]`. A typical choice of `λ` is the
> sum. Composition statements for generalized reductions follow similarly to Lemma 4.6.

Modeling — **the generalization is free**: a *list of problems is a product problem*. The clever
notation is the Pi type `∀ i` (the index `i` ranges over the list `1,…,n`): the tuple of solvers is
`∀ i, S i`, the product performance set `∀ i, Ω i` carries the §4.4.2 product order (`Pi`), and the
**direct product** `(p̄₁,…,p̄ₙ)` is the product problem's performance — `(p̄) s i = (p i)̄ (s i)`. So
the *same* `p̄` postfix and the *same* `Reduction p q τ` express (4.4) (product on the `p`-side), and
`p̄ ≤ lam ∘ q̄ ∘ tupling ρ` expresses (4.5) (product `q̄` + the §4.4.2 tupling `[ρ₁,…,ρₖ]`). Footnote
18's ≤-respecting `τ` is exactly `Monotone τ` for the Pi order. Consequently `reduction_comp`,
`upperBound_comp`, `Reduction.upperBound`, … apply to product problems *unchanged* (they are generic
over `Problem`), which is the paper's "composition statements follow similarly to Lemma 4.6". -/

section GeneralizedReductions

variable {ι : Type*} {P S Ω : ι → Type*} [∀ i, PartialOrder (Ω i)]
  [∀ i, Problem (P i) (S i) (Ω i)]

/-- §4.4.9: a **list/family of problems is one product problem**. For problems `(p i)_{i}` with
solver sets `S i` and performance sets `Ω i`, the product has solver set `∀ i, S i` (the tuple of
solvers), performance set `∀ i, Ω i` (the §4.4.2 product order), and performance the **direct
product** `(p̄₁,…,p̄ₙ)`. This makes a *generalized* reduction (4.4) `τ ∘ p̄ ≤ q̄ ∘ ρ` literally a
*basic* `Reduction` at the product problem, so all the reduction lemmas apply unchanged. -/
instance instProblemPi : Problem (∀ i, P i) (∀ i, S i) (∀ i, Ω i) where
  perf p s i := Problem.perf (p i) (s i)

/-- §4.4.9 (4.4): the product problem's performance is the **direct product** `(p̄₁,…,p̄ₙ)` —
`(p̄) s i = (p i)̄ (s i)`, the `i`-th problem's performance on the `i`-th solver. -/
@[simp] theorem perf_pi (p : ∀ i, P i) (s : ∀ i, S i) (i : ι) :
    (Problem.perf p s : ∀ i, Ω i) i = Problem.perf (p i) (s i) := rfl

/-- §4.4.9: footnote 18 — a ≤-respecting multi-argument `τ` is exactly `Monotone τ` for the Pi
order: `Monotone τ` *is* `(∀ i, a i ≤ b i) → τ a ≤ τ b`, since the Pi order `a ≤ b` unfolds to
`∀ i, a i ≤ b i`. -/
theorem monotone_iff_forall_le {Ωq : Type*} [Preorder Ωq] {τ : (∀ i, Ω i) → Ωq} :
    Monotone τ ↔ ∀ ⦃a b : ∀ i, Ω i⦄, (∀ i, a i ≤ b i) → τ a ≤ τ b :=
  Iff.rfl

/-- §4.4.9 (4.5): the **tupling** `[ρ₁,…,ρₖ]` of a family `ρ : ∀ i, A → B i` (the §4.4.2 tupling
generalized): `tupling ρ a i = ρ i a`. The generalized (4.5) reduction is the basic (4.3) bound
`p̄ ≤ lam ∘ q̄ ∘ tupling ρ`, with `q̄` the product performance and `lam : (∀ i, Ωqᵢ) → Ωp`. -/
def tupling {A : Type*} {B : ι → Type*} (ρ : ∀ i, A → B i) : A → (∀ i, B i) :=
  fun a i => ρ i a

end GeneralizedReductions

/-! ## §4.4.10 Worst-Case Problems — verbatim (anti-drift anchor)

> **Definition 4.4.** For a set `P` of problems with the same solver set `Σ` and the same
> performance set `Ω`, where `Ω ⊆ ℝ`, the **worst-case problem**, denoted also as `P`, is the
> problem whose performance function `P : Σ → ℝ` is defined as follows: the performance of a solver
> `s` is the **worst** performance for any problem in `P`:
>
> `P(s) = inf { p̄(s) | p ∈ P }`.

Modeling: the worst-case performance is the **infimum** over the set — `⨅ p ∈ ps, p̄(s)` (needs
`[InfSet Ω]`; the paper's `Ω ⊆ ℝ`). It is the *dual* of §4.4.7's `sup`. Def 4.4 says the worst-case
*is the problem* whose performance is this, so a set of problems *is* its worst-case problem
(`Problem (Set P)`), `(ps : Set P)̄ = worstCasePerf ps`, and the reduction lemmas apply. (`Σ` is `S`.) -/

section WorstCase

variable {P S Ω : Type*} [InfSet Ω] [PartialOrder Ω] [Problem P S Ω]

/-- §4.4.10, **Definition 4.4**: the **worst-case performance function** of a set `ps` of problems
(all with solver set `S` and performance set `Ω`): the worst — i.e. **infimum** — performance over
the set, `P(s) = ⨅ p ∈ ps, p̄(s)`. -/
def worstCasePerf (ps : Set P) : S → Ω :=
  fun s => ⨅ p ∈ ps, Problem.perf p s

/-- §4.4.10: a set of problems *is* its **worst-case problem** (Def 4.4, "denoted also as `P`") —
the `Problem` whose performance is `worstCasePerf`. So `(ps : Set P)̄ = worstCasePerf ps`, and
worst-case problems plug into the reduction framework unchanged. -/
instance instProblemWorstCase : Problem (Set P) S Ω where
  perf := worstCasePerf

end WorstCase

end

end RandomSystems.CR18
