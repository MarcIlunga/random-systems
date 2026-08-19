/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.PDS
import RandomSystems.GameEquivalence
import RandomSystems.SystemMBO
import RandomSystems.CR18TacticsCore
-- `CCDiagram` proof-widget engine: `|≡` goals draw automatically downstream.
import CCWidget

/-!
# CR18 Definition 4.19 — conditional equivalence `Ŝ |≡ T` (next-gen, function-based)

For a **game** `Ŝ` (an `(X, Y × Bool)`-system whose `Bool` is the monotone binary output `A`,
`false = 0 = not won`) and a plain `(X, Y)`-system `T`, CR18 Definition 4.19 (eq. (4.38)) says `Ŝ` is
**conditionally equivalent** to `T`, written `Ŝ |≡ T`, iff the cumulative `Yⁱ`-output distribution of
`Ŝ` **conditioned on the MBO event `Aᵢ = 0`** equals the cumulative output distribution of `T`:

> `p^{Ŝ}_{Yⁱ | Xⁱ, Aᵢ=0}(yⁱ, xⁱ) = p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)`.   (4.38)

To avoid division — and to honour CR18 footnote 29 ("equal for all arguments for which they are both
defined") — we state this in **cross-multiplied** (division-free) form, guarded by the two normalizers:

> `massYAfalse Ŝ i yⁱ xⁱ · massDom T xⁱ = massY T i yⁱ xⁱ · massAfalse Ŝ xⁱ`.

Everything is built from `Dist.mass` over a prefix-match predicate (`cumulativeBehavior`, Def 3.20):
no new probability machinery, and **no `DecidableEq`** — conditioning is not a decidability fact, it is
the classical `Dist.mass` over a `Prop`-valued event.

The `T`-side cumulative mass reuses `PFunPDS.cumulativeBehavior` (`bᶜ(T)`, Def 3.20, PDS.lean) verbatim.
The game-side pre-winning cumulative mass is the **same** `Dist.mass` prefix-match predicate, additionally
requiring every prefix MBO bit to be `false` — exactly the not-yet-won region of `prewinBehavior`
(GameEquivalence.lean), stated as a single `Dist.mass` to avoid a telescoping proof.

This ports the MATH/PROOF-STRUCTURE of the legacy struct development (Indist.lean:2303–2424) to the
next-gen PFun API: `PFunPDS = Dist (PFunDDS.DDS …)`, output read via `PFunDDS.output`, on `Vector` args.
-/

namespace RandomSystems.CR18.CondEquiv

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Game-side masses (the `Aᵢ = 0` numerator and the `Aᵢ = 0` normalizer) -/

/-- **CR18 Def 4.19 / eq. (4.38), game numerator** `p^{Ŝ}_{Yⁱ, Aᵢ=0 | Xⁱ}(yⁱ, xⁱ)` (unnormalized):
the cumulative probability, over the choice of deterministic `s ← Ŝ`, that on input transcript `xⁱ` the
game produces the visible output transcript `yⁱ` **and has not won by round `i`** (every prefix MBO bit
is `false`).

This is exactly the not-yet-won region of `prewinBehavior` (Def 4.15, GameEquivalence.lean) cumulated:
the *same* `Dist.mass` prefix-match predicate as `cumulativeBehavior` (Def 3.20), reading the `Y`
component (`.1`) of each prefix output against `yⁱ` and additionally requiring its MBO bit (`.2`) to be
`false`. Stated as one `Dist.mass` to avoid a telescoping proof. No `DecidableEq`. -/
noncomputable def massYAfalse (Shat : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : ℝ :=
  let ysl := ys.toList
  let xsl := xs.toList
  Dist.mass Shat (fun s =>
    ∀ k : Fin ysl.length,
      ∃ h : xsl.take (k.1 + 1) ∈ PFunDDS.dom s,
        (PFunDDS.output s (xsl.take (k.1 + 1)) h).1 = ysl.get k ∧
        (PFunDDS.output s (xsl.take (k.1 + 1)) h).2 = false)

/-- **CR18 Def 4.19, game normalizer** `p^{Ŝ}_{Aᵢ=0 | Xⁱ}(xⁱ)` (unnormalized): the total weight of
deterministic games `s ← Ŝ` for which `xⁱ` is in `s`'s domain and the MBO bit at `xⁱ` is `false`. -/
noncomputable def massAfalse (Shat : PFunPDS X (Y × Bool)) (xs : List X) : ℝ :=
  Dist.mass Shat (fun s =>
    ∃ h : xs ∈ PFunDDS.dom s, (PFunDDS.output s xs h).2 = false)

/-! ### Plain-system masses (reuse the next-gen cumulative behavior) -/

/-- **CR18 Def 4.19, plain numerator** `p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)` (unnormalized): the `T`-side cumulative
output mass, reusing `PFunPDS.cumulativeBehavior` (`bᶜ(T)`, Def 3.20) verbatim. -/
noncomputable def massY (T : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : ℝ :=
  PFunPDS.cumulativeBehavior T i (ys, xs)

/-- **CR18 Def 4.19, plain normalizer** `p^T_{Xⁱ}(xⁱ)` (unnormalized): the total weight of deterministic
systems `t ← T` for which `xⁱ` is in `t`'s domain — the normalizer for `T`'s conditional output
distribution at history `xⁱ`. -/
noncomputable def massDom (T : PFunPDS X Y) (xs : List X) : ℝ :=
  Dist.mass T (fun t => xs ∈ PFunDDS.dom t)

/-! ### Support-totality side condition (Maurer's "defined on the histories under discussion") -/

/-- CR18: the paper treats systems as defined on the histories under discussion. In the PFun partial
model, the corresponding support condition is that every realization in `T`'s support accepts every
nonempty input history. -/
def TotalOnNonempty (T : PFunPDS X Y) : Prop :=
  ∀ t ∈ T.support, ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom t

/-! ### CR18 Definition 4.19: conditional equivalence -/

/-- **CR18 Definition 4.19 (probabilistic layer)**: a game `Ŝ` (an `(X, Y × Bool)`-system) is
**conditionally equivalent** to a plain `(X, Y)`-system `T`, written `Ŝ |≡ T`, iff for every nonempty
input history `xⁱ` and visible output transcript `yⁱ` of the same length, the cumulative `Yⁱ`-output
distribution of `Ŝ` **conditioned on the MBO event `Aᵢ = 0`** equals the cumulative output distribution
of `T` (eq. (4.38)):

> `p^{Ŝ}_{Yⁱ | Xⁱ, Aᵢ=0}(yⁱ, xⁱ) = p^T_{Yⁱ | Xⁱ}(yⁱ, xⁱ)`.

Stated **cross-multiplied** (division-free), guarded by the two non-vanishing normalizers
(`massAfalse Ŝ xⁱ ≠ 0` and `massDom T xⁱ ≠ 0`):

> `massYAfalse Ŝ i yⁱ xⁱ · massDom T xⁱ = massY T i yⁱ xⁱ · massAfalse Ŝ xⁱ`,

which is equivalent to
`massYAfalse Ŝ i yⁱ xⁱ / massAfalse Ŝ xⁱ = massY T i yⁱ xⁱ / massDom T xⁱ`
wherever both denominators are nonzero — exactly the equality of the two conditional distributions, and
the cross-multiplied form is CR18 eq. (4.38) read at the unnormalized-mass level. No `DecidableEq`. -/
def CondEquiv (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) : Prop :=
  ∀ (i : ℕ) (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)),
    massAfalse Shat xs.toList ≠ 0 → massDom T xs.toList ≠ 0 →
      massYAfalse Shat i ys xs * massDom T xs.toList =
        massY T i ys xs * massAfalse Shat xs.toList

@[inherit_doc CondEquiv] scoped notation:50 Shat " |≡ " T => CondEquiv Shat T

/-! ### The `T`-side normalizer is `1` on Maurer's total systems -/

/-- On Maurer's total systems (every support realization accepts every nonempty history), the `T`-side
normalizer `massDom T xⁱ` is the full weight, hence `1` for a probability distribution: the conditioning
is vacuous on the histories under discussion. -/
theorem massDom_eq_weight_of_totalOnNonempty (T : PFunPDS X Y)
    (hTot : TotalOnNonempty T) {xs : List X} (hxs : xs ≠ []) :
    massDom T xs = T.weight := by
  classical
  unfold massDom Dist.mass Dist.weight
  refine Finsupp.sum_congr fun t ht => ?_
  rw [if_pos (hTot t ht xs hxs)]

/-- On Maurer's total systems, the `T`-side normalizer is `1` for a probability distribution `T`: the
conditioning event holds on all of support, so `massDom T xⁱ = |T| = 1`. -/
theorem massDom_eq_one_of_totalOnNonempty (T : PFunPDS X Y)
    (hT : T.isProbDist) (hTot : TotalOnNonempty T) {xs : List X} (hxs : xs ≠ []) :
    massDom T xs = 1 := by
  rw [massDom_eq_weight_of_totalOnNonempty T hTot hxs]; exact hT.weight_eq

/-! ### Query filtering preserves conditional equivalence

The `[q]` filter only restricts the domain (`… ∧ length ≤ q`) and preserves outputs, so on histories
of length `≤ q` every conditional-equivalence mass is unchanged, and on longer histories the game's
`Aᵢ = 0` weight vanishes.  Hence `S |≡ T → ⌈q⌉ S |≡ ⌈q⌉ T`. -/

theorem massAfalse_filterDom {S : PFunPDS X (Y × Bool)}
    {P : List X → Prop} {hP : PrefixClosed P} {xs : List X}
    (hxs : P xs) :
    massAfalse (PFunPDS.filterDom P hP S) xs = massAfalse S xs := by
  unfold massAfalse PFunPDS.filterDom
  cr18_pushforward
  refine Dist.mass_congr _ fun s =>
    ⟨fun ⟨h, hb⟩ => ⟨h.1, hb⟩, fun ⟨h, hb⟩ => ⟨⟨h, hxs⟩, hb⟩⟩

theorem massAfalse_filterDom_eq_zero {S : PFunPDS X (Y × Bool)}
    {P : List X → Prop} {hP : PrefixClosed P} {xs : List X}
    (hxs : ¬ P xs) :
    massAfalse (PFunPDS.filterDom P hP S) xs = 0 := by
  unfold massAfalse PFunPDS.filterDom
  cr18_pushforward
  refine Dist.mass_eq_zero_of_forall_not _ fun s => ?_
  rintro ⟨h, _⟩
  exact hxs h.2

theorem massDom_filterDom {Z : Type*} {T : PFunPDS X Z}
    {P : List X → Prop} {hP : PrefixClosed P} {xs : List X}
    (hxs : P xs) :
    massDom (PFunPDS.filterDom P hP T) xs = massDom T xs := by
  unfold massDom PFunPDS.filterDom
  cr18_pushforward
  exact Dist.mass_congr _ fun t => ⟨fun h => h.1, fun h => ⟨h, hxs⟩⟩

theorem massY_filterDom {T : PFunPDS X Y} {i : ℕ}
    {P : List X → Prop} {hP : PrefixClosed P}
    {ys : Vector Y (i + 1)} {xs : Vector X (i + 1)} (hxs : P xs.toList) :
    massY (PFunPDS.filterDom P hP T) i ys xs = massY T i ys xs := by
  unfold massY PFunPDS.cumulativeBehavior PFunPDS.filterDom
  cr18_pushforward
  refine Dist.mass_congr _ fun t => forall_congr' fun k => ?_
  have hk : P (xs.toList.take (k.1 + 1)) :=
    hP (List.take_prefix _ _) hxs
  exact ⟨fun ⟨h, ho⟩ => ⟨h.1, ho⟩, fun ⟨h, ho⟩ => ⟨⟨h, hk⟩, ho⟩⟩

theorem massYAfalse_filterDom {S : PFunPDS X (Y × Bool)} {i : ℕ}
    {P : List X → Prop} {hP : PrefixClosed P}
    {ys : Vector Y (i + 1)} {xs : Vector X (i + 1)} (hxs : P xs.toList) :
    massYAfalse (PFunPDS.filterDom P hP S) i ys xs = massYAfalse S i ys xs := by
  unfold massYAfalse PFunPDS.filterDom
  cr18_pushforward
  refine Dist.mass_congr _ fun s => forall_congr' fun k => ?_
  have hk : P (xs.toList.take (k.1 + 1)) :=
    hP (List.take_prefix _ _) hxs
  exact ⟨fun ⟨h, ho⟩ => ⟨h.1, ho⟩, fun ⟨h, ho⟩ => ⟨⟨h, hk⟩, ho⟩⟩

/-- Applying the same prefix-closed domain restriction to both sides preserves
conditional equivalence. -/
theorem condEquiv_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (S : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) (h : S |≡ T) :
    PFunPDS.filterDom P hP S |≡ PFunPDS.filterDom P hP T := by
  intro i xs ys hA hD
  by_cases hxs : P xs.toList
  · rw [massYAfalse_filterDom hxs, massDom_filterDom hxs,
      massY_filterDom hxs, massAfalse_filterDom hxs]
    exact h i xs ys (massAfalse_filterDom hxs ▸ hA)
      (massDom_filterDom hxs ▸ hD)
  · exact absurd (massAfalse_filterDom_eq_zero hxs) hA

theorem massAfalse_filterQueries {S : PFunPDS X (Y × Bool)} {q : ℕ} {xs : List X}
    (hlen : xs.length ≤ q) : massAfalse (⌈q⌉ S) xs = massAfalse S xs := by
  exact massAfalse_filterDom (hP := prefixClosed_length_le q) hlen

theorem massAfalse_filterQueries_eq_zero {S : PFunPDS X (Y × Bool)} {q : ℕ} {xs : List X}
    (hlen : q < xs.length) : massAfalse (⌈q⌉ S) xs = 0 := by
  exact massAfalse_filterDom_eq_zero (hP := prefixClosed_length_le q) (not_le.mpr hlen)

theorem massDom_filterQueries {Z : Type*} {T : PFunPDS X Z} {q : ℕ} {xs : List X}
    (hlen : xs.length ≤ q) : massDom (⌈q⌉ T) xs = massDom T xs := by
  exact massDom_filterDom (hP := prefixClosed_length_le q) hlen

theorem massY_filterQueries {T : PFunPDS X Y} {q i : ℕ} {ys : Vector Y (i + 1)}
    {xs : Vector X (i + 1)} (hlen : xs.toList.length ≤ q) :
    massY (⌈q⌉ T) i ys xs = massY T i ys xs := by
  exact massY_filterDom (hP := prefixClosed_length_le q) hlen

theorem massYAfalse_filterQueries {S : PFunPDS X (Y × Bool)} {q i : ℕ}
    {ys : Vector Y (i + 1)} {xs : Vector X (i + 1)} (hlen : xs.toList.length ≤ q) :
    massYAfalse (⌈q⌉ S) i ys xs = massYAfalse S i ys xs := by
  exact massYAfalse_filterDom (hP := prefixClosed_length_le q) hlen

/-- **Query-filtering preserves conditional equivalence**: `S |≡ T → ⌈q⌉ S |≡ ⌈q⌉ T`. -/
theorem condEquiv_filterQueries {q : ℕ} (S : PFunPDS X (Y × Bool)) (T : PFunPDS X Y)
    (h : S |≡ T) : (⌈q⌉ S) |≡ (⌈q⌉ T) := by
  exact condEquiv_filterDom (fun xs => xs.length ≤ q)
    (prefixClosed_length_le q) S T h

/-! ### History-evaluator games: reading the masses off the seed distribution

For a seed-indexed family of history evaluators — the standard way to build an MBO game whose bit
watches the query history (e.g. the CBC-MAC's collision monitor `Aᵢ`) — every conditional-equivalence
mass is a plain event over the seed distribution.  Proven once, at full generality; protocols
instantiate `out`/`bit` and never reopen the transcript. -/

theorem take_succ_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) (k : ℕ) : l.take (k + 1) ≠ [] := by
  rw [← List.length_pos_iff_ne_nil] at hl ⊢
  rw [List.length_take]
  omega

/-- **`Aᵢ = 0` is a seed event**: the game's not-won mass is the seed mass of "the bit is `false` at
the history". -/
theorem massAfalse_fTransform_historyEvaluator {A : Type*} (D : Dist A)
    (out : A → (l : List X) → l ≠ [] → Y) (bit : A → List X → Bool)
    {xs : List X} (hne : xs ≠ []) :
    massAfalse (Dist.fTransform
        (fun a => PFunDDS.historyEvaluator fun l hne => (out a l hne, bit a l)) D) xs
      = D.mass fun a => bit a xs = false := by
  unfold massAfalse
  cr18_pushforward
  refine Dist.mass_congr _ fun a => ?_
  simp only [PFunDDS.dom_historyEvaluator, PFunDDS.historyEvaluator_output, Set.mem_setOf_eq]
  exact ⟨fun ⟨_, hb⟩ => hb, fun hb => ⟨hne, hb⟩⟩

/-- **The transcript law is a seed event**: for a seed-indexed history system, the cumulative output
mass is the seed mass of "the outputs match on every prefix". -/
theorem massY_fTransform_historyEvaluator {A : Type*} (D : Dist A)
    (out : A → (l : List X) → l ≠ [] → Y) {i : ℕ}
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massY (Dist.fTransform (fun a => PFunDDS.historyEvaluator (out a)) D) i ys xs
      = D.mass fun a => ∀ k : Fin ys.toList.length,
          out a (xs.toList.take (k.1 + 1)) (take_succ_ne_nil (by simp) k.1)
            = ys.toList.get k := by
  unfold massY PFunPDS.cumulativeBehavior
  cr18_pushforward
  refine Dist.mass_congr _ fun a => forall_congr' fun k => ?_
  have hd : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom (PFunDDS.historyEvaluator (out a)) :=
    take_succ_ne_nil (by simp) k.1
  exact ⟨fun ⟨h, ho⟩ => by rwa [PFunDDS.historyEvaluator_output] at ho,
         fun ho => ⟨hd, by rwa [PFunDDS.historyEvaluator_output]⟩⟩

/-- **The joint "outputs match ∧ Aᵢ = 0" law is a seed event**: for a per-seed *monotone* bit, the
per-prefix bits collapse to the single final bit — outputs match on every prefix and the bit is
`false` at the full history. -/
theorem massYAfalse_fTransform_historyEvaluator {A : Type*} (D : Dist A)
    (out : A → (l : List X) → l ≠ [] → Y) (bit : A → List X → Bool)
    (hmono : ∀ a, ∀ {l₁ l₂ : List X}, l₁ <+: l₂ → bit a l₁ = true → bit a l₂ = true)
    {i : ℕ} (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse (Dist.fTransform
        (fun a => PFunDDS.historyEvaluator fun l hne => (out a l hne, bit a l)) D) i ys xs
      = D.mass fun a =>
          (∀ k : Fin ys.toList.length,
            out a (xs.toList.take (k.1 + 1)) (take_succ_ne_nil (by simp) k.1)
              = ys.toList.get k)
          ∧ bit a xs.toList = false := by
  have hxs : xs.toList.take (i + 1) = xs.toList := by
    have h : xs.toList.take xs.toList.length = xs.toList := List.take_length
    rwa [Vector.length_toList] at h
  unfold massYAfalse
  cr18_pushforward
  refine Dist.mass_congr _ fun a => ?_
  constructor
  · intro hP
    refine ⟨fun k => ?_, ?_⟩
    · obtain ⟨h, h1, _⟩ := hP k
      simpa [PFunDDS.historyEvaluator_output] using h1
    · obtain ⟨h, _, h2⟩ := hP ⟨i, by simp [Vector.length_toList]⟩
      simpa [PFunDDS.historyEvaluator_output, hxs] using h2
  · rintro ⟨hM, hB⟩ k
    have hdom : xs.toList.take (k.1 + 1)
        ∈ PFunDDS.dom (PFunDDS.historyEvaluator
          fun l hne => (out a l hne, bit a l)) :=
      take_succ_ne_nil (by simp) k.1
    refine ⟨hdom, by simpa [PFunDDS.historyEvaluator_output] using hM k, ?_⟩
    simp only [PFunDDS.historyEvaluator_output]
    by_contra hbt
    have hbit : bit a (xs.toList.take (k.1 + 1)) = true := by
      simpa using hbt
    have : bit a xs.toList = true :=
      hmono a (List.take_prefix (k.1 + 1) xs.toList) hbit
    simp [hB] at this

/-- A seed-indexed history game has a **monotone MBO** whenever each seed's bit is
prefix-monotone (CR18 Def 3.22, realization-wise). -/
theorem monotoneMBO_fTransform_historyEvaluator {A : Type*} (D : Dist A)
    (out : A → (l : List X) → l ≠ [] → Y) (bit : A → List X → Bool)
    (hmono : ∀ a, ∀ {l₁ l₂ : List X}, l₁ <+: l₂ → bit a l₁ = true → bit a l₂ = true) :
    MonotoneMBO (Dist.fTransform
      (fun a => PFunDDS.historyEvaluator fun l hne => (out a l hne, bit a l)) D) := by
  intro s hs
  obtain ⟨a, _ha, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  exact PFunDDS.historyEvaluator_pair_isGame_of_monotone (out a) (bit a)
    fun hpre => Bool.le_iff_imp.mpr (hmono a hpre)

/-- A seed-indexed history system is **total on nonempty histories** (each evaluator accepts every
nonempty list). -/
theorem totalOnNonempty_fTransform_historyEvaluator {A : Type*} (D : Dist A)
    (out : A → (l : List X) → l ≠ [] → Y) :
    TotalOnNonempty (Dist.fTransform (fun a => PFunDDS.historyEvaluator (out a)) D) := by
  intro s hs xs hne
  obtain ⟨a, _ha, rfl⟩ := Dist.mem_support_fTransform _ _ hs
  exact hne

end RandomSystems.CR18.CondEquiv
