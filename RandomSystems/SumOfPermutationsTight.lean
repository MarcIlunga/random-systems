/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SwitchingLemma
import RandomSystems.FilterDomNormalization
import RandomSystems.AbsorbDPI
import RandomSystems.PermFreshCounting

/-!
# Sum of two independent random permutations — how good is the bound?

Same construction as `RandomSystems.SumOfPermutations`: sample two independent uniform
permutations `π₁, π₂` of a finite abelian group `G` and answer a query `x` with
`π₁ x + π₂ x`.

That file proves the **birthday** bound `q²/N` by conditional equivalence, with the sampled
function's collision as the monitored condition.  The construction is known to be much
better than birthday, and this file asks for how much better: the bound `ε` is
**existentially quantified**, so it is an output of the proof rather than an input to it.

The second conjunct — strictly better than `q²/N` — is a *floor*, not the target.  It only
rules out restating the birthday bound.  The point of the statement is the `ε` you exhibit.

## What is proved

`ε N q = min 1 (Σ_{k<q} k²/(N−k)²)`, which is `≈ q³/3N²` — beyond birthday, and at `q = 2`,
where it is `1/(N−1)²` against a true distance of `1/(N(N−1))`, tight up to `N/(N−1)`.

## Where the bound says something

`Δ ≤ 1` is free, so the bound is content-free once `ε = 1`, i.e. `q ≳ 1.442·N^{2/3}`. The real
band is `√N < q < 1.442·N^{2/3}` — beyond birthday, near-tight at the bottom. It says nothing
at `q ≈ N`, where XoP is believed secure; that needs chi-squared or mirror theory, neither
formalized here. Verified against brute force in `review/audit-empirical.md`.

## The proof

Conditional equivalence (CR18 Thm 4.17) through the packaged seed-indexed endpoint
`maxAdvantage_filterQueries_seededConditionCGame_le`, with the game on the **real** side and
the URF as the conditionally-equivalent target.

The monitored condition is not a collision.  Lazy-sample the two permutations: after `k`
distinct queries the used values are `U`, `V` with `|U| = |V| = k`, and the fresh pair
`(u,v) = (π₁ x, π₂ x)` is uniform on `Ū × V̄`.  The answer `u + v = y` has
`N − 2k + r(y)` realizations, where `r(y) = #{(a,b) ∈ U × V : a + b = y}`, so the real
system's next answer is *not* uniform: it is biased upward exactly on the `y` that are sums of
already-used values, in particular on the answers already seen.

`sopTightBad` fires when the fresh pair falls outside a **balanced** subset of `Ū × V̄`, one
retaining exactly `N − 2k` pairs over *every* `y ∈ G` (`freshKeep`).  Conditioned on it not
firing, each answer is therefore *exactly* uniform — that is the conditional equivalence
(`sopTight_condEquiv`) — and the cost is the discarded excess, `Σ_y r(y) = k²` out of
`(N−k)²` pairs per step (`mass_sopTightBad_le`).

Against the collision condition of `SumOfPermutations`: that one insists the internal value
`π₂ x` be *fresh*, charging the full birthday cost of "`π₂` is not a random function", even
though a repeat of `π₂ x` is invisible behind `π₁ x`.  It charges `2k/N` per step where the
honest charge is `k²/N²`.

Note the direction.  `SumOfPermutations` puts its game on the *ideal* side, remarking that no
bad event on `(π₁, π₂)` can make the real system's conditioned law uniform, since conditioning
cannot enlarge a support and `sopReal`'s answer law is not full (in `ℤ/2` with two distinct
queries the two answers always agree).  That holds only of conditions that leave mass to
condition on: `freshKeep` is *empty* once `2k ≥ N`, so beyond `N/2` distinct queries this game
has no good world at all and eq. (4.38) holds there as `0 = 0`.  Below `N/2` the real answer
law is full, and the balanced subset makes it exactly uniform.
-/

noncomputable section

namespace RandomSystems.CR18.SoPTight

open RandomSystems (Dist)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G] [AddCommGroup G]

/-- The sum-of-permutations function determined by a pair of permutations:
`x ↦ π₁ x + π₂ x`. -/
def sopFunction (p : Equiv.Perm G × Equiv.Perm G) : G → G :=
  fun x => p.1 x + p.2 x

/-- **The real system** `XoP`: two independent uniform permutations, queried as the
function `x ↦ π₁ x + π₂ x`. -/
def sopReal : PFunPDS G G :=
  Dist.fTransform
    (fun p : Equiv.Perm G × Equiv.Perm G => PFunDDS.functionEvaluator (sopFunction p))
    (Dist.uniform (Equiv.Perm G × Equiv.Perm G))

/-- **The ideal system**: a uniform random function `G → G`. -/
def sopIdeal : PFunPDS G G :=
  Dist.fTransform PFunDDS.functionEvaluator (Dist.uniform (G → G))

/-! ## The balanced fresh set

`freshFiber U V y` is the set of values `π₁ x` may take so that the answer is `y` and neither
permutation repeats a used value; it has `N − |U| − |V| + r(y)` elements.  `freshKeep` cuts it
down to exactly `N − 2|U|` — the same number for *every* `y`, which is what makes the
conditioned answer law uniform. -/

/-- The values available to `π₁ x` that give answer `y` without repeating a used value. -/
def freshFiber (U V : Finset G) (y : G) : Finset G :=
  (Finset.univ \ U).filter (fun u => y - u ∉ V)

omit [Nonempty G] in
theorem mem_freshFiber {U V : Finset G} {y u : G} :
    u ∈ freshFiber U V y ↔ u ∉ U ∧ y - u ∉ V := by
  simp [freshFiber, Finset.mem_filter, Finset.mem_sdiff]

omit [Nonempty G] in
/-- Every answer has at least `N − |U| − |V|` realizations: the overlap `U ∩ (y − V)` is all
that inclusion–exclusion can remove. -/
theorem card_freshFiber_ge (U V : Finset G) (y : G) :
    Fintype.card G - (U.card + V.card) ≤ (freshFiber U V y).card := by
  classical
  have hff : (freshFiber U V y).card
      = (((Finset.univ : Finset G) \ U).filter (fun u => y - u ∉ V)).card := rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G) \ U) (p := fun u => y - u ∉ V)
  have hbad : (((Finset.univ : Finset G) \ U).filter (fun u => ¬ (y - u ∉ V))).card ≤ V.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun v => y - v) (s := V))
    intro u hu
    obtain ⟨_, hv⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_image.mpr ⟨y - u, not_not.mp hv, ?_⟩
    exact sub_sub_cancel y u
  have hcompl : ((Finset.univ : Finset G) \ U).card = Fintype.card G - U.card :=
    Finset.card_univ_diff U
  omega

/-- The **balanced** fresh set: exactly `N − 2|U|` available values, whatever `y` is. -/
def freshKeep (U V : Finset G) (y : G) : Finset G :=
  Counting.canonSubset (freshFiber U V y) (Fintype.card G - 2 * U.card)

omit [Nonempty G] in
theorem freshKeep_subset (U V : Finset G) (y : G) : freshKeep U V y ⊆ freshFiber U V y :=
  Counting.canonSubset_subset _ _

omit [Nonempty G] in
theorem card_freshKeep (U V : Finset G) (hUV : U.card = V.card) (y : G) :
    (freshKeep U V y).card = Fintype.card G - 2 * U.card := by
  refine Counting.canonSubset_card _ (le_trans (le_of_eq ?_) (card_freshFiber_ge U V y))
  omega

/-- The good fresh-pair predicate: the fresh pair lands in the balanced set. -/
def sopFresh (U V : Finset G) (u v : G) : Prop :=
  u ∈ freshKeep U V (u + v)

noncomputable instance sopFresh_decidable (U V : Finset G) (u v : G) :
    Decidable (sopFresh U V u v) := Classical.dec _

/-! ## The balanced count — the fresh pair is uniform on `G`

Exactly `N − 2k` available pairs realize each answer, and `N(N − 2k)` in total. -/

omit [Nonempty G] in
/-- **The balance identity.**  For every prescribed answer `c`, exactly `N − 2k` of the
available fresh pairs realize it and survive the monitor.  Independence of `c` is what makes
the conditioned answer law uniform. -/
theorem card_avail_fresh_answer (U V : Finset G) (hUV : U.card = V.card) (c : G) :
    ((Counting.availPairs U V).filter
        (fun uv : G × G => uv.1 + uv.2 = c ∧ sopFresh U V uv.1 uv.2)).card
      = Fintype.card G - 2 * U.card := by
  classical
  have hset : (Counting.availPairs U V).filter
        (fun uv : G × G => uv.1 + uv.2 = c ∧ sopFresh U V uv.1 uv.2)
      = (freshKeep U V c).image (fun u => (u, c - u)) := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_image, Counting.mem_availPairs]
    constructor
    · rintro ⟨⟨_, _⟩, hsum, hfresh⟩
      refine ⟨uv.1, ?_, ?_⟩
      · rw [sopFresh, hsum] at hfresh
        exact hfresh
      · refine Prod.ext rfl ?_
        rw [← hsum]
        exact add_sub_cancel_left uv.1 uv.2
    · rintro ⟨u, hu, huv⟩
      have hfib := freshKeep_subset U V c hu
      obtain ⟨h1, h2⟩ := mem_freshFiber.mp hfib
      have hsum : u + (c - u) = c := add_sub_cancel u c
      subst huv
      refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
      · exact h2
      · exact hsum
      · show u ∈ freshKeep U V (u + (c - u))
        rw [hsum]
        exact hu
  rw [hset, Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
    card_freshKeep U V hUV c]

omit [Nonempty G] in
/-- The total available-and-surviving count: `N` answers, `N − 2k` pairs each. -/
theorem card_avail_fresh (U V : Finset G) (hUV : U.card = V.card) :
    ((Counting.availPairs U V).filter (fun uv : G × G => sopFresh U V uv.1 uv.2)).card
      = Fintype.card G * (Fintype.card G - 2 * U.card) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun uv : G × G => uv.1 + uv.2) (t := (Finset.univ : Finset G))
    (fun uv _ => Finset.mem_univ _)]
  have hterm : ∀ c : G,
      (((Counting.availPairs U V).filter (fun uv => sopFresh U V uv.1 uv.2)).filter
        (fun uv => uv.1 + uv.2 = c)).card = Fintype.card G - 2 * U.card := by
    intro c
    rw [Finset.filter_filter]
    rw [show ((Counting.availPairs U V).filter
          (fun uv : G × G => sopFresh U V uv.1 uv.2 ∧ uv.1 + uv.2 = c))
        = (Counting.availPairs U V).filter
          (fun uv : G × G => uv.1 + uv.2 = c ∧ sopFresh U V uv.1 uv.2) from
      Finset.filter_congr (fun uv _ => and_comm)]
    exact card_avail_fresh_answer U V hUV c
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

/-! ## The monitored condition -/

/-- **The monitored condition.**  The pair of permutations is watched at every *first*
occurrence of a query: the fresh pair of values handed out there must land in the balanced
subset `freshKeep` of the unused product.  The condition fires as soon as one does not.

Stated over prefixes, so prefix-monotonicity is `IsPrefix.trans`. -/
def sopTightBad (p : Equiv.Perm G × Equiv.Perm G) (l : List G) : Prop :=
  ∃ pre : List G, ∃ x : G, pre ++ [x] <+: l ∧ x ∉ pre ∧
    ¬ sopFresh (pre.toFinset.image p.1) (pre.toFinset.image p.2) (p.1 x) (p.2 x)

noncomputable instance sopTightBad_decidable (p : Equiv.Perm G × Equiv.Perm G) (l : List G) :
    Decidable (sopTightBad p l) := Classical.dec _

omit [Nonempty G] in
theorem sopTightBad_monotone (p : Equiv.Perm G × Equiv.Perm G) {l₁ l₂ : List G}
    (hpre : l₁ <+: l₂) (h : sopTightBad p l₁) : sopTightBad p l₂ := by
  obtain ⟨pre, x, hp, hx, hf⟩ := h
  exact ⟨pre, x, hp.trans hpre, hx, hf⟩

omit [Nonempty G] in
/-- **The one-step unfolding.**  Appending a query either leaves the condition alone (a repeat
cannot fire it) or adds exactly the fresh-pair test at that query. -/
theorem sopTightBad_concat (p : Equiv.Perm G × Equiv.Perm G) (l : List G) (x : G) :
    sopTightBad p (l ++ [x]) ↔ sopTightBad p l ∨
      (x ∉ l ∧ ¬ sopFresh (l.toFinset.image p.1) (l.toFinset.image p.2) (p.1 x) (p.2 x)) := by
  constructor
  · rintro ⟨pre, y, hp, hy, hf⟩
    rcases (List.prefix_concat_iff).mp hp with heq | hpre
    · obtain ⟨rfl, rfl⟩ : pre = l ∧ y = x := by
        have h := List.append_inj' heq (by simp)
        exact ⟨h.1, by simpa using h.2⟩
      exact Or.inr ⟨hy, hf⟩
    · exact Or.inl ⟨pre, y, hpre, hy, hf⟩
  · rintro (h | ⟨hx, hf⟩)
    · exact sopTightBad_monotone p ⟨[x], rfl⟩ h
    · exact ⟨l, x, List.prefix_rfl, hx, hf⟩

omit [Nonempty G] in
/-- Only the values on the queried inputs matter. -/
theorem sopTightBad_congr {p p' : Equiv.Perm G × Equiv.Perm G} (l : List G)
    (h₁ : ∀ z ∈ l.toFinset, p.1 z = p'.1 z) (h₂ : ∀ z ∈ l.toFinset, p.2 z = p'.2 z)
    (h : sopTightBad p l) : sopTightBad p' l := by
  obtain ⟨pre, x, hp, hx, hf⟩ := h
  have hsub : ∀ z ∈ pre, z ∈ l.toFinset := fun z hz =>
    List.mem_toFinset.mpr (hp.subset (List.mem_append_left _ hz))
  have hxl : x ∈ l.toFinset :=
    List.mem_toFinset.mpr (hp.subset (List.mem_append_right _ (by simp)))
  refine ⟨pre, x, hp, hx, ?_⟩
  rw [show pre.toFinset.image p'.1 = pre.toFinset.image p.1 from
      Finset.image_congr (fun z hz => (h₁ z (hsub z (List.mem_toFinset.mp hz))).symm),
    show pre.toFinset.image p'.2 = pre.toFinset.image p.2 from
      Finset.image_congr (fun z hz => (h₂ z (hsub z (List.mem_toFinset.mp hz))).symm),
    ← h₁ x hxl, ← h₂ x hxl]
  exact hf

/-! ## The good-seed count

`goodCount d` is the number of permutation pairs that have survived `d` distinct queries with
a *prescribed* answer for each; the point is that it does not depend on which answers were
prescribed. -/

/-- The number of surviving permutation pairs realizing a prescribed transcript on `d`
distinct queries: `((N−d)!)²` extensions times one factor `N − 2k` per step. -/
def goodCount (G : Type u) [Fintype G] (d : ℕ) : ℕ :=
  (Fintype.card G - d).factorial * (Fintype.card G - d).factorial *
    ∏ k ∈ Finset.range d, (Fintype.card G - 2 * k)

theorem goodCount_step (G : Type u) [Fintype G] {d : ℕ} (hd : d < Fintype.card G) :
    (Fintype.card G - d) * (Fintype.card G - d) * goodCount G (d + 1)
      = (Fintype.card G - 2 * d) * goodCount G d := by
  obtain ⟨j, hj⟩ : ∃ j, Fintype.card G - d = j + 1 := ⟨Fintype.card G - d - 1, by omega⟩
  have hj1 : Fintype.card G - (d + 1) = j := by omega
  rw [goodCount, goodCount, hj, hj1, Finset.prod_range_succ, Nat.factorial_succ]
  ring

omit [Nonempty G] in
/-- **The conditional-equivalence count.**  Whatever transcript `a` is prescribed, exactly
`goodCount d` permutation pairs realize it and survive the monitor.  The count is independent
of `a`, which is eq. (4.38): conditioned on the monitor, the answers are uniform. -/
theorem card_goodAgree (l : List G) (a : G → G) :
    (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
        (¬ sopTightBad p l) ∧ ∀ x ∈ l, sopFunction p x = a x)).card
      = goodCount G l.toFinset.card := by
  classical
  induction l using List.reverseRecOn with
  | nil =>
      have hnone : ∀ p : Equiv.Perm G × Equiv.Perm G, ¬ sopTightBad p ([] : List G) := by
        rintro p ⟨pre, x, hp, -, -⟩
        have h := List.prefix_nil.mp hp
        simp at h
      simp only [List.toFinset_nil, Finset.card_empty, goodCount, Finset.range_zero,
        Finset.prod_empty, mul_one, Nat.sub_zero]
      rw [Finset.filter_true_of_mem (fun p _ => ⟨hnone p, by simp⟩), Finset.card_univ,
        Fintype.card_prod, Fintype.card_perm]
  | append_singleton l x ih =>
      by_cases hx : x ∈ l
      · -- a repeat: nothing changes
        have htf : (l ++ [x]).toFinset = l.toFinset := by
          simp [List.toFinset_append, Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hx)]
        rw [htf, ← ih]
        refine congrArg Finset.card (Finset.filter_congr (fun p _ => ?_))
        rw [sopTightBad_concat p l x]
        constructor
        · rintro ⟨hb, hag⟩
          exact ⟨fun h => hb (Or.inl h), fun z hz => hag z (List.mem_append_left _ hz)⟩
        · rintro ⟨hb, hag⟩
          refine ⟨fun h => ?_, fun z hz => ?_⟩
          · rcases h with h | ⟨hxl, -⟩
            · exact hb h
            · exact hxl hx
          · rcases List.mem_append.mp hz with h | h
            · exact hag z h
            · rw [show z = x from by simpa using h]
              exact hag x hx
      · -- a fresh query: one application of the lazy-sampling refinement
        have htf : (l ++ [x]).toFinset = insert x l.toFinset := by
          simp [List.toFinset_append]
        have hxQ : x ∉ l.toFinset := fun h => hx (List.mem_toFinset.mp h)
        have hcard : (l ++ [x]).toFinset.card = l.toFinset.card + 1 := by
          rw [htf, Finset.card_insert_of_notMem hxQ]
        have hlt : l.toFinset.card < Fintype.card G := by
          have hss : l.toFinset ⊂ Finset.univ :=
            Finset.ssubset_univ_iff.mpr fun h => hxQ (h ▸ Finset.mem_univ x)
          simpa using Finset.card_lt_card hss
        -- the refinement, applied with `R = "realizes a x and survives"`
        have himgcard : ∀ p : Equiv.Perm G × Equiv.Perm G,
            (l.toFinset.image p.1).card = (l.toFinset.image p.2).card := by
          intro p
          rw [Finset.card_image_of_injective _ p.1.injective,
            Finset.card_image_of_injective _ p.2.injective]
        have hrefine := Counting.card_fresh_pair_refine (X := G) l.toFinset x hxQ
          (P := fun p : Equiv.Perm G × Equiv.Perm G =>
            (¬ sopTightBad p l) ∧ ∀ z ∈ l, sopFunction p z = a z)
          (hP := by
            intro p p' hp1 hp2 hP
            refine ⟨fun h => hP.1 (sopTightBad_congr l (fun z hz => (hp1 z hz).symm)
              (fun z hz => (hp2 z hz).symm) h), fun z hz => ?_⟩
            have hzQ : z ∈ l.toFinset := List.mem_toFinset.mpr hz
            rw [sopFunction, ← hp1 z hzQ, ← hp2 z hzQ]
            exact hP.2 z hz)
          (R := fun U V u v => u + v = a x ∧ sopFresh U V u v)
          (m := Fintype.card G - 2 * l.toFinset.card)
          (hm := by
            intro p
            rw [card_avail_fresh_answer _ _ (himgcard p) (a x),
              Finset.card_image_of_injective _ p.1.injective])
        -- identify the refined filter with the next stage's good set
        have hfilter : (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
              ((¬ sopTightBad p l) ∧ ∀ z ∈ l, sopFunction p z = a z) ∧
                ((p.1 x + p.2 x = a x) ∧
                  sopFresh (l.toFinset.image p.1) (l.toFinset.image p.2) (p.1 x) (p.2 x))))
            = Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
              (¬ sopTightBad p (l ++ [x])) ∧ ∀ z ∈ l ++ [x], sopFunction p z = a z) := by
          refine Finset.filter_congr (fun p _ => ?_)
          rw [sopTightBad_concat p l x]
          constructor
          · rintro ⟨⟨hb, hag⟩, hans, hfr⟩
            refine ⟨?_, fun z hz => ?_⟩
            · rintro (h | ⟨-, hnf⟩)
              · exact hb h
              · exact hnf hfr
            · rcases List.mem_append.mp hz with h | h
              · exact hag z h
              · rw [show z = x from by simpa using h]
                exact hans
          · rintro ⟨hb, hag⟩
            refine ⟨⟨fun h => hb (Or.inl h), fun z hz => hag z (List.mem_append_left _ hz)⟩,
              hag x (List.mem_append_right _ (by simp)), ?_⟩
            by_contra hnf
            exact hb (Or.inr ⟨hx, hnf⟩)
        rw [hfilter, ih] at hrefine
        rw [hcard]
        have hpos : 0 < Fintype.card G - l.toFinset.card := by omega
        have hgs := goodCount_step G hlt
        refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hpos) ?_
        rw [hrefine, hgs]

omit [Nonempty G] in
/-- The total surviving count: `N^d` transcripts, `goodCount d` pairs each. -/
theorem card_good (l : List G) :
    (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G => ¬ sopTightBad p l)).card
      = Fintype.card G ^ l.toFinset.card * goodCount G l.toFinset.card := by
  classical
  induction l using List.reverseRecOn with
  | nil =>
      have hnone : ∀ p : Equiv.Perm G × Equiv.Perm G, ¬ sopTightBad p ([] : List G) := by
        rintro p ⟨pre, x, hp, -, -⟩
        have h := List.prefix_nil.mp hp
        simp at h
      simp only [List.toFinset_nil, Finset.card_empty, goodCount, Finset.range_zero,
        Finset.prod_empty, mul_one, Nat.sub_zero, pow_zero, one_mul]
      rw [Finset.filter_true_of_mem (fun p _ => hnone p), Finset.card_univ,
        Fintype.card_prod, Fintype.card_perm]
  | append_singleton l x ih =>
      by_cases hx : x ∈ l
      · have htf : (l ++ [x]).toFinset = l.toFinset := by
          simp [List.toFinset_append, Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hx)]
        rw [htf, ← ih]
        refine congrArg Finset.card (Finset.filter_congr (fun p _ => ?_))
        rw [sopTightBad_concat p l x]
        constructor
        · exact fun hb h => hb (Or.inl h)
        · intro hb h
          rcases h with h | ⟨hxl, -⟩
          · exact hb h
          · exact hxl hx
      · have htf : (l ++ [x]).toFinset = insert x l.toFinset := by
          simp [List.toFinset_append]
        have hxQ : x ∉ l.toFinset := fun h => hx (List.mem_toFinset.mp h)
        have hcard : (l ++ [x]).toFinset.card = l.toFinset.card + 1 := by
          rw [htf, Finset.card_insert_of_notMem hxQ]
        have hlt : l.toFinset.card < Fintype.card G := by
          have hss : l.toFinset ⊂ Finset.univ :=
            Finset.ssubset_univ_iff.mpr fun h => hxQ (h ▸ Finset.mem_univ x)
          simpa using Finset.card_lt_card hss
        have himgcard : ∀ p : Equiv.Perm G × Equiv.Perm G,
            (l.toFinset.image p.1).card = (l.toFinset.image p.2).card := by
          intro p
          rw [Finset.card_image_of_injective _ p.1.injective,
            Finset.card_image_of_injective _ p.2.injective]
        have hrefine := Counting.card_fresh_pair_refine (X := G) l.toFinset x hxQ
          (P := fun p : Equiv.Perm G × Equiv.Perm G => ¬ sopTightBad p l)
          (hP := by
            intro p p' hp1 hp2 hP h
            exact hP (sopTightBad_congr l (fun z hz => (hp1 z hz).symm)
              (fun z hz => (hp2 z hz).symm) h))
          (R := fun U V u v => sopFresh U V u v)
          (m := Fintype.card G * (Fintype.card G - 2 * l.toFinset.card))
          (hm := by
            intro p
            rw [card_avail_fresh _ _ (himgcard p),
              Finset.card_image_of_injective _ p.1.injective])
        have hfilter : (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
              (¬ sopTightBad p l) ∧
                sopFresh (l.toFinset.image p.1) (l.toFinset.image p.2) (p.1 x) (p.2 x)))
            = Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
              ¬ sopTightBad p (l ++ [x])) := by
          refine Finset.filter_congr (fun p _ => ?_)
          rw [sopTightBad_concat p l x]
          constructor
          · rintro ⟨hb, hfr⟩
            rintro (h | ⟨-, hnf⟩)
            · exact hb h
            · exact hnf hfr
          · intro hb
            refine ⟨fun h => hb (Or.inl h), ?_⟩
            by_contra hnf
            exact hb (Or.inr ⟨hx, hnf⟩)
        rw [hfilter, ih] at hrefine
        rw [hcard]
        have hgs := goodCount_step G hlt
        have hpos : 0 < Fintype.card G - l.toFinset.card := by omega
        have hexp : Fintype.card G ^ (l.toFinset.card + 1)
            = Fintype.card G * Fintype.card G ^ l.toFinset.card := by
          rw [pow_succ]
          ring
        rw [hexp]
        -- cancel `(N − d)²` from the refinement identity
        have hkey : (Fintype.card G - l.toFinset.card) * (Fintype.card G - l.toFinset.card) *
            (Fintype.card G * Fintype.card G ^ l.toFinset.card * goodCount G (l.toFinset.card + 1))
            = (Fintype.card G - l.toFinset.card) * (Fintype.card G - l.toFinset.card) *
              (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
                ¬ sopTightBad p (l ++ [x]))).card := by
          rw [hrefine]
          calc (Fintype.card G - l.toFinset.card) * (Fintype.card G - l.toFinset.card) *
                (Fintype.card G * Fintype.card G ^ l.toFinset.card *
                  goodCount G (l.toFinset.card + 1))
              = Fintype.card G ^ l.toFinset.card * Fintype.card G *
                ((Fintype.card G - l.toFinset.card) * (Fintype.card G - l.toFinset.card) *
                  goodCount G (l.toFinset.card + 1)) := by ring
            _ = Fintype.card G ^ l.toFinset.card * Fintype.card G *
                ((Fintype.card G - 2 * l.toFinset.card) * goodCount G l.toFinset.card) := by
                rw [hgs]
            _ = Fintype.card G * (Fintype.card G - 2 * l.toFinset.card) *
                (Fintype.card G ^ l.toFinset.card * goodCount G l.toFinset.card) := by ring
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) hkey).symm

/-! ## Standing side conditions -/

omit [AddCommGroup G] in
theorem sopIdeal_isProbDist : (sopIdeal (G := G)).isProbDist := by
  unfold sopIdeal
  cr18_prob

omit [AddCommGroup G] in
theorem sopIdeal_totalOnNonempty : CondEquiv.TotalOnNonempty (sopIdeal (G := G)) :=
  PFunPDS.ofFunDist_totalOnNonempty (Dist.uniform (G → G))

/-! ## The game -/

/-- The monitored condition-C game: the real system, watched for a fresh pair falling outside
the balanced set. -/
def sopTightGame : PFunPDS G (G × Bool) :=
  seededConditionCGame (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) sopFunction sopTightBad

omit [Nonempty G] in
theorem sopTightGame_ignoreMBO : PFunPDS.ignoreMBO (sopTightGame (G := G)) = sopReal := by
  rw [sopTightGame, seededConditionCGame_ignoreMBO, PFunPDS.ofFunDist, Dist.fTransform_comp]
  rfl

/-! ## Conditional equivalence -/

/-- **The fiber factorization — the whole content of the monitored condition.**

Over the queried set `S`, the seed mass of "the answers realize the assignment `a`, and no
fresh pair has yet fallen outside the balanced set" equals the *uniform* mass `N^{-|S|}` of
realizing `a`, times the not-yet-fired normalizer.  The balanced set has the same size over
every answer, so the surviving count `goodCount |S|` does not see `a` at all. -/
theorem mass_agree_and_good (S : Finset G) (a : ↥S → G) (l : List G)
    (hl : ∀ x, x ∈ l ↔ x ∈ S) :
    (Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
        (fun p => (∀ s : ↥S, sopFunction p ↑s = a s) ∧ ¬ sopTightBad p l)
      = (Dist.uniform (G → G)).mass (fun g => ∀ s : ↥S, g ↑s = a s)
        * (Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass (fun p => ¬ sopTightBad p l) := by
  classical
  have hSl : l.toFinset = S := by
    ext x
    rw [List.mem_toFinset]
    exact hl x
  have hd : S.card ≤ Fintype.card G := Finset.card_le_univ S
  -- the total extension of `a`, so the two spellings of "realizes `a`" agree
  set ã : G → G := fun z => if h : z ∈ S then a ⟨z, h⟩ else 0 with hã
  have hagree : ∀ p : Equiv.Perm G × Equiv.Perm G,
      ((∀ s : ↥S, sopFunction p ↑s = a s) ↔ ∀ x ∈ l, sopFunction p x = ã x) := by
    intro p
    constructor
    · intro h x hx
      have hxS : x ∈ S := (hl x).mp hx
      rw [hã]
      simpa [dif_pos hxS] using h ⟨x, hxS⟩
    · intro h s
      have := h s.1 ((hl s.1).mpr s.2)
      rw [hã] at this
      simpa [dif_pos s.2] using this
  refine Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq _ _ _ ?_
  -- the counting identity behind the product law
  have hleft : (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
        (∀ s : ↥S, sopFunction p ↑s = a s) ∧ ¬ sopTightBad p l)).card
      = goodCount G S.card := by
    rw [show (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
          (∀ s : ↥S, sopFunction p ↑s = a s) ∧ ¬ sopTightBad p l))
        = Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
          (¬ sopTightBad p l) ∧ ∀ x ∈ l, sopFunction p x = ã x) from
      Finset.filter_congr (fun p _ => by rw [hagree p]; exact and_comm), card_goodAgree l ã, hSl]
  have hright : (Finset.univ.filter (fun p : Equiv.Perm G × Equiv.Perm G =>
        ¬ sopTightBad p l)).card = Fintype.card G ^ S.card * goodCount G S.card := by
    rw [card_good l, hSl]
  rw [hleft, hright, Fintype.card_fun, Counting.card_function_fiber_finset S a]
  calc goodCount G S.card * Fintype.card G ^ Fintype.card G
      = Fintype.card G ^ (Fintype.card G - S.card + S.card) * goodCount G S.card := by
        rw [Nat.sub_add_cancel hd]
        ring
    _ = Fintype.card G ^ (Fintype.card G - S.card) *
        (Fintype.card G ^ S.card * goodCount G S.card) := by
        rw [pow_add]
        ring

/-- **Condition C for the balanced sum of permutations.**  Until a fresh pair falls outside
the balanced set, every answer is exactly uniform, so the game's conditioned law is the
URF's. -/
theorem sopTight_condEquiv : (sopTightGame (G := G)) |≡ (sopIdeal (G := G)) := by
  classical
  refine condEquiv_of_transcript_mass_reductions (sopTightGame (G := G)) sopIdeal
    (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) (Dist.uniform (G → G))
    sopFunction (fun g => g) (fun p l => ¬ sopTightBad p l)
    (fun {xs} hne => ?_)
    (fun ys xs => massY_fTransform_lastQuery _ _ ys xs)
    (fun ys xs => ?_)
    (fun xs a => ?_)
    (hT := sopIdeal_isProbDist) (hTot := sopIdeal_totalOnNonempty)
  · unfold sopTightGame seededConditionCGame
    rw [CondEquiv.massAfalse_fTransform_historyEvaluator _ _ _ hne]
    exact Dist.mass_congr _ fun p => by simp
  · unfold sopTightGame seededConditionCGame
    refine (massYAfalse_fTransform_lastQuery (Dist.uniform (Equiv.Perm G × Equiv.Perm G))
      sopFunction (fun p l => decide (sopTightBad p l)) ?_ ys xs).trans ?_
    · intro p l₁ l₂ hpre hb
      simpa using sopTightBad_monotone p hpre (by simpa using hb)
    · exact Dist.mass_congr _ fun p => by simp
  · exact mass_agree_and_good xs.toList.toFinset a xs.toList
      (fun x => List.mem_toFinset.symm)

/-! ## The bound

The monitor fires with probability `1 − ∏_{k<d} (1 − k²/(N−k)²)`, which the Weierstrass
product inequality turns into the sum. -/

/-- The bound: `min 1 (Σ_{k<q} k²/(N−k)²)`, which is `≈ q³/3N²`.

`max 1` on the denominator is load-bearing: unguarded, the `k = N` term is `x/0 = 0` and is
silently dropped, making the formula smaller than intended. For `k < N` it changes nothing
(`(N:ℝ) − k ≥ 1`); for `k ≥ N` it trips the `min 1` cap. Only `sopEps 1 2` moves (`0 → 1`). -/
def sopEps (N q : ℕ) : ℝ :=
  min 1 (∑ k ∈ Finset.range q, (k : ℝ) ^ 2 / max 1 (((N : ℝ) - k) ^ 2))

theorem sopEps_nonneg (N q : ℕ) : 0 ≤ sopEps N q := by
  refine le_min zero_le_one (Finset.sum_nonneg fun k _ => ?_)
  positivity

omit [Nonempty G] in
/-- **The surviving mass is the product.**  Below `N/2` distinct queries every factor is
positive and the good-world mass is exactly `∏_{k<d} (1 − k²/(N−k)²)`. -/
theorem mass_good_eq_prod (l : List G)
    (hsmall : ∀ k < l.toFinset.card, 2 * k < Fintype.card G) :
    (((Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
          (fun p => ¬ sopTightBad p l) : NNReal) : ℝ)
      = ∏ k ∈ Finset.range l.toFinset.card,
          (1 - (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2) := by
  classical
  have hd : l.toFinset.card ≤ Fintype.card G := Finset.card_le_univ _
  have hden : ∀ k ∈ Finset.range l.toFinset.card,
      (0 : ℝ) < (Fintype.card G : ℝ) - k := by
    intro k hk
    have h1 : k < l.toFinset.card := Finset.mem_range.mp hk
    have h2 : (k : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast lt_of_lt_of_le h1 hd
    linarith
  have hQpos : (0 : ℝ) < ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - k) :=
    Finset.prod_pos hden
  have hFpos : (0 : ℝ) < (((Fintype.card G - l.toFinset.card).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  -- the `N − 2k` product casts termwise, because every factor is positive below `N/2`
  have hprod2 : ((∏ k ∈ Finset.range l.toFinset.card, (Fintype.card G - 2 * k) : ℕ) : ℝ)
      = ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - 2 * k) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk2 : 2 * k ≤ Fintype.card G := le_of_lt (hsmall k (Finset.mem_range.mp hk))
    rw [Nat.cast_sub hk2]
    push_cast
    ring
  -- the numerator
  have hnum : ((Fintype.card G ^ l.toFinset.card * goodCount G l.toFinset.card : ℕ) : ℝ)
      = (Fintype.card G : ℝ) ^ l.toFinset.card
        * (((Fintype.card G - l.toFinset.card).factorial : ℕ) : ℝ) ^ 2
        * ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - 2 * k) := by
    rw [goodCount, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hprod2]
    ring
  -- `N! = (N−d)! · ∏_{k<d} (N−k)`
  have hfac : ((Fintype.card G).factorial : ℝ)
      = (((Fintype.card G - l.toFinset.card).factorial : ℕ) : ℝ)
        * ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - k) := by
    have h1 : (Fintype.card G - l.toFinset.card).factorial *
        (Fintype.card G).descFactorial l.toFinset.card = (Fintype.card G).factorial :=
      Nat.factorial_mul_descFactorial hd
    have h2 : (((Fintype.card G).descFactorial l.toFinset.card : ℕ) : ℝ)
        = ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - k) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk1 : k ≤ Fintype.card G :=
        le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) hd)
      rw [Nat.cast_sub hk1]
    rw [← h1, Nat.cast_mul, h2]
  -- the target product, factor by factor
  have hRHS : ∏ k ∈ Finset.range l.toFinset.card,
        (1 - (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2)
      = ((Fintype.card G : ℝ) ^ l.toFinset.card
          * ∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - 2 * k))
        / (∏ k ∈ Finset.range l.toFinset.card, ((Fintype.card G : ℝ) - k)) ^ 2 := by
    have hstep : ∀ k ∈ Finset.range l.toFinset.card,
        (1 - (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2)
          = ((Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 2 * k))
            / ((Fintype.card G : ℝ) - k) ^ 2 := by
      intro k hk
      have h0 : ((Fintype.card G : ℝ) - k) ≠ 0 := ne_of_gt (hden k hk)
      field_simp
      ring
    rw [Finset.prod_congr rfl hstep, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range, Finset.prod_pow]
  rw [Dist.uniform_mass_eq_card_filter, card_good l, Fintype.card_prod, Fintype.card_perm,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, hnum, hRHS, Nat.cast_mul, hfac]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem sopEps_ge_one_of_large {N q k : ℕ} (hk : k < q) (hkN : k < N) (h2 : N ≤ 2 * k) :
    (1 : ℝ) ≤ ∑ j ∈ Finset.range q, (j : ℝ) ^ 2 / max 1 (((N : ℝ) - j) ^ 2) := by
  have hkR : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hkN
  have hpos : (0 : ℝ) < (N : ℝ) - k := by linarith
  -- `k < N` makes the guard inert at the witness index
  have hmax : max 1 (((N : ℝ) - k) ^ 2) = ((N : ℝ) - k) ^ 2 := max_eq_right (by nlinarith)
  have hterm : (1 : ℝ) ≤ (k : ℝ) ^ 2 / max 1 (((N : ℝ) - k) ^ 2) := by
    rw [hmax, le_div_iff₀ (by positivity)]
    have h1 : ((N : ℝ) - k) ≤ (k : ℝ) := by
      have : (N : ℝ) ≤ 2 * k := by exact_mod_cast h2
      linarith
    nlinarith [hpos]
  refine le_trans hterm (Finset.single_le_sum
    (f := fun j : ℕ => (j : ℝ) ^ 2 / max 1 (((N : ℝ) - j) ^ 2))
    (fun j _ => div_nonneg (by positivity) (le_trans zero_le_one (le_max_left 1 _)))
    (Finset.mem_range.mpr hk))

omit [Nonempty G] in
/-- **The counting leaf.**  On a fixed schedule of at most `q` queries the monitor fires with
probability at most `Σ_{k<q} k²/(N−k)²`: the balanced set discards `k²` of the `(N−k)²`
available fresh pairs at the `k`-th distinct query, and the Weierstrass inequality turns the
surviving product into the sum. -/
theorem mass_sopTightBad_le (l : List G) (q : ℕ) (hlen : l.length ≤ q) :
    (((Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
        (fun p => sopTightBad p l) : NNReal) : ℝ) ≤ sopEps (Fintype.card G) q := by
  classical
  have hdq : l.toFinset.card ≤ q := le_trans l.toFinset_card_le hlen
  have hd : l.toFinset.card ≤ Fintype.card G := Finset.card_le_univ _
  have hmass_le_one : (((Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
      (fun p => sopTightBad p l) : NNReal) : ℝ) ≤ 1 := by
    exact_mod_cast Dist.mass_le_one Dist.uniform_isProbDist (fun p => sopTightBad p l)
  refine le_min hmass_le_one ?_
  by_cases hbig : ∃ k, k < l.toFinset.card ∧ Fintype.card G ≤ 2 * k
  · -- past `N/2` distinct queries the monitor has fired for certain, and the sum already
    -- exceeds `1`, so there is nothing to prove
    obtain ⟨k, hkd, hk2⟩ := hbig
    exact le_trans hmass_le_one
      (sopEps_ge_one_of_large (lt_of_lt_of_le hkd hdq) (lt_of_lt_of_le hkd hd) hk2)
  · have hsmall : ∀ k < l.toFinset.card, 2 * k < Fintype.card G := by
      intro k hk
      by_contra hcon
      exact hbig ⟨k, hk, by omega⟩
    -- `mass bad = 1 − ∏ (1 − k²/(N−k)²) ≤ Σ_{k<d} k²/(N−k)² ≤ Σ_{k<q} k²/(N−k)²`
    have hsum1 : (Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass (fun p => sopTightBad p l)
        + (Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass (fun p => ¬ sopTightBad p l)
        = 1 := by
      rw [Dist.mass_add_compl]
      exact Dist.uniform_isProbDist
    have hone : (((Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
          (fun p => sopTightBad p l) : NNReal) : ℝ)
        + (((Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
          (fun p => ¬ sopTightBad p l) : NNReal) : ℝ) = 1 := by
      rw [← NNReal.coe_add, hsum1, NNReal.coe_one]
    have hgood := mass_good_eq_prod l hsmall
    have hle1 : ∀ k < l.toFinset.card,
        (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2 ≤ 1 := by
      intro k hk
      have hkd : (k : ℝ) < (Fintype.card G : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hk hd
      have hkN : (0 : ℝ) < (Fintype.card G : ℝ) - k := by linarith
      have h2 : (2 : ℝ) * k < (Fintype.card G : ℝ) := by exact_mod_cast hsmall k hk
      rw [div_le_one (by positivity)]
      nlinarith [hkN, h2]
    have hlow : ∏ k ∈ Finset.range l.toFinset.card,
          (1 - (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2)
        ≥ 1 - ∑ k ∈ Finset.range l.toFinset.card,
            (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2 :=
      Counting.chain_product_lower_bound _ (fun k _ => by positivity) hle1
    -- on `range d` we have `k < N`, so the `max 1` guard is inert; past `d` it only helps
    have hmono : ∑ k ∈ Finset.range l.toFinset.card,
          (k : ℝ) ^ 2 / ((Fintype.card G : ℝ) - k) ^ 2
        ≤ ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 / max 1 (((Fintype.card G : ℝ) - k) ^ 2) := by
      refine le_trans (Finset.sum_le_sum (fun k hk => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hdq))
          (fun k _ _ => div_nonneg (by positivity) (le_trans zero_le_one (le_max_left 1 _))))
      have hkN : (k : ℝ) + 1 ≤ (Fintype.card G : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) hd)
      rw [max_eq_right (by nlinarith : (1 : ℝ) ≤ ((Fintype.card G : ℝ) - k) ^ 2)]
    linarith [hone, hgood, hlow, hmono]

/-! ## The result

The **primary** statement is `maxAdvantage_le_sopEps`, which names the bound explicitly.
`sop_randomness_expander_tight` is the existential repackaging, kept because it is the form
that was asked for — but note what it does and does not certify (see its docstring). -/

/-- **The bound, with the explicit `ε`.**

`Δ(⌈q⌉ XoP, ⌈q⌉ URF) ≤ sopEps N q = min 1 (∑_{k<q} k²/(N−k)²) ≈ q³/3N²`.

This is the theorem to cite. It is the beyond-birthday content: at `q = 2` it gives
`1/(N−1)²` against a birthday bound of `q²/2N ≈ 2/N`.

Three hops: strip the MBO from the monitored game, apply the packaged seed-indexed
condition-C endpoint (CR18 Thm 4.17) with `sopTight_condEquiv` and the fixed-schedule
bad-mass bound, then discharge the `NNReal` cast. -/
theorem maxAdvantage_le_sopEps (q : ℕ) :
    Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G))) ≤ sopEps (Fintype.card G) q :=
  calc Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G)))
      = Δ(⌈q⌉ PFunPDS.ignoreMBO (sopTightGame (G := G)), ⌈q⌉ (sopIdeal (G := G))) := by
        rw [sopTightGame_ignoreMBO]
    _ ≤ ((Real.toNNReal (sopEps (Fintype.card G) q) : NNReal) : ℝ) := by
        refine maxAdvantage_filterQueries_seededConditionCGame_le
          (Dist.uniform (Equiv.Perm G × Equiv.Perm G)) sopFunction sopTightBad
          (fun p => sopTightBad_monotone p) q sopIdeal _ sopTight_condEquiv
          Dist.uniform_isProbDist sopIdeal_isProbDist sopIdeal_totalOnNonempty
          (fun w _ => ?_)
        exact (Real.le_toNNReal_iff_coe_le (sopEps_nonneg _ _)).mpr
          (mass_sopTightBad_le (blindQueryList w q) q (blindQueryList_length_le w q))
    _ = sopEps (Fintype.card G) q := Real.coe_toNNReal _ (sopEps_nonneg _ _)

/-- **How secure is the sum of two independent random permutations?**

Exhibit a bound `ε N q` on the `q`-query distinguishing advantage over a group of order
`N`, together with a proof that it strictly improves on the birthday bound `q²/N` in the
range where `q²/N` says anything.

`ε` is quantified **outside** the group and takes `(N, q)`, so it must be one formula that
works for every group of that order.  That is deliberate: with `ε` chosen after the group
it could be instantiated as the advantage itself, making the first conjunct `le_refl` and
the theorem vacuous.

**What this form does NOT certify, and why `maxAdvantage_le_sopEps` is the theorem to
cite.**  `ε` here is a Prop-level existential witness: it is supplied inside the proof term
and is *not recoverable from the statement* — `Exists.choose` yields a witness with no
provable relation to `sopEps`.  So the only numeric consequence a consumer can extract from
this statement is `Δ ≤ ε N q < q²/N`, i.e. the **birthday** bound.  Concretely, this exact
statement is provable from the already-committed birthday chain alone, with
`ε N q := ½·q²/N` (stop `SumOfPermutations.lean`'s chain one step early at
`pairCollisionUnionBound_le_birthday`) — no `min 1` and no appeal to `Δ ≤ 1` required.

The improvement clause is therefore a floor *and* a ceiling here: it excludes restating the
birthday bound, but hiding `ε` behind `∃` means nothing stronger is exported either.  The
beyond-birthday content lives in `maxAdvantage_le_sopEps`, which this now cites. -/
theorem sop_randomness_expander_tight :
    ∃ ε : ℕ → ℕ → ℝ,
      (∀ (H : Type u) [Fintype H] [DecidableEq H] [Nonempty H] [AddCommGroup H] (q : ℕ),
          Δ(⌈q⌉ (sopReal (G := H)), ⌈q⌉ (sopIdeal (G := H))) ≤ ε (Fintype.card H) q) ∧
      (∀ N q : ℕ, 1 < q → q < N → ε N q < (q : ℝ) ^ 2 / (N : ℝ)) := by
  refine ⟨sopEps, ?_, ?_⟩
  · -- the conditional-equivalence bound, from the explicit-ε theorem
    exact fun H _ _ _ _ q => maxAdvantage_le_sopEps (G := H) q
  · -- strictly better than birthday
    intro N q hq hqN
    have hNpos : (0 : ℝ) < N := by
      have : 0 < N := lt_trans (by omega) hqN
      exact_mod_cast this
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    by_cases hcase : N < q ^ 2
    · -- the cap already beats `q²/N`
      refine lt_of_le_of_lt (min_le_left _ _) ?_
      rw [lt_div_iff₀ hNpos, one_mul]
      exact_mod_cast hcase
    · -- `q² ≤ N`, so `2q ≤ N`; bound the sum by `q³/(3(N−q+1)²)`
      have hcase' : q ^ 2 ≤ N := by omega
      have h2qN : 2 * q ≤ N := le_trans (by nlinarith) hcase'
      have h2qNR : (2 : ℝ) * q ≤ N := by exact_mod_cast h2qN
      have hgap : (0 : ℝ) < (N : ℝ) - q + 1 := by linarith
      refine lt_of_le_of_lt (min_le_right _ _) ?_
      -- `q < N` here, so every `k < q` has `k < N` and the `max 1` guard is inert
      have hterm : ∀ k ∈ Finset.range q,
          (k : ℝ) ^ 2 / max 1 (((N : ℝ) - k) ^ 2) ≤ (k : ℝ) ^ 2 / ((N : ℝ) - q + 1) ^ 2 := by
        intro k hk
        have hkq : (k : ℝ) ≤ (q : ℝ) - 1 := by
          have : k + 1 ≤ q := Finset.mem_range.mp hk
          have : (k : ℝ) + 1 ≤ q := by exact_mod_cast this
          linarith
        have hqN : (q : ℝ) < (N : ℝ) := by exact_mod_cast hqN
        rw [max_eq_right (by nlinarith : (1 : ℝ) ≤ ((N : ℝ) - k) ^ 2)]
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        refine pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.sum_div] at hsum
      have hcube : 3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 :=
        Counting.three_sum_sq_le_cube q
      have hfinal : (∑ k ∈ Finset.range q, (k : ℝ) ^ 2) / ((N : ℝ) - q + 1) ^ 2
          < (q : ℝ) ^ 2 / (N : ℝ) := by
        rw [div_lt_div_iff₀ (by positivity) hNpos]
        have hq2pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
        have hstep : ((N : ℝ) / 2 + 1) ^ 2 ≤ ((N : ℝ) - q + 1) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        have hkey : (q : ℝ) ^ 3 * N < 3 * ((q : ℝ) ^ 2 * ((N : ℝ) - q + 1) ^ 2) :=
          calc (q : ℝ) ^ 3 * N = (q : ℝ) ^ 2 * ((q : ℝ) * N) := by ring
            _ ≤ (q : ℝ) ^ 2 * ((N : ℝ) ^ 2 / 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hq2pos)
                nlinarith [hNpos, h2qNR]
            _ < (q : ℝ) ^ 2 * (3 * ((N : ℝ) / 2 + 1) ^ 2) := by
                refine mul_lt_mul_of_pos_left ?_ hq2pos
                nlinarith [hNpos]
            _ ≤ 3 * ((q : ℝ) ^ 2 * ((N : ℝ) - q + 1) ^ 2) := by
                nlinarith [hstep, hq2pos]
        have hmul : 3 * ((∑ k ∈ Finset.range q, (k : ℝ) ^ 2) * N) ≤ (q : ℝ) ^ 3 * N := by
          nlinarith [hcube, hNpos]
        linarith [hkey, hmul]
      exact lt_of_le_of_lt hsum hfinal

end RandomSystems.CR18.SoPTight
