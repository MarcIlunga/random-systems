/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import RandomSystems.DistSimpAttr
import RandomSystems.PDS

/-!
# CR18 proof automation — core layer

The layer-independent normalizers and closers of the CR18 tactic suite.  This file imports only
mathlib and the carrier layer (`PDS`, needed so the quoted lemma names pre-resolve), so the tactics
are available **everywhere at or above the carrier** — including the foundation files (`CondEquiv`,
`GameOf`, `SystemMBO`, `RelateGameDistinguishing`) that sit below the constructed-game layer.  Macros resolve the lemma names they mention at *use* site, so
each tactic works wherever its lemmas are in scope.

The game/transcript-aware tactics (`cr18_filter`, `cr18_game`, `cr18_simp`, `cr18_close`, …) live in
`RandomSystems.CR18Tactics`, which builds on this file.
-/

namespace RandomSystems.CR18

/-- Pushforward/distribution normalizer for CR18 proofs.

This delegates to the curated `dist_simp` set, which includes functoriality of deterministic
pushforwards (`Dist.fTransform_comp`) and the standard uniform/weight pushforward facts. -/
macro "cr18_pushforward" : tactic =>
  `(tactic| simp only [dist_simp,
      Dist.mass_fTransform,
      Dist.evalPred_fTransform
    ])

/-- Probability-system bookkeeping for CR18 proofs. -/
macro "cr18_prob" : tactic =>
  `(tactic| simp only [dist_simp,
      Dist.isProbDist_fTransform,
      PFunPDS.isProbDist_ofFunDist_iff,
      PFunPDS.URF_isProbDist,
      PFunPDS.isProbDist_ofPermDist_iff,
      PFunPDS.URP_isProbDist,
      PFunPDS.isProbDist_filterQueries_iff,
      Dist.uniform_isProbDist
    ])

/-- Mass/weight expander: unfold `probBad`/`Dist.mass`/`Dist.weight` and
`Finsupp.sum` down to `Finset.sum`s over supports.  First leg of the
recurring "expand → swap → collapse" mass computation. -/
macro "cr18_mass_expand" : tactic =>
  `(tactic| simp only [RandomSystems.probBad, RandomSystems.Dist.mass,
      RandomSystems.Dist.weight, Finsupp.sum])

/-- Swap a double `Finset` sum and reduce to the pointwise summand, naming
the surviving binder.  Second leg of "expand → swap → collapse". -/
macro "cr18_sum_swap" x:ident : tactic =>
  `(tactic| (rw [Finset.sum_comm]
             refine Finset.sum_congr rfl fun $x _ => ?_))

/-- Collapse `ite`-fiber sums (`Σ_i 𝟙[b = i]·c i` → `c b`) and push products
through `ite`.  Third leg of "expand → swap → collapse". -/
macro "cr18_ite_collapse" : tactic =>
  `(tactic| simp [mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm])

/-- Small arithmetic closer for CR18 side conditions.  Tries the relational
congruence closer `gcongr` first (monotonicity goals), then the standard
arithmetic finishers. -/
macro "cr18_arith" : tactic =>
  `(tactic| first | gcongr | omega | linarith | ring | norm_num | positivity)

/-- Heavier arithmetic/bound closer: `cr18_arith` plus `bound`/`grind`, which
also discharge `NNReal`/char-`p` goals the lighter closers miss.  Kept separate
so `cr18_arith` stays fast and predictable in existing proofs. -/
macro "cr18_arith!" : tactic =>
  `(tactic| first
      | gcongr | omega | linarith | ring | norm_num | positivity | bound | grind)

/-- **Mass computation in one shot**: the recurring "expand → swap → collapse"
pipeline (`cr18_mass_expand`, then `cr18_sum_swap`, then `cr18_ite_collapse`),
naming the surviving summation binder.  Turns a `Dist.mass`/`probBad`
computation over a fibered sum into its pointwise value. -/
macro "cr18_mass" x:ident : tactic =>
  `(tactic| (cr18_mass_expand; cr18_sum_swap $x <;> cr18_ite_collapse))

/-- **Cardinality normalizer** for the counting side of birthday/collision
bounds: unfold the standard product/sum/pi/`Fin` cardinalities and push casts,
so `|X|` computations reduce to `N`-arithmetic. -/
macro "cr18_card" : tactic =>
  `(tactic| simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_bool,
      Fintype.card_pi, Fintype.card_fun, Fintype.card_sigma, Fintype.card_fin,
      Fintype.card_perm, Fintype.card_coe,
      Nat.cast_pow, Nat.cast_mul, Nat.cast_add, pow_succ] <;> try push_cast)

/-- **Field / char-`p` / permutation algebra closer.**  Tries `ring`/`abel`
(fast, pure ring/abelian) then `grind`, which discharges char-2 XOR
cancellation, hash-congruence, and permutation-inverse (`π a = b ⟹ π.symm b = a`)
goals — the "obvious algebra" that should never appear in a paper proof. -/
macro "cr18_algebra" : tactic =>
  `(tactic| first | ring | abel | grind)

/-- Advantage-shell reducer: turn a law-level advantage bound into its
pointwise transcript bound by applying the shared `..._le_of_pointwise`
supremum shell.  Runs at reducible transparency so the wrong shell fails
fast on the head constant. -/
macro "cr18_adv_le" : tactic =>
  `(tactic| first
      | with_reducible apply PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise
      | with_reducible apply Dist.evalPred_uniform_le)

/-- The `cr18_standing` simp set: a protocol registers its **standing facts** — "the game is a
monotone-MBO probability system, total on the histories under discussion, whose stripped system is
the real construction" — once, with `attribute [cr18_standing] …`.  The `cr18_standing` tactic then
discharges every such side condition automatically, so paper theorems are applied with only their
mathematical inputs (Maurer's model carries these facts in the *types* of "game" and "random
system"; the unbundled `PFunPDS` carrier must restate them, and this attribute is where they live). -/
register_simp_attr cr18_standing

/-- **Standing-assumption discharger**: tries the common routines for the side conditions of
paper-facing theorems — a local hypothesis, the protocol's registered standing facts
(`@[cr18_standing]`), probability-system bookkeeping, and the routine arsenal. -/
macro "cr18_standing" : tactic =>
  `(tactic| first
      | assumption
      | simp only [cr18_standing]
      | cr18_prob
      | (simp only [cr18_standing]) <;> cr18_prob
      | grind
      | cr18_arith!)

/-- **Routine-argument closer** — the layer-independent "this is trivial" tactic:
`grind`, then the arithmetic/algebra arsenal, then a pushforward-normalize-and-grind
pass.  Use it for the routine side conditions that a paper proof would never spell
out.  (The full game-aware `cr18_close` lives in `RandomSystems.CR18Tactics`.) -/
macro "cr18_routine" : tactic =>
  `(tactic| first
      | grind
      | cr18_arith!
      | cr18_algebra
      | (cr18_pushforward <;> try grind))

end RandomSystems.CR18
