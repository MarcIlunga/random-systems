/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.CR18.DDS
import RandomSystems.CR18.PDS
import RandomSystems.CR18.Behavior

-- PORTED from hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:4588-4630 — UPSTREAM-CANDIDATE landed 2026-06-11

/-!
# Counterexamples: the applicability boundary of exact (conditional) equivalence

Two machine-checked counterexamples delimiting where the *exact-equality* forms of
game comparison apply, and why the one-sided **domination** form (the per-transcript
H-coefficient primitive, "Def 4.19′") is the right primitive for hidden-key modes.
Both are concrete finite computations (`decide` / `Finset` enumeration), kept at the
smallest instances that remain genuine witnesses.

## §1 The `hCross` impossibility (bug #11, commit `102296a` of hctr2-verification)

*Unnormalized* game equivalence (Def 4.16 `GameEquiv` probes the pre-winning
**sub-distribution masses** at every history) is the wrong level at which to compare
an independent-uniform ("power of `1/N`") world against a permutation world: at a
history with `1 + b` released values the two masses are `1 / N ^ (1 + b)` and
`1 / (N * (N-1) * ⋯ * (N - b))`, so equality forces the count identity

  `N ^ (1 + b) = N.descFactorial (1 + b)`  (i.e. `N^{1+b} = N·(N−1)⋯(N−b)`),

which is **false for every `N ≥ 2`** (`hCross_count_impossible` — the general
counting argument).  The minimal *system-level* instance is `N = 2`, `b = 1`: the
CR18 URF/URP pair over `Fin 2` already has different unnormalized transcript masses
(`1/4 ≠ 1/2`) at the two-query transcript `(0 ↦ 0, 1 ↦ 1)` (`hCross_minimal_instance`)
— even though the *normalized per-class* laws of this very pair satisfy the Ex 4.15
"miracle".  Normalization/conditioning is therefore load-bearing: it cannot be
discarded in favor of raw mass equality.

## §2 Exact conditional equivalence fails: per-class-equal, aggregate-different
(bug #12; machine-verified over GF(8) in hctr2-verification, `5/42 ≠ 3/28` at `N = 8`;
scaled down here to the minimal genuine witness `N = 3`)

The visible law of a hidden-key system is a **mixture** over key classes.  The
witness below has, over `F = Fin 3` with anchor `0` and internal input `mm h = h + 1`:

* ideal world `S`: key `h` and answer `z` independent uniform; bad event
  `badS = (mm h = anchor ∨ z = h)` (D-side anchor hit or R-side key hit);
* real world `T`: uniform permutation `π`; derived key `h = π anchor`; answer
  `z = π (mm h)` — note the internal-collision class `mm h = anchor`, where
  `z = π anchor = h` holds *consistently* and the mode emits an ordinary answer.

Then **every good key class has exactly equal conditional laws** in the two worlds
(`perClass_exact_equality` — both are uniform on `F \ {h}`, the classwise Ex 4.15
miracle), yet the **aggregate** conditioned-ideal vs unconditioned-real laws differ
at the generic point (`aggregate_exact_equality_fails`, `condEquiv_exact_fails`:
`1/9 ≠ (1/6)·(4/9)` in cross-multiplied form `6 ≠ 4`): the conditioned ideal weights
the classes uniformly over no-bad configurations while the real world weights them
by permutation-fiber sizes and *retains* its internally-colliding class.  Same
conditionals, different mixtures — a Simpson-paradox phenomenon for likelihood
ratios.  No exact Def 4.19 conditional equivalence against the unconditioned real
world can hold.

What **does** survive at the very same witness is the one-sided per-transcript
**dominance** `Pr_ideal[τ ∧ nobad] ≤ Pr_real[τ]` (`dominance_holds`, stated in
cross-multiplied count form like `PO3c_dominance`).  This is why the domination
form is the right primitive: it is exactly the statement that remains true at the
boundary instance where exactness dies, and it is what the H-coefficient route
(`PO3c_dominance` + the one-sided `PO3f_bridge` argument) consumes.

## Provenance

Ported from `hctr2-verification/HCTR2/Proofs/CR18/Sketch.lean` (the bug #11/#12
removal comments around `PO3c_dominance`, lines ~4588–4630 at HEAD) and
`TRANSCRIPT_AUGMENTATION.md` §4 (Prop 4.3 forced-form / Obs 4.2 / the GF(8)
enumeration).  The original `hCross` disproof lives in hctr2-verification git
history (commit `102296a`); the GF(8) eq-4.38 refutation in the deleted scratch
file `Pin9Check.lean` (see Sketch.lean §10 registry).  This module re-derives both
phenomena at minimal instances against the stable `RandomSystems` spine only.
-/

namespace RandomSystems.CR18.Counterexamples

open RandomSystems (Dist)

/-! ## §1 The `hCross` counting impossibility (bug #11)

The general counting argument: a falling factorial with at least two factors is
strictly below the matching power, so the identity forced by unnormalized
game-equivalence between a `1/N`-power world and a permutation world has no
solution with `N ≥ 2`. -/

/-- The strict counting inequality behind the `hCross` disproof: for `N ≥ 2` and at
least two factors, the falling factorial `N·(N−1)⋯(N−k+1)` is *strictly* below
`N^k` (the second factor `N − 1` is already strictly smaller than `N`). -/
theorem descFactorial_lt_pow {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) :
    N.descFactorial k < N ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hpow : 0 < N ^ (j + 1) := pow_pos (by omega) _
  calc N.descFactorial (j + 2)
      = (N - (j + 1)) * N.descFactorial (j + 1) := Nat.descFactorial_succ N (j + 1)
    _ ≤ (N - 1) * N ^ (j + 1) :=
        Nat.mul_le_mul (Nat.sub_le_sub_left (by omega) N) (Nat.descFactorial_le_pow N (j + 1))
    _ < N * N ^ (j + 1) := mul_lt_mul_of_pos_right (by omega) hpow
    _ = N ^ (j + 2) := by ring

/-- **bug #11 (`hCross`), the counting impossibility**: unnormalized game-equivalence
between an independent-uniform world (per-history mass `1 / N ^ (1+b)`, one answer
plus `b` released keystream values) and a permutation world (per-history mass
`1 / (N·(N−1)⋯(N−b))`) would force `N ^ (1+b) = N.descFactorial (1+b)` — false for
every `N ≥ 2`.  The exact-equality comparison of raw masses is the wrong level. -/
theorem hCross_count_impossible {N b : ℕ} (hN : 2 ≤ N) (hb : 1 ≤ b) :
    N ^ (1 + b) ≠ N.descFactorial (1 + b) :=
  (descFactorial_lt_pow hN (by omega)).ne'

/-! ## §1b Transcript-mass support lemmas (generic, reusable)

Closed forms for the unnormalized transcript mass (`jointProb`) of the canonical
random-function and random-permutation systems: fiber counting over the seed
space.  These are the generic "collapse the seed fiber to a count" steps of the
H-coefficient computations. -/

/-- A function-evaluator DDS answers every query pointwise: its output sequence on
`xs` is `xs.map (some ∘ f)` (every prefix is in the domain). -/
theorem outputSeq_functionEvaluator {X Y : Type*} (f : X → Y) (xs : List X) :
    (DDS.functionEvaluator f).outputSeq xs = xs.map fun x => some (f x) := by
  unfold DDS.outputSeq
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
    have hk : k < xs.length := by simpa using hk2
    have hne : xs.take (k + 1) ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp only [List.length_take]
      omega
    have hmem : xs.take (k + 1) ∈ (DDS.functionEvaluator f).dom := hne
    rw [dif_pos hmem]
    show some (f ((xs.take (k + 1)).getLast hne)) = some (f xs[k])
    congr 1
    rw [List.getLast_eq_getElem]
    simp [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ xs.length), List.getElem_take]

/-- Transcript mass of a canonical random function: the total seed mass of the
functions tabulating the transcript. -/
theorem jointProb_ofFunDist {X Y : Type} [DecidableEq Y]
    [Fintype (X → Y)] [DecidableEq (DDS X Y)] [DecidableEq (List (Option Y))]
    (Df : Dist (X → Y)) (xs : List X) (ys : List Y) :
    jointProb (RandomFunction.ofFunDist Df) xs ys
      = ∑ f ∈ Finset.univ.filter fun f : X → Y => xs.map f = ys, Df f := by
  unfold jointProb jointOutputDist RandomFunction.ofFunDist
  rw [Dist.fTransform_comp, Dist.fTransform_apply_eq_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    outputSeq_functionEvaluator]
  have hmm : (xs.map fun x => some (g x)) = (xs.map g).map some := by
    rw [List.map_map]; rfl
  rw [hmm]
  constructor
  · exact fun h => (List.map_injective_iff.mpr (Option.some_injective Y)) h
  · exact fun h => congrArg (List.map some) h

/-- Transcript mass of the URF: `#{f | f tabulates the transcript} / |X → Y|`. -/
theorem jointProb_URF {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Nonempty (X → Y)] [DecidableEq (DDS X Y)] [DecidableEq (List (Option Y))]
    (xs : List X) (ys : List Y) :
    jointProb (RandomFunction.URF (X := X) (Y := Y)) xs ys
      = ((Finset.univ.filter fun f : X → Y => xs.map f = ys).card : NNReal)
          / (Fintype.card (X → Y) : NNReal) := by
  unfold RandomFunction.URF
  rw [jointProb_ofFunDist]
  rw [Finset.sum_congr rfl fun f _ => Dist.uniform_apply f]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- Transcript mass of the URP: `#{π | π tabulates the transcript} / |Perm X|`. -/
theorem jointProb_URP {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty (Equiv.Perm X)] [DecidableEq (DDS X X)] [DecidableEq (List (Option X))]
    (xs ys : List X) :
    jointProb (RandomPermutation.URP X) xs ys
      = ((Finset.univ.filter fun π : Equiv.Perm X => xs.map ⇑π = ys).card : NNReal)
          / (Fintype.card (Equiv.Perm X) : NNReal) := by
  unfold jointProb jointOutputDist RandomPermutation.URP
  rw [Dist.fTransform_comp, Dist.fTransform_uniform_apply]
  have hset : (Finset.univ.filter fun π : Equiv.Perm X =>
        ((fun s => DDS.outputSeq s xs) ∘ fun σ : Equiv.Perm X =>
          DDS.functionEvaluator σ.toFun) π = ys.map some)
      = Finset.univ.filter fun π : Equiv.Perm X => xs.map ⇑π = ys := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Equiv.toFun_as_coe, outputSeq_functionEvaluator]
    have hmm : (xs.map fun x => some (π x)) = (xs.map ⇑π).map some := by
      rw [List.map_map]; rfl
    rw [hmm]
    constructor
    · exact fun h => (List.map_injective_iff.mpr (Option.some_injective X)) h
    · exact fun h => congrArg (List.map some) h
  rw [hset]

/-! ## §1c The minimal system-level `hCross` instance: `N = 2`, `b = 1`

The CR18 URF/URP pair over `Fin 2`, probed at the single two-query transcript
`(0 ↦ 0, 1 ↦ 1)`: unnormalized masses `1/4 = 1/N²` vs `1/2 = 1/(N·(N−1))`.
Equality would be the `N = 2, b = 1` case of the impossible identity above. -/

/-- DDS carriers contain a `Set` and a partial function, so equality is classical
(precedent: `PDS.Ex35.ddsDec`). -/
noncomputable scoped instance ddsDecEq (X Y : Type*) : DecidableEq (DDS X Y) :=
  Classical.decEq _

/-- The `Fin 2` URF: the independent-uniform ("power of `1/N`") world. -/
noncomputable def urf2 : PDS (Fin 2) (Fin 2) := RandomFunction.URF

/-- The `Fin 2` URP: the permutation ("falling factorial") world. -/
noncomputable def urp2 : PDS (Fin 2) (Fin 2) := RandomPermutation.URP (Fin 2)

/-- The seed-space cardinality of `urf2` is the power `N ^ (1+b)` at `N = 2, b = 1`. -/
theorem card_urf2_seeds : Fintype.card (Fin 2 → Fin 2) = 2 ^ (1 + 1) := by decide

/-- The seed-space cardinality of `urp2` is the falling factorial
`N.descFactorial (1+b)` at `N = 2, b = 1` — the two sides of the impossible
identity of `hCross_count_impossible`. -/
theorem card_urp2_seeds : Fintype.card (Equiv.Perm (Fin 2)) = Nat.descFactorial 2 (1 + 1) := by
  decide

/-- Unnormalized URF mass of the transcript `(0 ↦ 0, 1 ↦ 1)`: `1/4 = 1/N^{1+b}`. -/
theorem urf2_mass : jointProb urf2 [0, 1] [0, 1] = 1 / 4 := by
  unfold urf2
  rw [jointProb_URF]
  have hc : (Finset.univ.filter fun f : Fin 2 → Fin 2 =>
      List.map f [0, 1] = [0, 1]).card = 1 := by decide
  have hcard : Fintype.card (Fin 2 → Fin 2) = 4 := by decide
  rw [hc, hcard]
  norm_num

/-- Unnormalized URP mass of the same transcript: `1/2 = 1/(N·(N−1))`. -/
theorem urp2_mass : jointProb urp2 [0, 1] [0, 1] = 1 / 2 := by
  unfold urp2
  rw [jointProb_URP]
  have hc : (Finset.univ.filter fun π : Equiv.Perm (Fin 2) =>
      List.map ⇑π [0, 1] = [0, 1]).card = 1 := by decide
  have hcard : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by decide
  rw [hc, hcard]
  norm_num

/-- **bug #11 (`hCross`), minimal system instance**: the URF/URP pair over `Fin 2`
already violates unnormalized game-equivalence at a two-query transcript —
`1/4 ≠ 1/2`, the `N = 2, b = 1` instance of `hCross_count_impossible`.  (The
*conditioned/normalized* laws of this very pair agree — CR18 Ex 4.15; it is the
raw sub-distribution masses that differ.) -/
theorem hCross_minimal_instance :
    jointProb urf2 [0, 1] [0, 1] ≠ jointProb urp2 [0, 1] [0, 1] := by
  rw [urf2_mass, urp2_mass]
  intro h
  have h' := congrArg NNReal.toReal h
  push_cast at h'
  norm_num at h'

/-! ## §2 Exact conditional equivalence: the per-class-equal / aggregate-different
witness (bug #12, GF(8) scaled down to `N = 3`)

The smallest genuine witness: at `N = 2` the generic point disappears (both laws
degenerate to the same point mass), so `N = 3` is minimal. -/

/-- The internal input map of the mode: `mm h = h + 1`.  Exactly one key class —
`h = 2` — has `mm h = anchor`: the internal-collision class the real world retains
and the conditioned ideal world excludes. -/
def mm (h : Fin 3) : Fin 3 := h + 1

/-- The D-side anchor (the published input the derived key is extracted at). -/
def anchor : Fin 3 := 0

/-- Ideal-world sample space: (key `h`, fresh uniform answer `z`), independent. -/
abbrev WS : Type := Fin 3 × Fin 3

/-- Real-world seed space: a uniform permutation of `Fin 3`. -/
abbrev P3 : Type := Equiv.Perm (Fin 3)

/-- The bad event of the ideal world: D-side collision (`mm h` hits the anchor) or
R-side collision (the fresh answer hits the key). -/
def badS (w : WS) : Prop := mm w.1 = anchor ∨ w.2 = w.1

instance : DecidablePred badS := fun w =>
  inferInstanceAs (Decidable (mm w.1 = anchor ∨ w.2 = w.1))

/-- The real world's derived key: `h = π anchor`. -/
def realKey (π : P3) : Fin 3 := π anchor

/-- The real world's visible answer: `z = π (mm (π anchor))`.  On the
internal-collision class (`mm (π anchor) = anchor`) this *consistently* returns the
derived key itself — an ordinary-looking answer the function world's bad event
excludes. -/
def realAnswer (π : P3) : Fin 3 := π (mm (π anchor))

/-- **Per-class exact equality** (the Ex 4.15 miracle, classwise): for every *good*
key class `h` (no internal collision) and every answer `z`, the ideal class
conditional law equals the real class conditional law exactly — both are uniform on
`F \ {h}`.  Stated in cross-multiplied count form (no division):
`#S[class ∧ good ∧ z] · #T[class] = #T[class ∧ z] · #S[class ∧ good]`. -/
theorem perClass_exact_equality :
    ∀ h z : Fin 3, mm h ≠ anchor →
      (Finset.univ.filter fun w : WS => w.1 = h ∧ ¬ badS w ∧ w.2 = z).card
          * (Finset.univ.filter fun π : P3 => realKey π = h).card
        = (Finset.univ.filter fun π : P3 => realKey π = h ∧ realAnswer π = z).card
          * (Finset.univ.filter fun w : WS => w.1 = h ∧ ¬ badS w).card := by
  decide

/-- **Aggregate exact equality fails** (bug #12, the scaled-down GF(8) phenomenon):
the conditioned-ideal aggregate law and the unconditioned-real aggregate law differ
at the generic point `z = anchor` — in cross-multiplied count form,
`#S[good ∧ z] · |Perm F| ≠ #T[z] · #S[good]` (concretely `1·6 ≠ 1·4`, i.e.
`1/9 ≠ (1/6)·(4/9)`; over GF(8) the same computation gave `5/42 ≠ 3/28`).
Per-class equality (previous theorem) plus mixture reweighting by conditioning:
exact Def 4.19 conditional equivalence against the unconditioned real world is
refuted. -/
theorem aggregate_exact_equality_fails :
    (Finset.univ.filter fun w : WS => ¬ badS w ∧ w.2 = anchor).card
        * Fintype.card P3
      ≠ (Finset.univ.filter fun π : P3 => realAnswer π = anchor).card
        * (Finset.univ.filter fun w : WS => ¬ badS w).card := by
  decide

/-- **Dominance survives** (the Def 4.19′ / `PO3c_dominance` primitive): at the very
witness where exactness fails, the one-sided per-transcript count inequality
`Pr_ideal[z ∧ nobad] ≤ Pr_real[z]` holds at *every* answer — in cross-multiplied
count form `#S[good ∧ z] · |Perm F| ≤ #T[z] · |Ω_S|`.  This is why the domination
form, not exact (conditional) equivalence, is the right primitive for hidden-key
modes. -/
theorem dominance_holds :
    ∀ z : Fin 3,
      (Finset.univ.filter fun w : WS => ¬ badS w ∧ w.2 = z).card
          * Fintype.card P3
        ≤ (Finset.univ.filter fun π : P3 => realAnswer π = z).card
          * Fintype.card WS := by
  decide

/-! ### The same failure at the `Dist` level (equational doctrine) -/

/-- Predicate mass of the uniform distribution: `#filter / #carrier` (the `evalPred`
companion of `Dist.fTransform_uniform_apply`). -/
theorem evalPred_uniform {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) [DecidablePred P] :
    (Dist.uniform A).evalPred P
      = ((Finset.univ.filter P).card : NNReal) / (Fintype.card A : NNReal) := by
  unfold Dist.evalPred
  rw [Finset.sum_congr rfl fun a _ => Dist.uniform_apply a]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- The real world's visible law as a `Dist`: pushforward of the uniform permutation
along the visible answer. -/
noncomputable def realLaw : Dist (Fin 3) :=
  Dist.fTransform realAnswer (Dist.uniform P3)

/-- **bug #12 at the `Dist` level**: the exact conditional-equivalence identity
`Pr_S[z ∧ good] = Pr_T[z] · Pr_S[good]` (the cross-multiplied, division-free form of
`Pr_S[z | good] = Pr_T[z]`, Def 4.19 against the unconditioned real world) fails at
the generic point: `1/9 ≠ (1/6)·(4/9)`. -/
theorem condEquiv_exact_fails :
    (Dist.uniform WS).evalPred (fun w => ¬ badS w ∧ w.2 = anchor)
      ≠ realLaw anchor * (Dist.uniform WS).evalPred (fun w => ¬ badS w) := by
  unfold realLaw
  rw [Dist.fTransform_uniform_apply, evalPred_uniform, evalPred_uniform]
  have h1 : (Finset.univ.filter fun w : WS => ¬ badS w ∧ w.2 = anchor).card = 1 := by decide
  have h2 : (Finset.univ.filter fun w : WS => ¬ badS w).card = 4 := by decide
  have h3 : (Finset.univ.filter fun π : P3 => realAnswer π = anchor).card = 1 := by decide
  have h4 : Fintype.card WS = 9 := by decide
  have h5 : Fintype.card P3 = 6 := by decide
  rw [h1, h2, h3, h4, h5]
  intro h
  have h' := congrArg NNReal.toReal h
  push_cast at h'
  norm_num at h'

end RandomSystems.CR18.Counterexamples
