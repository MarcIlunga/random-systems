/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.FunctionEvaluator
import RandomSystems.HTechnique.FixedQueryLaw
import RandomSystems.HTechnique.TacticsBase
import RandomSystems.UniversalHash

/-!
# Hash-then-PRF on the migrated H-technique surface

This module starts the migration of the external
`HTechnique.Applications.HashThenPRF` application.

Source status:

* source theorem: Jha-Nandi §5.1, Lemma 5.1, bounding the fixed-query
  hash-then-PRF distinguishing distance by `choose2 q * eps`;
* support lemma forced by formalization: the paper's extended transcript
  distributions `(y^q, h)` are proof objects used to apply the
  equality-on-good H-technique, while the public theorem is stated over the
  CR18 fixed-query transcript-law surface.

The theorem-facing concrete object is the law-level PDS induced by sampling
`(h, rho)` and embedding the function `m |-> rho (H h m)` as a CR18
`functionEvaluator`.  The fixed-query transcript distributions are constructed
inside the theorem statement by `ProbPDS.fixedQueryTranscriptDist`.
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace RandomSystems
namespace HTechnique
namespace HashThenPRF

open RandomSystems
open RandomSystems.CR18

universe u v w z

attribute [local instance] Classical.propDecidable

/-- Source object: an epsilon-universal keyed hash family, bundled with its
scalar `eps`.

The universality field is the tree's one universality notion,
`RandomSystems.IsEpsUniversal` (`RandomSystems/UniversalHash.lean`), at a
uniform key law: this structure is the *packaging* of a family together with
its bound, not a second notion.  It is the length-independent case; a family
whose bound grows with the message length is carried by
`RandomSystems.IsAlmostUniversal` directly, with no bundle. -/
structure EpsUniversalHash (K : Type u) (M : Type v) (X : Type w)
    [Fintype K] [Nonempty K] where
  /-- The keyed hash function. -/
  hash : K → M → X
  /-- The scalar collision bound. -/
  eps : NNReal
  /-- Distinct messages collide under a uniform key with probability at most
  `eps`. -/
  universal :
    RandomSystems.IsEpsUniversal hash (RandomSystems.Dist.uniform K) eps

variable {K : Type u} {M : Type v} {X : Type w} {Y : Type z}
variable {q : Nat}

/-- The source construction: `m |-> rho (H h m)`. -/
def hashThenPRF [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) (h : K) (rho : X → Y) : M → Y :=
  fun m => rho (Hf.hash h m)

/-- Hash outputs on a fixed query vector. -/
def hashOutputs [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) (h : K) {q : Nat}
    (ms : Fin q → M) : Fin q → X :=
  fun i => Hf.hash h (ms i)

/-- The bad event from the source proof: two distinct fixed messages collide
under the sampled hash key. -/
def hashCollision [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) (h : K) {q : Nat}
    (ms : Fin q → M) : Prop :=
  ∃ i j : Fin q, i ≠ j ∧ Hf.hash h (ms i) = Hf.hash h (ms j)

/-- Source notation for `q choose 2` as an `NNReal`. -/
noncomputable abbrev choose2 (q : Nat) : NNReal :=
  (Nat.choose q 2 : Nat)

/-- The real system law: sample a key and a random function, then view the
resulting hash-then-function construction as a CR18 function evaluator. -/
noncomputable def hashThenPRFProbPDS
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) :
    ProbPDS M Y :=
  RandomSystems.CR18.PFunPDS.Prob.functionEvaluator
    (RandomSystems.Dist.prodProbDist
      (⟨RandomSystems.Dist.uniform K,
        RandomSystems.Dist.uniform_isProbDist⟩ :
        RandomSystems.Dist.ProbDist K)
      (⟨RandomSystems.Dist.uniform (X → Y),
        RandomSystems.Dist.uniform_isProbDist⟩ :
        RandomSystems.Dist.ProbDist (X → Y)))
    (fun p : K × (X → Y) => hashThenPRF Hf p.1 p.2)

/-- Output vector law for the real extended experiment, before exposing the
hash key. -/
noncomputable def realOutputDist
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    RandomSystems.Dist (Fin q → Y) :=
  RandomSystems.Dist.fTransform
    (fun p : K × (X → Y) => fun i : Fin q => hashThenPRF Hf p.1 p.2 (ms i))
    (RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (X → Y)))

/-- Output vector law for the ideal random function on the same fixed message
vector. -/
noncomputable def idealOutputDist
    [Fintype K] [Nonempty K] [Fintype M] [Fintype Y] [Nonempty Y]
    {q : Nat} (ms : Fin q → M) :
    RandomSystems.Dist (Fin q → Y) :=
  RandomSystems.Dist.fTransform
    (fun p : K × (M → Y) => fun i : Fin q => p.2 (ms i))
    (RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (M → Y)))

/-- The paper's real extended transcript distribution `(y^q, h)`. -/
noncomputable def realExtDist
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    RandomSystems.Dist ((Fin q → Y) × K) :=
  RandomSystems.Dist.fTransform
    (fun p : K × (X → Y) =>
      (fun i : Fin q => hashThenPRF Hf p.1 p.2 (ms i), p.1))
    (RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (X → Y)))

/-- The paper's ideal extended transcript distribution `(y^q, h)`. -/
noncomputable def idealExtDist
    [Fintype K] [Nonempty K] [Fintype M] [Fintype Y] [Nonempty Y]
    {q : Nat} (ms : Fin q → M) :
    RandomSystems.Dist ((Fin q → Y) × K) :=
  RandomSystems.Dist.fTransform
    (fun p : K × (M → Y) => (fun i : Fin q => p.2 (ms i), p.1))
    (RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (M → Y)))

/-- The bad predicate on the paper's extended transcript carrier. -/
def badEvent [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    ((Fin q → Y) × K) → Prop :=
  fun t => hashCollision Hf t.2 ms

/-- **Source-name compatibility; support-only.** The external HashThenPRF
source called the bad event `badPred` and packaged it as a `BadPredicate`.
The migrated density API uses plain event predicates, so this preserves the
old name without reintroducing the old wrapper type. -/
def badPred [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    ((Fin q → Y) × K) → Prop :=
  badEvent Hf ms

/-- **The scalar bundle is the constant-`δ` case of the general notion**, at
any length function: a scalar bound does not read the message length. -/
theorem EpsUniversalHash.isAlmostUniversal [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) (len : M → Nat) :
    RandomSystems.IsAlmostUniversal Hf.hash (RandomSystems.Dist.uniform K) len
      (fun _ => Hf.eps) :=
  (RandomSystems.isEpsUniversal_iff_isAlmostUniversal_const
    Hf.hash (RandomSystems.Dist.uniform K) Hf.eps len).mp Hf.universal

/-- Bad-key probability bound: a fixed injective message vector has a hash
collision with probability at most `choose2 q * eps`.  The constant-`δ`,
uniform-key case of `IsAlmostUniversalFor.mass_exists_ne_le_choose_two_mul`;
injectivity is what turns the query-index inequality of `hashCollision` into
the message inequality the union bound charges. -/
theorem hashCollision_prob_le
    [Fintype K] [Nonempty K]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    (RandomSystems.Dist.uniform K).mass
        (fun h => hashCollision Hf h ms) ≤ choose2 q * Hf.eps := by
  refine le_trans (RandomSystems.Dist.mass_mono RandomSystems.Dist.uniform_nonNeg
    (Q := fun h => ∃ i j : Fin q, ms i ≠ ms j ∧ Hf.hash h (ms i) = Hf.hash h (ms j))
    (fun h => fun ⟨i, j, hij, hcol⟩ => ⟨i, j, fun he => hij (h_distinct he), hcol⟩))
    (le_of_le_of_eq
      (Hf.universal.mass_exists_ne_le_choose_two_mul
        RandomSystems.Dist.uniform_nonNeg (fun _ _ h => h.symm) monotone_const ms
        (ℓ := 0) (q := q) (fun _ => le_rfl) le_rfl)
      (by rw [choose2]; push_cast; ring))

/-- Uniform evaluation on an empty query vector. -/
theorem uniformFunction_eval_empty
    (A Y : Type*) [Fintype A] [Fintype Y] [Nonempty Y] :
    RandomSystems.Dist.fTransform
        (fun _ : A → Y => (fun i : Fin 0 => Fin.elim0 i))
        (RandomSystems.Dist.uniform (A → Y)) =
      RandomSystems.Dist.uniform (Fin 0 → Y) := by
  classical
  apply Finsupp.ext
  intro ys
  have hys : ys = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  subst hys
  rw [RandomSystems.Dist.fTransform_apply_eq_sum]
  simp [RandomSystems.Dist.uniform]

/-- Evaluating a uniform random function at an injective message tuple gives a
uniform output tuple. -/
theorem idealEval_uniform
    [Fintype M] [Fintype Y] [Nonempty Y]
    {q : Nat} (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.Dist.fTransform
        (fun rho : M → Y => fun i : Fin q => rho (ms i))
        (RandomSystems.Dist.uniform (M → Y)) =
      RandomSystems.Dist.uniform (Fin q → Y) := by
  classical
  by_cases hq : q = 0
  · subst hq
    have h_eval0 :
        (fun rho : M → Y => fun i : Fin 0 => rho (ms i)) =
          (fun _ : M → Y => fun i : Fin 0 => Fin.elim0 i) := by
      funext rho i
      exact Fin.elim0 i
    simpa [h_eval0] using uniformFunction_eval_empty M Y
  · letI : Nonempty M := ⟨ms ⟨0, Nat.pos_of_ne_zero hq⟩⟩
    simpa using
      (RandomSystems.CR18.uniformFunction_eval_uniform
        (X := M) (Y := Y) (q := q) ms h_distinct)

/-- Evaluating the real random function at the hashed inputs gives a uniform
output tuple on good keys. -/
theorem realEval_uniform_of_good
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h : K)
    (h_good : ¬ hashCollision Hf h ms) :
    RandomSystems.Dist.fTransform
        (fun rho : X → Y => fun i : Fin q => rho (Hf.hash h (ms i)))
        (RandomSystems.Dist.uniform (X → Y)) =
      RandomSystems.Dist.uniform (Fin q → Y) := by
  classical
  by_cases hq : q = 0
  · subst hq
    have h_eval0 :
        (fun rho : X → Y => fun i : Fin 0 => rho (Hf.hash h (ms i))) =
          (fun _ : X → Y => fun i : Fin 0 => Fin.elim0 i) := by
      funext rho i
      exact Fin.elim0 i
    simpa [h_eval0] using uniformFunction_eval_empty X Y
  · let nonces := hashOutputs Hf h ms
    have h_inj : Function.Injective nonces := by
      intro i j hij
      by_contra hne
      exact h_good ⟨i, j, hne, hij⟩
    letI : Nonempty X := ⟨nonces ⟨0, Nat.pos_of_ne_zero hq⟩⟩
    simpa [nonces, hashOutputs] using
      (RandomSystems.CR18.uniformFunction_eval_uniform
        (X := X) (Y := Y) (q := q) nonces h_inj)

/-- Ideal extended transcripts factor as uniform key times uniform output. -/
theorem idealExtDist_apply_uniform
    [Fintype K] [Nonempty K] [Fintype M] [Fintype Y] [Nonempty Y]
    {q : Nat} (ms : Fin q → M) (h_distinct : Function.Injective ms)
    (ys : Fin q → Y) (h : K) :
    idealExtDist (K := K) (Y := Y) ms (ys, h) =
      (RandomSystems.Dist.uniform K) h *
        (RandomSystems.Dist.uniform (Fin q → Y)) ys := by
  classical
  let base : RandomSystems.Dist (K × (M → Y)) :=
    RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (M → Y))
  let evalIdeal : (M → Y) → Fin q → Y := fun rho => fun i => rho (ms i)
  let g : K × (M → Y) → ((Fin q → Y) × K) :=
    fun p => (evalIdeal p.2, p.1)
  calc
    idealExtDist (K := K) (Y := Y) ms (ys, h)
        = RandomSystems.Dist.fTransform g base (ys, h) := by
        rfl
    _ = base.mass (fun p => p.1 = h ∧ evalIdeal p.2 = ys) := by
        htechnique_mass_congr
        intro p
        constructor
        · intro hp
          exact ⟨by simpa [g] using congrArg Prod.snd hp,
            by simpa [g, evalIdeal] using congrArg Prod.fst hp⟩
        · intro hp
          exact Prod.ext (by simpa [g, evalIdeal, hp.1] using hp.2) hp.1
    _ = (RandomSystems.Dist.uniform K).mass (fun k => k = h) *
          (RandomSystems.Dist.uniform (M → Y)).mass (fun rho => evalIdeal rho = ys) := by
        simpa [base] using
          (RandomSystems.Dist.mass_prod_and
            (RandomSystems.Dist.uniform K)
            (RandomSystems.Dist.uniform (M → Y))
            (fun k : K => k = h)
            (fun rho : M → Y => evalIdeal rho = ys))
    _ = (RandomSystems.Dist.uniform K) h *
          (RandomSystems.Dist.fTransform evalIdeal
            (RandomSystems.Dist.uniform (M → Y))) ys := by
        htechnique_dist
    _ = (RandomSystems.Dist.uniform K) h *
          (RandomSystems.Dist.uniform (Fin q → Y)) ys := by
        rw [idealEval_uniform ms h_distinct]

/-- Real extended transcripts factor as uniform key times uniform output on good
keys. -/
theorem realExtDist_apply_uniform_of_good
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (ys : Fin q → Y) (h : K)
    (h_good : ¬ hashCollision Hf h ms) :
    realExtDist Hf ms (ys, h) =
      (RandomSystems.Dist.uniform K) h *
        (RandomSystems.Dist.uniform (Fin q → Y)) ys := by
  classical
  let base : RandomSystems.Dist (K × (X → Y)) :=
    RandomSystems.Dist.prod
      (RandomSystems.Dist.uniform K)
      (RandomSystems.Dist.uniform (X → Y))
  let evalReal : (X → Y) → Fin q → Y :=
    fun rho => fun i => rho (Hf.hash h (ms i))
  let g : K × (X → Y) → ((Fin q → Y) × K) :=
    fun p => (fun i => p.2 (Hf.hash p.1 (ms i)), p.1)
  calc
    realExtDist Hf ms (ys, h)
        = RandomSystems.Dist.fTransform g base (ys, h) := by
        rfl
    _ = base.mass (fun p => p.1 = h ∧ evalReal p.2 = ys) := by
        htechnique_mass_congr
        intro p
        constructor
        · intro hp
          have hk : p.1 = h := by simpa [g] using congrArg Prod.snd hp
          exact ⟨hk, by simpa [g, evalReal, hk] using congrArg Prod.fst hp⟩
        · intro hp
          exact Prod.ext (by simpa [g, evalReal, hp.1] using hp.2) hp.1
    _ = (RandomSystems.Dist.uniform K).mass (fun k => k = h) *
          (RandomSystems.Dist.uniform (X → Y)).mass (fun rho => evalReal rho = ys) := by
        simpa [base] using
          (RandomSystems.Dist.mass_prod_and
            (RandomSystems.Dist.uniform K)
            (RandomSystems.Dist.uniform (X → Y))
            (fun k : K => k = h)
            (fun rho : X → Y => evalReal rho = ys))
    _ = (RandomSystems.Dist.uniform K) h *
          (RandomSystems.Dist.fTransform evalReal
            (RandomSystems.Dist.uniform (X → Y))) ys := by
        htechnique_dist
    _ = (RandomSystems.Dist.uniform K) h *
          (RandomSystems.Dist.uniform (Fin q → Y)) ys := by
        rw [realEval_uniform_of_good Hf ms h h_good]

/-- Real and ideal extended transcript laws agree on good transcripts. -/
theorem realExtDist_eq_idealExtDist_on_good
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h_distinct : Function.Injective ms)
    (ys : Fin q → Y) (h : K)
    (h_good : ¬ hashCollision Hf h ms) :
    realExtDist Hf ms (ys, h) =
      idealExtDist (K := K) (Y := Y) ms (ys, h) := by
  calc
    realExtDist Hf ms (ys, h)
        = (RandomSystems.Dist.uniform K) h *
            (RandomSystems.Dist.uniform (Fin q → Y)) ys :=
            realExtDist_apply_uniform_of_good Hf ms ys h h_good
    _ = idealExtDist (K := K) (Y := Y) ms (ys, h) :=
            (idealExtDist_apply_uniform (K := K) (Y := Y) ms h_distinct ys h).symm

/-- Bad probability bound for the paper's ideal extended transcript law. -/
theorem idealExtDist_probBad_le
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.probBad (idealExtDist (K := K) (Y := Y) ms)
        (badEvent (Y := Y) Hf ms) ≤ choose2 q * Hf.eps := by
  classical
  have hmass :
      ∀ ys : Fin q → Y, ∀ h : K,
        idealExtDist (K := K) (Y := Y) ms (ys, h) =
          (RandomSystems.Dist.uniform K) h *
            (RandomSystems.Dist.uniform (Fin q → Y)) ys := by
    intro ys h
    exact idealExtDist_apply_uniform (K := K) (Y := Y) ms h_distinct ys h
  unfold RandomSystems.probBad badEvent
  rw [RandomSystems.Dist.mass_eq_sum]
  rw [Fintype.sum_prod_type]
  simp_rw [hmass]
  calc
    (∑ ys : Fin q → Y, ∑ h : K,
        if hashCollision Hf h ms then
          (RandomSystems.Dist.uniform K) h *
            (RandomSystems.Dist.uniform (Fin q → Y)) ys
        else 0)
        = ∑ ys : Fin q → Y,
            (RandomSystems.Dist.uniform (Fin q → Y)) ys *
              ∑ h : K,
                if hashCollision Hf h ms then
                  (RandomSystems.Dist.uniform K) h
                else 0 := by
            apply Finset.sum_congr rfl
            intro ys _
            calc
              (∑ h : K,
                  if hashCollision Hf h ms then
                    (RandomSystems.Dist.uniform K) h *
                      (RandomSystems.Dist.uniform (Fin q → Y)) ys
                  else 0)
                  = ∑ h : K,
                      (RandomSystems.Dist.uniform (Fin q → Y)) ys *
                        (if hashCollision Hf h ms then
                          (RandomSystems.Dist.uniform K) h
                        else 0) := by
                      apply Finset.sum_congr rfl
                      intro h _
                      by_cases hb : hashCollision Hf h ms <;> simp [hb, mul_comm]
              _ = (RandomSystems.Dist.uniform (Fin q → Y)) ys *
                    ∑ h : K,
                      if hashCollision Hf h ms then
                        (RandomSystems.Dist.uniform K) h
                      else 0 := by
                    rw [Finset.mul_sum]
    _ = (∑ ys : Fin q → Y, (RandomSystems.Dist.uniform (Fin q → Y)) ys) *
          ∑ h : K,
            if hashCollision Hf h ms then
              (RandomSystems.Dist.uniform K) h
            else 0 := by
            rw [← Finset.sum_mul]
    _ = ∑ h : K,
          if hashCollision Hf h ms then
            (RandomSystems.Dist.uniform K) h
          else 0 := by
            simp [dist_simp]
    _ = (RandomSystems.Dist.uniform K).mass
          (fun h => hashCollision Hf h ms) := by
            rw [RandomSystems.Dist.mass_eq_sum]
    _ ≤ choose2 q * Hf.eps := hashCollision_prob_le Hf ms h_distinct

/-- The real and ideal extended transcript distributions have equal total
weight. -/
theorem weight_realExtDist_eq_idealExtDist
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    (realExtDist (Y := Y) Hf ms).weight =
      (idealExtDist (K := K) (Y := Y) ms).weight := by
  simp only [realExtDist, idealExtDist, dist_simp]

/-- Source theorem on the paper's extended transcript carrier. -/
theorem hashThenPRF_extendedDist_bound
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.statDist
        (realExtDist Hf ms)
        (idealExtDist (K := K) (Y := Y) ms) ≤
      choose2 q * Hf.eps := by
  calc
    RandomSystems.statDist
        (realExtDist Hf ms)
        (idealExtDist (K := K) (Y := Y) ms)
        ≤ RandomSystems.probBad (idealExtDist (K := K) (Y := Y) ms)
            (badEvent (Y := Y) Hf ms) :=
            RandomSystems.hTechnique_eq_on_good
              (realExtDist Hf ms)
              (idealExtDist (K := K) (Y := Y) ms)
              (badEvent (Y := Y) Hf ms)
              ((RandomSystems.Dist.uniform_nonNeg.prod
                RandomSystems.Dist.uniform_nonNeg).fTransform _)
              ((RandomSystems.Dist.uniform_nonNeg.prod
                RandomSystems.Dist.uniform_nonNeg).fTransform _)
              (weight_realExtDist_eq_idealExtDist (Y := Y) Hf ms)
              (fun t ht => by
                rcases t with ⟨ys, h⟩
                exact realExtDist_eq_idealExtDist_on_good
                  (Y := Y) Hf ms h_distinct ys h ht)
    _ ≤ choose2 q * Hf.eps :=
        idealExtDist_probBad_le (Y := Y) Hf ms h_distinct

/-- Dropping the released hash key from the real extended distribution gives the
real output-vector distribution. -/
theorem realOutputDist_eq_fTransform_fst_realExtDist
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat} (ms : Fin q → M) :
    realOutputDist (Y := Y) Hf ms =
      RandomSystems.Dist.fTransform Prod.fst (realExtDist (Y := Y) Hf ms) := by
  unfold realOutputDist realExtDist
  rw [RandomSystems.Dist.fTransform_comp]
  rfl

/-- Dropping the released hash key from the ideal extended distribution gives
the ideal output-vector distribution. -/
theorem idealOutputDist_eq_fTransform_fst_idealExtDist
    [Fintype K] [Nonempty K] [Fintype M] [Fintype Y] [Nonempty Y]
    {q : Nat} (ms : Fin q → M) :
    idealOutputDist (K := K) (Y := Y) ms =
      RandomSystems.Dist.fTransform Prod.fst
        (idealExtDist (K := K) (Y := Y) ms) := by
  unfold idealOutputDist idealExtDist
  rw [RandomSystems.Dist.fTransform_fst_pair_eval_snd_prod_uniform]
  rw [RandomSystems.Dist.fTransform_eval_snd_prod_uniform]

/-- Output-vector version of Lemma 5.1, obtained by data processing from the
paper's extended transcript theorem. -/
theorem hashThenPRF_outputDist_bound
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    (Hf : EpsUniversalHash K M X) {q : Nat}
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.statDist
        (realOutputDist (Y := Y) Hf ms)
        (idealOutputDist (K := K) (Y := Y) ms) ≤
      choose2 q * Hf.eps := by
  calc
    RandomSystems.statDist
        (realOutputDist (Y := Y) Hf ms)
        (idealOutputDist (K := K) (Y := Y) ms)
        ≤ RandomSystems.probBad (idealExtDist (K := K) (Y := Y) ms)
            (badEvent (Y := Y) Hf ms) := by
            rw [realOutputDist_eq_fTransform_fst_realExtDist,
              idealOutputDist_eq_fTransform_fst_idealExtDist]
            exact RandomSystems.hTechnique_eq_on_good_fTransform
              (realExtDist Hf ms)
              (idealExtDist (K := K) (Y := Y) ms)
              Prod.fst
              (badEvent (Y := Y) Hf ms)
              ((RandomSystems.Dist.uniform_nonNeg.prod
                RandomSystems.Dist.uniform_nonNeg).fTransform _)
              ((RandomSystems.Dist.uniform_nonNeg.prod
                RandomSystems.Dist.uniform_nonNeg).fTransform _)
              (weight_realExtDist_eq_idealExtDist (Y := Y) Hf ms)
              (fun t ht => by
                rcases t with ⟨ys, h⟩
                exact realExtDist_eq_idealExtDist_on_good
                  (Y := Y) Hf ms h_distinct ys h ht)
    _ ≤ choose2 q * Hf.eps :=
        idealExtDist_probBad_le (Y := Y) Hf ms h_distinct

/-- The real HashThenPRF fixed-query transcript law is the fixed-input lift of
the real output-vector law. -/
theorem fixedQueryTranscriptDist_hashThenPRFProbPDS
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]
    [FiniteTranscriptSpace M Y q]
    (Hf : EpsUniversalHash K M X) (ms : Fin q → M) :
  ProbPDS.fixedQueryTranscriptDist
        (hashThenPRFProbPDS (Y := Y) Hf) ms =
      RandomSystems.CR18.fixedInputLiftDist ms (realOutputDist Hf ms) := by
  unfold hashThenPRFProbPDS realOutputDist
  htechnique_fixed_query_pds

/-- The ideal URF fixed-query transcript law is the fixed-input lift of the
ideal output-vector law. -/
theorem fixedQueryTranscriptDist_urf_eq_idealOutputDist
    [Fintype K] [Nonempty K] [Fintype M] [Fintype Y] [Nonempty Y]
    [FiniteTranscriptSpace M Y q]
    (ms : Fin q → M) :
    ProbPDS.fixedQueryTranscriptDist
        (ProbPDS.urf (X := M) (Y := Y)) ms =
      RandomSystems.CR18.fixedInputLiftDist ms
        (idealOutputDist (K := K) (Y := Y) ms) := by
  unfold idealOutputDist ProbPDS.urf
  htechnique_fixed_query_pds
  rw [RandomSystems.Dist.fTransform_eval_snd_prod_uniform]

/-- **Hash-then-PRF fixed-query bound on the migrated CR18 transcript-law
surface.** The real PDS and ideal URF PDS are constructed inside the statement;
the paper's extended transcript distributions are only proof support. -/
theorem hashThenPRF_fixedQueryTranscript_bound
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    [FiniteTranscriptSpace M Y q]
    (Hf : EpsUniversalHash K M X)
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (hashThenPRFProbPDS (Y := Y) Hf) ms)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := M) (Y := Y)) ms) ≤
      choose2 q * Hf.eps := by
  rw [fixedQueryTranscriptDist_hashThenPRFProbPDS,
    fixedQueryTranscriptDist_urf_eq_idealOutputDist (K := K)]
  unfold RandomSystems.CR18.fixedInputLiftDist
  rw [RandomSystems.statDist_fTransform_injective
    (realOutputDist Hf ms)
    (idealOutputDist (K := K) (Y := Y) ms)
    (RandomSystems.CR18.fixedInputTranscriptPrefix ms)
    (RandomSystems.CR18.fixedInputTranscriptPrefix_injective ms)]
  exact hashThenPRF_outputDist_bound (Y := Y) Hf ms h_distinct

/-- **Source-name compatibility.** Migrated replacement for the external
`HTechnique.Applications.HashThenPRF.hashThenPRF_security` endpoint.

The old source theorem compared the paper's extended distributions
`(y^q, h)`.  The promoted CR18 statement compares the fixed-query transcript
law of the concrete hash-then-PRF `ProbPDS` against the ideal URF law; the
extended distributions remain proof support inside
`hashThenPRF_fixedQueryTranscript_bound`. -/
theorem hashThenPRF_security
    [Fintype K] [Nonempty K] [Fintype M] [Fintype X] [Fintype Y] [Nonempty Y]
    [FiniteTranscriptSpace M Y q]
    (Hf : EpsUniversalHash K M X)
    (ms : Fin q → M) (h_distinct : Function.Injective ms) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (hashThenPRFProbPDS (Y := Y) Hf) ms)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := M) (Y := Y)) ms) ≤
      choose2 q * Hf.eps :=
  hashThenPRF_fixedQueryTranscript_bound (Y := Y) Hf ms h_distinct

end HashThenPRF
end HTechnique
end RandomSystems
