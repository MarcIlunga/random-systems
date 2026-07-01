/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.SoP.TranscriptPrefix
import NextGen.Migration.HTechnique.TacticsCore
import NextGen.Migration.HTechnique.Counting
import NextGen.FunctionEvaluator

/-!
# SoP system-side transcript laws

This module starts the system-side bridge from the migrated fixed visible-output
SoP law to concrete `PFunPDE.transcriptLaw` instances.

Source status:

* source-theorem bridge: define the difference-normalized SoP function system
  over pairs of permutations.  This is the coordinate system used by
  `CompatibleHiddenState`: visible output `y` satisfies `b = a + y`;
* source-theorem bridge: identify the concrete real/ideal SoP system factors
  with the migrated fixed visible-output masses, reusing the generic
  function-evaluator transcript-event bridge.
-/

noncomputable section

open scoped BigOperators NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

attribute [local instance] Classical.propDecidable

variable {G : Type*} {q : Nat}

/-- **Source-theorem bridge.** Difference-normalized SoP function:
`x ↦ -π₁(x) + π₂(x)`.  Sampling `π₁` uniformly is equivalent to sampling
`x ↦ -π₁(x)` uniformly, so this is the coordinate system matching the migrated
compatible-count law. -/
def normalizedSoPFunction [AddGroup G] (p : Equiv.Perm G × Equiv.Perm G) : G → G :=
  fun x => -p.1 x + p.2 x

/-- **Source-theorem bridge.** The normalized SoP random system as a CR18
PFun-native PDS random variable. -/
def normalizedSoPRV [AddGroup G] :
    RandomSystems.CR18.PFunPDS.RV (Equiv.Perm G × Equiv.Perm G) G G :=
  RandomSystems.CR18.functionEvaluatorRV (normalizedSoPFunction (G := G))

/-- **Source-theorem bridge.** The normalized SoP sample distribution: two
independent uniform permutations. -/
def normalizedSoPProbDist [Fintype G] [DecidableEq G] :
    RandomSystems.Dist.ProbDist (Equiv.Perm G × Equiv.Perm G) :=
  ⟨RandomSystems.Dist.uniform (Equiv.Perm G × Equiv.Perm G),
    RandomSystems.Dist.uniform_isProbDist⟩

/-- **Source-theorem bridge.** The normalized SoP real system as a law-level
PDS.  This is the paper-facing object used by public SoP endpoints. -/
noncomputable def normalizedSoPProbPDS
    [AddGroup G] [Fintype G] [DecidableEq G] : ProbPDS G G :=
  RandomSystems.CR18.PFunPDS.Prob.functionEvaluator
    (normalizedSoPProbDist (G := G))
    (normalizedSoPFunction (G := G))

/-- **Support lemma forced by formalization.** The normalized SoP law is
q-step-total because it is sampled from total function evaluators. -/
theorem normalizedSoPProbPDS_KStepTotal
    [AddGroup G] [Fintype G] [DecidableEq G] (k : Nat) :
    (normalizedSoPProbPDS (G := G)).KStepTotal k := by
  exact RandomSystems.CR18.functionEvaluatorProb_KStepTotal
    (normalizedSoPProbDist (G := G))
    (normalizedSoPFunction (G := G))
    k

/-- **Support lemma forced by formalization.** The normalized SoP law is total
on every nonempty input history in its support. -/
theorem normalizedSoPProbPDS_totalOnNonempty
    [AddGroup G] [Fintype G] [DecidableEq G] :
    RandomSystems.CR18.CondEquiv.TotalOnNonempty
      (normalizedSoPProbPDS (G := G)).val := by
  exact RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty
    (normalizedSoPProbDist (G := G))
    (normalizedSoPFunction (G := G))

/-- **Source-theorem bridge.** The ideal system event on fixed inputs is exactly
the pointwise equation `f(xᵢ)=yᵢ`. -/
theorem transcriptSystemEvent_urfRV_iff
    (xs yv : Fin q → G) (f : G → G) :
    RandomSystems.CR18.PFunPDE.transcriptSystemEvent
        (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G))
        (vectorOfFunction xs) (vectorOfFunction yv) f ↔
      ∀ i : Fin q, f (xs i) = yv i := by
  change RandomSystems.CR18.PFunPDE.transcriptSystemEvent
        (RandomSystems.CR18.functionEvaluatorRV (fun f : G → G => f)) (vectorOfFunction xs)
          (vectorOfFunction yv) f ↔
      ∀ i : Fin q, f (xs i) = yv i
  rw [RandomSystems.CR18.transcriptSystemEvent_functionEvaluatorRV_iff]
  simp [vectorOfFunction]

/-- **Source-theorem bridge.** The normalized SoP system event on fixed inputs is
exactly the pointwise equation `-π₁(xᵢ)+π₂(xᵢ)=yᵢ`. -/
theorem transcriptSystemEvent_normalizedSoPRV_iff [AddGroup G]
    (xs yv : Fin q → G) (p : Equiv.Perm G × Equiv.Perm G) :
    RandomSystems.CR18.PFunPDE.transcriptSystemEvent
        (normalizedSoPRV (G := G)) (vectorOfFunction xs) (vectorOfFunction yv) p ↔
      ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i := by
  change RandomSystems.CR18.PFunPDE.transcriptSystemEvent
        (RandomSystems.CR18.functionEvaluatorRV (normalizedSoPFunction (G := G))) (vectorOfFunction xs)
          (vectorOfFunction yv) p ↔
      ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i
  rw [RandomSystems.CR18.transcriptSystemEvent_functionEvaluatorRV_iff]
  simp [vectorOfFunction]

/-- **Source-theorem bridge.** The normalized SoP equation
`-π₁(xᵢ)+π₂(xᵢ)=yᵢ` is equivalent to the second permutation extending the
shifted first-permutation tuple `π₁(xᵢ)+yᵢ`. -/
theorem normalizedSoPFunction_event_iff_snd_eq_shifted [AddGroup G]
    (xs yv : Fin q → G) (p : Equiv.Perm G × Equiv.Perm G) :
    (∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i) ↔
      ∀ i : Fin q, p.2 (xs i) = shifted yv (fun j => p.1 (xs j)) i := by
  constructor
  · intro h i
    calc p.2 (xs i)
        = p.1 (xs i) + yv i := by
            rw [← h i]
            simp [normalizedSoPFunction]
      _ = shifted yv (fun j => p.1 (xs j)) i := rfl
  · intro h i
    simp [normalizedSoPFunction, h i, shifted]

/-- **Source-theorem bridge.** On injective input tuples, every normalized SoP
event witness determines a compatible hidden state in the migrated visible-law
coordinates. -/
theorem compatibleHiddenState_of_normalizedSoPFunction_event [AddGroup G]
    {xs yv : Fin q → G} {p : Equiv.Perm G × Equiv.Perm G}
    (hxs : Function.Injective xs)
    (hevent : ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i) :
    CompatibleHiddenState yv (fun i => p.1 (xs i)) := by
  constructor
  · exact p.1.injective.comp hxs
  · have hshift : shifted yv (fun i => p.1 (xs i)) = fun i => p.2 (xs i) := by
      funext i
      exact (normalizedSoPFunction_event_iff_snd_eq_shifted xs yv p).mp hevent i |>.symm
    rw [hshift]
    exact p.2.injective.comp hxs

/-- **Source-theorem bridge.** Permutation pairs whose normalized SoP output
matches a fixed visible-output tuple on fixed inputs. -/
def normalizedSoPOutputFiber [AddGroup G] (xs yv : Fin q → G) : Type _ :=
  {p : Equiv.Perm G × Equiv.Perm G //
    ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i}

/-- **Support lemma forced by formalization; candidate for upstream.** A
permutation-extension fiber for a fixed finite injective assignment. -/
def permFiber (xs a : Fin q → G) : Type _ :=
  {π : Equiv.Perm G // ∀ i : Fin q, π (xs i) = a i}

/-- **Source-theorem bridge.** Compatible hidden states for a fixed visible
output tuple, as a named fiber. -/
def compatibleHiddenFiber [AddGroup G] (yv : Fin q → G) : Type _ :=
  {a : Fin q → G // CompatibleHiddenState yv a}

instance normalizedSoPOutputFiberFintype [AddGroup G] [Fintype G] [DecidableEq G]
    (xs yv : Fin q → G) :
    Fintype (normalizedSoPOutputFiber (G := G) (q := q) xs yv) :=
  Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
      (fun p => ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i))
    (by intro p; simp)

instance permFiberFintype [Fintype G] [DecidableEq G] (xs a : Fin q → G) :
    Fintype (permFiber (G := G) (q := q) xs a) :=
  Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm G)).filter
      (fun π => ∀ i : Fin q, π (xs i) = a i))
    (by intro π; simp)

instance compatibleHiddenFiberFintype [AddGroup G] [Fintype G] (yv : Fin q → G) :
    Fintype (compatibleHiddenFiber (G := G) (q := q) yv) :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun a => CompatibleHiddenState yv a))
    (by intro a; simp)

/-- **Source-theorem bridge.** The concrete normalized SoP output fiber
decomposes over the compatible hidden tuple `aᵢ = π₁(xᵢ)`.  For each compatible
`a`, the remaining choices are exactly two independent permutation-extension
fibers: `π₁(xsᵢ)=aᵢ` and `π₂(xsᵢ)=aᵢ+yᵢ`. -/
def normalizedSoPOutputFiberEquivCompatibleSigma [AddGroup G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    normalizedSoPOutputFiber (G := G) (q := q) xs yv ≃
      Sigma (fun a : compatibleHiddenFiber (G := G) (q := q) yv =>
        permFiber (G := G) (q := q) xs a.1 ×
          permFiber (G := G) (q := q) xs (shifted yv a.1)) where
  toFun p := by
    refine ⟨⟨fun i => p.1.1 (xs i), ?_⟩, ?_⟩
    · exact compatibleHiddenState_of_normalizedSoPFunction_event (G := G) (q := q) hxs p.2
    · exact
        (⟨p.1.1, by intro i; rfl⟩,
          ⟨p.1.2, by
            intro i
            exact (normalizedSoPFunction_event_iff_snd_eq_shifted xs yv p.1).mp p.2 i⟩)
  invFun s := by
    refine ⟨(s.2.1.1, s.2.2.1), ?_⟩
    refine (normalizedSoPFunction_event_iff_snd_eq_shifted xs yv (s.2.1.1, s.2.2.1)).mpr ?_
    intro i
    calc s.2.2.1 (xs i)
        = shifted yv s.1.1 i := s.2.2.2 i
      _ = shifted yv (fun j => s.2.1.1 (xs j)) i := by
          simp [shifted, s.2.1.2 i]
  left_inv := by
    intro p
    cases p with
    | mk p hp =>
      cases p
      apply Subtype.ext
      rfl
  right_inv := by
    intro s
    rcases s with ⟨⟨a, ha⟩, ⟨⟨π₁, hπ₁⟩, ⟨π₂, hπ₂⟩⟩⟩
    have hhidden : (fun i => π₁ (xs i)) = a := by
      funext i
      exact hπ₁ i
    subst a
    simp [shifted]

/-- **Support lemma forced by formalization; candidate for upstream.** Named
subtype form of the generic permutation-extension fiber count. -/
theorem permFiber_card [Fintype G] [DecidableEq G]
    (xs : Fin q → G) (hxs : Function.Injective xs)
    (a : Fin q → G) (ha : Function.Injective a) :
    Fintype.card (permFiber (G := G) (q := q) xs a) =
      (Fintype.card G - q).factorial := by
  have hqle : q ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective xs hxs
  have hcard :=
    RandomSystems.CR18.Counting.card_perm_fiber (X := G) (q := q) xs hxs a ha hqle
  rw [← hcard]
  rw [← Fintype.card_subtype (p := fun π : Equiv.Perm G => ∀ i : Fin q, π (xs i) = a i)]
  rfl

@[simp]
theorem compatibleHiddenFiber_card [AddGroup G] [Fintype G] (yv : Fin q → G) :
    Fintype.card (compatibleHiddenFiber (G := G) (q := q) yv) =
      compatibleCountNat yv := by
  simp [compatibleHiddenFiber]

/-- **Source-theorem bridge.** The normalized SoP event fiber has the exact
visible-law numerator times two permutation-extension factors. -/
theorem normalizedSoPOutputFiber_card [AddGroup G] [Fintype G] [DecidableEq G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    Fintype.card (normalizedSoPOutputFiber (G := G) (q := q) xs yv) =
      compatibleCountNat yv *
        ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
  calc
    Fintype.card (normalizedSoPOutputFiber (G := G) (q := q) xs yv)
        = Fintype.card (Sigma (fun a : compatibleHiddenFiber (G := G) (q := q) yv =>
            permFiber (G := G) (q := q) xs a.1 ×
              permFiber (G := G) (q := q) xs (shifted yv a.1))) := by
          exact Fintype.card_congr
            (normalizedSoPOutputFiberEquivCompatibleSigma (G := G) (q := q) xs yv hxs)
    _ = ∑ a : compatibleHiddenFiber (G := G) (q := q) yv,
          Fintype.card (permFiber (G := G) (q := q) xs a.1 ×
            permFiber (G := G) (q := q) xs (shifted yv a.1)) := by
          rw [Fintype.card_sigma]
    _ = ∑ _a : compatibleHiddenFiber (G := G) (q := q) yv,
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Fintype.card_prod]
          rw [permFiber_card (G := G) (q := q) xs hxs a.1 a.2.1]
          rw [permFiber_card (G := G) (q := q) xs hxs (shifted yv a.1) a.2.2]
    _ = Fintype.card (compatibleHiddenFiber (G := G) (q := q) yv) *
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          simp [Finset.sum_const]
    _ = compatibleCountNat yv *
          ((Fintype.card G - q).factorial * (Fintype.card G - q).factorial) := by
          rw [compatibleHiddenFiber_card]

/-- **Source-theorem bridge.** The concrete normalized SoP system factor is
exactly the migrated real visible-output mass. -/
theorem transcriptSystemFactor_normalizedSoPRV_eq_realVisibleMass
    [AddGroup G] [Fintype G] [DecidableEq G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        (normalizedSoPProbDist (G := G)) (normalizedSoPRV (G := G))
        (vectorOfFunction xs) (vectorOfFunction yv) =
      realVisibleMass (G := G) (q := q) yv := by
  have hq : q ≤ Fintype.card G := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective xs hxs
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor normalizedSoPProbDist
  have hevent :
      (RandomSystems.Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
          (RandomSystems.CR18.PFunPDE.transcriptSystemEvent
            (normalizedSoPRV (G := G)) (vectorOfFunction xs) (vectorOfFunction yv)) =
        (RandomSystems.Dist.uniform (Equiv.Perm G × Equiv.Perm G)).mass
          (fun p : Equiv.Perm G × Equiv.Perm G =>
            ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i) := by
    apply RandomSystems.Dist.mass_congr
    intro p
    exact transcriptSystemEvent_normalizedSoPRV_iff xs yv p
  rw [hevent]
  rw [RandomSystems.Dist.uniform_mass_eq_card_filter]
  have hfilter :
      ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
          (fun p : Equiv.Perm G × Equiv.Perm G =>
            ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i)).card =
        Fintype.card (normalizedSoPOutputFiber (G := G) (q := q) xs yv) := by
    rw [← Fintype.card_subtype
      (p := fun p : Equiv.Perm G × Equiv.Perm G =>
        ∀ i : Fin q, normalizedSoPFunction p (xs i) = yv i)]
    rfl
  rw [hfilter, normalizedSoPOutputFiber_card (G := G) (q := q) xs yv hxs]
  rw [Fintype.card_prod, Fintype.card_perm]
  rw [realVisibleMass_eq, compatibleCountNNReal_eq_coe_nat]
  norm_num [Nat.cast_mul]
  have hfact_nat :
      (Fintype.card G - q).factorial * (Fintype.card G).descFactorial q =
        (Fintype.card G).factorial :=
    Nat.factorial_mul_descFactorial hq
  have hfact :
      (((Fintype.card G - q).factorial : Nat) : NNReal) *
          (((Fintype.card G).descFactorial q : Nat) : NNReal) =
        (((Fintype.card G).factorial : Nat) : NNReal) := by
    exact_mod_cast hfact_nat
  have hf : (((Fintype.card G - q).factorial : Nat) : NNReal) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card G - q)
  rw [← hfact]
  field_simp [hf]

/-- **Source-theorem bridge.** The concrete ideal random-function system factor
is exactly the migrated ideal visible-output mass. -/
theorem transcriptSystemFactor_urfRV_eq_idealVisibleMass
    [Fintype G] [DecidableEq G] [Nonempty G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G))
        (vectorOfFunction xs) (vectorOfFunction yv) =
      idealVisibleMass (G := G) (q := q) yv := by
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor
  have hevent :
      (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)).val.mass
          (RandomSystems.CR18.PFunPDE.transcriptSystemEvent
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (vectorOfFunction xs) (vectorOfFunction yv)) =
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)).val.mass
          (fun f : G → G => ∀ i : Fin q, f (xs i) = yv i) := by
    apply RandomSystems.Dist.mass_congr
    intro f
    exact transcriptSystemEvent_urfRV_iff xs yv f
  rw [hevent]
  unfold RandomSystems.CR18.PFunPDS.uniformP
  change (RandomSystems.Dist.uniform (G → G)).mass
      (fun f : G → G => ∀ i : Fin q, f (xs i) = yv i) =
    idealVisibleMass (G := G) (q := q) yv
  have hpointwise :
      (RandomSystems.Dist.uniform (G → G)).mass
          (fun f : G → G => ∀ i : Fin q, f (xs i) = yv i) =
        (RandomSystems.Dist.uniform (G → G)).mass
          (fun f : G → G => (fun i : Fin q => f (xs i)) = yv) := by
    apply RandomSystems.Dist.mass_congr
    intro f
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congr_fun h i
  rw [hpointwise]
  htechnique_dist
  rw [RandomSystems.CR18.uniformFunction_eval_uniform xs hxs]
  rfl

/-- **Source-theorem bridge.** Under the exact fixed-query CR18 environment,
the concrete normalized SoP transcript-prefix law is the migrated real visible
law at the embedded transcript. -/
theorem transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_of_eq
    [AddGroup G] [Fintype G] [DecidableEq G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.CR18.PFunPDE.transcriptLaw
        (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
        (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q
        (transcriptPrefixOfFixedInput xs yv) =
      realVisibleMass (G := G) (q := q) yv := by
  rw [transcriptPrefixOfFixedInput, fixedInputTranscriptPrefix]
  htechnique_fixed_query_core
  exact transcriptSystemFactor_normalizedSoPRV_eq_realVisibleMass
    (G := G) (q := q) xs yv hxs

/-- **Source-theorem bridge.** Under the exact fixed-query CR18 environment,
the concrete ideal random-function transcript-prefix law is the migrated ideal
visible law at the embedded transcript. -/
theorem transcriptLaw_fixedQueryEnvironment_urfRV_of_eq
    [Fintype G] [DecidableEq G] [Nonempty G]
    (xs yv : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.CR18.PFunPDE.transcriptLaw
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
        (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q
        (transcriptPrefixOfFixedInput xs yv) =
      idealVisibleMass (G := G) (q := q) yv := by
  rw [transcriptPrefixOfFixedInput, fixedInputTranscriptPrefix]
  htechnique_fixed_query_core
  exact transcriptSystemFactor_urfRV_eq_idealVisibleMass
    (G := G) (q := q) xs yv hxs

/-- **Source-theorem bridge.** The output-vector law induced by sampling the
normalized SoP system and evaluating it on an injective fixed query tuple is
exactly the migrated real visible-output law. -/
theorem normalizedSoP_outputLaw_eq_realVisibleDist
    [AddGroup G] [Fintype G] [DecidableEq G]
    (xs : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.Dist.fTransform
        (fun p : Equiv.Perm G × Equiv.Perm G =>
          fun i : Fin q => normalizedSoPFunction p (xs i))
        (normalizedSoPProbDist (G := G)).val =
      realVisibleDist (G := G) (q := q) := by
  classical
  apply Finsupp.ext
  intro y
  rw [realVisibleDist_apply]
  rw [← transcriptSystemFactor_normalizedSoPRV_eq_realVisibleMass
    (G := G) (q := q) xs y hxs]
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor normalizedSoPProbDist
  htechnique_mass_event transcriptSystemEvent_normalizedSoPRV_iff
  constructor
  · intro h i
    exact congr_fun h i
  · intro h
    funext i
    exact h i

/-- **Source-theorem bridge.** The output-vector law induced by sampling a
uniform function and evaluating it on an injective fixed query tuple is exactly
the migrated ideal visible-output law. -/
theorem urfRV_outputLaw_eq_idealVisibleDist
    [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (hxs : Function.Injective xs) :
    RandomSystems.Dist.fTransform
        (fun f : G → G => fun i : Fin q => f (xs i))
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)).val =
      idealVisibleDist (G := G) (q := q) := by
  classical
  apply Finsupp.ext
  intro y
  rw [idealVisibleDist_apply]
  rw [← transcriptSystemFactor_urfRV_eq_idealVisibleMass
    (G := G) (q := q) xs y hxs]
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor RandomSystems.CR18.PFunPDS.uniformP
  htechnique_mass_event transcriptSystemEvent_urfRV_iff
  constructor
  · intro h i
    exact congr_fun h i
  · intro h
    funext i
    exact h i

/-- **Source-theorem bridge.** As a finite distribution on CR18 transcript
prefixes, the concrete fixed-query normalized SoP transcript law is exactly the
lifted migrated real visible-output law. -/
theorem transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_dist_eq_liftedRealVisibleDist
    [AddGroup G] [Fintype G] [DecidableEq G]
    (xs : Fin q → G) (hxs : Function.Injective xs) :
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q) =
      liftedRealVisibleDist (G := G) (q := q) xs := by
  calc
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q)
        = fixedInputLiftDist xs
            (RandomSystems.Dist.fTransform
              (fun p : Equiv.Perm G × Equiv.Perm G =>
                fun i : Fin q => normalizedSoPFunction p (xs i))
              (normalizedSoPProbDist (G := G)).val) := by
            simpa [TranscriptLawBridge.dist, normalizedSoPRV] using
              RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist
                (pΩ := normalizedSoPProbDist (G := G))
                (F := normalizedSoPFunction (G := G)) xs
    _ = liftedRealVisibleDist (G := G) (q := q) xs := by
            rw [normalizedSoP_outputLaw_eq_realVisibleDist (G := G) (q := q) xs hxs]

/-- **Source-theorem bridge.** As a finite distribution on CR18 transcript
prefixes, the concrete fixed-query ideal random-function transcript law is
exactly the lifted migrated ideal visible-output law. -/
theorem transcriptLaw_fixedQueryEnvironment_urfRV_dist_eq_liftedIdealVisibleDist
    [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (hxs : Function.Injective xs) :
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q) =
      liftedIdealVisibleDist (G := G) (q := q) xs := by
  change TranscriptLawBridge.dist
      (RandomSystems.CR18.PFunPDE.transcriptLaw
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
        RandomSystems.Dist.unitProbDist.{0}
        (RandomSystems.CR18.functionEvaluatorRV (fun f : G → G => f))
        (fixedQueryEnvironment xs) q) =
    liftedIdealVisibleDist (G := G) (q := q) xs
  calc
    TranscriptLawBridge.dist
        (RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
          RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.functionEvaluatorRV (fun f : G → G => f))
          (fixedQueryEnvironment xs) q)
        = fixedInputLiftDist xs
            (RandomSystems.Dist.fTransform
              (fun f : G → G => fun i : Fin q => f (xs i))
              (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)).val) := by
            simpa [TranscriptLawBridge.dist] using
              RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist
                (pΩ := RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
                (F := fun f : G → G => f) xs
    _ = liftedIdealVisibleDist (G := G) (q := q) xs := by
            rw [urfRV_outputLaw_eq_idealVisibleDist (G := G) (q := q) xs hxs]

/-- **Source-theorem bridge.** Fixed-query SoP H-technique step in the concrete
CR18 transcript-law presentation.  This is the paper proof shape: after the
fixed-query transcript laws are identified with the migrated visible laws, the
one-sided H-technique bound is exactly the visible-law bound. -/
theorem fixedQuerySoP_oneSided_hTechnique
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (eps : NNReal)
    (hxs : Function.Injective xs) (hq : q ≤ Fintype.card G)
    (h_lower : ∀ y : Fin q → G,
      (1 - eps) * idealVisibleMass (G := G) (q := q) y ≤
        realVisibleMass (G := G) (q := q) y) :
    RandomSystems.statDist
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q))
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q)) ≤ eps := by
  rw [transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_dist_eq_liftedRealVisibleDist
      (G := G) (q := q) xs hxs,
    transcriptLaw_fixedQueryEnvironment_urfRV_dist_eq_liftedIdealVisibleDist
      (G := G) (q := q) xs hxs]
  refine liftedVisible_oneSided_hTechnique (G := G) (q := q) xs eps hq ?_
  intro y
  simpa using h_lower y

/-- **Source-theorem bridge.** A pointwise visible-output lower bound transfers
to the concrete fixed-query CR18 transcript law.  This packages the recurring
fixed-query proof step: split a transcript prefix by whether its input vector is
the fixed query vector, reduce the on-vector branch to the visible law, and
close the off-vector branch by zero mass on both sides. -/
theorem fixedQuerySoP_transcriptLaw_lower_bound_of_visible_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (eps : NNReal) (hxs : Function.Injective xs)
    (h_lower : ∀ y : Fin q → G,
      (1 - eps) * idealVisibleMass (G := G) (q := q) y ≤
        realVisibleMass (G := G) (q := q) y)
    (t : TranscriptPrefix G G q) :
    (1 - eps) *
        RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q t ≤
      RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q t := by
  rw [← TranscriptLawBridge.dist_apply
      (RandomSystems.CR18.PFunPDE.transcriptLaw
        (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G))
        RandomSystems.Dist.unitProbDist.{0}
        (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G))
        (fixedQueryEnvironment xs) q) t,
    ← TranscriptLawBridge.dist_apply
      (RandomSystems.CR18.PFunPDE.transcriptLaw
        (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
        (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q) t]
  rw [transcriptLaw_fixedQueryEnvironment_urfRV_dist_eq_liftedIdealVisibleDist
      (G := G) (q := q) xs hxs,
    transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_dist_eq_liftedRealVisibleDist
      (G := G) (q := q) xs hxs]
  change (1 - eps) *
      fixedInputLiftDist xs (idealVisibleDist (G := G) (q := q)) t ≤
    fixedInputLiftDist xs (realVisibleDist (G := G) (q := q)) t
  refine RandomSystems.CR18.fixedInputLiftDist_pointwise_lower_bound xs
    (realVisibleDist (G := G) (q := q)) (idealVisibleDist (G := G) (q := q))
    eps ?_ t
  intro ys
  rw [idealVisibleDist_apply, realVisibleDist_apply]
  exact h_lower ys

/-- **Source theorem bridge.** Pointwise fixed-query SoP transcript-law ratio
with the paper's concrete error term.  This is the local ratio used before
taking statistical distance or passing through adaptive environments. -/
theorem fixedQuerySoP_transcriptLaw_lower_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (hxs : Function.Injective xs)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (t : TranscriptPrefix G G q) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        RandomSystems.CR18.PFunPDE.transcriptLaw
          (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
          (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q t ≤
      RandomSystems.CR18.PFunPDE.transcriptLaw
          (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
          (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q t := by
  exact fixedQuerySoP_transcriptLaw_lower_bound_of_visible_bound
    (G := G) (q := q) xs ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
    hxs (fun y => realVisibleMass_lower_bound (G := G) (q := q) h_bound y) t

/-- **Source theorem bridge.** Fixed-query SoP H-technique theorem with the
paper's concrete error term `q^3 / |G|^2`. -/
theorem fixedQuerySoP_bound
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (xs : Fin q → G) (hxs : Function.Injective xs)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    RandomSystems.statDist
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (normalizedSoPProbDist (G := G)) RandomSystems.Dist.unitProbDist.{0}
            (normalizedSoPRV (G := G)) (fixedQueryEnvironment xs) q))
        (TranscriptLawBridge.dist
          (RandomSystems.CR18.PFunPDE.transcriptLaw
            (RandomSystems.CR18.PFunPDS.uniformP (X := G) (Y := G)) RandomSystems.Dist.unitProbDist.{0}
            (RandomSystems.CR18.PFunPDS.urfRV (X := G) (Y := G)) (fixedQueryEnvironment xs) q)) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact fixedQuerySoP_oneSided_hTechnique (G := G) (q := q) xs
    ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2)
    hxs (RandomSystems.CR18.Counting.q_le_of_cube_le_sq h_bound)
    (fun y => realVisibleMass_lower_bound (G := G) (q := q) h_bound y)

end SoP
end HTechnique
end Migration
end NextGen
