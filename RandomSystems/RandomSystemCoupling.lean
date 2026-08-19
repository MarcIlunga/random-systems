/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BoundedAttainment

/-!
# Probability couplings for attained random-system representatives

Lanzenberger--Maurer Lemma 4 and thesis Lemma 2.8 state the classical
coupling lemma for probability distributions.  Their random-system coupling
theorems (LanMau20 Theorem 2 and thesis Theorem 2.32) first use the attained
representatives supplied by the preceding distance theorem and then apply
that probability-level lemma.

Source receipt: the original PDFs were checked directly at LanMau20
PDF/printed page 11 (Lemma 4) and page 15 (Theorem 2), and at thesis printed
page 13 (Lemma 2.8), page 20 (Theorems 2.31--2.32), page 21 (the
arbitrary-weight induction lemma), and pages 22--23 (attainment).  The
arbitrary weights belong inside the induction; the public coupling conclusion
is probability-level.

This module isolates exactly the second step.  The finite-support bridge in
`optimal_coupling_exists_finsupp` already handles an arbitrary ambient
carrier by transporting to the finite union of supports.  Here its joint is
proved normalized and packaged as a `Dist.ProbDist`, with both marginals and
the disagreement probability explicit.

The conditional theorem accepts supplied attained representatives.  The final
source-bounded theorem obtains those representatives from Theorem 2.31's
finite/common-domain/bounded induction and then applies the same probability
coupling bridge.  The representatives themselves remain raw PDS laws:
transcript equivalence to the normalized source laws derives their weight one
before the joint is constructed.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-- Two normalized PDS laws on an arbitrary DDS carrier have a normalized
joint whose marginals are the laws and whose disagreement probability is
their statistical distance. -/
theorem optimal_probability_coupling_exists
    (S T : PFunPDS.Prob X Y) :
    ∃ joint : Dist.ProbDist
        (PFunDDS.DDS X Y × PFunDDS.DDS X Y),
      Dist.fTransform Prod.fst joint.val = S.val ∧
      Dist.fTransform Prod.snd joint.val = T.val ∧
      joint.val.mass (fun pair => pair.1 ≠ pair.2) = δ S.val T.val := by
  have hweight : S.val.weight = T.val.weight :=
    Dist.weight_eq_weight_of_isProbDist S.property T.property
  obtain ⟨joint, hjointnn, hfirst, hsecond, hdisagreement⟩ :=
    optimal_coupling_exists_finsupp S.property.nonNeg T.property.nonNeg hweight
  have hprobability : joint.isProbDist := by
    refine ⟨hjointnn, ?_⟩
    calc
      joint.weight = (Dist.fTransform Prod.fst joint).weight :=
        (Dist.weight_fTransform Prod.fst joint).symm
      _ = S.val.weight := congrArg Dist.weight hfirst
      _ = 1 := S.property.weight_eq
  exact ⟨⟨joint, hprobability⟩, hfirst, hsecond, hdisagreement⟩

/-- Given transcript-equivalent representatives attaining `Adv S T`, there
is a normalized joint of those representatives whose disagreement probability
is exactly that advantage.  The orientation is the transcript orientation:
`Adv S T` is the one-sided excess of `S` over `T`; no verdict-advantage swap
is performed here. -/
theorem probability_coupling_exists_with_advantage_disagreement_of_attained_representatives
    (S T : PFunPDS.Prob X Y) (S' T' : PFunPDS X Y)
    (hS'nn : S'.NonNeg) (hT'nn : T'.NonNeg)
    (hS : Equivalent S.val S') (hT : Equivalent T.val T')
    (hattained : (δ S' T' : ℝ) = Adv S.val T.val) :
    ∃ joint : Dist.ProbDist
        (PFunDDS.DDS X Y × PFunDDS.DDS X Y),
      Dist.fTransform Prod.fst joint.val = S' ∧
      Dist.fTransform Prod.snd joint.val = T' ∧
      (joint.val.mass (fun pair => pair.1 ≠ pair.2) : ℝ) =
        Adv S.val T.val := by
  have hSprobability : S'.isProbDist := by
    refine ⟨hS'nn, ?_⟩
    calc
      S'.weight = S.val.weight := (weight_eq_of_equivalent hS).symm
      _ = 1 := S.property.weight_eq
  have hTprobability : T'.isProbDist := by
    refine ⟨hT'nn, ?_⟩
    calc
      T'.weight = T.val.weight := (weight_eq_of_equivalent hT).symm
      _ = 1 := T.property.weight_eq
  let normalizedS : PFunPDS.Prob X Y := ⟨S', hSprobability⟩
  let normalizedT : PFunPDS.Prob X Y := ⟨T', hTprobability⟩
  obtain ⟨joint, hfirst, hsecond, hdisagreement⟩ :=
    optimal_probability_coupling_exists normalizedS normalizedT
  refine ⟨joint, ?_, ?_, ?_⟩
  · simpa [normalizedS] using hfirst
  · simpa [normalizedT] using hsecond
  · calc
      joint.val.mass (fun pair => pair.1 ≠ pair.2) =
          δ S' T' := by
        simpa [normalizedS, normalizedT] using hdisagreement
      _ = Adv S.val T.val := hattained

/-- Lanzenberger--Maurer Theorem 2 / thesis Theorem 2.32 at the source-bounded
boundary.  Normalized systems with a finite input alphabet, one common domain,
and a uniform query bound have equivalent raw representatives and a normalized
joint of those representatives whose disagreement probability is their
optimal transcript advantage. -/
theorem exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded
    [Fintype X] (S T : PFunPDS.Prob X Y) {D : Set (List X)} {q : Nat}
    (h : PFunPDS.HaveCommonDomainAndBounded S.val T.val D q) :
    ∃ S' T' : PFunPDS X Y,
      ∃ joint : Dist.ProbDist
          (PFunDDS.DDS X Y × PFunDDS.DDS X Y),
        Equivalent S' S.val ∧
        Equivalent T' T.val ∧
        Dist.fTransform Prod.fst joint.val = S' ∧
        Dist.fTransform Prod.snd joint.val = T' ∧
        (joint.val.mass (fun pair => pair.1 ≠ pair.2) : ℝ) =
          Adv S.val T.val := by
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', _, _, hdelta⟩ :=
    exists_equivalent_representatives_with_delta_eq_optimal_advantage_of_finite_common_domain_and_bounded
      S.property.nonNeg T.property.nonNeg h
  obtain ⟨joint, hfirst, hsecond, hdisagreement⟩ :=
    probability_coupling_exists_with_advantage_disagreement_of_attained_representatives
      S T S' T' hS'nn hT'nn (fun e n => (hS' e n).symm)
        (fun e n => (hT' e n).symm) hdelta
  exact ⟨S', T', joint, hS', hT', hfirst, hsecond, hdisagreement⟩

end RandomSystems.CR18
