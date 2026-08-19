/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite
import Applications.Frost.Construction

/-!
# FROST on the typed random-systems carrier

This module is the application-facing migration boundary from the abstract
FROST theorem to the production typed random-systems instantiation of AC.
It deliberately does not introduce a witness carrier or a second metric.

The carrier obligations are discharged by `RandomSystemsCC.TypedFinite`:

* resources are `TypedFinite.Phi I U`;
* converters at interface `i` are `TypedFinite.Gamma I U i`;
* protocols are `TypedFinite.Protocol I U`;
* the tuple action and its metric non-expansion are the production instances.

The distinguisher class, its comparison with the operational RS metric, and
the DKG/signing simulator and game leaves remain explicit.  Those are the
application-specific receipts still required for a concrete FROST model; this
bridge must not hide them behind the old maximal-test witness construction.
-/

open scoped ENNReal

namespace RandomSystemsCC.Frost

open AbstractCrypto
open RandomSystems.CR18.TypedResource

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [Fintype I] [DecidableEq I] [DecidableEq U.Code]

/-- The abstract epsilon-relaxed FROST theorem specialized to the production
typed random-systems carrier.  All AC typeclass obligations are inferred from
`RandomSystemsCC.TypedFinite`; only the cryptographic/modeling receipts remain
as hypotheses.

For every tolerated dishonest set `Z`, the composed typed protocol constructs
the `Z`-relaxed ideal within `epsilonDkg + epsilonSign`, and the resulting real
resource satisfies the game bound `epsilonGame + epsilonDkg + epsilonSign`.
-/
theorem frost_instantiated
    (adversaryStructure : AdversaryStructure I)
    (dkgProtocol signingProtocol : TypedFinite.Protocol I U)
    (networkSpecification : Set I → Set (TypedFinite.Phi I U))
    (keyResource thresholdSignatureResource : TypedFinite.Phi I U)
    (distinguishers :
      DistinguisherClass (TypedFinite.Protocol I U) (TypedFinite.Phi I U))
    (distinguisherDistanceLeOperationalDistance :
      ∀ left right : TypedFinite.Phi I U,
        distinguishers.edistD left right ≤ edist left right)
    (tests : Set I → Set (TypedFinite.Phi I U → ℝ≥0∞))
    (epsilonDkg epsilonSign epsilonGame : ℝ≥0∞)
    (testsAdmitted : ∀ dishonest,
      tests dishonest ⊆ distinguishers.tests)
    (dkgSimulation :
      ∀ dishonest ∈ adversaryStructure.sets,
        ∀ resource ∈ networkSpecification dishonest,
          ∃ simulator ∈
              zSub (M := TypedFinite.Protocol I U) tupleGamma dishonest,
            edist
                (patternAttach dishonestᶜ dkgProtocol • resource)
                (simulator • keyResource) ≤
              epsilonDkg)
    (signingSimulation :
      ∀ dishonest ∈ adversaryStructure.sets,
        ∀ resource ∈
            zStar (M := TypedFinite.Protocol I U) tupleGamma dishonest
              {keyResource},
          ∃ simulator ∈
              zSub (M := TypedFinite.Protocol I U) tupleGamma dishonest,
            edist
                (patternAttach dishonestᶜ signingProtocol • resource)
                (simulator • thresholdSignatureResource) ≤
              epsilonSign)
    (testsClosed : ∀ dishonest ∈ adversaryStructure.sets,
      ZClosed (M := TypedFinite.Protocol I U) tupleGamma dishonest
        (tests dishonest))
    (idealGameBound : ∀ dishonest ∈ adversaryStructure.sets,
      thresholdSignatureResource ∈ gameSpec (tests dishonest) epsilonGame) :
    ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ networkSpecification dishonest,
        patternAttach dishonestᶜ (signingProtocol * dkgProtocol) • resource ∈
            Relaxation.eball (epsilonDkg + epsilonSign)
              (zStar (M := TypedFinite.Protocol I U) tupleGamma dishonest
                {thresholdSignatureResource})
        ∧ patternAttach dishonestᶜ
              (signingProtocol * dkgProtocol) • resource ∈
            gameSpec (tests dishonest)
              (epsilonGame + (epsilonDkg + epsilonSign)) :=
  frost_end_to_end_eps adversaryStructure dkgProtocol signingProtocol
    networkSpecification keyResource thresholdSignatureResource
    distinguishers distinguisherDistanceLeOperationalDistance tests
    epsilonDkg epsilonSign epsilonGame testsAdmitted dkgSimulation
    signingSimulation testsClosed idealGameBound

end RandomSystemsCC.Frost
