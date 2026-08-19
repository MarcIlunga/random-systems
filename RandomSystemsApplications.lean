/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- The Boneh–Shoup game-based layer and its cost models.
import RandomSystems.Complexity.All
import RandomSystems.Complexity.AdvantageSeq
import RandomSystems.Complexity.BitGuessing
import RandomSystems.Complexity.CPA
import RandomSystems.Complexity.ConverterBridge
import RandomSystems.Complexity.CostMap
import RandomSystems.Complexity.CostModels
import RandomSystems.Complexity.DifferenceLemmaBridge
import RandomSystems.Complexity.GameBased
import RandomSystems.Complexity.GameEquivBridge
import RandomSystems.Complexity.GameHop
import RandomSystems.Complexity.GameReduction
import RandomSystems.Complexity.GameSeq
import RandomSystems.Complexity.IidGames
import RandomSystems.Complexity.PFunProblems
import RandomSystems.Complexity.PRF
import RandomSystems.Complexity.PRG
import RandomSystems.Complexity.SwitchingBridge
import RandomSystems.Complexity.Tactics
-- Boneh–Shoup Part I: the symmetric-primitive library (declarations only).
import RandomSystems.BonehShoup.All
-- HCTR2 (ePrint 2021/1441): the paper development over GF(2^128).
import RandomSystems.BitVecFacts
import RandomSystems.HCTR2
import RandomSystems.HTechnique.GF2Field
import RandomSystems.HTechnique.HCTR2Paper
import RandomSystems.HTechnique.TweakablePRP
-- SpoC-128 AEAD real/ideal distinction and concrete attack.
import RandomSystems.SpoC.NIST
import RandomSystems.SpoC.Distinguishing
-- CBC-MAC beyond the birthday bound (Jha–Nandi structure graphs).
import RandomSystems.CBCStructureGraph
-- Sum of two independent random permutations, by conditional equivalence.
import RandomSystems.SumOfPermutations
-- The same construction beyond the birthday bound, by a balanced-fiber monitored condition.
import RandomSystems.SumOfPermutationsTight
-- The exact DNS mirror proof on the XOR carrier; its group-general reach remains explicit.
import RandomSystems.SumOfPermutationsOptimal
-- Collision-proxy/broken-cycle proof for XOR SoP, with tight finite tail constants.
import RandomSystems.SoP.XORGainGraph
-- Signed degree-two-plus-three certificate with an exact sparse main term.
import RandomSystems.SoP.XORSignedDegreeThree
-- Exact four-row coefficient classification and retained degree-four certificate.
import RandomSystems.SoP.XORSignedDegreeFour
-- Explicit fixed-query collision distinguisher matching that certificate.
import RandomSystems.SoP.XORCollisionAttack
-- Honest signed local-repair representative and its two-sided sparse certificate.
import RandomSystems.SoP.SignedLocalRepair
-- Collision-count threshold distinguisher matching the proxy across regimes.
import RandomSystems.SoP.XORCollisionThreshold
-- Exact Poisson/Gaussian MAD targets and the finite normal-transfer certificate.
import RandomSystems.SoP.XORCollisionAsymptotics
-- Independent finite collision-count Stein bound and birthday/Poisson limits.
import RandomSystems.SoP.CollisionCountPoisson
-- Planted-edge size-bias proof of the full fixed-rate Poisson interpolation.
import RandomSystems.SoP.CollisionCountPoissonFixed
-- General signed-distance layer instantiated by the XOR visible truncation.
import RandomSystems.SoP.XORVirtualRepresentative
-- Full-deck checksum and global-shift quotient identities for the high-query regime.
import RandomSystems.SoP.XORComplement
-- Exact spectral deletion of the constant and translated two-row quotient modes.
import RandomSystems.SoP.XORComplementSpectrum
-- No-loss split of the remaining full-deck spectrum into majority and balanced profiles.
import RandomSystems.SoP.XORComplementMultiplicity
-- Explicit Pascal bound for every quotient profile with multiplicity above three quarters.
import RandomSystems.SoP.XORComplementSparse
-- Exact profile symmetries and the finite balanced-hyperplane reduction for the remaining tail.
import RandomSystems.SoP.XORComplementProfiles
-- Finite-torus square-root bound for each balanced row profile.
import RandomSystems.SoP.XORComplementSquareRoot
-- Elementary support-layer aggregation closing the full-deck residual.
import RandomSystems.SoP.XORComplementEntropy
-- Exact signed marginal bridge from the full deck to every prefix with at
-- least three hidden rows.
import RandomSystems.SoP.XORComplementMarginal
-- Exact final-two-prefix corrections and the unified all-q<N endpoint.
import RandomSystems.SoP.XORComplementBoundary
-- H-technique application machinery and sum-of-permutations.
import RandomSystems.HTechnique.All
import RandomSystems.HTechnique.AdaptiveBridge
import RandomSystems.HTechnique.AdaptiveTranscriptAdvantage
import RandomSystems.HTechnique.AdaptiveTranscriptLawAdvantage
import RandomSystems.HTechnique.Density
import RandomSystems.HTechnique.FixedQuery
import RandomSystems.HTechnique.FixedQueryCompatibility
import RandomSystems.HTechnique.IdealCompression
import RandomSystems.HTechnique.SoP.AdaptiveAdvantage
import RandomSystems.HTechnique.TranscriptLaw

/-!
# The application layer over the random-systems foundation

Aggregator root of `lean_lib RandomSystemsApplications`: the applications and
examples built **on** the foundation — HCTR2 (ePrint 2021/1441), CBC-MAC
beyond the birthday bound, the Boneh–Shoup game-based layer with its cost
models, sum-of-permutations, and the H-technique application machinery.
Every module classed `application` in `module_audit_baseline.json`
(owner's classification, 2026-07-27) is imported here explicitly, so dropping
one from this list makes it a NEW orphan and fails `lake run moduleAudit`.

This target exists for **coverage, not coupling**:

* It is NOT a `@[default_target]`, and nothing in `lean_lib RandomSystems` or
  `lean_lib RandomSystemsCC` imports it.  The dependency arrow points
  applications → foundation, never back.  These modules may later move to
  their own project.
* Build and gate with `lake build RandomSystemsApplications`.

Two deliberate inclusions:

* `RandomSystems.CBCStructureGraph` is parked and holds the **only** live
  `sorry` under `RandomSystems/**` (`mass_cbcGraphBad_le`, the documented
  residual pure-combinatorics bound).  It is imported here **on purpose**: the
  admission then surfaces as a compiler warning on every build of this target
  instead of hiding in an uncompiled file.  The build still exits 0 and no
  syntactic gate scans this tree for `sorry`, so the tree stays green.
* `RandomSystems.HTechnique.SoP.AdaptiveAdvantage` (classed `application`)
  imports `RandomSystems.HTechnique.SoP.CompressionLegacy` (classed
  `legacy-bridge`), which does **not** import the quarantined
  `RandomSystems.Legacy` tree — so it compiles here as an ordinary
  dependency.  The bridges that do import `RandomSystems.Legacy.*` are NOT
  imported here; they stay behind the `RandomSystems.HTechnique.LegacyChecks`
  gate.
-/
