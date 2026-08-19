/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import RandomSystems.DistExpect
import RandomSystems.DistCoupling
import RandomSystems.StatDist
import RandomSystems.DistLift
import RandomSystems.DistMeasure
import RandomSystems.DistCond
import RandomSystems.DistIndepMeasure
import RandomSystems.KWiseIndepPoly
import RandomSystems.Entropy
import RandomSystems.UniversalHash
import RandomSystems.Coupling
import RandomSystems.StrictContext
import RandomSystems.StrictContextAdvantage
import RandomSystems.StrictContextTotal
import RandomSystems.StrictContextSharedDomain
import RandomSystems.StrictRelabel
import RandomSystems.TypedResource
import RandomSystems.ResourceMachine
import RandomSystems.Jost
import RandomSystems.TypedAction
import RandomSystems.TypedParallel
import RandomSystems.TypedFraming
import RandomSystems.TypedFramingMetric
import RandomSystems.TypedUnitCoherence
import RandomSystems.TypedUnitMetric
import RandomSystems.RandomSystemParallel
import RandomSystems.StrictParallel
import RandomSystems.ClosedApplication
import RandomSystems.TypedTensor
import RandomSystems.TypedInterfaceRelabel
import RandomSystems.TypedTensorShuffle
import RandomSystems.TypedAttachRelabel
import RandomSystems.TypedPullback
import RandomSystems.AttainmentCounterexample
import RandomSystems.StatefulConverterChecks
import RandomSystems.BoundedAttainment
import RandomSystems.RandomSystemCoupling
import RandomSystems.VirtualPDS
import RandomSystems.GameWinnability
import RandomSystems.ThesisModel
import RandomSystems.LanzenbergerChain
import RandomSystems.TranscriptHybrid
import RandomSystems.Example216
import RandomSystems.RandomSystemMetric
import RandomSystems.CascadeRealization
import RandomSystems.CombineRealization
import RandomSystems.DependentTranscript
import RandomSystems.ReductionByConverter
import RandomSystems.ReductionByInstantiation
import RandomSystems.HTechnique.Surface

/-!
# Maurer's Random Systems Framework

Lean 4 formalization of Lanzenberger-Maurer (TCC 2020):
"Coupling of Random Systems."

A fixed-signature source-theorem random system remains an equivalence class of
normalized distributions over partial deterministic systems under equality of
observable transcript laws, with maximal distinguishing advantage as its
metric.  The deterministic AC-facing path is separate and strict:
`StrictContext` treats `Part.none` as blocking divergence, while
`TypedResource`/`TypedAction` provide dependent typed interfaces, contextual
behavior and arbitrary stateful `IsDDC` attachment without `Emulable` or
`FrameCompatible`.

`StrictParallel` extends the strict path with the parallel axis: parallel
composition descends to the strict quotient, is `‖`-non-expanding there
(Maurer11 eq. (3) for the strict metric — proved directly by
fixed-component absorption, not transferred from `Δ`), and has unique
decompositions (strict cancellation via component-embedding converters).

The pure root defines no Abstract-Crypto instance.  The one selected instance
is exported by the sibling-facing `RandomSystemsCC` root.
The source theorem identifying that metric with minimum representative
distance is proved separately under its finite/common-domain/bounded-depth
hypotheses and is not assumed by the public carrier. Its normalized coupling
corollary is likewise exposed as a separate source-bounded result.

The historical bounded API remains importable under `RandomSystems.Legacy`
but is intentionally outside this selected public root.
-/
