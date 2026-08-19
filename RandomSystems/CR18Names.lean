/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Canonical short spellings for the CR18 law-level surface

Paper-facing names for the law-level probability objects, owned by the core
`RandomSystems.CR18` namespace.  These were introduced by the H-technique
migration (`RandomSystems.HTechnique.TranscriptLawPublic`, formerly marked
"candidate for upstream") and are promoted here as the canonical spellings;
the `HTechnique` aliases remain as compatibility until that layer's final
deprecation.
-/

namespace RandomSystems.CR18

universe u v

/-- A probability law over PFun-native deterministic systems (CR18
Definition 3.14 with the probability constraint bundled). -/
abbrev ProbPDS (X : Type u) (Y : Type v) :=
  PFunPDS.Prob X Y

/-- A probability law over PFun-native deterministic environments. -/
abbrev ProbPDE (X : Type u) (Y : Type v) :=
  PFunPDE.Prob X Y

/-- The CR18 transcript-prefix carrier for `q` queries. -/
abbrev TranscriptPrefix (X : Type u) (Y : Type v) (q : Nat) :=
  PFunPDE.TranscriptPrefix X Y q

/-- Finiteness of the transcript space, named after the mathematical
assumption rather than the implementation carrier. -/
abbrev FiniteTranscriptSpace (X : Type u) (Y : Type v) (q : Nat) :=
  Fintype (TranscriptPrefix X Y q)

/-- Deterministic CR18 environments issuing exactly the `q` concrete queries
of a length-`q` transcript-prefix law. -/
abbrev QQueryEnvironment (X : Type u) (Y : Type v) (q : Nat) :=
  PFunPDE.QQueryEnvironment X Y q

/-- Decidability of transcript equality, kept separate from
`FiniteTranscriptSpace` so statements that only need finiteness do not
acquire a decidable-equality hypothesis. -/
abbrev DiscreteTranscriptSpace (X : Type u) (Y : Type v) (q : Nat) :=
  DecidableEq (TranscriptPrefix X Y q)

end RandomSystems.CR18
