/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Public CR18 transcript-law surface

This module contains the law-level transcript objects used by the curated
H-technique migration surface.  It deliberately avoids representative
structures: public endpoints should speak about PDS/PDE laws, deterministic CR18
environments, and transcript-prefix distributions.
-/

noncomputable section

universe u v

namespace RandomSystems
namespace HTechnique

/-- **Source-theorem bridge; candidate for upstream.** The CR18 transcript
carrier used by the H-technique migration. Naming this carrier keeps public
statements at the transcript level instead of exposing the underlying
`PFunPDE.TranscriptPrefix` implementation path. -/
abbrev TranscriptPrefix (X : Type u) (Y : Type v) (q : Nat) :=
  RandomSystems.CR18.PFunPDE.TranscriptPrefix X Y q

/-- **Source-theorem bridge; candidate for upstream.** The finite transcript
space assumption needed to turn a CR18 transcript law into a finite
distribution. This is definitionally the existing `Fintype` requirement; the
name records the mathematical object rather than the implementation carrier. -/
abbrev FiniteTranscriptSpace (X : Type u) (Y : Type v) (q : Nat) :=
  Fintype (TranscriptPrefix X Y q)

/-- **Source-theorem bridge; candidate for upstream.** The decidable transcript
space assumption used by finite H-technique summation lemmas. This is kept
separate from `FiniteTranscriptSpace` so statements that only need finiteness do
not acquire a decidable-equality hypothesis. -/
abbrev DiscreteTranscriptSpace (X : Type u) (Y : Type v) (q : Nat) :=
  DecidableEq (TranscriptPrefix X Y q)

/-- **Source-theorem bridge; candidate for upstream.** A probability
distribution over PFun-native deterministic systems.  This is the law-level
probability PDS object used by paper-facing H-technique endpoints. -/
abbrev ProbPDS (X : Type u) (Y : Type v) :=
  RandomSystems.CR18.PFunPDS.Prob X Y

/-- **Source-theorem bridge; candidate for upstream.** A probability
distribution over PFun-native deterministic environments, reusing the core
`PFunPDE` law type and bundling the standing probability assumption. -/
abbrev ProbPDE (X : Type u) (Y : Type v) :=
  RandomSystems.CR18.PFunPDE.Prob X Y

/-- Compatibility alias for deterministic CR18 environment query-totality.
The reusable predicate lives in core as `PFunPDE.DDEKQueryTotal`; the migration
name keeps existing H-technique statements stable while the surface is being
promoted. -/
abbrev DDEKQueryTotal {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) (q : Nat) : Prop :=
  RandomSystems.CR18.PFunPDE.DDEKQueryTotal E q

/-- Deterministic CR18 environments that issue exactly the `q` concrete queries
needed to define a length-`q` transcript-prefix law. -/
abbrev QQueryEnvironment (X : Type u) (Y : Type v) (q : Nat) :=
  RandomSystems.CR18.PFunPDE.QQueryEnvironment X Y q

namespace ProbPDE

/-- **Source-theorem bridge; candidate for upstream.** Embed a deterministic
CR18 environment as the degenerate law-level PDE concentrated on that
environment. -/
noncomputable abbrev ofDDE {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) : ProbPDE X Y :=
  RandomSystems.CR18.PFunPDE.Prob.ofDDE E

/-- Law-level totality for exactly `q` environment queries: every deterministic
environment in the law's support issues a concrete next query on output histories
of length `< q`. -/
abbrev KQueryTotal {X : Type u} {Y : Type v} (E : ProbPDE X Y) (q : Nat) : Prop :=
  RandomSystems.CR18.PFunPDE.Prob.KQueryTotal E q

/-- **Source-theorem bridge; candidate for upstream.** If a deterministic CR18
environment is q-query-total, then its degenerate law-level PDE is
q-query-total. -/
theorem ofDDE_KQueryTotal {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) {q : Nat}
    (hE : DDEKQueryTotal E q) :
    KQueryTotal (ofDDE E) q := by
  exact RandomSystems.CR18.PFunPDE.Prob.ofDDE_KQueryTotal E hE

end ProbPDE

namespace ProbPDS

/-- Law-level totality up to `q` system queries: every deterministic system in
the law's support produces a concrete output on every nonempty input history of
length at most `q`. -/
abbrev KStepTotal {X : Type u} {Y : Type v} (S : ProbPDS X Y) (q : Nat) : Prop :=
  RandomSystems.CR18.PFunPDS.Prob.KStepTotal S q

/-- The transcript-prefix law induced by law-level system and environment
objects.  The sample spaces are the deterministic systems/environments
themselves; no representative wrapper is exposed. -/
noncomputable abbrev transcriptLaw {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) (E : ProbPDE X Y) (q : Nat) :
    RandomSystems.CR18.PFunPDE.TranscriptLaw X Y q :=
  RandomSystems.CR18.PFunPDS.Prob.transcriptLaw S E q

/-- The transcript-prefix distribution induced by law-level system and
environment objects. -/
noncomputable abbrev transcriptDist {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : ProbPDE X Y) :
    RandomSystems.Dist (TranscriptPrefix X Y q) :=
  RandomSystems.CR18.PFunPDS.Prob.transcriptDist (q := q) S E

/-- **Source-theorem bridge; candidate for upstream.** A law-level CR18
transcript distribution is always a subdistribution. -/
theorem transcriptDist_weight_le_one {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : ProbPDE X Y) :
    (transcriptDist (q := q) S E).weight ≤ 1 := by
  exact RandomSystems.CR18.PFunPDS.Prob.transcriptDist_weight_le_one (q := q) S E

/-- **Source-theorem bridge; candidate for upstream.** If the law-level system
and environment are total on their supports, their CR18 transcript distribution
has total mass one. -/
theorem transcriptDist_weight_eq_one_of_total {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : ProbPDE X Y)
    (hS : S.KStepTotal q) (hE : E.KQueryTotal q) :
    (transcriptDist (q := q) S E).weight = 1 := by
  exact RandomSystems.CR18.PFunPDS.Prob.transcriptDist_weight_eq_one_of_total
    (q := q) S E hS hE

/-- **Source-theorem bridge; candidate for upstream.** Transcript distribution
for a law-level PDS against a deterministic CR18 environment.  The public inputs
are exactly the PDS law and the deterministic environment. -/
noncomputable abbrev deterministicTranscriptDist {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    RandomSystems.Dist (TranscriptPrefix X Y q) :=
  RandomSystems.CR18.PFunPDS.Prob.deterministicTranscriptDist (q := q) S E

/-- The deterministic-environment transcript distribution is pointwise
non-negative: each entry is an event mass under a product probability law. -/
theorem deterministicTranscriptDist_nonNeg {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    (deterministicTranscriptDist (q := q) S E).NonNeg :=
  RandomSystems.CR18.PFunPDE.deterministicTranscriptLawDist_nonNeg S E

/-- **Source-theorem bridge; candidate for upstream.** A degenerate law-level
PDE concentrated on a deterministic environment induces the same transcript
distribution as the deterministic transcript-law specialization. -/
@[simp]
theorem transcriptDist_ofDDE {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    transcriptDist (q := q) S (ProbPDE.ofDDE E) =
      deterministicTranscriptDist (q := q) S E := by
  exact RandomSystems.CR18.PFunPDS.Prob.transcriptDist_ofDDE (q := q) S E

/-- **Source-theorem bridge; candidate for upstream.** The ideal uniform random
function as a law-level PDS. -/
noncomputable abbrev urf {X : Type u} {Y : Type v}
    [Fintype (X → Y)] [Nonempty (X → Y)] : ProbPDS X Y :=
  RandomSystems.CR18.PFunPDS.Prob.urf (X := X) (Y := Y)

/-- **Source-theorem bridge; candidate for upstream.** The ideal uniform random
permutation as a law-level PDS. -/
noncomputable abbrev urp {X : Type u} [Fintype X] : ProbPDS X X :=
  RandomSystems.CR18.PFunPDS.Prob.urp (X := X)

end ProbPDS

end HTechnique
end RandomSystems
