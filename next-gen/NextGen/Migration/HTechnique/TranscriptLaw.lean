/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.TranscriptLawPublic
import NextGen.Migration.HTechnique.TranscriptLawCore

/-!
# Transcript-law H-technique bridge

This module connects the distribution-level migrated H-technique facts to the
`NextGen.PDS.transcriptLaw` API.

Source status:

* support lemma forced by formalization: the distribution-level H-technique
  applies to finite transcript-law mass functions;
* source-theorem bridge: CR18/thesis transcript laws can therefore be used as
  the transcript distributions in H-coefficient proofs.

The generic finite-mass-function and support-subtype adapters live in
`RandomSystems.Dist` as `RandomSystems.Dist.ofFiniteMassFunction` and
`RandomSystems.Dist.supportProbDist`; the CR18 transcript-law distribution
adapter now lives at the source surface as `PFunPDE.transcriptLawDist`.

The law-level public aliases and deterministic transcript distributions live in
`TranscriptLawPublic`.  This module keeps representative-level adapters and
H-technique proof wrappers.

Migration note: this module is compatibility-only.  New public theorems should
be stated on `ProbPDS`, `ProbPDE`, deterministic CR18 environments, and named
transcript laws; representative objects remain support-level only.
-/

noncomputable section

open scoped BigOperators NNReal

universe u v w z r

namespace NextGen
namespace Migration
namespace HTechnique

/-- **Source-theorem bridge; candidate for upstream.** A CR18 representative of
a probabilistic discrete system, bundling the ambient sample space, its
probability distribution, and the system-valued random variable.

Public H-technique endpoints should take this object rather than exposing
`Ω`, `pΩ`, and the random variable as separate theorem parameters. -/
structure PDSRepresentative (X : Type u) (Y : Type v) where
  /-- Ambient sample space for the representative. -/
  Ω : Type w
  /-- Probability distribution on samples. -/
  prob : RandomSystems.Dist.ProbDist Ω
  /-- System-valued random variable. -/
  rv : RandomSystems.CR18.PFunPDS.RV Ω X Y

/-- **Source-theorem bridge; candidate for upstream.** A CR18 representative of
a probabilistic discrete environment, bundling the ambient sample space, its
probability distribution, and the environment-valued random variable.

This is the environment-side analogue of `PDSRepresentative`: public
H-technique endpoints should take this object rather than exposing `Ω`, `pΩ`,
and the random environment as separate theorem parameters. -/
structure PDERepresentative (X : Type u) (Y : Type v) where
  /-- Ambient sample space for the representative. -/
  Ω : Type w
  /-- Probability distribution on samples. -/
  prob : RandomSystems.Dist.ProbDist Ω
  /-- Environment-valued random variable. -/
  rv : RandomSystems.CR18.PFunPDE.RV Ω X Y

namespace PDERepresentative

/-- Representative-level totality for exactly `q` environment queries. -/
def KQueryTotal {X : Type u} {Y : Type v} (E : PDERepresentative X Y) (q : Nat) :
    Prop :=
  RandomSystems.CR18.PFunPDE.RV.KQueryTotal E.rv q

/-- Deterministic environments as representatives over the one-point
probability space. -/
def deterministic {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunPDE.RV PUnit X Y) :
    PDERepresentative.{u, v, 0} X Y where
  Ω := PUnit
  prob := RandomSystems.Dist.unitProbDist
  rv := E

/-- **Source-theorem bridge; candidate for upstream.** A deterministic CR18
environment as a representative over the one-point probability space.  This is
the tight adapter for thesis-style deterministic environments; it avoids
exposing an artificial one-point random variable in public statements. -/
def ofDDE {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    PDERepresentative.{u, v, 0} X Y :=
  deterministic
    ((fun _ : PUnit => E) : RandomSystems.CR18.PFunPDE.RV PUnit X Y)

/-- Canonical representative of a law-level PDE: use the deterministic
environments in the law's finite support as samples.  This is support-based so
representative-level side conditions such as query-totality range over exactly
the environments that can occur under the law. -/
noncomputable def ofProbPDE {X : Type u} {Y : Type v}
    (E : ProbPDE X Y) : PDERepresentative X Y where
  Ω := {e : RandomSystems.CR18.PFunDDS.DDE X Y // e ∈ E.val.support}
  prob := RandomSystems.Dist.supportProbDist E
  rv := fun e => e.1

end PDERepresentative

@[simp]
theorem PDERepresentative.ofDDE_KQueryTotal {X : Type u} {Y : Type v}
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) (q : Nat) :
    (PDERepresentative.ofDDE E).KQueryTotal q ↔ DDEKQueryTotal E q := by
  constructor
  · intro h ys hlen
    exact h PUnit.unit ys hlen
  · intro h _ω ys hlen
    exact h ys hlen

@[simp]
theorem PDERepresentative.ofProbPDE_KQueryTotal {X : Type u} {Y : Type v}
    (E : ProbPDE X Y) (q : Nat) :
    (PDERepresentative.ofProbPDE E).KQueryTotal q ↔ E.KQueryTotal q := by
  constructor
  · intro h e he ys hlen
    exact h ⟨e, he⟩ ys hlen
  · intro h e ys hlen
    exact h e.1 e.2 ys hlen

namespace PDSRepresentative

/-- The raw `PFunPDS` law induced by a representative. -/
noncomputable def law {X : Type u} {Y : Type v} (S : PDSRepresentative X Y) :
    RandomSystems.CR18.PFunPDS X Y :=
  RandomSystems.CR18.PFunPDS.RV.law S.prob S.rv

/-- Canonical representative of a law-level PDS: use the deterministic systems
in the law's finite support as samples.  This is support-based so
representative-level side conditions such as query-totality range over exactly
the systems that can occur under the law. -/
noncomputable def ofProbPDS {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) : PDSRepresentative X Y where
  Ω := {s : RandomSystems.CR18.PFunDDS.DDS X Y // s ∈ S.val.support}
  prob := RandomSystems.Dist.supportProbDist S
  rv := fun s => s.1

/-- **Source-theorem bridge; candidate for upstream.** The ideal uniform random
function packaged as a CR18 representative.

This is a constructor adapter: theorem statements can name the represented
system while the function sample space, uniform probability distribution, and
function-evaluator RV stay inside the construction. -/
noncomputable def urf {X : Type u} {Y : Type v}
    [Fintype (X → Y)] [Nonempty (X → Y)] : PDSRepresentative X Y where
  Ω := X → Y
  prob := RandomSystems.CR18.PFunPDS.uniformP (X := X) (Y := Y)
  rv := RandomSystems.CR18.PFunPDS.urfRV (X := X) (Y := Y)

/-- Representative-level totality up to `q` system queries. -/
def KStepTotal {X : Type u} {Y : Type v} (S : PDSRepresentative X Y) (q : Nat) : Prop :=
  RandomSystems.CR18.PFunPDS.RV.KStepTotal S.rv q

@[simp]
theorem ofProbPDS_KStepTotal {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) (q : Nat) :
    (ofProbPDS S).KStepTotal q ↔ S.KStepTotal q := by
  constructor
  · intro h s hs xs hxs hlen
    exact h ⟨s, hs⟩ xs hxs hlen
  · intro h s xs hxs hlen
    exact h s.1 s.2 xs hxs hlen

/-- The transcript-prefix law induced by a system representative and an
environment representative. -/
noncomputable def transcriptLaw {X : Type u} {Y : Type v}
    (S : PDSRepresentative X Y)
    (E : PDERepresentative.{u, v, r} X Y) (q : Nat) :
    RandomSystems.CR18.PFunPDE.TranscriptLaw X Y q :=
  RandomSystems.CR18.PFunPDE.transcriptLaw S.prob E.prob S.rv E.rv q

/-- The transcript-prefix distribution induced by a system representative and an
environment representative. -/
noncomputable def transcriptDist {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : PDSRepresentative X Y)
    (E : PDERepresentative.{u, v, r} X Y) :
    RandomSystems.Dist (TranscriptPrefix X Y q) :=
  RandomSystems.CR18.PFunPDE.transcriptLawDist (transcriptLaw S E q)

/-- A representative and its canonical law representative have the same system
factor.  This is the law-invariance bridge that keeps paper-facing statements
on PDS laws while reusing representative-level transcript infrastructure. -/
theorem transcriptSystemFactor_ofProbPDS_pmf
    {X : Type u} {Y : Type v}
    (S : PDSRepresentative.{u, v, w} X Y)
    {q : Nat} (xs : TranscriptPrefix X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        (ofProbPDS (RandomSystems.Dist.PMF S.prob S.rv)).prob
        (ofProbPDS (RandomSystems.Dist.PMF S.prob S.rv)).rv xs.1 xs.2 =
      RandomSystems.CR18.PFunPDE.transcriptSystemFactor S.prob S.rv xs.1 xs.2 := by
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor ofProbPDS RandomSystems.Dist.PMF
  calc
    (RandomSystems.Dist.supportProbDist
          ⟨RandomSystems.Dist.fTransform S.rv S.prob.val,
            RandomSystems.Dist.fTransform_isProbDist S.rv S.prob.property⟩).val.mass
        (fun s =>
          RandomSystems.CR18.PFunPDE.transcriptSystemEvent
            ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
              RandomSystems.CR18.PFunPDS.RV
                (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
            xs.1 xs.2 s.1)
      = (RandomSystems.Dist.fTransform S.rv S.prob.val).mass
          (RandomSystems.CR18.PFunPDE.transcriptSystemEvent
            ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
              RandomSystems.CR18.PFunPDS.RV
                (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
            xs.1 xs.2) := by
          exact RandomSystems.Dist.supportProbDist_mass_preimage _ _
    _ = S.prob.val.mass (RandomSystems.CR18.PFunPDE.transcriptSystemEvent S.rv xs.1 xs.2) := by
          rw [RandomSystems.Dist.mass_fTransform]
          exact RandomSystems.Dist.mass_congr S.prob.val (fun _ => Iff.rfl)

/-- **Source-theorem bridge; candidate for upstream.** Replacing a law-level
PDS by its finite-support representative preserves every transcript system
factor. -/
theorem transcriptSystemFactor_ofProbPDS
    {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) {q : Nat} (xs : TranscriptPrefix X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        (ofProbPDS S).prob (ofProbPDS S).rv xs.1 xs.2 =
      RandomSystems.CR18.PFunPDE.transcriptSystemFactor S
        ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
          RandomSystems.CR18.PFunPDS.RV
            (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
        xs.1 xs.2 := by
  unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor ofProbPDS
  simpa using
    (RandomSystems.Dist.supportProbDist_mass_preimage S
      (RandomSystems.CR18.PFunPDE.transcriptSystemEvent
        ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
          RandomSystems.CR18.PFunPDS.RV
            (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
        xs.1 xs.2))

/-- **Source-theorem bridge; candidate for upstream.** Replacing a law-level
PDE by its finite-support representative preserves every transcript
environment factor. -/
theorem transcriptEnvironmentFactor_ofProbPDE
    {X : Type u} {Y : Type v}
    (E : ProbPDE X Y) {q : Nat} (xs : TranscriptPrefix X Y q) :
    RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor
        (PDERepresentative.ofProbPDE E).prob
        (PDERepresentative.ofProbPDE E).rv xs.1 xs.2 =
      RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E
        ((fun e : RandomSystems.CR18.PFunDDS.DDE X Y => e) :
          RandomSystems.CR18.PFunPDE.RV
            (RandomSystems.CR18.PFunDDS.DDE X Y) X Y)
        xs.1 xs.2 := by
  unfold RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor
    PDERepresentative.ofProbPDE
  simpa using
    (RandomSystems.Dist.supportProbDist_mass_preimage E
      (RandomSystems.CR18.PFunPDE.transcriptEnvironmentEvent
        ((fun e : RandomSystems.CR18.PFunDDS.DDE X Y => e) :
          RandomSystems.CR18.PFunPDE.RV
            (RandomSystems.CR18.PFunDDS.DDE X Y) X Y)
        xs.1 xs.2))

/-- **Source-theorem bridge; candidate for upstream.** Direct law-level PDS/PDE
transcript laws are the same as the transcript laws of their finite-support
representatives. -/
theorem transcriptLaw_ofProbPDS_probPDE
    {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) (E : ProbPDE X Y)
    {q : Nat} (t : TranscriptPrefix X Y q) :
    ProbPDS.transcriptLaw S E q t =
      transcriptLaw (ofProbPDS S) (PDERepresentative.ofProbPDE E) q t := by
  have hsystem :
      RandomSystems.CR18.PFunPDE.transcriptSystemFactor S
          ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
            RandomSystems.CR18.PFunPDS.RV
              (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
          t.1 t.2 =
        RandomSystems.CR18.PFunPDE.transcriptSystemFactor
          (ofProbPDS S).prob (ofProbPDS S).rv t.1 t.2 := by
    exact (transcriptSystemFactor_ofProbPDS S t).symm
  have henvironment :
      RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E
          ((fun e : RandomSystems.CR18.PFunDDS.DDE X Y => e) :
            RandomSystems.CR18.PFunPDE.RV
              (RandomSystems.CR18.PFunDDS.DDE X Y) X Y)
          t.1 t.2 =
        RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor
          (PDERepresentative.ofProbPDE E).prob
          (PDERepresentative.ofProbPDE E).rv t.1 t.2 := by
    exact (transcriptEnvironmentFactor_ofProbPDE E t).symm
  unfold ProbPDS.transcriptLaw RandomSystems.CR18.PFunPDS.Prob.transcriptLaw transcriptLaw
  rw [RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    hsystem, henvironment]

/-- Distribution-level form of `transcriptLaw_ofProbPDS_probPDE`. -/
@[simp]
theorem transcriptDist_ofProbPDS_probPDE
    {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : ProbPDE X Y) :
    ProbPDS.transcriptDist (q := q) S E =
      transcriptDist (q := q) (ofProbPDS S) (PDERepresentative.ofProbPDE E) := by
  ext t
  simp [ProbPDS.transcriptDist, RandomSystems.CR18.PFunPDS.Prob.transcriptDist,
    transcriptDist,
    transcriptLaw_ofProbPDS_probPDE]

/-- **Source-theorem bridge; candidate for upstream.** Direct law-level PDS
transcript laws against a deterministic DDE are the same as the transcript laws
of the law's finite-support representative against the one-point deterministic
environment representative. -/
theorem deterministicTranscriptLaw_ofProbPDS_ofDDE
    {X : Type u} {Y : Type v}
    (S : ProbPDS X Y) (E : RandomSystems.CR18.PFunDDS.DDE X Y)
    {q : Nat} (t : TranscriptPrefix X Y q) :
    RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw S E q t =
      transcriptLaw (ofProbPDS S) (PDERepresentative.ofDDE E) q t := by
  have hsystem :
      RandomSystems.CR18.PFunPDE.transcriptSystemFactor S
          ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
            RandomSystems.CR18.PFunPDS.RV
              (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
          t.1 t.2 =
        RandomSystems.CR18.PFunPDE.transcriptSystemFactor
          (ofProbPDS S).prob (ofProbPDS S).rv t.1 t.2 := by
    exact (transcriptSystemFactor_ofProbPDS S t).symm
  unfold RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw transcriptLaw
    PDERepresentative.ofDDE PDERepresentative.deterministic
  rw [RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    hsystem]

/-- Distribution-level form of `deterministicTranscriptLaw_ofProbPDS_ofDDE`. -/
@[simp]
theorem deterministicTranscriptDist_ofProbPDS_ofDDE
    {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    ProbPDS.deterministicTranscriptDist (q := q) S E =
      transcriptDist (q := q) (ofProbPDS S) (PDERepresentative.ofDDE E) := by
  ext t
  simp [ProbPDS.deterministicTranscriptDist,
    RandomSystems.CR18.PFunPDS.Prob.deterministicTranscriptDist,
    transcriptDist,
    deterministicTranscriptLaw_ofProbPDS_ofDDE]

/-- A representative and its canonical law representative induce the same
transcript law in every environment. -/
theorem transcriptLaw_ofProbPDS_pmf
    {X : Type u} {Y : Type v}
    (S : PDSRepresentative.{u, v, w} X Y)
    (E : PDERepresentative.{u, v, r} X Y)
    {q : Nat} (t : TranscriptPrefix X Y q) :
    transcriptLaw (ofProbPDS (RandomSystems.Dist.PMF S.prob S.rv)) E q t =
      transcriptLaw S E q t := by
  unfold transcriptLaw
  rw [RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    transcriptSystemFactor_ofProbPDS_pmf]

/-- Distribution-level form of `transcriptLaw_ofProbPDS_pmf`. -/
@[simp]
theorem transcriptDist_ofProbPDS_pmf
    {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : PDSRepresentative.{u, v, w} X Y)
    (E : PDERepresentative.{u, v, r} X Y) :
    transcriptDist (q := q) (ofProbPDS (RandomSystems.Dist.PMF S.prob S.rv)) E =
      transcriptDist (q := q) S E := by
  ext t
  simp [transcriptDist, transcriptLaw_ofProbPDS_pmf]

/-- Distribution-level deterministic form of `transcriptLaw_ofProbPDS_pmf`. -/
@[simp]
theorem deterministicTranscriptDist_ofProbPDS_pmf
    {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : PDSRepresentative.{u, v, w} X Y)
    (E : RandomSystems.CR18.PFunDDS.DDE X Y) :
    ProbPDS.deterministicTranscriptDist (q := q)
        (RandomSystems.Dist.PMF S.prob S.rv) E =
      transcriptDist (q := q) S (PDERepresentative.ofDDE E) := by
  calc
    ProbPDS.deterministicTranscriptDist (q := q)
        (RandomSystems.Dist.PMF S.prob S.rv) E
        = transcriptDist (q := q)
            (ofProbPDS (RandomSystems.Dist.PMF S.prob S.rv))
            (PDERepresentative.ofDDE E) := by
            exact deterministicTranscriptDist_ofProbPDS_ofDDE
              (RandomSystems.Dist.PMF S.prob S.rv) E
    _ = transcriptDist (q := q) S (PDERepresentative.ofDDE E) := by
            exact transcriptDist_ofProbPDS_pmf S (PDERepresentative.ofDDE E)

/-- **Source-theorem bridge; candidate for upstream.** A law-level PDS obtained
from a representative and a law-level PDE induce the same transcript law as the
two corresponding support representatives. -/
theorem transcriptLaw_ofProbPDS_ofProbPDE
    {X : Type u} {Y : Type v}
    (S : PDSRepresentative.{u, v, w} X Y)
    (E : ProbPDE X Y)
    {q : Nat} (t : TranscriptPrefix X Y q) :
    ProbPDS.transcriptLaw (RandomSystems.Dist.PMF S.prob S.rv) E q t =
      transcriptLaw S (PDERepresentative.ofProbPDE E) q t := by
  have hsystem :
      RandomSystems.CR18.PFunPDE.transcriptSystemFactor
          (RandomSystems.Dist.PMF S.prob S.rv)
          ((fun s : RandomSystems.CR18.PFunDDS.DDS X Y => s) :
            RandomSystems.CR18.PFunPDS.RV
              (RandomSystems.CR18.PFunDDS.DDS X Y) X Y)
          t.1 t.2 =
        RandomSystems.CR18.PFunPDE.transcriptSystemFactor
          S.prob S.rv t.1 t.2 := by
    unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor RandomSystems.Dist.PMF
    rw [RandomSystems.Dist.mass_fTransform]
    exact RandomSystems.Dist.mass_congr S.prob.val (fun _ => Iff.rfl)
  have henvironment :
      RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E
          ((fun e : RandomSystems.CR18.PFunDDS.DDE X Y => e) :
            RandomSystems.CR18.PFunPDE.RV
              (RandomSystems.CR18.PFunDDS.DDE X Y) X Y)
          t.1 t.2 =
        RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor
          (PDERepresentative.ofProbPDE E).prob
          (PDERepresentative.ofProbPDE E).rv t.1 t.2 := by
    exact (transcriptEnvironmentFactor_ofProbPDE E t).symm
  unfold ProbPDS.transcriptLaw RandomSystems.CR18.PFunPDS.Prob.transcriptLaw transcriptLaw
  rw [RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    RandomSystems.CR18.PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
    hsystem, henvironment]

/-- Distribution-level form of `transcriptLaw_ofProbPDS_ofProbPDE`. -/
@[simp]
theorem transcriptDist_ofProbPDS_ofProbPDE
    {X : Type u} {Y : Type v} {q : Nat}
    [FiniteTranscriptSpace X Y q]
    (S : PDSRepresentative.{u, v, w} X Y)
    (E : ProbPDE X Y) :
    ProbPDS.transcriptDist (q := q) (RandomSystems.Dist.PMF S.prob S.rv) E =
      transcriptDist (q := q) S (PDERepresentative.ofProbPDE E) := by
  ext t
  simp [ProbPDS.transcriptDist, RandomSystems.CR18.PFunPDS.Prob.transcriptDist,
    transcriptDist,
    transcriptLaw_ofProbPDS_ofProbPDE]

end PDSRepresentative

namespace TranscriptLawBridge

/-- **Source-theorem bridge.** Ratio-form H-technique specialized to concrete
CR18 transcript laws generated by two systems and a common environment. -/
theorem hTechnique_ratio_experiment
    {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    [DiscreteTranscriptSpace X Y k]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y)
    (E : PDERepresentative.{u, v, r} X Y)
    (B : TranscriptPrefix X Y k → Prop)
    (eps : NNReal)
    (h_weight :
      (PDSRepresentative.transcriptDist (q := k) R E).weight =
        (PDSRepresentative.transcriptDist (q := k) I E).weight)
    (h_ideal_le : (PDSRepresentative.transcriptDist (q := k) I E).weight ≤ 1)
    (h_ratio : ∀ t, ¬ B t →
      (1 - eps) * PDSRepresentative.transcriptLaw I E k t ≤
        PDSRepresentative.transcriptLaw R E k t) :
    RandomSystems.statDist (PDSRepresentative.transcriptDist (q := k) R E)
        (PDSRepresentative.transcriptDist (q := k) I E) ≤
      RandomSystems.probBad (PDSRepresentative.transcriptDist (q := k) I E) B + eps := by
  exact hTechnique_ratio
    (PDSRepresentative.transcriptLaw R E k)
    (PDSRepresentative.transcriptLaw I E k)
    B eps h_weight h_ideal_le h_ratio

/-- **Source-theorem bridge.** One-sided H-technique specialized to concrete
CR18 transcript laws generated by two systems and a common environment. -/
theorem oneSided_hTechnique_experiment
    {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    [DiscreteTranscriptSpace X Y k]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y)
    (E : PDERepresentative.{u, v, r} X Y)
    (eps : NNReal)
    (h_weight :
      (PDSRepresentative.transcriptDist (q := k) R E).weight =
        (PDSRepresentative.transcriptDist (q := k) I E).weight)
    (h_ideal_le : (PDSRepresentative.transcriptDist (q := k) I E).weight ≤ 1)
    (h_lower : ∀ t,
      (1 - eps) * PDSRepresentative.transcriptLaw I E k t ≤
        PDSRepresentative.transcriptLaw R E k t) :
    RandomSystems.statDist (PDSRepresentative.transcriptDist (q := k) R E)
        (PDSRepresentative.transcriptDist (q := k) I E) ≤ eps := by
  exact oneSided_hTechnique
    (PDSRepresentative.transcriptLaw R E k)
    (PDSRepresentative.transcriptLaw I E k)
    eps h_weight h_ideal_le h_lower

end TranscriptLawBridge

end HTechnique
end Migration
end NextGen
