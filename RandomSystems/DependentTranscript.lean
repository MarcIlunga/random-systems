/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Derivation

/-!
# Dependent-fiber transcripts (M4-E1)

The core library's `TranscriptPrefix X Y q = List.Vector X q × List.Vector Y q`
is *non-dependent*: the response alphabet `Y` is one fixed type.  Oracles whose
response space depends on the query — the HCTR2 `TotMsg` sigma pattern, where a
query `(dir, tweak, ⟨ℓ, msg⟩)` must be answered by a message of the *same*
block length `ℓ` — can only be represented by flattening the fibers into
`Σ x, Y x` and carrying length-match/coherence side conditions through every
statement.  That flattening is the root cause of two soundness-of-meaning
gaps in the HCTR2 development:

* the `facIO` junk-comparison branch (#7): incoherent transcripts (response
  fiber ≠ query fiber) are representable, so case splits must dismiss them
  pointwise;
* the `hctrAdmissible` length-match conjunct, threaded through every
  admissibility argument by hand.

This module adds the *typed view* without rewriting the core:

1. `DTranscriptPrefix X Y q` — dependent transcripts as first-class objects
   (`Σ xs : List.Vector X q, ∀ i, Y (xs.get i)`), with `Fintype`/`DecidableEq`
   instances;
2. `flatten` / `Coherent` / `unflatten` — the boundary to the flat
   representation: `flatten` is injective with image exactly the coherent flat
   transcripts, and `unflatten` inverts it on that image;
3. `flattenDist` / `unflattenDist` — mass-preserving law transport across the
   boundary, with round-trip and mass-characterization theorems;
4. `flatFun` / `flatEvaluator` / `depTranscriptDist` — the library-level
   endpoint: a fiber-respecting oracle `f : ∀ x, Y x`, embedded through the
   existing `PFunPDS.Prob.functionEvaluator` surface, has its transcript law
   supported on coherent transcripts
   (`flatEvaluator_transcriptDist_support_coherent`), so it transports to a
   *dependent* transcript law `depTranscriptDist` with a clean mass
   characterization (`depTranscriptDist_mass`).  Future proofs work typed and
   cross the boundary once, here.

## Roadmap (M4-E2, not implemented here)

E2 is consumer-driven — to be built when the first proof adopts this layer
(candidate: the HCTR2Bit build or a future HCTR2 mode).  Planned items:

* **dependent environments**: a dependent `envRun`/`envReplay` and
  `QQueryEnvironment` view whose queries are typed against the fibers, so
  `EnvRespects`/`SelfAnswerFilter` arguments never see incoherent transcripts;
* **dependent H-technique endpoints**: ratio/bad-event lemmas stated directly
  on `Dist (DTranscriptPrefix X Y q)`, obtained by transporting the flat
  endpoints of `HTechnique/Derivation.lean` along `flattenDist`;
* **HCTR2 retrofit**: `hctrAdmissible`'s length-match conjunct becomes
  `Coherent` (discharged once by
  `flatEvaluator_transcriptDist_support_coherent`), and the `facIO` junk
  branch dies at the source because incoherent comparisons are no longer
  representable in the typed view.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.CR18
namespace DepTranscript

universe u v

variable {X : Type u} {Y : X → Type v} {q : ℕ}

/-! ## The dependent carrier -/

/-- A length-`q` *dependent* transcript prefix: a query vector together with,
for each position, a response in the fiber of that position's query.  This is
the typed counterpart of `TranscriptPrefix X (Σ x, Y x) q`; the flattening is
`flatten` below. -/
def DTranscriptPrefix (X : Type u) (Y : X → Type v) (q : ℕ) : Type (max u v) :=
  Σ xs : List.Vector X q, ∀ i : Fin q, Y (xs.get i)

instance instDecidableEq [DecidableEq X] [∀ x, DecidableEq (Y x)] :
    DecidableEq (DTranscriptPrefix X Y q) :=
  inferInstanceAs
    (DecidableEq (Σ xs : List.Vector X q, ∀ i : Fin q, Y (xs.get i)))

instance instFintype [Fintype X] [DecidableEq X] [∀ x, Fintype (Y x)] :
    Fintype (DTranscriptPrefix X Y q) :=
  inferInstanceAs
    (Fintype (Σ xs : List.Vector X q, ∀ i : Fin q, Y (xs.get i)))

/-! ## Flattening and coherence -/

/-- Flatten a dependent transcript into the non-dependent carrier over the
sigma alphabet: each response is tagged with its query. -/
def flatten (t : DTranscriptPrefix X Y q) :
    TranscriptPrefix X (Σ x, Y x) q :=
  (t.1, List.Vector.ofFn fun i => ⟨t.1.get i, t.2 i⟩)

/-- A flat transcript over the sigma alphabet is *coherent* when every
response lives in the fiber of the query it answers.  This is the single side
condition that replaces the per-application length-match conjuncts (e.g. the
HCTR2 `hctrAdmissible` length-match clause). -/
def Coherent (t : TranscriptPrefix X (Σ x, Y x) q) : Prop :=
  ∀ i, (t.2.get i).1 = t.1.get i

/-- Flattened transcripts are coherent. -/
theorem flatten_coherent (t : DTranscriptPrefix X Y q) :
    Coherent (flatten t) := by
  intro i
  simp [flatten, List.Vector.get_ofFn]

/-- **UPSTREAM-CANDIDATE** (generic `Sigma` lemma; belongs next to
`Sigma.mk.inj_iff`).  Rebuilding a sigma pair from its transported second
component recovers the pair. -/
theorem sigma_mk_cast_snd {p : Σ x, Y x} {x : X} (h : p.1 = x) :
    (⟨x, h ▸ p.2⟩ : Σ x, Y x) = p := by
  obtain ⟨a, b⟩ := p
  subst h
  rfl

/-- Recover the dependent transcript from a coherent flat one: transport each
response back into the fiber of its query along the coherence proof. -/
def unflatten (t : TranscriptPrefix X (Σ x, Y x) q) (h : Coherent t) :
    DTranscriptPrefix X Y q :=
  ⟨t.1, fun i => h i ▸ (t.2.get i).2⟩

/-- `flatten` is a right inverse of `unflatten` on coherent transcripts. -/
theorem flatten_unflatten (t : TranscriptPrefix X (Σ x, Y x) q)
    (h : Coherent t) :
    flatten (unflatten t h) = t := by
  obtain ⟨xs, ys⟩ := t
  refine congrArg (Prod.mk xs) (List.Vector.ext fun i => ?_)
  rw [List.Vector.get_ofFn]
  exact sigma_mk_cast_snd (h i)

/-- `flatten` is injective: the typed view loses no information. -/
theorem flatten_injective :
    Function.Injective (flatten (Y := Y) (q := q)) := by
  rintro ⟨xs, f⟩ ⟨ys, g⟩ hfg
  have h1 : xs = ys := congrArg Prod.fst hfg
  subst h1
  have h2 : ∀ i, (⟨xs.get i, f i⟩ : Σ x, Y x) = ⟨xs.get i, g i⟩ := by
    intro i
    have := congrArg
      (fun v : List.Vector (Σ x, Y x) q => v.get i) (congrArg Prod.snd hfg)
    simpa [flatten, List.Vector.get_ofFn] using this
  have h3 : f = g :=
    funext fun i => eq_of_heq (Sigma.mk.inj_iff.mp (h2 i)).2
  rw [h3]

/-- `unflatten` is a left inverse of `flatten`. -/
theorem unflatten_flatten (t : DTranscriptPrefix X Y q)
    (h : Coherent (flatten t)) :
    unflatten (flatten t) h = t :=
  flatten_injective (flatten_unflatten (flatten t) h)

/-- The image of `flatten` is exactly the coherent flat transcripts
(surjectivity onto coherence). -/
theorem exists_flatten_eq_iff_coherent (t : TranscriptPrefix X (Σ x, Y x) q) :
    (∃ d : DTranscriptPrefix X Y q, flatten d = t) ↔ Coherent t :=
  ⟨fun ⟨d, hd⟩ => hd ▸ flatten_coherent d,
    fun h => ⟨unflatten t h, flatten_unflatten t h⟩⟩

/-! ## Law transport

The point of the layer: distributions over dependent transcripts and
coherently-supported distributions over flat transcripts carry the same mass,
and the transport maps are mutually inverse.  `unflattenDist` is the exact
*pullback* along the injection `flatten` (`Finsupp.comapDomain`); no junk
default and no `Nonempty` side conditions are needed, and any incoherent mass
of the input is dropped (there is none in the intended use, by
`flattenDist_support_coherent` / `flatEvaluator_transcriptDist_support_coherent`). -/

/-- Push a dependent transcript law to the flat carrier. -/
def flattenDist (D : Dist (DTranscriptPrefix X Y q)) :
    Dist (TranscriptPrefix X (Σ x, Y x) q) :=
  Dist.fTransform flatten D

/-- Mass is preserved across flattening: the flat mass of `P` is the dependent
mass of `P ∘ flatten`. -/
theorem flattenDist_mass (D : Dist (DTranscriptPrefix X Y q))
    (P : TranscriptPrefix X (Σ x, Y x) q → Prop) :
    (flattenDist D).mass P = D.mass fun d => P (flatten d) :=
  Dist.mass_fTransform flatten D P

/-- Flattening preserves total mass. -/
theorem flattenDist_weight (D : Dist (DTranscriptPrefix X Y q)) :
    (flattenDist D).weight = D.weight :=
  Dist.weight_fTransform flatten D

/-- A flattened law is supported on coherent transcripts. -/
theorem flattenDist_support_coherent (D : Dist (DTranscriptPrefix X Y q)) :
    ∀ t ∈ (flattenDist D).support, Coherent t := by
  intro t ht
  obtain ⟨d, -, rfl⟩ := Dist.mem_support_fTransform flatten D ht
  exact flatten_coherent d

/-- Pull a flat transcript law back to the dependent carrier along `flatten`.
Mass at incoherent transcripts (outside the image of `flatten`) is dropped;
on coherently-supported laws this is an exact inverse of `flattenDist`
(`flattenDist_unflattenDist`). -/
def unflattenDist (D : Dist (TranscriptPrefix X (Σ x, Y x) q)) :
    Dist (DTranscriptPrefix X Y q) :=
  Finsupp.comapDomain flatten D flatten_injective.injOn

@[simp]
theorem unflattenDist_apply (D : Dist (TranscriptPrefix X (Σ x, Y x) q))
    (d : DTranscriptPrefix X Y q) :
    unflattenDist D d = D (flatten d) :=
  rfl

/-- Round trip, dependent side: pulling back a pushed-forward law is the
identity (no coherence hypothesis needed). -/
theorem unflattenDist_flattenDist (D : Dist (DTranscriptPrefix X Y q)) :
    unflattenDist (flattenDist D) = D :=
  Finsupp.ext fun d =>
    Dist.fTransform_injective_apply D flatten flatten_injective d

/-- Round trip, flat side: pushing a pulled-back law forward is the identity
on laws supported on coherent transcripts. -/
theorem flattenDist_unflattenDist (D : Dist (TranscriptPrefix X (Σ x, Y x) q))
    (h : ∀ t ∈ D.support, Coherent t) :
    flattenDist (unflattenDist D) = D := by
  refine Finsupp.ext fun t => ?_
  by_cases hc : Coherent t
  · obtain ⟨d, rfl⟩ := (exists_flatten_eq_iff_coherent t).mpr hc
    rw [show flattenDist (unflattenDist D) (flatten d)
          = unflattenDist D d from
        Dist.fTransform_injective_apply _ flatten flatten_injective d,
      unflattenDist_apply]
  · rw [show flattenDist (unflattenDist D) t = 0 from
        Dist.fTransform_apply_of_forall_ne _ flatten t
          fun d hd => hc (hd ▸ flatten_coherent d)]
    exact (Finsupp.notMem_support_iff.mp fun hmem => hc (h t hmem)).symm

/-- Pull-back preserves total mass on coherently-supported laws. -/
theorem unflattenDist_weight (D : Dist (TranscriptPrefix X (Σ x, Y x) q))
    (h : ∀ t ∈ D.support, Coherent t) :
    (unflattenDist D).weight = D.weight := by
  conv_rhs => rw [← flattenDist_unflattenDist D h]
  exact (flattenDist_weight (unflattenDist D)).symm

/-- **Mass characterization of the pull-back**: for a coherently-supported
flat law, the dependent mass of `P` is the flat mass of the transported
predicate.  This is the crossing lemma future dependent proofs use to consume
flat-side facts. -/
theorem unflattenDist_mass (D : Dist (TranscriptPrefix X (Σ x, Y x) q))
    (h : ∀ t ∈ D.support, Coherent t)
    (P : DTranscriptPrefix X Y q → Prop) :
    (unflattenDist D).mass P
      = D.mass fun t => ∃ hc : Coherent t, P (unflatten t hc) := by
  conv_rhs => rw [← flattenDist_unflattenDist D h]
  rw [flattenDist_mass]
  exact Dist.mass_congr _ fun d =>
    ⟨fun hP => ⟨flatten_coherent d, by rwa [unflatten_flatten]⟩,
      fun ⟨hc, hP⟩ => by rwa [unflatten_flatten] at hP⟩

/-! ## The dependent oracle and its transcript law -/

/-- A memoryless dependent oracle: a fiber-respecting response function. -/
abbrev DOracle (X : Type u) (Y : X → Type v) : Type (max u v) :=
  ∀ x, Y x

/-- Flatten a dependent oracle into an ordinary function to the sigma
alphabet (the HCTR2 `lpUrfFunction` pattern, application-independent form). -/
def flatFun (f : DOracle X Y) : X → Σ x, Y x :=
  fun x => ⟨x, f x⟩

/-- The uniform dependent oracle: `Dist.uniform` on the dependent function
space (the dependent counterpart of the uniform random function). -/
def uniformDOracle [Fintype X] [DecidableEq X]
    [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)] :
    Dist.ProbDist (DOracle X Y) :=
  ⟨Dist.uniform (DOracle X Y), Dist.uniform_isProbDist⟩

/-- A sampled dependent oracle embedded on the existing library surface: the
flat function evaluator of the flattened oracle. -/
def flatEvaluator (base : Dist.ProbDist (DOracle X Y)) :
    ProbPDS X (Σ x, Y x) :=
  PFunPDS.Prob.functionEvaluator base fun f => flatFun f

section TranscriptLaw

variable [FiniteTranscriptSpace X (Σ x, Y x) q]

open HTechniqueDerivation in
/-- The flat transcript law of a sampled dependent oracle is the pushforward
of the base law along the deterministic run map (specialization of the
promoted pushforward identity to `flatEvaluator`). -/
theorem flatEvaluator_transcriptDist_eq_fTransform
    (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q) :
    PFunPDS.Prob.deterministicTranscriptDist (q := q) (flatEvaluator base) E.1
      = Dist.fTransform (fun f => envRun E (flatFun f)) base.val :=
  deterministicTranscriptDist_functionEvaluator_eq_fTransform
    base (fun f => flatFun f) E

open HTechniqueDerivation in
/-- **Key endpoint**: the library-level transcript law of a fiber-respecting
oracle is supported on coherent transcripts.  Route: the transcript law is the
pushforward of the base law along `envRun` (pushforward identity above), and
every `envRun` response is a `flatFun` value, hence fiber-tagged with its own
query. -/
theorem flatEvaluator_transcriptDist_support_coherent
    (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q) :
    ∀ t ∈ (PFunPDS.Prob.deterministicTranscriptDist (q := q)
        (flatEvaluator base) E.1).support,
      Coherent t := by
  intro t ht
  rw [flatEvaluator_transcriptDist_eq_fTransform] at ht
  obtain ⟨f, -, rfl⟩ := Dist.mem_support_fTransform _ _ ht
  intro i
  have hi := ((envRun_eq_iff E (flatFun f) (envRun E (flatFun f))).mp rfl).2 i
  rw [← hi]
  rfl

/-- **The dependent transcript law** of a sampled dependent oracle against a
deterministic `q`-query-total environment: the flat transcript law, pulled
back to the typed carrier.  This is the endpoint future dependent proofs
target. -/
def depTranscriptDist (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q) :
    Dist (DTranscriptPrefix X Y q) :=
  unflattenDist
    (PFunPDS.Prob.deterministicTranscriptDist (q := q) (flatEvaluator base) E.1)

/-- Crossing the boundary once: flattening the dependent transcript law
recovers the library-level flat transcript law exactly. -/
theorem flattenDist_depTranscriptDist (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q) :
    flattenDist (depTranscriptDist base E)
      = PFunPDS.Prob.deterministicTranscriptDist (q := q)
          (flatEvaluator base) E.1 :=
  flattenDist_unflattenDist _
    (flatEvaluator_transcriptDist_support_coherent base E)

/-- **Mass characterization of the dependent transcript law**: dependent
events evaluate as flat events under the transported predicate.  Flat-side
H-technique facts transfer to the typed view through this equation. -/
theorem depTranscriptDist_mass (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q)
    (P : DTranscriptPrefix X Y q → Prop) :
    (depTranscriptDist base E).mass P
      = (PFunPDS.Prob.deterministicTranscriptDist (q := q)
            (flatEvaluator base) E.1).mass
          fun t => ∃ hc : Coherent t, P (unflatten t hc) :=
  unflattenDist_mass _
    (flatEvaluator_transcriptDist_support_coherent base E) P

open HTechniqueDerivation in
/-- The dependent transcript law is an honest probability distribution: no
mass is lost in the pull-back, because the flat law is coherently supported
and has weight one (function evaluators are total). -/
theorem depTranscriptDist_weight_eq_one (base : Dist.ProbDist (DOracle X Y))
    (E : QQueryEnvironment X (Σ x, Y x) q) :
    (depTranscriptDist base E).weight = 1 := by
  unfold depTranscriptDist
  rw [unflattenDist_weight _
    (flatEvaluator_transcriptDist_support_coherent base E)]
  exact deterministicTranscriptDist_weight_eq_one (flatEvaluator base) E
    (functionEvaluatorProb_KStepTotal base (fun f => flatFun f) q)

end TranscriptLaw

end DepTranscript
end RandomSystems.CR18
