/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystemParallel
import RandomSystems.TypedResource
import RandomSystems.StrictContextAdvantage
import CC

/-!
# CR18 random systems as Abstract Cryptography resources

At a fixed signature, a resource is the strict behavioral class of a
normalized CR18 probabilistic system (`StrictContext.System`), and its
extended distance is the strict contextual metric.  The fibre is separated —
zero distance IS equality (`System.edist_eq_zero_iff_eq`) — so the carrier
meets AC's modeling invariant that behavior, not presentation, is the
resource.  Different signatures live in one heterogeneous carrier at
distance `⊤`.

Every CR18 deterministic discrete converter (Definition 3.8, `IsDDC`) acts
on strict behavior, and every such action is non-expanding
(`System.edist_apply_le`): a strict test composed with an `IsDDC` converter
is again a strict test, structurally and with no `Emulable` certificate.
The operational protocol monoid `Protocol` — CR18's Γ as *syntax*, converter
words modulo the serial monoid laws only — therefore interprets into
`nonexpandingEnd` and carries `IsNonexpandingSMul` — exactly what AC's
ε-composition calculus (`Constructs.eball_trans`) consumes, so approximate
constructions on this carrier compose with radii adding.  The extensional
submonoid `Protocol` used to be is kept as its interpretation image
(`mrange_protocolInclusion_eq_generatedConverterMonoid`), so nothing the old
presentation could express was lost.

The paper-facing `Δ` surface survives through the sound inequality
`maxEDist ≤ ENNReal.ofReal Δ` (`StrictContextAdvantage`): a CR18 advantage
bound transfers to a strict construction bound for free
(`edist_liftProb_le_advantage`).  The converse is FALSE in general — a CR18
distinguisher can observe an invalid query as `none` and continue, which no
strict test can do (`RandomSystems.AttainmentCounterexample` exhibits
`maxAdvantage = 1/2` with attainment failure); equality needs support totality,
`StrictContextTotal`).  Construction statements therefore only ever use the
`≤` direction; there is deliberately no `edist = ENNReal.ofReal Δ` lemma on
this carrier.

The former Maurer–Renner "compatible" subclass (`CompatibleConverter`,
`CompatiblePrimitive`, `CompatibleProtocol`: `Emulable`-certified converters
with their own non-expanding submonoid) is deleted, not repaired.  It
existed solely because the earlier fibre metrized *raw laws* with `Δ`, for
which CR18 Definition 3.8 membership alone does not give non-expansion
(`PFunConverter.not_emulable_probeFn` is the proven boundary).  On the
strict quotient the restriction is unnecessary — non-expansion is
structural for the full `IsDDC` class — and the subclass had no instances
anywhere in either repository.  The `Emulable` boundary remains a genuine
mathematical fact about the `Δ` metric; it lives with `Δ`
(`RandomSystems.CompatibleMetric.maxAdvantage_apply_le`), not on this
carrier.

## What this carrier is for, and why `Phi` does not subsume it

Measured.  This carrier has **one** downstream model —
`RandomSystemsCC.CBCMAC` (`CBCModel.lean`, `CBC.lean`) — and carries **zero**
`CC.SecurelyConstructs` judgments; every CC endpoint of the estate lives on
the interface-indexed `RandomSystemsCC.TypedFinite.Phi I U`.  That split is
decided, not accidental, and two facts keep it.

**1.  A randomness expander is not a CC construction.**  CBC's protocol
*changes the resource's signature* — `Primitive.act` sends a resource at
`source` to one at `target`, `U(X,X)` to `M → X` — and there is no honest
interface, no dishonest interface, and no simulator.  `Phi`'s
`boundary : I → U.Code` is the *world selector* across a fixed interface set
(STATUS §11.27); CBC has nothing to put in it.  On `Phi Unit U` the boundary
would be constant by construction and every statement would carry a
`singleView` chart, in exchange for nothing.

**2.  This is the estate's only carrier with AC's parallel *protocol*
algebra.**  `Constructs.eball_par`, `Constructs.eball_par_resource`,
`Constructs.relax_par`, `Constructs.simulator_par` and
`CC.SecurelyConstructs.par`/`par_left` each require four classes: `Par Φ`,
`IsNonexpandingPar Φ`, `Par M`, and `SMulParClass M Φ`.  `Phi` has the first
two (`RandomSystemsCC.TypedParallel`); the last two exist nowhere but
`RandomSystemsCC.ResourceParallel` (`ParProtocol U`, `SMulParClass`) — one
instance in the estate — and `RandomSystemsCC.ParallelChecks.
extract_constructs_par` is the kernel-checked receipt that AC's parallel
calculus fires on this carrier and only here.  `Phi` cannot simply copy it:
STATUS §11.5 refutes par-act non-expansion by counterexample, and §11.10.1
records that a `par` on `ConverterTerm` — which interprets into
`nonexpandingEnd (Phi I U)` — would break `IsNonexpandingSMul`, hence
`SecurelyConstructs.trans`, for every existing endpoint.  `ParProtocol`
escapes exactly by interpreting into plain `Function.End` and asserting no
metric law; installing that pattern on `Phi` is deferred, not unavailable.

**The relationship to `Phi` is already pinned by theorem, at the fibre.**
`RandomSystems.TypedUnitMetric` proves metric full abstraction at one
interface: `DependentPDS.contextualEDist_eq_maxEDist_singleView` says the
`Phi`-side fibre metric at `I = Unit` *is* the flat strict metric of the
local view — which is this carrier's fibre metric — with
`DependentRandomSystem.of_prob_eq_of_single_view_eq` for injectivity and
`DependentPDS.singleView_is_probability_distribution_iff` for normalization.
A bundled carrier-level `Phi Unit U ↪ Resource U` is therefore packaging, not
mathematics, and it has no consumer: every `Phi` model runs at three
interfaces (`Symmetric.Interface`), this carrier's one model at one.
-/

namespace RandomSystemsCC.CR18

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.StrictContextAdvantage
open scoped AbstractCrypto ENNReal

noncomputable section

universe c u v

variable {U : SignatureUniverse.{c, u, v}} [DecidableEq U.Code]

/-- Source-facing name for a typed family of resource interfaces. -/
abbrev InterfaceUniverse := SignatureUniverse

/-- CR18 converter application to a probabilistic law, written by
juxtaposition in the paper. -/
scoped notation:67 converter:67 " ∙ " system:68 =>
  PFunPDS.apply converter system

/-! ## Heterogeneous resources -/

variable {X : Type u} {Y : Type v}

/-- The strict behavior of a normalized CR18 law at one signature in `U`.
The fibre is the separated contextual quotient, not a raw law: two
presentations that no strict deterministic test tells apart are the same
resource. -/
structure Resource (U : SignatureUniverse.{c, u, v}) where
  code : U.Code
  system : StrictContext.System (U.input code) (U.output code)

namespace Resource

/-- Strict contextual distance within one signature; distinct signatures are
incomparable. -/
def boundaryEDist (left right : Resource U) : ENNReal :=
  match left, right with
  | ⟨leftCode, leftSystem⟩, ⟨rightCode, rightSystem⟩ =>
      if same : leftCode = rightCode then
        edist (same ▸ leftSystem) rightSystem
      else
        ⊤

instance instPseudoEMetricSpace : PseudoEMetricSpace (Resource U) where
  edist := boundaryEDist
  edist_self := by
    rintro ⟨code, system⟩
    simp [boundaryEDist]
  edist_comm := by
    rintro ⟨leftCode, leftSystem⟩ ⟨rightCode, rightSystem⟩
    by_cases same : leftCode = rightCode
    · subst rightCode
      simpa [boundaryEDist] using edist_comm leftSystem rightSystem
    · have reverse : rightCode ≠ leftCode := Ne.symm same
      simp [boundaryEDist, same, reverse]
  edist_triangle := by
    rintro ⟨leftCode, leftSystem⟩
      ⟨middleCode, middleSystem⟩
      ⟨rightCode, rightSystem⟩
    by_cases leftMiddle : leftCode = middleCode
    · subst middleCode
      by_cases leftRight : leftCode = rightCode
      · subst rightCode
        simpa [boundaryEDist] using
          edist_triangle leftSystem middleSystem rightSystem
      · simp [boundaryEDist, leftRight]
    · by_cases middleRight : middleCode = rightCode
      · subst rightCode
        simp [boundaryEDist, leftMiddle]
      · by_cases leftRight : leftCode = rightCode
        · subst rightCode
          simp [boundaryEDist, leftMiddle, middleRight]
        · simp [boundaryEDist, leftMiddle, middleRight, leftRight]

@[simp]
theorem edist_same (code : U.Code)
    (left right : StrictContext.System (U.input code) (U.output code)) :
    edist (Resource.mk code left) (Resource.mk code right) =
      edist left right := by
  show boundaryEDist _ _ = _
  simp [boundaryEDist]

theorem edist_ne {leftCode rightCode : U.Code}
    (different : leftCode ≠ rightCode)
    (left : StrictContext.System (U.input leftCode) (U.output leftCode))
    (right : StrictContext.System (U.input rightCode) (U.output rightCode)) :
    edist (Resource.mk leftCode left) (Resource.mk rightCode right) = ⊤ := by
  show boundaryEDist _ _ = _
  simp [boundaryEDist, different]

/-- The heterogeneous carrier inherits the fibre's separation: zero distance
is equality.  This is the non-degeneracy receipt for the quotient — the
metric genuinely identifies behavior, and only behavior. -/
theorem edist_eq_zero_iff_eq (left right : Resource U) :
    edist left right = 0 ↔ left = right := by
  constructor
  · rcases left with ⟨leftCode, leftSystem⟩
    rcases right with ⟨rightCode, rightSystem⟩
    intro zero
    by_cases same : leftCode = rightCode
    · subst rightCode
      rw [edist_same] at zero
      exact congrArg (Resource.mk leftCode)
        ((StrictContext.System.edist_eq_zero_iff_eq leftSystem rightSystem).mp
          zero)
    · rw [edist_ne same] at zero
      exact absurd zero (by simp)
  · rintro rfl
    exact edist_self _

end Resource

/-- The signature code carrying inputs `X` and outputs `Y`. -/
class HasResourceCode (U : SignatureUniverse.{c, u, v})
    (X : Type u) (Y : Type v) where
  code : U.Code
  input_eq : U.input code = X
  output_eq : U.output code = Y

/-- The strict behavior of a normalized CR18 law as a heterogeneous
resource. -/
noncomputable def liftProb {X : Type u} {Y : Type v}
    [code : HasResourceCode U X Y] (system : PFunPDS.Prob X Y) : Resource U := by
  rcases code with ⟨signature, rfl, rfl⟩
  exact ⟨signature, StrictContext.System.ofProb system⟩

/-- `liftProb` at an **explicitly named** signature code.

`liftProb` infers the code from the law's alphabets, which is convenient but
means *instance resolution decides what the statement says*.  Two instances
whose `(X, Y)` heads unify at some instantiation of the model's type variables
are then disambiguated by priority rather than by the alphabets.

That is **sound but silently relabelling**, and it is worth being precise about
which.  Resolution is deterministic and cached per head, so at such an
instantiation *every* occurrence collapses to the same winning code together:
the statement carries the same mathematics under the other of several labels
for one signature, rather than becoming false.  But placement is observable —
`Resource.mk` is injective in its code — so the collapsed statement is not the
one the author wrote.

The rule this buys: a carrier whose heads can unify must (i) pin the winner
with a regression, so a priority change is a compile error rather than a silent
move, and (ii) name the code here at every statement boundary whose intent
matters.  `RandomSystemsCC.CBCMAC` is the worked example of both.

Reducible and stated through `liftProb`, so every `liftProb` lemma still
applies. -/
noncomputable abbrev liftProbAt (code : U.Code)
    (system : PFunPDS.Prob (U.input code) (U.output code)) : Resource U :=
  liftProb (U := U) (code := ⟨code, rfl, rfl⟩) system

/-- On embedded laws, AC distance is strict contextual distance. -/
@[simp]
theorem edist_liftProb {X : Type u} {Y : Type v}
    [code : HasResourceCode U X Y]
    (left right : PFunPDS.Prob X Y) :
    edist (liftProb (U := U) left) (liftProb (U := U) right) =
      StrictContext.maxEDist left.val right.val := by
  rcases code with ⟨signature, rfl, rfl⟩
  simp [liftProb]

/-- The sound direction of the source-metric bridge: a CR18 advantage bound
on the displayed laws is an AC distance bound on the embedded resources.
The converse is false in general (`RandomSystems.AttainmentCounterexample`);
construction proofs must use this inequality and never an equality. -/
theorem edist_liftProb_le_advantage {X : Type u} {Y : Type v}
    [HasResourceCode U X Y]
    (left right : PFunPDS.Prob X Y) :
    edist (liftProb (U := U) left) (liftProb (U := U) right) ≤
      ENNReal.ofReal Δ(left.val, right.val) := by
  rw [edist_liftProb]
  exact maxEDist_le_maxAdvantage left.val right.val
    left.property right.property

noncomputable instance {X : Type u} {Y : Type v}
    [HasResourceCode U X Y] :
    CoeTC (PFunPDS.Prob X Y) (Resource U) :=
  ⟨liftProb⟩

noncomputable instance {X : Type u} {Y : Type v}
    [HasResourceCode U X Y] :
    CoeTC (PFunPDS.Prob X Y) (Set (Resource U)) :=
  ⟨fun system => {liftProb system}⟩

instance : CoeTC (Resource U) (Set (Resource U)) :=
  ⟨fun resource => {resource}⟩

/-! ## CR18 converters and their operational protocol monoid -/

/-- A deterministic discrete converter, with exactly CR18 Definition 3.8's
membership proof. -/
structure DDConverter
    (targetInput : Type u) (targetOutput : Type v)
    (sourceInput : Type u) (sourceOutput : Type v) where
  run : PFunConverter.ProtocolFn
    targetInput targetOutput sourceInput sourceOutput
  isDDC : PFunConverter.IsDDC run

namespace DDConverter

/-- A bundled DDC is usable wherever its underlying CR18 converter is
expected.  The determinism evidence remains attached to the source object. -/
instance
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v} :
    Coe
      (DDConverter
        targetInput targetOutput sourceInput sourceOutput)
      (PFunConverter.ProtocolFn
        targetInput targetOutput sourceInput sourceOutput) :=
  ⟨DDConverter.run⟩

/-- Bundled DDCs are equal when their converter functions are equal; the
membership witnesses are propositions. -/
@[ext]
theorem ext
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    {left right : DDConverter
      targetInput targetOutput sourceInput sourceOutput}
    (same : left.run = right.run) :
    left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Serial composition of typed DDCs, with the intermediate alphabet enforced
by the type of multiplication. -/
noncomputable def comp
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput middleInput middleOutput)
    (inner : DDConverter
      middleInput middleOutput sourceInput sourceOutput) :
    DDConverter targetInput targetOutput sourceInput sourceOutput :=
  ⟨PFunConverter.comp outer.run inner.run,
    PFunConverter.serial_composition_is_ddc outer.isDDC inner.isDDC⟩

noncomputable instance
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v} :
    HMul
      (DDConverter
        targetInput targetOutput middleInput middleOutput)
      (DDConverter
        middleInput middleOutput sourceInput sourceOutput)
      (DDConverter
        targetInput targetOutput sourceInput sourceOutput) :=
  ⟨comp⟩

/-- A typed DDC acts directly on a raw CR18 system.  Multiplication dispatches
on the right-hand type: DDC × DDC is serial composition, while DDC × PDS is
converter application. -/
noncomputable instance
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v} :
    HMul
      (DDConverter
        targetInput targetOutput sourceInput sourceOutput)
      (PFunPDS sourceInput sourceOutput)
      (PFunPDS targetInput targetOutput) :=
  ⟨fun converter system => PFunPDS.apply converter.run system⟩

@[simp]
theorem mul_system
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (system : PFunPDS sourceInput sourceOutput) :
    converter * system = PFunPDS.apply converter.run system :=
  rfl

@[simp]
theorem run_mul
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput middleInput middleOutput)
    (inner : DDConverter
      middleInput middleOutput sourceInput sourceOutput) :
    (outer * inner).run =
      PFunConverter.comp outer.run inner.run :=
  rfl

/-- Bundling a converter also bundles the sole side condition needed to
reassociate its action on a CR18 law. -/
theorem apply_law_comp
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput middleInput middleOutput)
    (inner : PFunConverter.ProtocolFn
      middleInput middleOutput sourceInput sourceOutput)
    (system : PFunPDS sourceInput sourceOutput) :
    PFunPDS.apply (PFunConverter.comp outer.run inner) system =
      PFunPDS.apply outer.run (PFunPDS.apply inner system) :=
  StrictContext.apply_law_comp outer.run inner system outer.isDDC.1

/-- Applying a typed composite is nested converter application.  The DDC
evidence carried by the outer converter discharges the sole reassociation
side condition, so consumers see the ordinary action law. -/
@[simp]
theorem apply_mul
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput middleInput middleOutput)
    (inner : DDConverter
      middleInput middleOutput sourceInput sourceOutput)
    (system : PFunPDS sourceInput sourceOutput) :
    PFunPDS.apply (outer * inner).run system =
      PFunPDS.apply outer.run (PFunPDS.apply inner.run system) := by
  exact outer.apply_law_comp inner.run system

/-- Typed composition acts associatively on a raw system. -/
@[simp]
theorem mul_mul_system
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput middleInput middleOutput)
    (inner : DDConverter
      middleInput middleOutput sourceInput sourceOutput)
    (system : PFunPDS sourceInput sourceOutput) :
    (outer * inner) * system = outer * (inner * system) := by
  exact apply_mul outer inner system

/-- Typed serial composition associates when applied to a law.  This is the
source-level action law behind the operational protocol monoid. -/
theorem apply_law_mul_assoc
    {targetInput firstInput secondInput sourceInput : Type u}
    {targetOutput firstOutput secondOutput sourceOutput : Type v}
    (outer : DDConverter
      targetInput targetOutput firstInput firstOutput)
    (middle : DDConverter
      firstInput firstOutput secondInput secondOutput)
    (inner : DDConverter
      secondInput secondOutput sourceInput sourceOutput)
    (system : PFunPDS sourceInput sourceOutput) :
    PFunPDS.apply ((outer * middle) * inner).run system =
      PFunPDS.apply (outer * (middle * inner)).run system := by
  calc
    _ = PFunPDS.apply (outer * middle).run
          (PFunPDS.apply inner.run system) :=
      (outer * middle).apply_law_comp inner.run system
    _ = PFunPDS.apply outer.run
          (PFunPDS.apply middle.run
            (PFunPDS.apply inner.run system)) :=
      outer.apply_law_comp middle.run (PFunPDS.apply inner.run system)
    _ = PFunPDS.apply outer.run
          (PFunPDS.apply (middle * inner).run system) := by
      congr 1
      exact (middle.apply_law_comp inner.run system).symm
    _ = _ :=
      (outer.apply_law_comp (middle * inner).run system).symm

end DDConverter

/-- A local converter placed between two signature codes. -/
structure Primitive (U : SignatureUniverse.{c, u, v}) where
  source : U.Code
  target : U.Code
  run : PFunConverter.ProtocolFn
    (U.input target) (U.output target)
    (U.input source) (U.output source)
  isDDC : PFunConverter.IsDDC run

namespace Primitive

/-- Apply a converter to strict behavior when its source signature matches. -/
noncomputable def act (primitive : Primitive U) : Resource U → Resource U
  | ⟨code, system⟩ =>
      if sourceMatches : code = primitive.source then
        ⟨primitive.target,
          StrictContext.System.apply ⟨primitive.run, primitive.isDDC⟩
            (sourceMatches ▸ system)⟩
      else
        ⟨code, system⟩

theorem act_of_matches (primitive : Primitive U)
    (system : StrictContext.System
      (U.input primitive.source) (U.output primitive.source)) :
    primitive.act ⟨primitive.source, system⟩ =
      ⟨primitive.target,
        StrictContext.System.apply ⟨primitive.run, primitive.isDDC⟩ system⟩ := by
  simp [act]

theorem act_of_not_matches (primitive : Primitive U) (code : U.Code)
    (different : code ≠ primitive.source)
    (system : StrictContext.System (U.input code) (U.output code)) :
    primitive.act ⟨code, system⟩ = ⟨code, system⟩ := by
  simp [act, different]

/-- **Every** CR18 deterministic discrete converter acts non-expandingly on
strict behavior — structurally, by test absorption, with no `Emulable`
certificate.  This is the fact the raw-`Δ` carrier could not provide and the
reason approximate constructions on this carrier compose. -/
theorem edist_act_le (primitive : Primitive U)
    (left right : Resource U) :
    edist (primitive.act left) (primitive.act right) ≤ edist left right := by
  rcases left with ⟨leftCode, leftSystem⟩
  rcases right with ⟨rightCode, rightSystem⟩
  by_cases same : leftCode = rightCode
  · subst rightCode
    by_cases sourceMatches : leftCode = primitive.source
    · subst leftCode
      rw [act_of_matches, act_of_matches, Resource.edist_same,
        Resource.edist_same]
      exact StrictContext.System.edist_apply_le
        ⟨primitive.run, primitive.isDDC⟩ leftSystem rightSystem
    · rw [act_of_not_matches primitive _ sourceMatches,
        act_of_not_matches primitive _ sourceMatches]
  · rw [Resource.edist_ne same]
    exact le_top

theorem act_lipschitz_with_one (primitive : Primitive U) :
    LipschitzWith 1 primitive.act :=
  LipschitzWith.of_edist_le primitive.edist_act_le

/-- A primitive as its extensional non-expanding resource endomorphism. -/
noncomputable def toNonexpandingEnd (primitive : Primitive U) :
    nonexpandingEnd (Resource U) :=
  ⟨primitive.act, primitive.act_lipschitz_with_one⟩

@[simp]
theorem to_nonexpanding_end_apply (primitive : Primitive U)
    (resource : Resource U) :
    (primitive.toNonexpandingEnd : Function.End (Resource U)) resource =
      primitive.act resource :=
  rfl

end Primitive

/-- Endomorphisms generated by all CR18 deterministic discrete converters.
They land in `nonexpandingEnd` because non-expansion is structural for the
whole Definition 3.8 class on strict behavior. -/
noncomputable def primitiveRange :
    Set (nonexpandingEnd (Resource U)) :=
  Set.range (Primitive.toNonexpandingEnd (U := U))

/-- The extensional submonoid of non-expanding resource endomorphisms
generated by every `IsDDC` converter.  This is the *interpretation image* of
the syntactic protocol monoid `Protocol`
(`mrange_protocolInclusion_eq_generatedConverterMonoid`), not the protocol
type itself: CR18's Γ is a set of converter programs closed under serial
composition, never a quotient by behavior, and identifying action-equal
programs is exactly what forecloses a representation-independent parallel
operator (MauRen11 fn. 23, `RandomSystemsCC.CR18.ParProtocol`). -/
noncomputable def generatedConverterMonoid
    (U : SignatureUniverse.{c, u, v}) [DecidableEq U.Code] :
    Submonoid (nonexpandingEnd (Resource U)) :=
  Submonoid.closure (primitiveRange (U := U))

/-- Converter words on this carrier: the free serial `{1, ∘}`-algebra over the
CR18 deterministic discrete converters placed between signature codes — the
paper's constructor set, as syntax. -/
inductive ConverterTerm (U : SignatureUniverse.{c, u, v}) : Type (max c u v)
  | prim (primitive : Primitive U)
  | one
  | mul (left right : ConverterTerm U)

namespace ConverterTerm

/-- Interpretation of a converter word as a non-expanding resource
endomorphism: a primitive acts natively (`Primitive.act`, non-expanding by
`Primitive.edist_act_le`) and serial composition is endomorphism composition
(right factor first, the mathlib action order). -/
noncomputable def eval : ConverterTerm U → nonexpandingEnd (Resource U)
  | prim primitive => primitive.toNonexpandingEnd
  | one => 1
  | mul left right => left.eval * right.eval

/-- The monoid-law congruence on converter words: associativity and the two
unit laws for serial composition, closed under composition.  Nothing else —
in particular no behavioral identification. -/
inductive Rel : ConverterTerm U → ConverterTerm U → Prop
  | refl (a) : Rel a a
  | symm {a b} : Rel a b → Rel b a
  | trans {a b c} : Rel a b → Rel b c → Rel a c
  | assoc (a b c) : Rel (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a) : Rel (mul one a) a
  | mul_one (a) : Rel (mul a one) a
  | mul_congr {a a' b b'} : Rel a a' → Rel b b' → Rel (mul a b) (mul a' b')

theorem eval_congr {a b : ConverterTerm U} (h : Rel a b) : a.eval = b.eval := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | assoc a b c => exact mul_assoc _ _ _
  | one_mul a => exact one_mul _
  | mul_one a => exact mul_one _
  | mul_congr _ _ ih₁ ih₂ =>
      show _ * _ = _ * _
      rw [ih₁, ih₂]

instance setoid (U : SignatureUniverse.{c, u, v}) [DecidableEq U.Code] :
    Setoid (ConverterTerm U) :=
  ⟨Rel, ⟨Rel.refl, Rel.symm, Rel.trans⟩⟩

end ConverterTerm

/-- The operational CR18 protocol monoid: converter words modulo the serial
monoid laws only — CR18's syntactic Γ.  AC's contract asks for a monoid with
an action, not for extensionality, and the quotient by action-equality that
used to live here bought nothing downstream while being unsound for a parallel
operator (MauRen11 fn. 23).  The extensional monoid it used to be is retained
as its interpretation image (`generatedConverterMonoid`,
`mrange_protocolInclusion_eq_generatedConverterMonoid`).  Global non-expansion
(`IsNonexpandingSMul` below) still holds — the interpretation lands in
`nonexpandingEnd` — and is what `Constructs.eball_trans` consumes. -/
def Protocol
    (U : SignatureUniverse.{c, u, v}) [DecidableEq U.Code] :
    Type (max c u v) :=
  Quotient (ConverterTerm.setoid U)

namespace Protocol

/-- Display a converter word. -/
def mk (a : ConverterTerm U) : Protocol U :=
  Quotient.mk (ConverterTerm.setoid U) a

instance : One (Protocol U) :=
  ⟨mk ConverterTerm.one⟩

instance : Mul (Protocol U) :=
  ⟨Quotient.map₂ ConverterTerm.mul
    (fun _ _ ha _ _ hb => ConverterTerm.Rel.mul_congr ha hb)⟩

@[simp]
theorem mk_mul (a b : ConverterTerm U) :
    mk a * mk b = mk (ConverterTerm.mul a b) :=
  rfl

instance instMonoid : Monoid (Protocol U) where
  mul_assoc a b c := by
    induction a using Quotient.inductionOn with
    | _ a =>
        induction b using Quotient.inductionOn with
        | _ b =>
            induction c using Quotient.inductionOn with
            | _ c => exact Quot.sound (ConverterTerm.Rel.assoc a b c)
  one_mul a := by
    induction a using Quotient.inductionOn with
    | _ a => exact Quot.sound (ConverterTerm.Rel.one_mul a)
  mul_one a := by
    induction a using Quotient.inductionOn with
    | _ a => exact Quot.sound (ConverterTerm.Rel.mul_one a)

/-- Interpretation: the underlying non-expanding endomorphism of a converter
word — the value AC's action consumes.  Named `val` so that action statements
read exactly as under the former extensional presentation. -/
noncomputable def val : Protocol U → nonexpandingEnd (Resource U) :=
  Quotient.lift ConverterTerm.eval fun _ _ h => ConverterTerm.eval_congr h

@[simp]
theorem val_mk (a : ConverterTerm U) : (mk a).val = a.eval :=
  rfl

@[simp]
theorem val_one : (1 : Protocol U).val = 1 :=
  rfl

@[simp]
theorem val_mul (a b : Protocol U) : (a * b).val = a.val * b.val := by
  induction a using Quotient.inductionOn with
  | _ a =>
      induction b using Quotient.inductionOn with
      | _ b => rfl

end Protocol

/-- Interpretation of the protocol monoid into all non-expanding resource
endomorphisms — the homomorphism through which the AC action factors. -/
noncomputable def protocolInclusion :
    Protocol U →* nonexpandingEnd (Resource U) where
  toFun := Protocol.val
  map_one' := rfl
  map_mul' := Protocol.val_mul

/-- Insert one deterministic discrete converter into the operational monoid. -/
def protocolOfPrimitive (primitive : Primitive U) : Protocol U :=
  Protocol.mk (ConverterTerm.prim primitive)

/-- The protocol monoid acts through its interpretation: an element applies
the endomorphism its word denotes.  This is the only `SMul` path for these
types, so `simp`-level coherence between construction statements and the
action lemmas is preserved. -/
noncomputable instance instMulAction : MulAction (Protocol U) (Resource U) :=
  MulAction.compHom (Resource U)
    ((Submonoid.subtype (nonexpandingEnd (Resource U))).comp
      (protocolInclusion (U := U)))

/-- The full CR18 converter class acts non-expandingly — the metric half of
the AC contract, with no compatibility subclass. -/
instance : IsNonexpandingSMul (Protocol U) (Resource U) where
  lipschitz_smul protocol := (protocolInclusion protocol).property

/-- Interpretation-membership induction: a submonoid of the ambient
endomorphisms containing every primitive action contains the whole interpreted
protocol monoid.  This is the syntactic replacement for
`Submonoid.closure_induction` under the former extensional `Protocol`. -/
theorem protocolInclusion_mem_of_forall_primitive_mem
    {S : Submonoid (nonexpandingEnd (Resource U))}
    (primitiveMember :
      ∀ primitive : Primitive U, primitive.toNonexpandingEnd ∈ S)
    (protocol : Protocol U) :
    protocolInclusion protocol ∈ S := by
  induction protocol using Quotient.inductionOn with
  | _ word =>
      induction word with
      | prim primitive => exact primitiveMember primitive
      | one => exact one_mem S
      | mul left right leftMember rightMember =>
          exact mul_mem leftMember rightMember

/-- **The de-quotienting receipt.**  The extensional monoid this carrier used
to call `Protocol` is exactly the interpretation image of the syntactic one:
nothing that could be expressed by the old presentation was lost, and the
representation is now the paper's. -/
theorem mrange_protocolInclusion_eq_generatedConverterMonoid :
    MonoidHom.mrange (protocolInclusion (U := U)) =
      generatedConverterMonoid U := by
  refine le_antisymm ?_ (Submonoid.closure_le.mpr ?_)
  · rintro _ ⟨protocol, rfl⟩
    exact protocolInclusion_mem_of_forall_primitive_mem
      (fun primitive =>
        Submonoid.subset_closure (Set.mem_range_self primitive))
      protocol
  · rintro _ ⟨primitive, rfl⟩
    exact ⟨protocolOfPrimitive primitive, rfl⟩

noncomputable instance : CoeTC (Primitive U) (Protocol U) :=
  ⟨protocolOfPrimitive⟩

noncomputable instance : SMul (Primitive U) (Resource U) :=
  ⟨fun primitive resource => primitive.act resource⟩

@[simp]
theorem primitive_smul_eq_act (primitive : Primitive U)
    (resource : Resource U) :
    primitive • resource = primitive.act resource :=
  rfl

@[simp]
theorem protocolOfPrimitive_smul (primitive : Primitive U)
    (resource : Resource U) :
    protocolOfPrimitive primitive • resource = primitive.act resource :=
  rfl

/-- Place a pure deterministic discrete converter at its source and target
signatures. -/
noncomputable def liftConverter
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput) : Primitive U := by
  rcases targetCode with ⟨target, rfl, rfl⟩
  rcases sourceCode with ⟨source, rfl, rfl⟩
  exact ⟨source, target, converter.run, converter.isDDC⟩

omit [DecidableEq U.Code] in
@[simp]
theorem liftConverter_source
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput) :
    (liftConverter (U := U) converter).source = sourceCode.code := by
  rcases targetCode with ⟨target, rfl, rfl⟩
  rcases sourceCode with ⟨source, rfl, rfl⟩
  rfl

omit [DecidableEq U.Code] in
@[simp]
theorem liftConverter_target
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput) :
    (liftConverter (U := U) converter).target = targetCode.code := by
  rcases targetCode with ⟨target, rfl, rfl⟩
  rcases sourceCode with ⟨source, rfl, rfl⟩
  rfl

noncomputable instance
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput] :
    CoeTC
      (DDConverter targetInput targetOutput sourceInput sourceOutput)
      (Primitive U) :=
  ⟨liftConverter⟩

noncomputable instance
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput] :
    CoeTC
      (DDConverter targetInput targetOutput sourceInput sourceOutput)
      (Protocol U) :=
  ⟨fun converter => protocolOfPrimitive (liftConverter converter)⟩

/-- A typed DDC acts directly on a resource.  Its source and target signatures
are recovered from the bundled converter and the ambient resource universe;
the operational protocol embedding is not part of the expression. -/
noncomputable instance
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput] :
    HMul
      (DDConverter targetInput targetOutput sourceInput sourceOutput)
      (Resource U)
      (Resource U) :=
  ⟨fun converter resource =>
    (liftConverter (U := U) converter).act resource⟩

/-- The AC protocol embedding and the native typed DDC action agree.  This is
the coherence law that lets construction proofs stay entirely on the
`DDConverter * Resource` surface. -/
@[simp]
theorem protocolOf_liftConverter_smul_eq_mul
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (resource : Resource U) :
    protocolOfPrimitive
          (liftConverter (U := U) (targetCode := targetCode)
            (sourceCode := sourceCode) converter) • resource =
      converter * resource :=
  rfl

/-- Coercion-facing form of `protocolOf_liftConverter_smul_eq_mul`. -/
@[simp]
theorem coe_smul_eq_mul
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (resource : Resource U) :
    (converter : Protocol U) • resource = converter * resource :=
  protocolOf_liftConverter_smul_eq_mul converter resource

noncomputable instance {X : Type u} {Y : Type v}
    [HasResourceCode U X Y] :
    HSMul (Protocol U) (PFunPDS.Prob X Y) (Resource U) :=
  ⟨fun protocol system => protocol • liftProb system⟩

noncomputable instance {X : Type u} {Y : Type v}
    [HasResourceCode U X Y] :
    HSMul (Protocol U) (PFunPDS.Prob X Y) (Set (Resource U)) :=
  ⟨fun protocol system => {protocol • liftProb system}⟩

@[simp]
theorem protocol_smul_prob {X : Type u} {Y : Type v}
    [HasResourceCode U X Y]
    (protocol : Protocol U) (system : PFunPDS.Prob X Y) :
    protocol • system = protocol • liftProb (U := U) system :=
  rfl

/-- Lifted converter application is exactly ordinary CR18 application. -/
@[simp]
theorem protocolOf_liftConverter_smul_liftProb
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (system : PFunPDS.Prob sourceInput sourceOutput) :
    protocolOfPrimitive
          (liftConverter (U := U) (targetCode := targetCode)
            (sourceCode := sourceCode) converter) •
        liftProb (U := U) (code := sourceCode) system =
      liftProb (U := U) (code := targetCode)
        (PFunPDS.Prob.applyConverter converter.run system) := by
  rcases targetCode with ⟨target, rfl, rfl⟩
  rcases sourceCode with ⟨source, rfl, rfl⟩
  simp [liftConverter, liftProb, Primitive.act]
  rfl

@[simp]
theorem converter_smul_liftProb
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [targetCode : HasResourceCode U targetInput targetOutput]
    [sourceCode : HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (system : PFunPDS.Prob sourceInput sourceOutput) :
    (converter : Protocol U) • liftProb (U := U) system =
      liftProb (U := U)
        (PFunPDS.Prob.applyConverter converter.run system) :=
  protocolOf_liftConverter_smul_liftProb converter system

@[simp]
theorem converter_mul_liftProb
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (system : PFunPDS.Prob sourceInput sourceOutput) :
    converter * liftProb (U := U) system =
      liftProb (U := U)
        (PFunPDS.Prob.applyConverter converter.run system) := by
  change
    (converter : Protocol U) • liftProb (U := U) system =
      liftProb (U := U)
        (PFunPDS.Prob.applyConverter converter.run system)
  exact converter_smul_liftProb converter system

/-! ## Construction notation -/

/-- A bare typed DDC labels its AC construction through the operational
embedding inferred from its source and target resource codes. -/
@[reducible]
noncomputable def constructs
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput]
    (converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput)
    (ε : ℝ) (assumed constructed : Resource U) : Prop :=
  AbstractCrypto.ApproximatelyConstructs
    (converter : Protocol U) (ENNReal.ofReal ε) {assumed} {constructed}

@[inherit_doc] scoped notation:50
  assumed:51 " —[" converter "; " ε "]→ " constructed:51 =>
    constructs converter ε assumed constructed

namespace DDConverter

/-- A native real-valued CR18 advantage bound is a typed DDC construction
between embedded strict behaviors.  Only this sound direction exists: strict
contextual distance is bounded by `Δ` but not equal to it
(`RandomSystems.AttainmentCounterexample`). -/
theorem constructs_liftProb_of_advantage
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput]
    {converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput}
    {left : PFunPDS.Prob sourceInput sourceOutput}
    {right : PFunPDS.Prob targetInput targetOutput}
    {ε : ℝ} (bound : Δ(converter * left.val, right.val) ≤ ε) :
    constructs (U := U) converter ε
      (liftProb (U := U) left)
      (liftProb (U := U) right) := by
  unfold constructs AbstractCrypto.ApproximatelyConstructs
  rw [AbstractCrypto.constructs_singleton_eball_iff]
  change
    edist
        (converter * liftProb (U := U) left)
        (liftProb (U := U) right) ≤ ENNReal.ofReal ε
  rw [converter_mul_liftProb]
  exact (edist_liftProb_le_advantage _ _).trans
    (ENNReal.ofReal_le_ofReal bound)

/-- A typed construction with a common outer converter follows from the
native CR18 advantage bound.  All resource-interface witnesses are shared in
this statement, so neither internal action embeddings nor interface alignment
appear at the call site. -/
theorem constructs_mul_liftProb_of_advantage
    {targetInput middleInput sourceInput : Type u}
    {targetOutput middleOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U middleInput middleOutput]
    [HasResourceCode U sourceInput sourceOutput]
    {outer : DDConverter
      targetInput targetOutput middleInput middleOutput}
    {inner : DDConverter
      middleInput middleOutput sourceInput sourceOutput}
    {left : PFunPDS.Prob sourceInput sourceOutput}
    {right : PFunPDS.Prob middleInput middleOutput}
    {ε : ℝ}
    (bound : Δ(outer * (inner * left.val), outer * right.val) ≤ ε) :
    constructs (U := U) (outer * inner) ε
      (liftProb (U := U) left)
      (outer * liftProb (U := U) right) := by
  rw [converter_mul_liftProb]
  exact constructs_liftProb_of_advantage
    (by simpa only [PFunPDS.Prob.applyConverter, mul_system, apply_mul]
      using bound)

/-- A typed construction whose constructed resource is the same converter
over a second assumed law follows from the native two-sided CR18 advantage
bound — the substitution shape of a distinguishing lemma (URF/URP switching)
as a construction. -/
theorem constructs_apply_liftProb_of_advantage
    {targetInput sourceInput : Type u}
    {targetOutput sourceOutput : Type v}
    [HasResourceCode U targetInput targetOutput]
    [HasResourceCode U sourceInput sourceOutput]
    {converter : DDConverter
      targetInput targetOutput sourceInput sourceOutput}
    {left right : PFunPDS.Prob sourceInput sourceOutput}
    {ε : ℝ}
    (bound : Δ(converter * left.val, converter * right.val) ≤ ε) :
    constructs (U := U) converter ε
      (liftProb (U := U) left)
      (converter * liftProb (U := U) right) := by
  rw [converter_mul_liftProb]
  exact constructs_liftProb_of_advantage
    (by simpa only [PFunPDS.Prob.applyConverter, mul_system] using bound)

end DDConverter

/-- Enter the native CR18 advantage goal for a scalar AC construction between
embedded strict behaviors.  Typed converter composition, converter action,
interface alignment, the sound metric bridge, and the `ℝ`/`ℝ≥0∞` boundary are
discharged here; the remaining goal is the paper's real-valued `Δ`
inequality. -/
macro "cr18_construct" : tactic =>
  `(tactic|
    first
      | apply
          RandomSystemsCC.CR18.DDConverter.constructs_mul_liftProb_of_advantage
      | apply
          RandomSystemsCC.CR18.DDConverter.constructs_apply_liftProb_of_advantage
      | apply
          RandomSystemsCC.CR18.DDConverter.constructs_liftProb_of_advantage)

end

end RandomSystemsCC.CR18
