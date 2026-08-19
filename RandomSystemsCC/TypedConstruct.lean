/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite
import RandomSystemsCC.TypedFramingAdvantage
import RandomSystemsCC.AdversaryStructure

/-!
# Construction assembly on the interface-indexed carrier

`RandomSystemsCC.CR18.cr18_construct` (`ResourceLift.lean`) enters the native
CR18 advantage goal for a scalar AC construction — but only on the
fixed-signature strict carrier `RandomSystemsCC.CR18.Resource U`, which has
exactly one downstream model.  Every `CC.SecurelyConstructs` judgment of the
estate, all of `Symmetric/**` and all of `Frost/**`, lives on the
interface-indexed carrier `Phi I U` instead, and that carrier had no
construction tactic at all.  This module is its analogue, plus the small
assembly layer the endpoint proofs were writing by hand.

## What `rs_construct` discharges

The same four things `cr18_construct` discharges, at this carrier:

* **typed composition** — a protocol tuple is a product of single-interface
  converter words, and the endpoint's own normalization equation says what the
  product does; the tuple/monoid embedding never enters the leaf;
* **the action** — `Primitive.act` on a displayed law is the attached law
  (`primitive_smul_coe_prob`), so the leaf is stated about laws, not about
  resources;
* **boundary alignment** — the heterogeneous carrier puts unequal boundaries
  at distance `⊤`, so a distance goal is only informative inside one fibre;
  `Resource.edist_same` moves it there and `edist_coe_prob_le_advantage`
  keeps it there;
* **the `ℝ`/`ℝ≥0∞` boundary** — a real-valued paper bound becomes an
  `ℝ≥0∞` construction radius through `ENNReal.ofReal`.

What is left is the paper's leaf: either the native contextual distance
`DependentPDS.contextualEDist` or the real-valued CR18 advantage `Δ`.

Only the **sound** direction of the source-metric bridge exists here, exactly
as on the fixed-signature carrier: `contextualEDist ≤ ENNReal.ofReal Δ` is
`TypedFramingAdvantage.edist_of_prob_le_max_advantage_flatten`, and the
converse needs support totality
(`RandomSystems.AttainmentCounterexample` is the refutation in general).
Construction statements therefore only ever use `≤`.

## What the assembly layer adds

Three facts the endpoint proofs of `Symmetric/**` were re-deriving:

* `availability_of_security` — MauRen11 Definition 3's availability clause
  from its security clause, given that the honest protocol commutes with the
  availability filter and that the simulator is idle on the assumed resource.
  This is `Symmetric.OTP.availability_eq_of_security_eq` with the model
  removed;
* `commute_honest_of_supported` — the honest/adversary commutation premise of
  `CC.SecurelyConstructs.trans`, from simulator support alone.  This is
  `Symmetric.MACThenOTP.commute_honest_simulators` with the model removed;
* `securelyConstructs_trans_of_supported` — serial composition of two
  fixed-`Z` judgments with that premise already discharged.

## Relationship to the AC assemblers

`AbstractCrypto.ProofAutomation` already ships `ac_construct`, `ac_commute`,
`ac_triangle`, `ac_nonexpand`, `ac_compose`, `ac_chain`, `ac_simulator`,
`ac_relax`, `ac_filtered`, `ac_transport`, `ac_normalize`, `ac_routine`,
`ac_parallel`, `ac_context_left`, `ac_context_right` and
`ac_transfer_property`.  Nothing in `RandomSystemsCC/` used any of them.  The
wrappers below are exactly the ones with a leaf this carrier owns; the file
docstring of `RandomSystemsCC.TypedConstructChecks` records which AC
assemblers were deliberately not wrapped and why.
-/

namespace RandomSystemsCC.TypedFinite

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open scoped AbstractCrypto ENNReal

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code]

/-! ## The action, on displayed laws

The carrier's action is defined on the behavioral quotient.  These two facts
say that on a *displayed* law it is the law-level attachment, which is what
lets the leaf of a construction proof be stated about laws. -/

/-- A local converter placed at a matching code acts on a displayed law by
law-level attachment.  This is the well-placedness receipt in the form a
construction proof consumes: the hypothesis `placed` is exactly the obligation
`ConverterTerm.WellPlaced` records, and its conclusion moves the boundary as
the converter's type says. -/
theorem primitive_smul_coe_prob {interface : I}
    (primitive : Primitive I U interface) {boundary : Boundary U I}
    (placed : boundary interface = primitive.source)
    (law : DependentPDS.Prob U boundary) :
    primitive • (law : Phi I U) =
      ((law.attach interface primitive.converter placed :
          DependentPDS.Prob U
            (replaceBoundary boundary interface primitive.target)) :
        Phi I U) := by
  show primitive.act ⟨boundary, DependentRandomSystem.ofProb law⟩ = _
  rw [Primitive.act_of_matches primitive boundary placed]
  rfl

/-- The same fact for the AC protocol embedding of a local converter, so a
construction statement written with the tuple `Pi.mulSingle` never has to
mention it again. -/
theorem protocolOfPrimitive_smul_coe_prob [Fintype I] {interface : I}
    (primitive : Primitive I U interface) {boundary : Boundary U I}
    (placed : boundary interface = primitive.source)
    (law : DependentPDS.Prob U boundary) :
    (protocolOfPrimitive primitive : Protocol I U) • (law : Phi I U) =
      ((law.attach interface primitive.converter placed :
          DependentPDS.Prob U
            (replaceBoundary boundary interface primitive.target)) :
        Phi I U) := by
  rw [coe_primitive_smul]
  exact primitive_smul_coe_prob primitive placed law

/-! ## The metric bridge and the `ℝ`/`ℝ≥0∞` boundary -/

/-- Two displayed laws at one boundary are at their fibre's contextual
distance.  This is the boundary-alignment step: off the diagonal the
heterogeneous carrier answers `⊤`, and every construction leaf must therefore
be read inside one fibre. -/
@[simp]
theorem edist_coe_prob {boundary : Boundary U I}
    (left right : DependentPDS.Prob U boundary) :
    edist (left : Phi I U) (right : Phi I U) =
      DependentPDS.contextualEDist left.val right.val :=
  Resource.edist_same boundary _ _

/-- **The sound direction of the source-metric bridge on this carrier.**  A
CR18 advantage bound on the flattened global laws is an AC distance bound on
the displayed resources.  The converse is false in general
(`RandomSystems.AttainmentCounterexample`); construction proofs use this
inequality and never an equality. -/
theorem edist_coe_prob_le_advantage {boundary : Boundary U I}
    (left right : DependentPDS.Prob U boundary) :
    edist (left : Phi I U) (right : Phi I U) ≤
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) := by
  rw [edist_coe_prob]
  exact TypedFramingAdvantage.contextual_edist_prob_le_max_advantage_flatten
    left right

/-! ## Entering the native leaf

The three theorems `rs_construct` selects between.  Each takes the endpoint's
own normalization of the protocol action — the equation that says what the
tuple did — and leaves exactly the paper's leaf. -/

section Entry

variable [Fintype I]

/-- **Native contextual-distance entry.**  A scalar AC construction between
displayed resources follows from the contextual distance of the two laws.
`applied` is the endpoint's normalization of the protocol action and `target`
the packing of the ideal resource; both are the model's data, so neither the
tuple embedding nor the boundary bookkeeping appears in the leaf. -/
theorem constructs_of_contextualEDist {π : Protocol I U} {assumed ideal : Phi I U}
    {boundary : Boundary U I}
    {applied idealLaw : DependentPDS.Prob U boundary} {ε : ℝ≥0∞}
    (normalized : π • assumed = (applied : Phi I U))
    (target : ideal = (idealLaw : Phi I U))
    (bound : DependentPDS.contextualEDist applied.val idealLaw.val ≤ ε) :
    ⟪assumed⟫ —[π; ε]→ ⟪ideal⟫ := by
  refine constructs_singleton_eball_iff.mpr ?_
  rw [normalized, target, edist_coe_prob]
  exact bound

/-- **Native CR18 advantage entry.**  The same statement with the paper's
real-valued leaf: the maximal distinguishing advantage between the two
flattened global laws.  The `ℝ`/`ℝ≥0∞` boundary is crossed here. -/
theorem constructs_of_advantage {π : Protocol I U} {assumed ideal : Phi I U}
    {boundary : Boundary U I}
    {applied idealLaw : DependentPDS.Prob U boundary} {ε : ℝ}
    (normalized : π • assumed = (applied : Phi I U))
    (target : ideal = (idealLaw : Phi I U))
    (bound :
      Δ(DependentPDS.flatten applied.val, DependentPDS.flatten idealLaw.val) ≤
        ε) :
    ⟪assumed⟫ —[π; ENNReal.ofReal ε]→ ⟪ideal⟫ := by
  refine constructs_of_contextualEDist normalized target ?_
  exact (TypedFramingAdvantage.contextual_edist_prob_le_max_advantage_flatten
    applied idealLaw).trans (ENNReal.ofReal_le_ofReal bound)

/-- **Perfect entry.**  A construction at every radius from one behavioral
equality — the shape a coupling argument produces, and the shape the perfect
symmetric endpoints actually prove. -/
theorem constructs_of_smul_eq {π : Protocol I U} {assumed ideal : Phi I U}
    (ε : ℝ≥0∞) (coupling : π • assumed = ideal) :
    ⟪assumed⟫ —[π; ε]→ ⟪ideal⟫ :=
  constructs_singleton_eball_iff.mpr (by rw [coupling]; simp)

/-- Bare-converter form of `constructs_of_smul_eq`: a local converter is
usable directly in the construction notation, so its perfect construction
should be too. -/
theorem primitive_constructs_of_smul_eq {interface : I}
    {primitive : Primitive I U interface} {assumed ideal : Phi I U}
    (ε : ℝ≥0∞) (coupling : primitive • assumed = ideal) :
    ⟪assumed⟫ —[primitive; ε]→ ⟪ideal⟫ :=
  constructs_of_smul_eq (π := protocolOfPrimitive primitive) ε
    (by rw [coe_primitive_smul]; exact coupling)

end Entry

/-! ## The assembly layer

Three facts the fixed-`Z` endpoints were re-deriving by hand.  Each is stated
with the model removed, so it is the *inference* and nothing else. -/

section Assembly

variable [Fintype I]

/-- **MauRen11 Definition 3's availability clause from its security clause.**

The availability filter of every symmetric endpoint factors as
`filter * simulator`: the simulator is the dishonest-interface converter the
security clause names, and `filter` blocks the remaining dishonest port.  On
the *assumed* resource the simulator is idle — its source code is the ideal
one, and `Primitive.act` is the identity off its source — while the honest
protocol and the filter act at disjoint interfaces and therefore commute.
Those two facts turn the security equation into the availability equation.

This is `Symmetric.OTP.availability_eq_of_security_eq` with the model
removed. -/
theorem availability_of_security {protocol filter simulator : Protocol I U}
    {assumed ideal : Phi I U}
    (idle : simulator • assumed = assumed)
    (commuting : ∀ resource : Phi I U,
      protocol • (filter • resource) = filter • (protocol • resource))
    (security : protocol • assumed = simulator • ideal) :
    protocol • ((filter * simulator) • assumed) =
      (filter * simulator) • ideal := by
  rw [mul_smul, idle, commuting, security, mul_smul]

omit [Fintype I] in
/-- **The honest/adversary commutation premise, from simulator support
alone.**  `CC.SecurelyConstructs.trans` asks that the honest attachment of the
second protocol commute with every admitted simulator; when the admitted class
is the tuples supported at the dishonest interfaces — which is what every
endpoint of this estate uses — that is exactly MauRen11's implicit interface
disjointness, and nothing else is needed.

This is `Symmetric.MACThenOTP.commute_honest_simulators` with the model
removed. -/
theorem commute_honest_of_supported {Z : Set I}
    {simulators : Submonoid (Protocol I U)}
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    (protocol : Protocol I U) {simulator : Protocol I U}
    (member : simulator ∈ simulators) :
    Commute (protocol ⇂ Zᶜ) simulator :=
  commute_patternAttach_supportedOn (H := fun _ => ⊤)
    (by simpa only [compl_compl] using admitted member) protocol

omit [Fintype I] in
/-- **Admission of a named simulator into LiuMau20's joint dishonest class.**

The specification-form leaf
(`RandomSystemsCC.constructsForAdversaryStructure_of_leaves`) asks for a
simulator in `zSub tupleGamma Z`, while every endpoint of this estate names
its simulator class as `supportedOn Z ⊤`.  At a finite dishonest set the two
classes are equal (`AbstractCrypto.zSub_tupleGamma_eq_supportedOn`); this is
that equality in the direction a simulator leaf consumes.  It is what
`Symmetric.OTP.otpSimulators_eq_zSub` does inline. -/
theorem mem_zSub_of_supported {Z : Set I} (finite : Z.Finite)
    {simulator : Protocol I U}
    (member : simulator ∈ supportedOn Z (fun _ => ⊤)) :
    simulator ∈ zSub (M := Protocol I U) tupleGamma Z := by
  rw [zSub_tupleGamma_eq_supportedOn finite]
  exact member

/-- **Serial composition of two fixed-`Z` judgments** (MauRen11 Theorem 1(i))
with the commutation premise discharged from simulator support.  The right
factor acts first, so the protocols compose as `second * first` and the radii
add. -/
theorem securelyConstructs_trans_of_supported {Z : Set I}
    {simulators : Submonoid (Protocol I U)}
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    {protocol protocol' bottom : Protocol I U} {ε ε' : ℝ≥0∞}
    {R S T : Phi I U}
    (first : CC.SecurelyConstructs Z simulators protocol bottom ε R S)
    (second : CC.SecurelyConstructs Z simulators protocol' bottom ε' S T) :
    CC.SecurelyConstructs Z simulators (protocol' * protocol) bottom
      (ε + ε') R T :=
  CC.SecurelyConstructs.trans first second
    (fun _ member => commute_honest_of_supported admitted protocol' member)

end Assembly

end RandomSystemsCC.TypedFinite

/-! ## Tactics

Deterministic, in the sense the AC assemblers are: a fixed finite ladder of
named theorems, no environment search, no widened simp set. -/

/-- Enter the native leaf of a scalar AC construction on the interface-indexed
carrier, from the endpoint's own normalization of the protocol action
(`normalized`) and packing of the ideal resource (`target`).  Typed converter
composition, the converter action, boundary alignment and the `ℝ`/`ℝ≥0∞`
boundary are discharged here; the remaining goal is the paper's leaf — the
real-valued `Δ` inequality when the radius is displayed as `ENNReal.ofReal`,
and the native contextual distance otherwise.

This is the `RandomSystemsCC.TypedFinite.Phi` analogue of `cr18_construct`.

The radius test is run `with_reducible` on purpose: at full transparency the
unifier tries to see whether an opaque `ε : ℝ≥0∞` is an `ENNReal.ofReal`, and
that search costs more than the whole tactic (measured: a `maxHeartbeats`
timeout).  Reducible transparency makes the shape test syntactic, so the
`ℝ`-valued branch is selected exactly when the paper displays an
`ENNReal.ofReal` radius. -/
macro "rs_construct" " using " normalized:term ", " target:term : tactic =>
  `(tactic|
    first
      | with_reducible
          refine
            RandomSystemsCC.TypedFinite.constructs_of_advantage
              $normalized $target ?_
      | refine
          RandomSystemsCC.TypedFinite.constructs_of_contextualEDist
            $normalized $target ?_
      | fail "rs_construct expected a scalar construction goal on `Phi I U` together with a protocol-action normalization and an ideal-resource packing")

/-- Close a scalar AC construction on the interface-indexed carrier from one
behavioral equality — the shape a coupling argument produces.  The radius is
read off the goal and may be anything: a perfect construction is an
`ε`-approximate one at every radius. -/
macro "rs_construct" " using " coupling:term : tactic =>
  `(tactic|
    first
      | exact RandomSystemsCC.TypedFinite.constructs_of_smul_eq _ $coupling
      | exact
          RandomSystemsCC.TypedFinite.primitive_constructs_of_smul_eq _
            $coupling
      | fail "rs_construct expected a scalar construction goal on `Phi I U` and a matching protocol-action equality")

/-- Name the simulator of a LiuMau20 specification-form leaf and discharge its
admission from the endpoint's own `supportedOn Z ⊤` membership.  What remains
is the behavioral leg — the equality or distance bound the simulator is there
to witness.

Deliberately **not** `ac_simulator`: that command targets
`Relaxation.star simulators`, whereas this leaf is the `zSub tupleGamma Z`
existential, so reusing it would silently change which ideal specification the
statement is about. -/
macro "rs_simulator" simulator:term " using " member:term : tactic =>
  `(tactic|
    first
      | refine ⟨$simulator,
          RandomSystemsCC.TypedFinite.mem_zSub_of_supported
            (by first | exact Set.finite_singleton _ | assumption)
            $member, ?_⟩
      | refine ⟨$simulator, $member, ?_⟩
      | fail "rs_simulator expected a simulator-leaf existential and a matching `supportedOn Z ⊤` membership")

/-- Discharge MauRen11 Definition 3's availability clause from the supplied
security clause.  The two hypotheses the inference genuinely uses — that the
simulator is idle on the assumed resource, and that the honest protocol
commutes with the availability filter — remain as visible goals. -/
macro "rs_availability" " using " security:term : tactic =>
  `(tactic|
    first
      | refine RandomSystemsCC.TypedFinite.availability_of_security ?_ ?_
          $security
      | fail "rs_availability expected an availability equation whose filter is displayed as `filter * simulator`")

/-- Discharge the honest/adversary commutation premise from simulator support.
`ac_commute using` alone cannot see it: the admitted class of every endpoint
here is `supportedOn Z ⊤` while the premise is stated at the honest pattern
`Zᶜ`, so the double complement has to be normalized first. -/
macro "rs_commute" " using " admitted:term ", " member:term : tactic =>
  `(tactic|
    first
      | exact RandomSystemsCC.TypedFinite.commute_honest_of_supported
          $admitted _ $member
      | ac_commute using (by
          simpa only [compl_compl] using $admitted $member)
      | fail "rs_commute expected a converter commutation goal, a simulator-class inclusion into `supportedOn Z ⊤`, and a membership proof")

/-- Compose two named constructions in execution order.  A fixed-`Z` CC
judgment composes by MauRen11 Theorem 1(i) with the commutation premise taken
from simulator support; a bare AC construction composes by `ac_compose`. -/
macro "rs_compose" first:term ", " second:term " using " admitted:term : tactic =>
  `(tactic|
    first
      | exact
          RandomSystemsCC.TypedFinite.securelyConstructs_trans_of_supported
            $admitted $first $second
      | fail "rs_compose expected two fixed-`Z` CC judgments over one admitted simulator class")

/-- Split a scalar construction on the interface-indexed carrier through an
explicit intermediate resource.  The construction goal is reduced to its
distance form first, which is what `ac_triangle` cannot do on its own. -/
macro "rs_triangle" " via " intermediate:term : tactic =>
  `(tactic|
    first
      | (refine AbstractCrypto.constructs_singleton_eball_iff.mpr ?_
         ac_triangle via $intermediate)
      | ac_triangle via $intermediate
      | fail "rs_triangle expected a scalar construction or distance goal with an additive error bound")

/-- Select the non-expansion theorem for a converter action on the
interface-indexed carrier.  `ac_nonexpand` covers the protocol tuple; the bare
local-converter form has no `IsNonexpandingSMul` instance and is covered by
the native `Primitive.edist_act_le`. -/
macro "rs_nonexpand" : tactic =>
  `(tactic|
    first
      | ac_nonexpand
      | exact RandomSystems.CR18.TypedResource.Primitive.edist_act_le _ _ _
      | fail "rs_nonexpand expected a converter-action or parallel non-expansion goal on `Phi I U`")
