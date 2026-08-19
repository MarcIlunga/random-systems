/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.ControlledNaturalLanguage
import RandomSystemsCC.TypedFiniteChecks

/-!
# Permanent regression gate for the construction-assembly surface

The sibling of `RandomSystemsCC.NotationChecks`, for tactics and sentences
instead of notation.  Every statement here is a *usability* receipt: each
`example` asserts that a command fires on the goal shape a model actually
produces, **and leaves exactly the goals a reader would expect** — the leaves
are discharged from named hypotheses, never by `assumption` or a solver, so a
drift in what a tactic hides shows up as a build failure here rather than as
silent re-hand-rolling inside `Symmetric/**`.

The carrier is `RandomSystemsCC.TypedFiniteChecks.testUniverse` over
`Fin 2` — the estate's existing hostile generic model, not a new toy.

## Which AC assemblers are wrapped, and which are not

`AbstractCrypto.ProofAutomation` ships sixteen commands.  The card that
commissioned this work listed four of them (`ac_compose`, `ac_simulator`,
`ac_context_left`, `ac_transfer_property`) as non-existent and gave a
ten-command list as the correction; **both lists are wrong**.  All sixteen
exist — `ac_normalize`, `ac_normalize?`, `ac_routine`, `ac_construct`,
`ac_transport`, `ac_simulator`, `ac_relax`, `ac_filtered`, `ac_triangle`,
`ac_nonexpand`, `ac_commute`, `ac_transfer_property`, `ac_compose`,
`ac_compose_simulators`, `ac_parallel`, `ac_context_left`,
`ac_context_right`, `ac_chain`, plus the `ac?` diagnostic — and, measured on
2026-07-29, **none of them was used anywhere under `RandomSystemsCC/`.**

Wrapped, because this carrier owns a leaf the AC command cannot reach:

* `ac_commute using` → `rs_commute using`.  The admitted class of every
  endpoint here is `supportedOn Z ⊤` while the premise is stated at the
  honest pattern `Zᶜ`; the double complement has to be normalized first.
* `ac_triangle via` → `rs_triangle via`.  The goal is a construction
  judgment, not a distance; the reduction to `edist` comes first.
* `ac_nonexpand` → `rs_nonexpand`.  There is no
  `IsNonexpandingSMul (Primitive …) (Phi …)` instance — a bare local
  converter is not a monoid — so the bare-converter form falls to the native
  `Primitive.edist_act_le`.
* `ac_compose` → `rs_compose`.  The endpoints are `CC.SecurelyConstructs`
  judgments, whose composition theorem carries an extra commutation premise
  that the plain AC serial-composition theorems do not have.

Not wrapped, with reasons:

* `ac_construct`, `ac_construct using` — subsumed.  `rs_construct` *is* the
  carrier-specific construct command; a second thin alias would compete with
  it for the same goals.
* `ac_normalize`, `ac_routine` — carrier-free bookkeeping over the curated AC
  registries.  There is no `Phi`-specific obligation for them to discharge;
  they already fire unchanged, which the receipts below pin.
* `ac_transport using` — fires unchanged on this carrier (receipt below).  A
  protocol-label replacement has no boundary, action or metric leg, so a
  wrapper would add nothing.
* `ac_simulator` — deliberately **not** wrapped.  It targets
  `Relaxation.star simulators`, whereas this estate's simulator leaf is
  LiuMau20's `zSub tupleGamma Z` existential
  (`RandomSystemsCC.constructsForAdversaryStructure_of_leaves`).  Wrapping it
  would silently retarget the sentence at a different ideal specification —
  precisely the "no hidden choice of ideal resource" rule.  `CC` already
  consumes `ac_simulator` at the one place it does apply
  (`SecurelyConstructs.security_constructs`).
* `ac_relax`, `ac_filtered` — `Relaxation`-compatibility and
  `FilteredSpecifications` assemblers with no consumer on this carrier: no
  endpoint states a `filteredAt` construction or a relax-through step, so a
  wrapper would have no obligation to discharge.
* `ac_parallel`, `ac_context_left`, `ac_context_right`,
  `ac_compose_simulators` — these need `Par` and `SMulParClass` on the
  *protocol* side, which `Phi` deliberately does not have: STATUS §11.5
  refutes par-action non-expansion by counterexample and §11.10.1 records
  that a `par` on `ConverterTerm` would break `IsNonexpandingSMul`, hence
  `SecurelyConstructs.trans`, for every existing endpoint.  A wrapper here
  would be unusable by construction.
* `ac_transfer_property` — needs a `DistinguisherClass`;
  `RandomSystemsCC.TypedPropertyTransfer` already consumes
  `one_tsub_le_test_of_close` directly, so there is no second obligation.
-/

namespace RandomSystemsCC.TypedConstructChecks

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open RandomSystemsCC.TypedFiniteChecks (testUniverse Interface bitBoundary)
open scoped AbstractCrypto ENNReal CryptoControlledNaturalLanguage

local notation "Φ" => Phi Interface testUniverse
local notation "Π" => Protocol Interface testUniverse
local notation "Λ" => DependentPDS.Prob testUniverse bitBoundary

/-! ### `rs_construct`: the leaf is the paper's advantage inequality

The command is given the model's two normalizations and leaves the CR18
advantage bound — nothing else.  The leaf is closed from a *named* hypothesis,
so if the command ever started hiding the estimate this example would report
"no goals". -/

example (π : Π) (assumed idealResource : Φ) (applied idealLaw : Λ) (ε : ℝ)
    (normalized : π • assumed = (applied : Φ))
    (target : idealResource = (idealLaw : Φ))
    (advantageBound :
      Δ(DependentPDS.flatten applied.val, DependentPDS.flatten idealLaw.val) ≤
        ε) :
    ⟪assumed⟫ —[π; ENNReal.ofReal ε]→ ⟪idealResource⟫ := by
  rs_construct using normalized, target
  exact advantageBound

/-- At a radius that is not displayed as `ENNReal.ofReal`, the same command
leaves the *native* contextual-distance leaf instead.  This is the branch the
statistical endpoints need, whose radii read `1 / (Fintype.card T : ℝ≥0∞)`. -/
example (π : Π) (assumed idealResource : Φ) (applied idealLaw : Λ) (ε : ℝ≥0∞)
    (normalized : π • assumed = (applied : Φ))
    (target : idealResource = (idealLaw : Φ))
    (distanceBound : DependentPDS.contextualEDist applied.val idealLaw.val ≤ ε) :
    ⟪assumed⟫ —[π; ε]→ ⟪idealResource⟫ := by
  rs_construct using normalized, target
  exact distanceBound

/-- The perfect form: one behavioral equality closes the construction at every
radius.  A protocol tuple… -/
example (π : Π) (R S : Φ) (ε : ℝ≥0∞) (coupling : π • R = S) :
    ⟪R⟫ —[π; ε]→ ⟪S⟫ := by
  rs_construct using coupling

/-- …and a **bare** local converter, which has no monoid and therefore no
`IsNonexpandingSMul`; the construction notation still takes it directly. -/
example (primitive : Primitive Interface testUniverse 0) (R S : Φ)
    (ε : ℝ≥0∞) (coupling : primitive • R = S) :
    ⟪R⟫ —[primitive; ε]→ ⟪S⟫ := by
  rs_construct using coupling

/-! ### The four discharged boundaries, individually

Each of the four things `rs_construct` hides is a named theorem, so a reader
can check them one at a time. -/

/-- **The action.**  A placed local converter acts on a displayed law by
law-level attachment, and moves the boundary as its type says. -/
example (primitive : Primitive Interface testUniverse 0) (law : Λ)
    (placed : bitBoundary 0 = primitive.source) :
    primitive • (law : Φ) =
      ((law.attach 0 primitive.converter placed :
          DependentPDS.Prob testUniverse
            (replaceBoundary bitBoundary 0 primitive.target)) : Φ) :=
  primitive_smul_coe_prob primitive placed law

/-- **Typed composition.**  The same, through the AC protocol embedding, so a
statement written with the tuple never has to unfold it. -/
example (primitive : Primitive Interface testUniverse 0) (law : Λ)
    (placed : bitBoundary 0 = primitive.source) :
    (protocolOfPrimitive primitive : Π) • (law : Φ) =
      ((law.attach 0 primitive.converter placed :
          DependentPDS.Prob testUniverse
            (replaceBoundary bitBoundary 0 primitive.target)) : Φ) :=
  protocolOfPrimitive_smul_coe_prob primitive placed law

/-- **Boundary alignment.**  Inside one fibre the carrier distance is the
contextual distance of the two laws. -/
example (left right : Λ) :
    edist (left : Φ) (right : Φ) =
      DependentPDS.contextualEDist left.val right.val :=
  edist_coe_prob left right

/-- **The `ℝ`/`ℝ≥0∞` boundary**, in the sound direction only. -/
example (left right : Λ) :
    edist (left : Φ) (right : Φ) ≤
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) :=
  edist_coe_prob_le_advantage left right

/-! ### `rs_availability`: MauRen11 Definition 3's two clauses

The command performs the one inference and leaves exactly the two reasons the
sentence names, in that order. -/

example (protocol filter simulator : Π) (assumed idealResource : Φ)
    (idle : simulator • assumed = assumed)
    (commuting : ∀ resource : Φ,
      protocol • (filter • resource) = filter • (protocol • resource))
    (security : protocol • assumed = simulator • idealResource) :
    protocol • ((filter * simulator) • assumed) =
      (filter * simulator) • idealResource := by
  rs_availability using security
  · exact idle
  · exact commuting

/-! ### `rs_commute`: the honest/adversary commutation premise -/

example (Z : Set Interface) (simulators : Submonoid Π)
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    (protocol simulator : Π) (member : simulator ∈ simulators) :
    Commute (protocol ⇂ Zᶜ) simulator := by
  rs_commute using admitted, member

/-! ### `rs_simulator`: the LiuMau20 specification-form leaf

The simulator is named by the caller and its admission into the joint
dishonest class is discharged; the behavioral leg stays visible.  This is
`Symmetric.OTP.otp_constructs_for_adversary_structure`'s second leg, with the
model removed. -/

example (protocol simulator : Π) (R S : Φ)
    (member :
      simulator ∈ supportedOn ({0} : Set Interface) (fun _ => ⊤))
    (leaf : protocol • R = simulator • S) :
    ∃ σ ∈ zSub (M := Π) tupleGamma ({0} : Set Interface),
      protocol • R = σ • S := by
  rs_simulator simulator using member
  exact leaf

/-- The `ε`-close variant, which the statistical endpoints need. -/
example (protocol simulator : Π) (R S : Φ) (ε : ℝ≥0∞)
    (member :
      simulator ∈ supportedOn ({0} : Set Interface) (fun _ => ⊤))
    (leaf : edist (protocol • R) (simulator • S) ≤ ε) :
    ∃ σ ∈ zSub (M := Π) tupleGamma ({0} : Set Interface),
      edist (protocol • R) (σ • S) ≤ ε := by
  rs_simulator simulator using member
  exact leaf

/-! ### `rs_compose`: MauRen11 Theorem 1(i) on fixed-`Z` judgments -/

example (Z : Set Interface) (simulators : Submonoid Π)
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    (protocol protocol' bottom : Π) (ε ε' : ℝ≥0∞) (R S T : Φ)
    (firstStage : CC.SecurelyConstructs Z simulators protocol bottom ε R S)
    (secondStage : CC.SecurelyConstructs Z simulators protocol' bottom ε' S T) :
    CC.SecurelyConstructs Z simulators (protocol' * protocol) bottom
      (ε + ε') R T := by
  rs_compose firstStage, secondStage using admitted

/-! ### `rs_triangle`: a hybrid step on a construction goal

`ac_triangle` alone does not fire here — the goal is a construction judgment,
not a distance — so the wrapper's reduction is the whole of its content. -/

example (π : Π) (R S intermediate : Φ) (ε ε' : ℝ≥0∞)
    (firstLeg : edist (π • R) intermediate ≤ ε)
    (secondLeg : edist intermediate S ≤ ε') :
    ⟪R⟫ —[π; ε + ε']→ ⟪S⟫ := by
  rs_triangle via intermediate
  · exact firstLeg
  · exact secondLeg

/-! ### `rs_nonexpand`: both action forms -/

/-- The protocol tuple, through AC's own `edist_smul_le`. -/
example (π : Π) (R S : Φ) : edist (π • R) (π • S) ≤ edist R S := by
  rs_nonexpand

/-- The bare local converter, which AC's command cannot see: there is no
`IsNonexpandingSMul (Primitive …) (Phi …)` instance and no reason for one. -/
example (primitive : Primitive Interface testUniverse 0) (R S : Φ) :
    edist (primitive • R) (primitive • S) ≤ edist R S := by
  rs_nonexpand

/-! ### The AC assemblers that already fire unchanged

These are the receipts behind the "not wrapped" entries of the file header:
the command needs no carrier-specific leaf, so no wrapper exists. -/

/-- `ac_construct` reduces an exact construction on this carrier. -/
example (π : Π) (R S : Φ) (coupling : π • R = S) : ⟪R⟫ —[π]→ ⟪S⟫ := by
  ac_construct using coupling

/-- `ac_transport using` replaces a protocol label with no wrapper. -/
example (π π' : Π) (ε : ℝ≥0∞) (R S : Set Φ) (same : π = π') :
    (R —[π; ε]→ S) ↔ R —[π'; ε]→ S := by
  ac_transport using same

/-- `ac_routine` closes carrier-free bookkeeping. -/
example (π : Π) (R : Φ) : (1 : Π) • (π • R) = π • R := by
  ac_routine

/-! ### Controlled-language sentences

One compiled instance of each `rs.construction.*` sentence, on the same goal
shapes.  This is the grammar gate: it pins that each sentence parses in the
presence of every other sentence of this module *and* of
`AbstractCrypto.ControlledNaturalLanguage`, and that it lowers to the backend
the docstring advertises. -/

section Sentences

example (π : Π) (assumed idealResource : Φ) (applied idealLaw : Λ) (ε : ℝ)
    (normalized : π • assumed = (applied : Φ))
    (target : idealResource = (idealLaw : Φ))
    (advantageBound :
      Δ(DependentPDS.flatten applied.val, DependentPDS.flatten idealLaw.val) ≤
        ε) :
    ⟪assumed⟫ —[π; ENNReal.ofReal ε]→ ⟪idealResource⟫ := by
  It remains to bound the distinguishing advantage, by normalized and target
  exact advantageBound

example (π : Π) (R S : Φ) (ε : ℝ≥0∞) (coupling : π • R = S) :
    ⟪R⟫ —[π; ε]→ ⟪S⟫ := by
  The perfect construction follows from the coupling coupling

example (protocol filter simulator : Π) (assumed idealResource : Φ)
    (idle : simulator • assumed = assumed)
    (commuting : ∀ resource : Φ,
      protocol • (filter • resource) = filter • (protocol • resource))
    (security : protocol • assumed = simulator • idealResource) :
    protocol • ((filter * simulator) • assumed) =
      (filter * simulator) • idealResource := by
  The availability condition follows from security, since the simulator is
    idle and the honest protocol commutes with the availability filter
  · exact idle
  · exact commuting

example (Z : Set Interface) (simulators : Submonoid Π)
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    (protocol simulator : Π) (member : simulator ∈ simulators) :
    Commute (protocol ⇂ Zᶜ) simulator := by
  We obtain the commutation of the honest protocol with every admitted
    simulator, by admitted and member

example (Z : Set Interface) (simulators : Submonoid Π)
    (admitted : simulators ≤ supportedOn Z (fun _ => ⊤))
    (protocol protocol' bottom : Π) (ε ε' : ℝ≥0∞) (R S T : Φ)
    (firstStage : CC.SecurelyConstructs Z simulators protocol bottom ε R S)
    (secondStage : CC.SecurelyConstructs Z simulators protocol' bottom ε' S T) :
    CC.SecurelyConstructs Z simulators (protocol' * protocol) bottom
      (ε + ε') R T := by
  The composition of firstStage and secondStage is secure, by admitted

example (protocol simulator : Π) (R S : Φ)
    (member :
      simulator ∈ supportedOn ({0} : Set Interface) (fun _ => ⊤))
    (leaf : protocol • R = simulator • S) :
    ∃ σ ∈ zSub (M := Π) tupleGamma ({0} : Set Interface),
      protocol • R = σ • S := by
  We use simulator to prove the security condition, by member
  exact leaf

/-- An annotated citation still elaborates, and the annotation is ignored —
the same contract as the AC sentences. -/
example (π : Π) (R S : Φ) (ε : ℝ≥0∞) (coupling : π • R = S) :
    ⟪R⟫ —[π; ε]→ ⟪S⟫ := by
  The perfect construction follows from the coupling
    coupling ("the two sample spaces are in bijection")

-- **Negative receipt.**  A near-miss wording is a controlled-language error
-- naming the expected word, not a silent reinterpretation.
/--
error: expected `coupling` in this controlled-language sentence
-/
#guard_msgs in
example (π : Π) (R S : Φ) (ε : ℝ≥0∞) (coupling : π • R = S) :
    ⟪R⟫ —[π; ε]→ ⟪S⟫ := by
  The perfect construction follows from the bijection coupling

end Sentences

/-! ### Token-trap receipts

The two atoms this layer adds are `availability` and `composition`.  Every
other content word stays an ordinary identifier, and these binders are the
compiled proof of it — a regression to string atoms breaks this file, not
`Symmetric/OTP.lean`. -/

example (construction simulator protocol honest filter advantage coupling
    distinguishing secure admitted commutes idle : Nat) : Nat :=
  construction + simulator + protocol + honest + filter + advantage +
    coupling + distinguishing + secure + admitted + commutes + idle

/-- An AC sentence of the parent language still parses with this module's two
atoms installed, and is not shadowed by the `perfect` variant added here.

Not every AC sentence does, and that is **not** caused by this module.
`AbstractCrypto.ControlledNaturalLanguage` parses the article `the` as an
`ident` (`cnlReplaceProtocol`, `cnlUseSimulator`, `cnlParallelContext`), while
`RandomSystemsCC.ControlledNaturalLanguage` has declared `the` a parser atom
since the Condition-C sentences landed; an atom always wins over `ident`, so
those three AC sentences cannot parse in any file that imports the RS
controlled language.  The same pre-existing collision covers `a`, `is`, `in`,
`of`, `to`, `at`, `on`, `no`, `one`, `most`, `least`, `it`, `this`, `real`,
`ideal`, `bound`, `event`, `game`, `ratio`, `defect`, `probability`, `good`,
`bad`, `equal` and `world(s)`, none of which can be a Lean identifier
downstream of that import.  Repairing it is an AC-side change (atomize the
articles there too) and is deliberately out of scope here; this receipt
records the measurement. -/
example (π : Π) (R S : Φ) (coupling : π • R = S) : ⟪R⟫ —[π]→ ⟪S⟫ := by
  The construction follows from coupling

end RandomSystemsCC.TypedConstructChecks
