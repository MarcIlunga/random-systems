/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Shared-state resources with typed interfaces

This module is the native operational typed boundary for the finite-interface
random-systems instantiation of Abstract Cryptography.  It deliberately has no
dependency on Abstract Crypto and makes no observational-equivalence choice.

A boundary assigns a signature code to every interface.  Queries form the
dependent sum of the corresponding input alphabets.  A deterministic resource
sees the complete interleaved query history, so its state may be shared across
interfaces, but its answer type is indexed by the interface of the active
query.  `DependentDDS.flatten` crosses once into the existing fixed-alphabet
`PFunDDS` engine by tagging each answer with that active interface.

This is not the common-output simplification and not the memoryless localized
converter experiment.  The downstream attachment operation accepts arbitrary
deterministic typed protocol functions carrying `IsDDC`; contextual behavior
and the metric are installed only after attachment has been defined.
-/

namespace RandomSystems.CR18

namespace TypedResource

universe c i u v

/-- A controlled universe of interface signatures.  Codes are data; their
input and output alphabets may be different Lean types. -/
structure SignatureUniverse where
  Code : Type c
  input : Code → Type u
  output : Code → Type v

/-- The **one-code-per-interface** universe: a resource that owns its universe
needs no code layer at all, and the author declares only the per-interface
input and output alphabets.  `Code := I`, and the boundary is the identity
(`Boundary.ofInterfaces`).

Scope, stated precisely because the opposite case is the one in this tree:
this applies exactly when a universe hosts **one** world.  It is *not* usable
when several worlds must live at the same interfaces — there the code is
precisely what keeps the real and ideal resources at incomparable signatures
(`Resource.boundaryEDist` is `⊤` across distinct codes) and the boundary is
the world selector.  Every `SignatureUniverse` currently instantiated under
`RandomSystemsCC/Symmetric/` is of that second kind: e.g.
`RandomSystemsCC.Symmetric.MACThenOTPModel.signatures` carries ten codes over
three interfaces and four different boundaries over the one universe. -/
def SignatureUniverse.ofInterfaces {I : Type c}
    (input : I → Type u) (output : I → Type v) : SignatureUniverse.{c, u, v} where
  Code := I
  input := input
  output := output

instance SignatureUniverse.decidableEqOfInterfacesCode {I : Type c}
    [DecidableEq I] (input : I → Type u) (output : I → Type v) :
    DecidableEq (SignatureUniverse.ofInterfaces input output).Code :=
  inferInstanceAs (DecidableEq I)

/-- `⊕`-closure of a signature universe: a sum code for every pair of
codes, whose alphabets are the tagged sums of the components' (parallel
composition sends `(X, Y)` and `(X', Y')` to `(X ⊕ X', Y ⊕ Y')`).
`sumCode` is injective: the class describes a genuine sum-like structure
— e.g. a free code constructor — not an arbitrary pairing, and the
injectivity is what makes the parallel decomposition of a code
well-defined for the converter-side parallel action. -/
class HasSumCode (U : SignatureUniverse.{c, u, v}) where
  sumCode : U.Code → U.Code → U.Code
  /-- Queries at a sum code re-associate as a tagged sum of the components'
  queries.  This is an **equivalence, not a type equality**: the two consumers
  (`queryEquiv`, `answerEquiv`) immediately did `Equiv.cast` on the old equality
  field, so equality was strictly more than the class ever used — and demanding
  it excluded signatures whose alphabets distribute only up to isomorphism.
  `withEvents` is exactly such a signature: `(X ⊕ Y) × ℰ` and
  `(X × ℰ) ⊕ (Y × ℰ)` are `Equiv.sumProdDistrib`-equivalent but not equal, so
  under the old field the whole event carrier had no parallel composition. -/
  inputEquiv : ∀ a b, U.input (sumCode a b) ≃ (U.input a ⊕ U.input b)
  /-- Answers at a sum code, re-associated the same way.  See `inputEquiv`. -/
  outputEquiv : ∀ a b, U.output (sumCode a b) ≃ (U.output a ⊕ U.output b)
  sumCode_inj : ∀ {a b a' b' : U.Code},
    sumCode a b = sumCode a' b' → a = a' ∧ b = b'

/-- One signature code at each resource interface. -/
abbrev Boundary (U : SignatureUniverse) (I : Type i) := I → U.Code

/-- The identity boundary of `SignatureUniverse.ofInterfaces`: interface `i`
carries code `i`.  Together with `SignatureUniverse.ofInterfaces` this is the
whole signature declaration for a single-world resource — there is no code
inductive to name and no interface-to-code map to get wrong. -/
abbrev Boundary.ofInterfaces {I : Type c}
    (input : I → Type u) (output : I → Type v) :
    Boundary (SignatureUniverse.ofInterfaces input output) I :=
  fun interface => interface

/-- The global query alphabet at a boundary, retaining the owning interface. -/
abbrev Query {I : Type i} (U : SignatureUniverse) (sigma : Boundary U I) :=
  Σ interface, U.input (sigma interface)

/-- The flattened global answer alphabet.  The native resource below returns
only an answer in the fibre selected by the active query; this sigma is used
only at the boundary to the existing fixed-alphabet engine. -/
abbrev FlatAnswer {I : Type i} (U : SignatureUniverse)
    (sigma : Boundary U I) :=
  Σ interface, U.output (sigma interface)

/-- The answer fibre selected by a particular global query. -/
abbrev AnswerAt {I : Type i} {U : SignatureUniverse}
    {sigma : Boundary U I} (query : Query U sigma) :=
  U.output (sigma query.1)

/-- A partial deterministic resource with a single shared query history and a
dependent answer fibre.  The explicit nonempty proof makes the output type
refer to the last (active) query without assigning a dummy answer type to the
empty history. -/
structure DependentDDS {I : Type i} (U : SignatureUniverse)
    (sigma : Boundary U I) where
  domain : Set (List (Query U sigma))
  empty_not_mem : [] ∉ domain
  prefix_closed : ∀ {left right : List (Query U sigma)},
    left <+: right → left ≠ [] → right ∈ domain → left ∈ domain
  output : (history : List (Query U sigma)) →
    (nonempty : history ≠ []) → history ∈ domain →
      AnswerAt (history.getLast nonempty)

namespace DependentDDS

variable {I : Type i} {U : SignatureUniverse} {sigma : Boundary U I}

/-- Membership in the native dependent resource domain. -/
abbrev dom (system : DependentDDS U sigma) : Set (List (Query U sigma)) :=
  system.domain

/-- A domain member is necessarily a nonempty history. -/
theorem history_ne_nil (system : DependentDDS U sigma)
    {history : List (Query U sigma)} (member : history ∈ system.domain) :
    history ≠ [] := by
  intro empty
  subst empty
  exact system.empty_not_mem member

/-- Evaluate a dependent resource on an admitted history. -/
def answer (system : DependentDDS U sigma)
    (history : List (Query U sigma)) (member : history ∈ system.domain) :
    AnswerAt (history.getLast (history_ne_nil system member)) :=
  system.output history (history_ne_nil system member) member

/-- The answer does not depend on the proofs used to establish nonemptiness or
domain membership. -/
theorem output_proof_irrel (system : DependentDDS U sigma)
    (history : List (Query U sigma))
    (nonempty₁ nonempty₂ : history ≠ [])
    (member₁ member₂ : history ∈ system.domain) :
    system.output history nonempty₁ member₁ =
      system.output history nonempty₂ member₂ := by
  rfl

/-! ### Scheduling: can a resource constrain the *order* of activation?

`DependentDDS` carries a prefix-closed `domain`, so a resource **can** refuse a
query and thereby forbid an interleaving.  That is the only mechanism by which
this model could bake in a scheduling assumption, and it is worth naming,
because a resource that used it to deny a *rushing* adversary — one who reads
before the honest parties act — would make every security statement about it
weaker than it looks: the distinguisher would be denied a legitimate attack and
the quantifier would range over too small a set.

A resource is **schedule-agnostic** when domain membership depends only on
*which* queries have been asked, never on the order in which they were
interleaved.  Such a resource may still constrain multiplicity — "Alice may
submit at most once", the one-time-pad restriction — but never scheduling, so
no interleaving is excluded that some other ordering of the same queries
admits.

This is the model-side counterpart of LiuMau20's semi-round split.  Its Def 4
resource consumes a *complete input list* per invocation and thereby silently
forbids rushing (p. 12: "any (dishonest) party's input depends solely on the
previous outputs seen by the party.  In practice this assumption is often not
justified"); the r.a/r.b split of Fig. 4 is its remedy.  Our resources answer
one query at a time over a single interleaved history, so there is no round in
which an input could be withheld — provided the domains are schedule-agnostic,
which `rushing_not_excluded` turns from an argument into an obligation. -/
def ScheduleAgnostic (system : DependentDDS U sigma) : Prop :=
  ∀ {left right : List (Query U sigma)}, left.Perm right →
    (left ∈ system.domain ↔ right ∈ system.domain)

/-- The shape every live domain actually has: a nonemptiness clause conjoined
with a predicate that only counts queries. -/
theorem scheduleAgnostic_of_perm_invariant {system : DependentDDS U sigma}
    (predicate : List (Query U sigma) → Prop)
    (domain_eq : system.domain = {history | history ≠ [] ∧ predicate history})
    (invariant : ∀ {left right : List (Query U sigma)}, left.Perm right →
      (predicate left ↔ predicate right)) :
    ScheduleAgnostic system := by
  intro left right perm
  simp only [domain_eq, Set.mem_setOf_eq]
  refine and_congr (not_congr ?_) (invariant perm)
  have hlen : left.length = right.length := perm.length_eq
  constructor
  · rintro rfl; exact List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
  · rintro rfl; exact List.eq_nil_of_length_eq_zero (by simpa using hlen)

/-- A resource that admits every nonempty history constrains nothing at all,
scheduling included. -/
theorem scheduleAgnostic_of_total {system : DependentDDS U sigma}
    (total : system.domain = {history | history ≠ []}) :
    ScheduleAgnostic system :=
  scheduleAgnostic_of_perm_invariant (fun _ => True)
    (by simp [total]) (fun _ => Iff.rfl)

/-- **Rushing is not excluded.**  On a schedule-agnostic resource, whenever the
honest parties' queries followed by the adversary's are admitted, so are the
adversary's followed by the honest parties'.  The adversary may therefore act
*first* on the same multiset of queries — precisely the capability LiuMau20's
Def 4 resource silently denies and recovers only through its semi-round split.

The converse direction is `rushing_not_excluded` applied to the symmetric
permutation, so admission is genuinely order-blind rather than merely
one-directionally permissive. -/
theorem rushing_not_excluded {system : DependentDDS U sigma}
    (agnostic : ScheduleAgnostic system)
    (honest adversarial : List (Query U sigma))
    (member : (honest ++ adversarial) ∈ system.domain) :
    (adversarial ++ honest) ∈ system.domain :=
  (agnostic List.perm_append_comm).mp member

/-- Flatten a native typed resource into the established PFun DDS carrier.
The answer is tagged by the active query's interface, so incoherent output
tags are unrepresentable in the image. -/
def flatten (system : DependentDDS U sigma) :
    PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma) :=
  ⟨(fun history =>
      (⟨history ∈ system.domain, fun member =>
        let nonempty := history_ne_nil system member
        let query := history.getLast nonempty
        ⟨query.1, system.output history nonempty member⟩⟩ :
        Part (FlatAnswer U sigma))),
    ⟨system.empty_not_mem, fun hprefix nonempty member =>
      system.prefix_closed hprefix nonempty member⟩⟩

@[simp]
theorem flatten_dom (system : DependentDDS U sigma) :
    PFunDDS.dom system.flatten = system.domain :=
  rfl

/-- Evaluating the flattening on an admitted history is the tagged native
answer, with the active interface read off the history's last query.  Keeping
this equation at the dependent boundary spares converter receipts the descent
through proof-dependent `Part.get` terms. -/
theorem flatten_apply_eq_some (system : DependentDDS U sigma)
    (history : List (Query U sigma)) (member : history ∈ system.domain) :
    system.flatten.1 history =
      Part.some
        ⟨(history.getLast (history_ne_nil system member)).1,
          system.output history (history_ne_nil system member) member⟩ := by
  have rawMember : (system.flatten.1 history).Dom := member
  rw [← Part.some_get rawMember]
  congr

/-- A flat DDS is tag-faithful when every defined answer is tagged by the
interface of the active query. -/
def TagFaithful (system :
    PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma)) : Prop :=
  ∀ (history : List (Query U sigma))
    (member : history ∈ PFunDDS.dom system),
      (PFunDDS.output system history member).1 =
        (history.getLast (by
          intro empty
          subst empty
          exact PFunDDS.empty_not_mem system member)).1

/-- Flattening a dependent resource always produces a tag-faithful flat DDS. -/
theorem flatten_tag_faithful (system : DependentDDS U sigma) :
    TagFaithful system.flatten := by
  intro history member
  rfl

/-- Rebuilding a sigma pair at an equal first component recovers the original
pair.  This is the transport step used by the inverse flattening. -/
private theorem sigma_mk_cast_snd
    {family : I → Type v} {pair : Σ interface, family interface}
    {interface : I} (same : pair.1 = interface) :
    (⟨interface, Eq.mp (congrArg family same) pair.2⟩ :
      Σ interface, family interface) = pair := by
  obtain ⟨actual, value⟩ := pair
  subst same
  rfl

/-- Recover a native dependent resource from a tag-faithful flat DDS. -/
def unflatten (system :
    PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma))
    (faithful : TagFaithful system) : DependentDDS U sigma where
  domain := PFunDDS.dom system
  empty_not_mem := PFunDDS.empty_not_mem system
  prefix_closed := fun hprefix nonempty member =>
    PFunDDS.prefix_closed system hprefix nonempty member
  output := fun history _nonempty member =>
    let answer := PFunDDS.output system history member
    Eq.mp
      (congrArg (fun interface => U.output (sigma interface))
        (faithful history member))
      answer.2

/-- Flattening the native resource recovered from a tag-faithful flat DDS is
the original DDS. -/
theorem flatten_unflatten
    (system : PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma))
    (faithful : TagFaithful system) :
    flatten (unflatten system faithful) = system := by
  apply Subtype.ext
  funext history
  apply Part.ext'
  · rfl
  · intro left right
    change
      (⟨(history.getLast (history_ne_nil (unflatten system faithful) left)).1,
          _⟩ : FlatAnswer U sigma) =
        PFunDDS.output system history right
    simpa only [unflatten] using
      sigma_mk_cast_snd (faithful history right)

/-- The image of native flattening is exactly the tag-faithful flat systems. -/
theorem exists_flatten_eq_iff_tag_faithful
    (system : PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma)) :
    (∃ native : DependentDDS U sigma, flatten native = system) ↔
      TagFaithful system := by
  constructor
  · rintro ⟨native, rfl⟩
    exact flatten_tag_faithful native
  · intro faithful
    exact ⟨unflatten system faithful, flatten_unflatten system faithful⟩

/-- Native dependent resources are faithfully represented by their flat,
tag-faithful presentations.  The proof packages the tag-faithfulness witness
with the flat system before applying `unflatten`, so proof transport never
becomes part of the public equality. -/
theorem flatten_injective : Function.Injective
    (flatten : DependentDDS U sigma →
      PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma)) := by
  intro left right same
  let unflattenBundle :
      {system : PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma) //
        TagFaithful system} → DependentDDS U sigma :=
    fun system => unflatten system.val system.property
  have bundleSame :
      (⟨left.flatten, left.flatten_tag_faithful⟩ :
        {system : PFunDDS.DDS (Query U sigma) (FlatAnswer U sigma) //
          TagFaithful system}) =
      ⟨right.flatten, right.flatten_tag_faithful⟩ :=
    Subtype.ext same
  calc
    left = unflattenBundle ⟨left.flatten, left.flatten_tag_faithful⟩ := by
      rfl
    _ = unflattenBundle ⟨right.flatten, right.flatten_tag_faithful⟩ :=
      congrArg unflattenBundle bundleSame
    _ = right := by rfl

/-- A native history evaluator.  It is fully defined on every nonempty global
history but may base its answer on the entire interleaving of interfaces. -/
def historyEvaluator
    (evaluate : (history : List (Query U sigma)) →
      (nonempty : history ≠ []) → AnswerAt (history.getLast nonempty)) :
    DependentDDS U sigma where
  domain := {history | history ≠ []}
  empty_not_mem := by simp
  prefix_closed := by
    intro left _ _ nonempty _
    exact nonempty
  output := fun history nonempty _ => evaluate history nonempty

@[simp]
theorem history_evaluator_domain
    (evaluate : (history : List (Query U sigma)) →
      (nonempty : history ≠ []) → AnswerAt (history.getLast nonempty)) :
    (historyEvaluator evaluate).domain = {history | history ≠ []} :=
  rfl

/-- A memoryless dependent oracle is only a constructor/example; it is not the
converter class used by the AC instance. -/
def functionEvaluator
    (evaluate : (query : Query U sigma) → AnswerAt query) :
    DependentDDS U sigma :=
  historyEvaluator fun history nonempty =>
    evaluate (history.getLast nonempty)

/-- Flattening the dependent history evaluator agrees with the ordinary flat
history evaluator after tagging the result with the active interface. -/
theorem flatten_history_evaluator
    (evaluate : (history : List (Query U sigma)) →
      (nonempty : history ≠ []) → AnswerAt (history.getLast nonempty)) :
    flatten (historyEvaluator evaluate) =
      PFunDDS.historyEvaluator (fun history nonempty =>
        let query := history.getLast nonempty
        ⟨query.1, evaluate history nonempty⟩) := by
  apply Subtype.ext
  funext history
  apply Part.ext'
  · rfl
  · intro left right
    rfl

end DependentDDS

/-! ## Probability laws and the one-time flat boundary -/

open RandomSystems (Dist)

/-- A finite-support law over native shared-state dependent resources. -/
abbrev DependentPDS {I : Type i} (U : SignatureUniverse)
    (sigma : Boundary U I) :=
  Dist (DependentDDS U sigma)

namespace DependentPDS

variable {I : Type i} {U : SignatureUniverse} {sigma : Boundary U I}

/-- Push a native dependent law through the tag-faithful flattening into the
existing fixed-alphabet PDS engine. -/
noncomputable def flatten (system : DependentPDS U sigma) :
    PFunPDS (Query U sigma) (FlatAnswer U sigma) :=
  Dist.fTransform DependentDDS.flatten system

/-- Flattening preserves total mass. -/
@[simp]
theorem flatten_weight (system : DependentPDS U sigma) :
    (flatten system).weight = system.weight :=
  Dist.weight_fTransform DependentDDS.flatten system

/-- Probability normalization is preserved and reflected by flattening.

Over the signed carrier `isProbDist` is `NonNeg ∧ weight = 1`, so the
weight equation alone no longer settles it: the reflection direction needs
non-negativity back, and it comes from the tag-faithful injectivity of
`DependentDDS.flatten` — an injective pushforward cannot merge cancelling
signed masses (`Dist.isProbDist_fTransform_of_injective`). -/
@[simp]
theorem flatten_is_probability_distribution_iff
    (system : DependentPDS U sigma) :
    (flatten system).isProbDist ↔ system.isProbDist :=
  Dist.isProbDist_fTransform_of_injective DependentDDS.flatten_injective system

/-- A normalized native dependent PDS. -/
abbrev Prob (U : SignatureUniverse) (sigma : Boundary U I) :=
  {system : DependentPDS U sigma // system.isProbDist}

/-- Flatten a normalized native law to a normalized law in the existing PDS
engine. -/
noncomputable def Prob.flatten (system : Prob U sigma) :
    PFunPDS.Prob (Query U sigma) (FlatAnswer U sigma) :=
  ⟨DependentPDS.flatten system.val,
    (flatten_is_probability_distribution_iff system.val).2 system.property⟩

@[simp]
theorem prob_flatten_coe (system : Prob U sigma) :
    system.flatten.val = DependentPDS.flatten system.val :=
  rfl

end DependentPDS

end TypedResource

end RandomSystems.CR18
