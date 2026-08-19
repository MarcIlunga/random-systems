/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceCarrier
import RandomSystemsCC.TypedFinite

/-!
# The authoring surface, part 5: Definition 1 completed

Maurer's Definition 1 (Maurer11 p. 44–45) and its refinements ask for more
than attachment: the converter set `Σ` is closed under **serial
composition** with a **neutral converter** (`id`, MauRen16 §3.3:
`id ∘ α = α ∘ id = α`), there is a **blocking converter** (MaRuTa12
Def. 2's `⊥`, MauRen16 §3.4's `⊣`), security is the **two-condition**
simulator/availability pair (MaRuTa12 Def. 2), and protocols are tuples of
converter–interface pairs applied in one stroke (JosMau20 §2.1, whose
Prop. 1 is composition-order independence).  This module completes the
bundled carrier of part 4 to that surface.

`Σ` is realized by the kernel's **syntactic converter monoid** (the
paper's `Γ`, `RandomSystemsCC/TypedFinite.lean`): words over converters
modulo the monoid laws only.  That choice makes Definition 1 *citable*
rather than re-proven — the neutral law is `one_smul`, the serial law
`(αβ)^i R = α^i (β^i R)` is `mul_smul`, and distinct-interface commutation
is the kernel's `gamma_commute` — and it is faithful: MauRen16's `Σ` is a
set of programs closed under `∘`, never a quotient by behavior.

Layering note: this module imports `RandomSystemsCC.TypedFinite` (the
AC-facing instance) from the `RandomSystems` surface — the one place the
Jost folder reaches upward.  The alternative was re-proving the monoid
action; reuse won.

**Delivered elsewhere, in Jost's form — parallel of converters.**
MaRuTa12 §2.1's `(ψ‖φ)^I (R‖S) = ψ^I R ‖ φ^I S` was scoped here as an
obligation while `∥` merged interfaces: it then needed a composite
converter and the padded analogue of
`RandomSystemParallel.Prob.apply_parallel_eq_parallel_apply` through a sum
re-coding.  At DISJOINT interface sets no composite converter is needed —
a converter attached at `Sum.inl i` reaches only the left component — and
the statement is Jost's Prop. 2.2.3 (2),
`Converter.attachAt_par_left : α •[Sum.inl i] (R ∥ Q) = (α •[i] R) ∥ Q`,
proved total and coding-free in `Jost/SurfaceCarrier.lean`.  Its
construction-level corollary is Jost Thm 2.2.5 (2),
`Converter.close_par_attachAt_left`.

**The `⊥` laws, and why they cost almost nothing.**  `⊣` is *not* an
element of `Σ`: the papers' `⊥` is one service-agnostic converter, whereas
on the typed carrier `block` is the family `Converter.bot service`, indexed
by the service the interface currently provides, applied at its
always-matching member.  So idempotence, commutation of two blocks and
non-expansion cannot be `one_smul`/`gamma_commute`/`close_smul`.  They are
proved here instead — and the route is cheaper than the module previously
scoped it to be:

* the second block of `block_idem` attaches `Converter.bot` *out of the
  blocked service*, whose outer alphabet is empty, and a memoryless
  converter with an empty outer alphabet is not merely unobservable, it is
  literally `ofMaps id id` — its round function is nowhere defined
  (`Converter.ofMaps_eq_of_no_input`, `SurfaceCarrier.lean`).  So
  `block_idem` reduces to `Converter.attachAt_id`; no "attachment at an
  unqueryable interface is a behavioral identity" is needed;
* `block_comm` is `Converter.attachAt_comm` once `block_eq_attachAt` has
  named each `⊣`'s member of the family, which `layoutAt_block_of_ne`
  licenses;
* `close_block` is `close_attachAt` with **no** layout-agreement
  hypothesis: `R ≈[ε] Q` already forces `R` and `Q` to provide the same
  service at every interface (`layoutAt_eq_of_close`), so they are blocked
  by the same member of the family.

Even a genuinely service-agnostic `⊥` would not shorten this.  `Γ` is the
*free* monoid on primitives modulo the monoid laws only, so `w * w = w`
never holds in it; idempotence would still be an action-level fact.  And
the only way to make one word block every layout is to enumerate the
services, i.e. to demand `Fintype S.Service`, which `Services` does not
carry.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped Converter ResourceSystem

/-! ## Σ: converters closed under serial composition, with identity -/

/-- **The converter set `Σ` at an interface** (MauRen16 §3.3): converters
closed under serial composition, containing the identity — the kernel's
syntactic converter monoid.  `1` is MauRen16's `id`; `*` is `∘` in the
paper order (`(α * β) • R = α • (β • R)`, right factor first). -/
@[cc_surface]
abbrev Converters (S : Services) (I : Type) [DecidableEq I] (interface : I) :=
  Gamma I S.sig interface

namespace Converters

variable {S : Services} {I : Type} [DecidableEq I]

/-- A converter word acts on resource systems. -/
noncomputable instance instSMul {interface : I} :
    SMul (Converters S I interface) (ResourceSystem S I) :=
  ⟨fun converter resource => converter.val.val resource⟩

theorem smul_def {interface : I} (converter : Converters S I interface)
    (resource : ResourceSystem S I) :
    converter • resource = converter.val.val resource :=
  rfl

/-- Definition 1 (ii) and MauRen16 §3.3 in one instance: `Σ` acts, `id`
acts trivially, serial composition acts serially. -/
noncomputable instance instMulAction {interface : I} :
    MulAction (Converters S I interface) (ResourceSystem S I) where
  one_smul _ := rfl
  mul_smul converter₁ converter₂ resource := by
    rw [smul_def, Gamma.val_mul]
    rfl

/-- MauRen16 §3.3: the identity converter uses the resource "as is". -/
@[cc_surface]
theorem id_smul {interface : I} (resource : ResourceSystem S I) :
    (1 : Converters S I interface) • resource = resource :=
  one_smul _ resource

/-- The serial law `(β ∘ α)^i R = β^i (α^i R)` (MauRen16 §3.3, MaRuTa12
§2.1) — the paper order, right factor first. -/
@[cc_surface]
theorem comp_smul {interface : I}
    (outer inner : Converters S I interface) (resource : ResourceSystem S I) :
    (outer * inner) • resource = outer • (inner • resource) :=
  mul_smul outer inner resource

/-- **Definition 1 (i) for `Σ`**: converters at distinct interfaces
commute, as a plain equality. -/
@[cc_surface]
theorem smul_comm_of_ne {interface₁ interface₂ : I}
    (different : interface₁ ≠ interface₂)
    (converter₁ : Converters S I interface₁)
    (converter₂ : Converters S I interface₂)
    (resource : ResourceSystem S I) :
    converter₁ • (converter₂ • resource) =
      converter₂ • (converter₁ • resource) := by
  have commute := gamma_commute different converter₁ converter₂
  calc converter₁ • (converter₂ • resource)
      = (converter₁.val * converter₂.val).val resource := rfl
    _ = (converter₂.val * converter₁.val).val resource := by rw [commute.eq]
    _ = converter₂ • (converter₁ • resource) := rfl

/-- Attachment never expands distance — eq. (4) for all of `Σ` (a word's
interpretation is a `1`-Lipschitz endomorphism by construction). -/
@[cc_surface]
theorem close_smul {interface : I} {epsilon : ℝ}
    (converter : Converters S I interface)
    {left right : ResourceSystem S I} (h : left ≈[epsilon] right) :
    (converter • left) ≈[epsilon] (converter • right) := by
  have nonexpanding : edist (converter • left) (converter • right) ≤
      edist left right := by
    simpa using converter.val.property left right
  exact le_trans nonexpanding h

/-- Off its interface, a converter changes no service: the layout at every
other interface survives attachment — the single-converter locality fact
(`ResourceSystem.layoutAt_attachAt_of_ne`) extended through the word
structure. -/
theorem layoutAt_smul_of_ne {interface other : I}
    (different : other ≠ interface)
    (converter : Converters S I interface) (resource : ResourceSystem S I) :
    (converter • resource).layoutAt other = resource.layoutAt other := by
  induction converter using Quotient.inductionOn with
  | _ word =>
      induction word generalizing resource with
      | prim primitive =>
          exact ResourceSystem.layoutAt_attachAt_of_ne different
            primitive.converter resource
      | one => rfl
      | mul left right leftIH rightIH =>
          show ((Gamma.mk left) • ((Gamma.mk right) • resource)).layoutAt
              other = resource.layoutAt other
          exact (leftIH _).trans (rightIH resource)

end Converters

namespace Converter

variable {S : Services} {I : Type} [DecidableEq I]

/-- A single converter, as an element of `Σ` at an interface.  Its action
IS the part-4 attachment (`word_smul`), so nothing is re-proved. -/
@[cc_surface]
noncomputable def word {source target : S.Service}
    (converter : Converter S source target) (interface : I) :
    Converters S I interface :=
  Gamma.ofPrimitive (Primitive.mk source target converter)

/-- The embedded converter acts as the part-4 total attachment. -/
@[cc_surface]
theorem word_smul {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    (resource : ResourceSystem S I) :
    converter.word interface • resource = converter •[interface] resource :=
  rfl

end Converter

/-! ## The blocking converter (MaRuTa12's `⊥`, MauRen16's `⊣`) -/

/-- A development with a **blocked service**: no input can be formed at it
(so a blocked interface cannot be queried), and its output alphabet is
inhabited (so converters into it exist). -/
class HasBlockedService (S : Services) where
  blocked : S.Service
  no_input : IsEmpty (S.In blocked)
  some_output : Inhabited (S.Out blocked)

namespace Converter

variable {S : Services} {I : Type} [DecidableEq I] [HasBlockedService S]

/-- The blocking converter out of any service: its outer interface carries
the blocked service, so no query ever reaches it. -/
@[cc_surface]
noncomputable def bot (source : S.Service) :
    Converter S source (HasBlockedService.blocked) :=
  Converter.ofMaps
    (fun query => (HasBlockedService.no_input.false query).elim)
    (fun _ => HasBlockedService.some_output.default)

end Converter

namespace ResourceSystem

variable {S : Services} {I : Type} [DecidableEq I]

section Block

variable [HasBlockedService S]

/-- **`⊣[i] R`** (MauRen16 §3.4's `⊣`, MaRuTa12 Def. 2's `⊥`): block
interface `i` — whatever service it provides, replace it by the blocked
one.  (The papers' `⊥` is one service-agnostic converter; on the typed
carrier it is this family, indexed by the service currently provided,
applied at its always-matching member.) -/
@[cc_surface]
noncomputable def block (interface : I) (resource : ResourceSystem S I) :
    ResourceSystem S I :=
  Converter.bot (resource.layoutAt interface) •[interface] resource

@[inherit_doc block]
scoped notation:73 "⊣[" i "] " R:73 => ResourceSystem.block i R

/-- **`⊣[i]` names its member of the `⊥` family**: on a resource that
provides `service` at `i`, blocking IS attachment of the blocking
converter out of `service`.  The one bookkeeping step every law below
needs — it turns the layout-dependent definition into an ordinary
attachment, at the cost of a `provides` equation. -/
@[cc_surface]
theorem block_eq_attachAt {service : S.Service} (interface : I)
    {resource : ResourceSystem S I}
    (provides : resource.layoutAt interface = service) :
    ⊣[interface] resource = Converter.bot service •[interface] resource := by
  subst provides
  rfl

/-- A blocked interface provides the blocked service. -/
@[cc_surface]
theorem layoutAt_block (interface : I) (resource : ResourceSystem S I) :
    (⊣[interface] resource).layoutAt interface =
      HasBlockedService.blocked :=
  layoutAt_attachAt _ interface rfl

/-- Blocking is local: it leaves every other interface's service alone. -/
@[cc_surface]
theorem layoutAt_block_of_ne {interface other : I}
    (different : other ≠ interface) (resource : ResourceSystem S I) :
    (⊣[interface] resource).layoutAt other = resource.layoutAt other :=
  layoutAt_attachAt_of_ne different _ resource

/-- **`⊥` is idempotent** (MaRuTa12 Def. 2, MauRen16 §3.4): blocking an
already-blocked interface does nothing.

Not a behavioural argument.  The second block is attachment of
`Converter.bot` *out of the blocked service*, whose outer alphabet is the
blocked service's — empty.  A memoryless converter with an empty outer
alphabet is literally `ofMaps id id` (`Converter.ofMaps_eq_of_no_input`),
and that converter is idle (`Converter.attachAt_id`).  So the equation
holds on the nose, with no appeal to "nothing can be observed at `i`". -/
@[cc_surface]
theorem block_idem (interface : I) (resource : ResourceSystem S I) :
    ⊣[interface] (⊣[interface] resource) = ⊣[interface] resource := by
  rw [block_eq_attachAt interface (layoutAt_block interface resource)]
  exact Converter.attachAt_of_no_input HasBlockedService.no_input _ _
    interface _

/-- **Blocks at distinct interfaces commute** — Definition 1 (i) for `⊣`.
Nothing new: once `block_eq_attachAt` has replaced each `⊣` by its own
member of the `⊥` family (legal because blocking at one interface does not
disturb the service at the other, `layoutAt_block_of_ne`), this is the
carrier's own order independence, `Converter.attachAt_comm`. -/
@[cc_surface]
theorem block_comm {interface₁ interface₂ : I}
    (different : interface₁ ≠ interface₂) (resource : ResourceSystem S I) :
    ⊣[interface₁] (⊣[interface₂] resource) =
      ⊣[interface₂] (⊣[interface₁] resource) := by
  rw [block_eq_attachAt interface₁ (layoutAt_block_of_ne different resource),
    block_eq_attachAt interface₂
      (layoutAt_block_of_ne (Ne.symm different) resource)]
  exact Converter.attachAt_comm different _ _ resource

/-- **The characteristic fact**: after blocking, no query exists at the
interface — the type-level reading of "the distinguisher has no access to
the blocked interface". -/
@[cc_surface]
theorem no_queries_at_block (interface : I) (resource : ResourceSystem S I) :
    IsEmpty (S.In ((⊣[interface] resource).layoutAt interface)) := by
  rw [layoutAt_block]
  exact HasBlockedService.no_input

/-- Blocking commutes with converters at other interfaces. -/
@[cc_surface]
theorem block_smul_of_ne {interfaceC interfaceB : I}
    (different : interfaceC ≠ interfaceB)
    (converter : Converters S I interfaceC) (resource : ResourceSystem S I) :
    ⊣[interfaceB] (converter • resource) =
      converter • (⊣[interfaceB] resource) := by
  unfold block
  rw [Converters.layoutAt_smul_of_ne (Ne.symm different) converter resource,
    ← Converter.word_smul, ← Converter.word_smul,
    Converters.smul_comm_of_ne (Ne.symm different)]

/-- **Blocking is non-expanding** — eq. (4) for `⊣`, and the step the
availability condition of MaRuTa12 Def. 2 needs.

No layout-agreement hypothesis: `block`'s converter does depend on the
resource's own service at `i`, so `R` and `Q` could in principle be
blocked by *different* members of the `⊥` family — but they cannot be, and
that is a theorem, not an assumption.  `R ≈[ε] Q` already forces the two
layouts to agree everywhere (`layoutAt_eq_of_close`; differing layouts are
at infinite distance), so one converter serves both and
`close_attachAt` applies. -/
@[cc_surface]
theorem close_block {epsilon : ℝ} (interface : I)
    {left right : ResourceSystem S I} (h : left ≈[epsilon] right) :
    (⊣[interface] left) ≈[epsilon] (⊣[interface] right) := by
  rw [block_eq_attachAt interface (layoutAt_eq_of_close h interface).symm]
  exact close_attachAt _ interface h

end Block

/-! ## Closeness bookkeeping for the composition theorem -/

/-- `≈[·]` is reflexive at radius zero. -/
@[cc_surface]
theorem close_refl (resource : ResourceSystem S I) : resource ≈[0] resource :=
  (close_zero_iff resource resource).mpr rfl

/-- The triangle inequality of `≈[·]` — the error accounting of every
composition theorem. -/
@[cc_surface]
theorem close_trans {epsilon₁ epsilon₂ : ℝ}
    (nonneg₁ : 0 ≤ epsilon₁) (nonneg₂ : 0 ≤ epsilon₂)
    {left middle right : ResourceSystem S I}
    (h₁ : left ≈[epsilon₁] middle) (h₂ : middle ≈[epsilon₂] right) :
    left ≈[epsilon₁ + epsilon₂] right := by
  show edist left right ≤ ENNReal.ofReal (epsilon₁ + epsilon₂)
  calc edist left right
      ≤ edist left middle + edist middle right := edist_triangle ..
    _ ≤ ENNReal.ofReal epsilon₁ + ENNReal.ofReal epsilon₂ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (epsilon₁ + epsilon₂) :=
        (ENNReal.ofReal_add nonneg₁ nonneg₂).symm

end ResourceSystem

/-! ## The two-condition secure construction (MaRuTa12 Def. 2) -/

section Constructs

variable {S : Services} {I : Type} [DecidableEq I] [HasBlockedService S]

open ResourceSystem

/-- **Secure construction, MaRuTa12 Definition 2**: the protocol
`(π₁, π₂)` (converters for the two honest interfaces) constructs `ideal`
from `assumed` within `ε`, with respect to adversarial interface `iE`, if
(security) some simulator `σ` at `iE` makes the real and ideal systems
`ε`-close, and (availability) with the adversarial interface blocked on
both sides they are `ε`-close outright. -/
@[cc_surface]
structure Constructs (iA iB iE : I)
    (pi₁ : Converters S I iA) (pi₂ : Converters S I iB)
    (assumed ideal : ResourceSystem S I) (epsilon : ℝ) : Prop where
  security : ∃ sim : Converters S I iE,
    (pi₁ • pi₂ • assumed) ≈[epsilon] (sim • ideal)
  availability :
    (pi₁ • pi₂ • (⊣[iE] assumed)) ≈[epsilon] (⊣[iE] ideal)

/-- **Sequential composability, MaRuTa12 Theorem 1**: constructions
compose — protocols compose serially per interface (`ψ * π`: run `π`,
then `ψ`), simulators compose serially at the adversarial interface, and
the errors add. -/
@[cc_surface]
theorem Constructs.sequential {iA iB iE : I}
    (hAB : iA ≠ iB) (hAE : iA ≠ iE) (hBE : iB ≠ iE)
    {pi₁ : Converters S I iA} {pi₂ : Converters S I iB}
    {psi₁ : Converters S I iA} {psi₂ : Converters S I iB}
    {assumed middle ideal : ResourceSystem S I} {epsilon₁ epsilon₂ : ℝ}
    (nonneg₁ : 0 ≤ epsilon₁) (nonneg₂ : 0 ≤ epsilon₂)
    (first : Constructs iA iB iE pi₁ pi₂ assumed middle epsilon₁)
    (second : Constructs iA iB iE psi₁ psi₂ middle ideal epsilon₂) :
    Constructs iA iB iE (psi₁ * pi₁) (psi₂ * pi₂) assumed ideal
      (epsilon₁ + epsilon₂) := by
  have reorder : ∀ X : ResourceSystem S I,
      (psi₁ * pi₁) • (psi₂ * pi₂) • X =
        psi₁ • psi₂ • (pi₁ • pi₂ • X) := fun X => by
    rw [Converters.comp_smul, Converters.comp_smul,
      Converters.smul_comm_of_ne hAB pi₁ psi₂ (pi₂ • X)]
  obtain ⟨sim₁, security₁⟩ := first.security
  obtain ⟨sim₂, security₂⟩ := second.security
  constructor
  · -- security: the composed simulator is the serial `sim₁ * sim₂`.
    refine ⟨sim₁ * sim₂, ?_⟩
    have hop : psi₁ • psi₂ • (sim₁ • middle) =
        sim₁ • (psi₁ • psi₂ • middle) := by
      rw [Converters.smul_comm_of_ne hBE psi₂ sim₁ middle,
        Converters.smul_comm_of_ne hAE psi₁ sim₁ (psi₂ • middle)]
    have chain₁ : ((psi₁ * pi₁) • (psi₂ * pi₂) • assumed) ≈[epsilon₁]
        (sim₁ • (psi₁ • psi₂ • middle)) := by
      rw [reorder assumed, ← hop]
      exact Converters.close_smul psi₁ (Converters.close_smul psi₂ security₁)
    have chain₂ : (sim₁ • (psi₁ • psi₂ • middle)) ≈[epsilon₂]
        ((sim₁ * sim₂) • ideal) := by
      rw [Converters.comp_smul]
      exact Converters.close_smul sim₁ security₂
    exact close_trans nonneg₁ nonneg₂ chain₁ chain₂
  · -- availability: `⊣` threads through both constructions directly.
    have chain₁ : ((psi₁ * pi₁) • (psi₂ * pi₂) • (⊣[iE] assumed)) ≈[epsilon₁]
        (psi₁ • psi₂ • (⊣[iE] middle)) := by
      rw [reorder (⊣[iE] assumed)]
      exact Converters.close_smul psi₁
        (Converters.close_smul psi₂ first.availability)
    exact close_trans nonneg₁ nonneg₂ chain₁ second.availability

end Constructs

/-! ## Protocols as converter–interface tuples (JosMau20 §2.1) -/

/-- **A protocol** (JosMau20 §2.1): finitely many converters, each wired
to its own interface, pairwise distinct.  Application is one stroke;
JosMau20 Prop. 1 (composition-order independence) makes the order
immaterial (`smul_perm`). -/
@[cc_surface]
structure Protocol (S : Services) (I : Type) [DecidableEq I] where
  entries : List ((interface : I) × Converters S I interface)
  distinct : entries.Pairwise (fun left right => left.1 ≠ right.1)

namespace Protocol

variable {S : Services} {I : Type} [DecidableEq I]

/-- Apply a protocol: attach every converter at its interface. -/
noncomputable instance instSMul : SMul (Protocol S I) (ResourceSystem S I) :=
  ⟨fun protocol resource =>
    protocol.entries.foldl (fun acc entry => entry.2 • acc) resource⟩

theorem smul_def (protocol : Protocol S I) (resource : ResourceSystem S I) :
    protocol • resource =
      protocol.entries.foldl (fun acc entry => entry.2 • acc) resource :=
  rfl

private theorem foldl_perm {left right : List ((i : I) × Converters S I i)}
    (perm : left.Perm right) :
    left.Pairwise (fun a b => a.1 ≠ b.1) →
    ∀ resource : ResourceSystem S I,
      left.foldl (fun acc entry => entry.2 • acc) resource =
        right.foldl (fun acc entry => entry.2 • acc) resource := by
  induction perm with
  | nil => intro _ _; rfl
  | cons entry _ ih =>
      intro distinct resource
      simp only [List.foldl_cons]
      exact ih distinct.of_cons (entry.2 • resource)
  | swap a b l =>
      intro distinct resource
      have hba : b.1 ≠ a.1 :=
        (List.pairwise_cons.mp distinct).1 a (List.mem_cons_self ..)
      simp only [List.foldl_cons]
      rw [Converters.smul_comm_of_ne (Ne.symm hba) a.2 b.2 resource]
  | trans permL _ ihL ihR =>
      intro distinct resource
      exact (ihL distinct resource).trans
        (ihR ((permL.pairwise_iff fun h => h.symm).mp distinct) resource)

/-- **JosMau20 Proposition 1** at the protocol surface: application does
not depend on the order of the converter–interface pairs. -/
@[cc_surface]
theorem smul_perm (protocolL protocolR : Protocol S I)
    (perm : protocolL.entries.Perm protocolR.entries)
    (resource : ResourceSystem S I) :
    protocolL • resource = protocolR • resource :=
  foldl_perm perm protocolL.distinct resource

end Protocol

/-! ## Receipts -/

namespace AlgebraDemo

open ResourceSystem Converters Converter CarrierDemo
open scoped Converter ResourceSystem

/-- Σ's laws on the carrier-demo toys. -/
example : (1 : Converters demoServices Party Party.u) • toyR = toyR :=
  Converters.id_smul toyR

example :
    (mask.word Party.u * mask.word Party.u) • toyR =
      mask.word Party.u • (mask.word Party.u • toyR) :=
  Converters.comp_smul _ _ toyR

example :
    mask.word Party.u • (mask.word Party.v • toyR) =
      mask.word Party.v • (mask.word Party.u • toyR) :=
  Converters.smul_comm_of_ne (by decide) _ _ toyR

/-- The embedded single converter is the part-4 attachment. -/
example : mask.word Party.u • toyR = mask •[Party.u] toyR :=
  Converter.word_smul mask Party.u toyR

/-! A three-party development with a blocked service, for `⊣` and the
two-condition construction. -/

inductive Svc3 | plain | quiet
  deriving DecidableEq

def services3 : Services where
  Service := Svc3
  In := fun | .plain => Bool | .quiet => Empty
  Out := fun | .plain => Bool | .quiet => Unit

instance : HasBlockedService services3 where
  blocked := .quiet
  no_input := ⟨fun query => nomatch query⟩
  some_output := ⟨()⟩

inductive Party3 | a | b | e
  deriving DecidableEq

abbrev layout3 : services3.Layout Party3 := fun _ => .plain

/-- A toy deterministic box at the all-plain layout. -/
def box3 : Machine services3.sig layout3 where
  State := Unit
  init := ()
  step _ _query := some ((), (false : Bool))

noncomputable def toy3 : ResourceSystem services3 Party3 :=
  ResourceSystem.ofLayout
    (DependentRandomSystem.ofProb
      ⟨Finsupp.single box3.toDDS 1, RandomSystems.Dist.isProbDist_single _⟩)

/-- Blocking: the adversarial interface ends unqueryable. -/
example : IsEmpty (services3.In ((⊣[Party3.e] toy3).layoutAt Party3.e)) :=
  ResourceSystem.no_queries_at_block Party3.e toy3

/-- …and blocking it again changes nothing. -/
example : ⊣[Party3.e] (⊣[Party3.e] toy3) = ⊣[Party3.e] toy3 :=
  ResourceSystem.block_idem Party3.e toy3

/-- Two blocked interfaces, in either order. -/
example : ⊣[Party3.a] (⊣[Party3.e] toy3) = ⊣[Party3.e] (⊣[Party3.a] toy3) :=
  ResourceSystem.block_comm (by decide) toy3

/-- Blocking never expands a distance. -/
example (resource : ResourceSystem services3 Party3) :
    (⊣[Party3.e] resource) ≈[0] (⊣[Party3.e] resource) :=
  ResourceSystem.close_block Party3.e (ResourceSystem.close_refl resource)

/-- The identity protocol constructs anything from itself, exactly. -/
theorem toy_constructs :
    Constructs Party3.a Party3.b Party3.e
      (1 : Converters services3 Party3 Party3.a)
      (1 : Converters services3 Party3 Party3.b) toy3 toy3 0 := by
  constructor
  · refine ⟨1, ?_⟩
    rw [Converters.id_smul, Converters.id_smul, Converters.id_smul]
    exact ResourceSystem.close_refl toy3
  · rw [Converters.id_smul, Converters.id_smul]
    exact ResourceSystem.close_refl _

/-- MaRuTa12 Theorem 1 exercised: the identity construction composes with
itself. -/
example :
    Constructs Party3.a Party3.b Party3.e
      ((1 : Converters services3 Party3 Party3.a) * 1)
      ((1 : Converters services3 Party3 Party3.b) * 1) toy3 toy3 (0 + 0) :=
  Constructs.sequential (by decide) (by decide) (by decide)
    le_rfl le_rfl toy_constructs toy_constructs

/-- JosMau20 Prop. 1: protocol application is order-independent. -/
example (resource : ResourceSystem services3 Party3) :
    (Protocol.mk [⟨Party3.a, 1⟩, ⟨Party3.b, 1⟩]
        (by simp [List.pairwise_cons]) : Protocol services3 Party3) •
        resource =
      (Protocol.mk [⟨Party3.b, 1⟩, ⟨Party3.a, 1⟩]
        (by simp [List.pairwise_cons]) : Protocol services3 Party3) •
        resource :=
  Protocol.smul_perm _ _ (List.Perm.swap _ _ _) resource

/-- info: 'RandomSystems.CC.ResourceSystem.block_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.block_idem

/-- info: 'RandomSystems.CC.ResourceSystem.block_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.block_comm

/-- info: 'RandomSystems.CC.ResourceSystem.close_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.close_block

#cc_surface_check Converters.id_smul
#cc_surface_check Converters.smul_comm_of_ne
#cc_surface_check ResourceSystem.no_queries_at_block
#cc_surface_check ResourceSystem.block_eq_attachAt
#cc_surface_check ResourceSystem.block_idem
#cc_surface_check ResourceSystem.layoutAt_block_of_ne
#cc_surface_check ResourceSystem.block_comm
#cc_surface_check ResourceSystem.close_block
#cc_surface_check Constructs.sequential
#cc_surface_check Protocol.smul_perm

end AlgebraDemo

end RandomSystems.CC
