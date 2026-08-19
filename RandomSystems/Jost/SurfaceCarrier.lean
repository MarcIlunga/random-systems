/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfacePar

/-!
# The authoring surface, part 4: the bundled carrier (Maurer11 Def. 1)

Maurer's algebra (Maurer11, p. 44–45) is a set `Φ` of resources with a
TOTAL attachment `α^i R ∈ Φ` — *"the resulting system is again a resource
with the same interface set"* (fn. 9) — and composition-order independence
as a plain equality, `α^i β^j R = β^j α^i R`.  The layout-indexed surface
(`ResourceAt S layout`, part 2) cannot say this: its attachment moves the
type, demands a `provides` proof, and its interchange is heterogeneous.

This module re-seats the algebra on the bundled carrier: a
**resource system** (`ResourceSystem`, the papers' own long form —
Maurer11 §4.3 "resource systems", MauRen16 §3 "cryptographic resource
systems") carries its service layout *inside* the object, so

* attachment `α •[i] R` is **total** — it converts the interface when the
  interface provides the converter's source service and is the identity
  otherwise (the identity-on-mismatch semantics is the kernel's own
  stated contract, DESIGN §10.9: *"on a nonmatching local code its total
  AC action is the identity"*);
* **Prop. 2.2.3 / Def. 1 (i)** is a bare `=` (`attachAt_comm`), retiring
  the `HEq` form from the author's path (the layout-indexed
  `ResourceAt.attach_comm` remains underneath as the kernel-facing form);
* distance is spoken as the papers speak it: `R ≈[ε] Q` and
  `d(R, Q) ≤ ε` (Maurer11 Def. 2, MauRen16 §2.3), with eq. (3)
  (`close_par`) and eq. (4) (`close_attachAt`) in that notation and
  `R ≈[0] Q ↔ R = Q` as the exact-equivalence face.

Everything from parts 1–3 flows in through `ResourceSystem.ofLayout`; the
coherence receipts (`attachAt_of_provides`) pin the new total operation to
the old proof-carrying one on matching layouts.
-/

namespace RandomSystems.CR18.TypedResource.Resource

/-- Surface alias for the bundled resource's service assignment.  (The
kernel field is `boundary`; the surface word is the layout it carries.) -/
abbrev layout {I : Type} {U : SignatureUniverse}
    [DecidableEq I] [DecidableEq U.Code]
    (R : RandomSystems.CR18.TypedResource.Resource I U) : Boundary U I :=
  R.boundary

end RandomSystems.CR18.TypedResource.Resource

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource

/-- **A resource system** (Maurer11 §4.3, MauRen16 §3): a resource carrying
its own service layout, the element of Maurer's `Φ`.  Attachment and
parallel composition are total operations on this carrier, and the algebra
laws are plain equalities. -/
@[cc_surface]
abbrev ResourceSystem (S : Services) (I : Type) [DecidableEq I] :=
  RandomSystems.CR18.TypedResource.Resource I S.sig

namespace ResourceSystem

variable {S : Services} {I : Type} [DecidableEq I]

/-- Bundle a layout-indexed resource (everything parts 1–3 produce) into a
resource system. -/
@[cc_surface]
def ofLayout {layout : S.Layout I} (resource : ResourceAt S layout) :
    ResourceSystem S I :=
  ⟨layout, resource⟩

@[simp]
theorem ofLayout_layout {layout : S.Layout I} (resource : ResourceAt S layout) :
    (ofLayout resource).layout = layout :=
  rfl

/-- The service an interface of a resource system provides — the
surface-typed accessor (`S.Service`-valued; the raw `layout` alias is
kernel-facing). -/
@[cc_surface]
def layoutAt (resource : ResourceSystem S I) (interface : I) : S.Service :=
  resource.boundary interface

@[simp]
theorem layoutAt_ofLayout {layout : S.Layout I}
    (resource : ResourceAt S layout) (interface : I) :
    layoutAt (ofLayout resource) interface = layout interface :=
  rfl

end ResourceSystem

namespace Converter

variable {S : Services} {I : Type} [DecidableEq I]

/-- **Total converter attachment** `α^i R` (Maurer11 §4.3/§4.4): convert
interface `i` when it provides the converter's source service; otherwise
the resource is untouched.  No side condition, no proof argument, same
carrier — the resulting system "is again a resource" (fn. 9).  The
identity-on-mismatch clause is the kernel's stated §10.9 contract. -/
@[cc_surface]
noncomputable def attachAt {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    (resource : ResourceSystem S I) : ResourceSystem S I :=
  (Primitive.mk source target converter :
    Primitive I S.sig interface).act resource

@[inherit_doc attachAt]
scoped notation:73 α:74 " •[" i "] " R:73 => Converter.attachAt α i R

/-- On a layout that provides the source service, total attachment agrees
with the layout-indexed proof-carrying attachment of part 2 — the
coherence receipt pinning the new operation to the old one.  (Bridge: the
right-hand side's bundled layout is the kernel's updated one.) -/
@[cc_surface_bridge]
theorem attachAt_of_provides {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    {layout : S.Layout I} (provides : layout interface = source)
    (resource : ResourceAt S layout) :
    converter •[interface] ResourceSystem.ofLayout resource =
      ResourceSystem.ofLayout
        (ResourceAt.attach interface converter provides resource) :=
  Primitive.act_of_matches
    (Primitive.mk source target converter : Primitive I S.sig interface)
    layout provides resource

/-- On an interface that does not provide the source service, attachment
is the identity — totality doing real work. -/
@[cc_surface]
theorem attachAt_of_not_provides {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    (resource : ResourceSystem S I)
    (mismatch : ResourceSystem.layoutAt resource interface ≠ source) :
    converter •[interface] resource = resource := by
  rcases resource with ⟨boundary, system⟩
  exact Primitive.act_of_not_matches
    (Primitive.mk source target converter : Primitive I S.sig interface)
    boundary mismatch system

/-- **The identity converter is idle** (MauRen16 §3.3's neutral element,
at the *converter* rather than at the `Σ`-word): attaching the memoryless
converter that renames nothing returns the resource.  Total, like
attachment itself — no hypothesis that the interface provides the source,
because on a nonmatching interface attachment is already the identity and
on a matching one the boundary move installs the service the interface
already provides.

This is the converter-level companion of `Converters.id_smul`: `1` lives
in the word monoid, where the unit law is `one_smul`; `ofMaps id id` is a
converter, and its idleness is a fact about the action.  Proved as the
`e = f = Equiv.refl` case of "a memoryless *bijection* converter is a
relabelling"
(`DependentDDS.flatten_attach_ofMaps_eq_relabel`, `TypedFraming.lean`). -/
@[cc_surface]
theorem attachAt_id {service : S.Service} (interface : I)
    (resource : ResourceSystem S I) :
    (Converter.ofMaps id id : Converter S service service) •[interface]
        resource =
      resource := by
  show (Primitive.mk service service (Converter.ofMaps id id) :
    Primitive I S.sig interface).act resource = resource
  exact Primitive.act_ofFunctions_id (interface := interface) service resource

/-- **A memoryless converter into an unqueryable service is already the
identity converter.**  If the *outer* service of `ofMaps` carries no input
then nothing can ever be asked of the converter, and the two maps are not
merely unused — they are unreachable: a memoryless converter *is* its
round function, and that function is nowhere defined once the outer
alphabet is empty.  So this is an equality of converters, not of
behaviours, and it needs no attachment, no resource and no quotient. -/
@[cc_surface]
theorem ofMaps_eq_of_no_input {source target : S.Service}
    (noInput : IsEmpty (S.In target))
    (query query' : S.In target → S.In source)
    (answer answer' : S.Out source → S.Out target) :
    (Converter.ofMaps query answer : Converter S source target) =
      Converter.ofMaps query' answer' := by
  have determined : ∀ left right : Converter S source target,
      left.protocol = right.protocol → left = right := by
    rintro ⟨leftProtocol, _⟩ ⟨rightProtocol, _⟩ same
    cases same
    rfl
  refine determined _ _ ?_
  funext pair
  obtain ⟨outer, inner⟩ := pair
  cases outer with
  | nil =>
      have absurdRound : ¬ ((0 : ℕ) = inner.length ∧ 0 < inner.length) := by omega
      simp [Converter.ofMaps, RandomSystems.CR18.PFunConverter.simpleFn,
        absurdRound]
  | cons head _ => exact (noInput.false head).elim

/-- **Attachment at an unqueryable interface is idle.**  A memoryless
converter whose outer service carries no input is `ofMaps id id` on the
nose (`ofMaps_eq_of_no_input`), and that converter is already known to be
idle (`attachAt_id`) — so no behavioural argument is needed: the two
attachments are literally the same attachment.  Total, like `attachAt_id`:
on a nonmatching interface attachment is the identity anyway. -/
@[cc_surface]
theorem attachAt_of_no_input {service : S.Service}
    (noInput : IsEmpty (S.In service))
    (query : S.In service → S.In service)
    (answer : S.Out service → S.Out service)
    (interface : I) (resource : ResourceSystem S I) :
    (Converter.ofMaps query answer : Converter S service service) •[interface]
        resource = resource := by
  rw [ofMaps_eq_of_no_input noInput query id answer id]
  exact attachAt_id interface resource

/-- **Composition-order independence as a plain equality** (Maurer11
Def. 1 (i), Prop. 2.2.3): converters attached at distinct interfaces
commute — no transport, no heterogeneous equality.  This is the form the
author cites; the layout-indexed `ResourceAt.attach_comm` remains the
kernel-facing receipt underneath. -/
@[cc_surface]
theorem attachAt_comm {source₁ target₁ source₂ target₂ : S.Service}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : Converter S source₁ target₁)
    (converter₂ : Converter S source₂ target₂)
    (resource : ResourceSystem S I) :
    converter₁ •[interface₁] (converter₂ •[interface₂] resource) =
      converter₂ •[interface₂] (converter₁ •[interface₁] resource) :=
  Primitive.act_comm different _ _ resource

end Converter

namespace ResourceSystem

variable {S : Services} {I : Type} [DecidableEq I]

open scoped Converter

/-- The service left at the converted interface: total attachment moves a
providing interface to the converter's target. -/
@[cc_surface]
theorem layoutAt_attachAt {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    {resource : ResourceSystem S I}
    (provides : resource.layoutAt interface = source) :
    (converter •[interface] resource).layoutAt interface = target := by
  rcases resource with ⟨boundary, system⟩
  show ((Primitive.mk source target converter :
      Primitive I S.sig interface).act ⟨boundary, system⟩).boundary
      interface = target
  have sourceMatches : boundary interface = source := provides
  rw [Primitive.act_of_matches (Primitive.mk source target converter)
    boundary sourceMatches system]
  exact replace_boundary_same boundary interface target

/-- **Attachment is local**: converting one interface leaves the service
every *other* interface provides exactly as it was — Maurer11 fn. 9's
"again a resource with the same interface set", read off interface by
interface.  Total: true on the matching branch (where the layout move
touches only `interface`) and on the mismatch branch (where there is no
move at all). -/
@[cc_surface]
theorem layoutAt_attachAt_of_ne {source target : S.Service}
    {interface other : I} (different : other ≠ interface)
    (converter : Converter S source target) (resource : ResourceSystem S I) :
    (converter •[interface] resource).layoutAt other =
      resource.layoutAt other := by
  rcases resource with ⟨boundary, system⟩
  show ((Primitive.mk source target converter :
      Primitive I S.sig interface).act ⟨boundary, system⟩).boundary other =
    boundary other
  by_cases sourceMatches : boundary interface = source
  · rw [Primitive.act_of_matches _ boundary sourceMatches system]
    exact replace_boundary_ne boundary different target
  · rw [Primitive.act_of_not_matches _ boundary sourceMatches system]

/-- `R ≈[ε] Q` — the resources are ε-close (Maurer11 Def. 2, MauRen16
§2.3's `≈_ε`).  Also written `d(R, Q) ≤ ε`.  Stated for any carrier with
a behavioral distance, so the one notation serves the bundled carrier,
the layout-indexed quotient, and single-world resources alike. -/
@[cc_surface]
def close {α : Type*} [EDist α] (epsilon : ℝ) (left right : α) : Prop :=
  edist left right ≤ ENNReal.ofReal epsilon

@[inherit_doc close]
scoped notation:50 R:51 " ≈[" ε "] " Q:51 => ResourceSystem.close ε R Q

/-- Zero distance is equality — Maurer's `≡` (identical behavior) IS the
carrier's `=`. -/
@[cc_surface]
theorem close_zero_iff (left right : ResourceSystem S I) :
    (left ≈[0] right) ↔ left = right := by
  unfold close
  rw [ENNReal.ofReal_zero]
  constructor
  · intro h
    exact (Resource.edist_eq_zero_iff_eq left right).mp
      (le_antisymm h (zero_le _))
  · rintro rfl
    simp

/-- **Eq. (4)** (Maurer11 Def. 2): converter attachment is non-expanding,
in the papers' notation. -/
@[cc_surface]
theorem close_attachAt {epsilon : ℝ} {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    {left right : ResourceSystem S I} (h : left ≈[epsilon] right) :
    (converter •[interface] left) ≈[epsilon] (converter •[interface] right) :=
  le_trans (Primitive.edist_act_le _ left right) h

/-- **`≈[ε]` already fixes the interface layout**: resource systems at any
finite distance provide the *same* service at every interface.  Maurer's
`d(R, Q)` is only ever written between resources with the same interface
set, and on this carrier that convention is a theorem rather than a
convention — differing layouts sit at infinite distance, which no real `ε`
can bound.  So a "the two agree at `i`" hypothesis is never needed
alongside `≈[ε]`; it is derivable. -/
@[cc_surface]
theorem layoutAt_eq_of_close {epsilon : ℝ} {left right : ResourceSystem S I}
    (h : left ≈[epsilon] right) (interface : I) :
    left.layoutAt interface = right.layoutAt interface := by
  rcases left with ⟨leftLayout, leftSystem⟩
  rcases right with ⟨rightLayout, rightSystem⟩
  by_cases same : leftLayout = rightLayout
  · exact congrFun same interface
  · refine absurd (top_le_iff.mp ?_) (ENNReal.ofReal_ne_top (r := epsilon))
    have bounded : edist (Resource.mk leftLayout leftSystem)
        (Resource.mk rightLayout rightSystem) ≤ ENNReal.ofReal epsilon := h
    rwa [Resource.edist_ne same leftSystem rightSystem] at bounded

section Par

variable {J : Type} [DecidableEq J]

/-- **`[R, Q]`** (Jost §2.2.2, printed p. 17), rendered `∥`: two resource
systems with **disjoint** interface sets, side by side, on the union of the
two interface sets.  `∥` is Maurer11 eq. (3)'s notation for the operation
Jost prints `[R, Q]` (`[·,·]` is list syntax in Lean).

The interface set grows, so `Φ` is a family `I ↦ ResourceSystem S I` rather
than one set — which is Jost's own definition and costs Maurer11 Def. 1
nothing: fn. 9's "again a resource with the same interface set" constrains
**attachment**, and attachment is still an endo-operation
(`Converter.attachAt`). -/
@[cc_surface]
noncomputable def par (left : ResourceSystem S I) (right : ResourceSystem S J) :
    ResourceSystem S (I ⊕ J) :=
  RandomSystems.CR18.TypedResource.Resource.tensor left right

@[inherit_doc par]
scoped infixr:70 " ∥ " => ResourceSystem.par

/-- Each interface of a composite provides exactly what it provided in its
own component — the left flank. -/
@[cc_surface]
theorem layoutAt_par_inl (left : ResourceSystem S I)
    (right : ResourceSystem S J) (interface : I) :
    (left ∥ right).layoutAt (Sum.inl interface) = left.layoutAt interface :=
  rfl

/-- …and the right flank. -/
@[cc_surface]
theorem layoutAt_par_inr (left : ResourceSystem S I)
    (right : ResourceSystem S J) (interface : J) :
    (left ∥ right).layoutAt (Sum.inr interface) = right.layoutAt interface :=
  rfl

/-- **Eq. (3)** (Maurer11 Def. 2): parallel composition is non-expanding —
the error accounting of the composition theorem, in the papers'
notation. -/
@[cc_surface]
theorem close_par {epsilonL epsilonR : ℝ}
    (nonnegL : 0 ≤ epsilonL) (nonnegR : 0 ≤ epsilonR)
    {leftA leftB : ResourceSystem S I} {rightA rightB : ResourceSystem S J}
    (closeL : leftA ≈[epsilonL] leftB) (closeR : rightA ≈[epsilonR] rightB) :
    (leftA ∥ rightA) ≈[epsilonL + epsilonR] (leftB ∥ rightB) := by
  unfold close par at *
  calc edist (RandomSystems.CR18.TypedResource.Resource.tensor leftA rightA)
        (RandomSystems.CR18.TypedResource.Resource.tensor leftB rightB)
      ≤ edist leftA leftB + edist rightA rightB :=
        RandomSystems.CR18.TypedResource.Resource.edist_tensor_le
          leftA leftB rightA rightB
    _ ≤ ENNReal.ofReal epsilonL + ENNReal.ofReal epsilonR :=
        add_le_add closeL closeR
    _ = ENNReal.ofReal (epsilonL + epsilonR) :=
        (ENNReal.ofReal_add nonnegL nonnegR).symm

/-- Eq. (3) with the second component held fixed: a composite is exactly as
distinguishable as the component that changed.  (The `0` on the untouched
flank is the whole content of Jost Thm 2.2.5 (2)'s error accounting.) -/
@[cc_surface]
theorem close_par_left {epsilon : ℝ} (nonneg : 0 ≤ epsilon)
    {left right : ResourceSystem S I} (other : ResourceSystem S J)
    (close : left ≈[epsilon] right) :
    (left ∥ other) ≈[epsilon] (right ∥ other) := by
  have bound := close_par nonneg le_rfl close
    ((close_zero_iff other other).mpr rfl)
  rwa [add_zero] at bound

end Par

end ResourceSystem

/-! ## Jost Prop. 2.2.3 (2) and Thm 2.2.5 (2) -/

namespace Converter

open scoped ResourceSystem

variable {S : Services} {I J : Type} [DecidableEq I] [DecidableEq J]

/-- **Jost Proposition 2.2.3, second clause** (printed p. 18):
`π^γ [R, Q] = [π^γ R, Q]` — a converter whose connection lands in the left
component's interfaces converts that component and leaves the other one
untouched.

A plain equality, and **total**: no side condition that the interface
provides the converter's source, because on a nonmatching interface both
sides are the identity, and `Sum.elim` makes the composite's service at
`Sum.inl i` be the left component's at `i` definitionally.  (The kernel
receipt underneath is heterogeneous only because updating the layout at
`Sum.inl i` and at `i` are propositionally, not definitionally, the same
move; the bundled carrier absorbs that.) -/
@[cc_surface]
theorem attachAt_par_left {source target : S.Service}
    (converter : Converter S source target) (interface : I)
    (left : ResourceSystem S I) (right : ResourceSystem S J) :
    converter •[Sum.inl interface] (left ∥ right) =
      (converter •[interface] left) ∥ right := by
  rcases left with ⟨leftBoundary, leftSystem⟩
  rcases right with ⟨rightBoundary, rightSystem⟩
  show (Primitive.mk source target converter :
      Primitive (I ⊕ J) S.sig (Sum.inl interface)).act
      ⟨Sum.elim leftBoundary rightBoundary,
        DependentRandomSystem.tensor leftSystem rightSystem⟩ =
    RandomSystems.CR18.TypedResource.Resource.tensor
      ((Primitive.mk source target converter :
        Primitive I S.sig interface).act ⟨leftBoundary, leftSystem⟩)
      ⟨rightBoundary, rightSystem⟩
  by_cases sourceMatches : leftBoundary interface = source
  · rw [Primitive.act_of_matches (Primitive.mk source target converter :
        Primitive (I ⊕ J) S.sig (Sum.inl interface))
      (Sum.elim leftBoundary rightBoundary) sourceMatches,
      Primitive.act_of_matches (Primitive.mk source target converter :
        Primitive I S.sig interface) leftBoundary sourceMatches]
    show (⟨replaceBoundary (Sum.elim leftBoundary rightBoundary)
        (Sum.inl interface) target, _⟩ : ResourceSystem S (I ⊕ J)) = ⟨_, _⟩
    congr 1
    · exact tensor_replaceBoundary_inl interface target leftBoundary
        rightBoundary
    · exact DependentRandomSystem.attach_tensor_inl interface
        converter sourceMatches leftSystem rightSystem
  · rw [Primitive.act_of_not_matches (Primitive.mk source target converter :
        Primitive (I ⊕ J) S.sig (Sum.inl interface))
      (Sum.elim leftBoundary rightBoundary) sourceMatches,
      Primitive.act_of_not_matches (Primitive.mk source target converter :
        Primitive I S.sig interface) leftBoundary sourceMatches]
    rfl

/-- **Jost Theorem 2.2.5 (2), parallel composability.**  Jost's proof is one
line — *"the second property follows from Proposition 2.2.3:
`π[R,T] = [πR,T] ⊆ [S,T]`"* — and this is that line: rewrite by clause 2,
then compose in parallel with the untouched `T` at no extra error (eq. (3)
with `0` on the right flank).

A construction statement for `R` therefore yields one for `[R, T]` with the
same `ε`, the protocol unchanged. -/
@[cc_surface]
theorem close_par_attachAt_left {epsilon : ℝ} (nonneg : 0 ≤ epsilon)
    {source target : S.Service} (converter : Converter S source target)
    (interface : I) {assumed ideal : ResourceSystem S I}
    (other : ResourceSystem S J)
    (construction : (converter •[interface] assumed) ≈[epsilon] ideal) :
    (converter •[Sum.inl interface] (assumed ∥ other)) ≈[epsilon]
      (ideal ∥ other) := by
  rw [attachAt_par_left]
  exact ResourceSystem.close_par_left nonneg other construction

end Converter

namespace ResourceAt

open scoped ResourceSystem

variable {S : Services} {I J : Type} [DecidableEq I] [DecidableEq J]

/-- **Eq. (3)** (Maurer11 Def. 2) at the layout-indexed quotient, in the
papers' notation: parallel composition is non-expanding.  Surface
successor of `ResourceAt.edist_par_le`. -/
@[cc_surface]
theorem close_par {epsilonL epsilonR : ℝ}
    (nonnegL : 0 ≤ epsilonL) (nonnegR : 0 ≤ epsilonR)
    {layoutL : S.Layout I} {layoutR : S.Layout J}
    {leftA leftB : ResourceAt S layoutL}
    {rightA rightB : ResourceAt S layoutR}
    (closeL : leftA ≈[epsilonL] leftB) (closeR : rightA ≈[epsilonR] rightB) :
    (leftA ∥ rightA) ≈[epsilonL + epsilonR] (leftB ∥ rightB) := by
  unfold ResourceSystem.close at *
  calc edist (leftA ∥ rightA) (leftB ∥ rightB)
      ≤ edist leftA leftB + edist rightA rightB :=
        edist_par_le leftA leftB rightA rightB
    _ ≤ ENNReal.ofReal epsilonL + ENNReal.ofReal epsilonR :=
        add_le_add closeL closeR
    _ = ENNReal.ofReal (epsilonL + epsilonR) :=
        (ENNReal.ofReal_add nonnegL nonnegR).symm

end ResourceAt

/-! ## Jost's connection function γ: a converter reaching two interfaces

Jost's converter attachment (printed p. 18) is parameterised by an
**injective connection function** `γ : I_in ↪ I_P` from the converter's inner
interfaces into the resource's; `π^γ R` removes `img(γ)` and adds the
converter's outer interfaces.  Fig. 2.3's protocol converter π_ε^A reaches
TWO of them — *"interface A of Key"* and *"interface A of AuthChan"* — which
`α •[i] R` cannot express.

This section gives that case directly.  A `Connection K rest` is γ: it names
the two interfaces of `K` the converter reaches and gives a name to each
interface it leaves alone; `α ••[γ] R` is `π^γ R`, whose interface set is
`rest ⊕ Unit` — Jost's `(I_P \ img(γ)) ∪ I_out` exactly, with the converter's
single outer interface at `Sum.inr ()`.

Underneath: *a converter reaching two interfaces at once is a unary converter
at their merge.*  The two connected interfaces are merged into one carrying
the **paired** service — which is what `Services.free`'s coding is for — and
the converter is attached there with the ordinary `•[·]`.  The author never
writes the re-indexing or the merge.
-/

/-- **Jost's connection function `γ`** (printed p. 18), two-interface case: a
converter's inner interfaces, injected into a resource's.  `split` presents
the resource's interface set as the interfaces the converter leaves alone
(`rest`) together with the two it reaches — `img(γ)`, which `split` sends to
`Sum.inr (Sum.inl ())` and `Sum.inr (Sum.inr ())`. -/
@[cc_surface]
structure Connection (K rest : Type) where
  /-- The interface set, split into the untouched interfaces and the two the
  converter reaches. -/
  split : K ≃ rest ⊕ (Unit ⊕ Unit)

namespace Connection

variable {K rest : Type}

/-- The first interface the connection reaches (Fig. 2.3: interface A of
`Key`). -/
@[cc_surface]
def first (γ : Connection K rest) : K := γ.split.symm (Sum.inr (Sum.inl ()))

/-- The second interface the connection reaches (Fig. 2.3: interface A of
`AuthChan`). -/
@[cc_surface]
def second (γ : Connection K rest) : K := γ.split.symm (Sum.inr (Sum.inr ()))

/-- The interface an untouched interface came from. -/
@[cc_surface]
def untouched (γ : Connection K rest) (interface : rest) : K :=
  γ.split.symm (Sum.inl interface)

end Connection

/-- **The paired service** of two services: what the merge of two interfaces
provides, and therefore what the inner side of a two-interface converter
faces.  Over `S.free` it is `.sum a b`, whose alphabets **are** the tagged
sums of the components' (`Jost/SurfacePar.lean`). -/
@[cc_surface]
abbrev Services.paired (S : Services) [HasSumCode S.sig] (a b : S.Service) :
    S.Service :=
  @HasSumCode.sumCode S.sig _ a b

namespace ResourceSystem

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

/-! ### The split, and why it is public

`mergeAlong` is *re-index along the split, then merge the trailing block*, and
every algebraic law about it has to name the alphabet equivalences it
re-indexes along.  These four therefore cannot be `private`: two downstream
modules (`Jost/SurfaceMergeLocality.lean`, `Jost/SurfaceMergePar.lean`) are
proofs about exactly this re-indexing.  They remain implementation vocabulary —
kernel-named, never `@[cc_surface]` — and an author never writes one. -/

/-- The layout of the split presentation: untouched interfaces keep their
services, the two connected ones sit in a two-interface block.
(Implementation.) -/
def splitLayout (γ : Connection K rest) (layout : Boundary S.sig K) :
    Boundary S.sig (rest ⊕ (Unit ⊕ Unit)) :=
  Sum.elim (fun interface => layout (γ.untouched interface))
    (twoBlock (layout γ.first) (layout γ.second))

omit [DecidableEq K] [DecidableEq rest] in
theorem splitLayout_split (γ : Connection K rest)
    (layout : Boundary S.sig K) (interface : K) :
    splitLayout γ layout (γ.split interface) = layout interface := by
  conv_rhs => rw [← γ.split.symm_apply_apply interface]
  rcases γ.split interface with untouched | connected
  · rfl
  · rcases connected with _ | _ <;> rfl

/-- Queries relocate along the split.  (Implementation.) -/
def splitQueryEquiv (γ : Connection K rest)
    (layout : Boundary S.sig K) :
    Query S.sig layout ≃ Query S.sig (splitLayout γ layout) :=
  (Equiv.sigmaCongrRight fun interface =>
      Equiv.cast (congrArg S.sig.input
        (splitLayout_split γ layout interface).symm)).trans
    (Equiv.sigmaCongrLeft (β := fun interface => S.sig.input
      (splitLayout γ layout interface)) γ.split)

/-- Answers relocate the same way.  (Implementation.) -/
def splitAnswerEquiv (γ : Connection K rest)
    (layout : Boundary S.sig K) :
    FlatAnswer S.sig layout ≃ FlatAnswer S.sig (splitLayout γ layout) :=
  (Equiv.sigmaCongrRight fun interface =>
      Equiv.cast (congrArg S.sig.output
        (splitLayout_split γ layout interface).symm)).trans
    (Equiv.sigmaCongrLeft (β := fun interface => S.sig.output
      (splitLayout γ layout interface)) γ.split)

omit [DecidableEq K] [DecidableEq rest] in
/-- Re-indexing along the split is tag-compatible, by the route criterion at
`route = γ.split`.  (Implementation.) -/
theorem tagCompatible_split (γ : Connection K rest)
    (layout : Boundary S.sig K) :
    TagCompatible (splitQueryEquiv γ layout) (splitAnswerEquiv γ layout) :=
  tagCompatible_of_route γ.split (fun _ => rfl) fun _ => rfl

/-- **The two interfaces a connection reaches, addressed as one.**  The
merged interface provides the paired service; every other interface is
untouched.  A relabelling, and an isometry (`close_mergeAlong`): nothing
about distinguishability is created or destroyed by it. -/
@[cc_surface]
noncomputable def mergeAlong [HasSumCode S.sig] (γ : Connection K rest)
    (resource : ResourceSystem S K) : ResourceSystem S (rest ⊕ Unit) :=
  ⟨Sum.elim (fun interface => resource.layoutAt (γ.untouched interface))
      fun _ => S.paired (resource.layoutAt γ.first) (resource.layoutAt γ.second),
    DependentRandomSystem.mergeTwo _ _ _
      (DependentRandomSystem.reindex (tagCompatible_split γ resource.boundary)
        resource.system)⟩

/-- An untouched interface keeps the service it provided. -/
@[cc_surface]
theorem layoutAt_mergeAlong_untouched [HasSumCode S.sig] (γ : Connection K rest)
    (resource : ResourceSystem S K) (interface : rest) :
    (resource.mergeAlong γ).layoutAt (Sum.inl interface) =
      resource.layoutAt (γ.untouched interface) :=
  rfl

/-- **The service a connection faces**: the paired service of the two
interfaces it reaches — what the inner side of a two-interface converter
must provide, the way `layoutAt i` is what a unary one must. -/
@[cc_surface]
def layoutAlong [HasSumCode S.sig] (resource : ResourceSystem S K)
    (γ : Connection K rest) : S.Service :=
  S.paired (resource.layoutAt γ.first) (resource.layoutAt γ.second)

/-- **The merged interface provides exactly the service the connection
faces** — the paired service of the two interfaces it reaches. -/
@[cc_surface]
theorem layoutAt_mergeAlong [HasSumCode S.sig] (γ : Connection K rest)
    (resource : ResourceSystem S K) :
    (resource.mergeAlong γ).layoutAt (Sum.inr ()) = resource.layoutAlong γ :=
  rfl

/-- **Merging along a connection is an isometry**: addressing two interfaces
through one costs no distinguishing advantage in either direction, so no
error accounting is spent on it. -/
@[cc_surface]
theorem close_mergeAlong [HasSumCode S.sig] {epsilon : ℝ}
    (γ : Connection K rest) {left right : ResourceSystem S K}
    (close : left ≈[epsilon] right) :
    (left.mergeAlong γ) ≈[epsilon] (right.mergeAlong γ) := by
  have layouts : ∀ interface, left.layoutAt interface = right.layoutAt interface :=
    layoutAt_eq_of_close close
  rcases left with ⟨layout, leftSystem⟩
  rcases right with ⟨rightLayout, rightSystem⟩
  have same : layout = rightLayout := funext fun interface => layouts interface
  subst same
  show edist (mergeAlong γ ⟨layout, leftSystem⟩) (mergeAlong γ ⟨layout, rightSystem⟩)
    ≤ ENNReal.ofReal epsilon
  show edist (Resource.mk (I := rest ⊕ Unit) _
      (DependentRandomSystem.mergeTwo _ _ _
        (DependentRandomSystem.reindex (tagCompatible_split γ layout) leftSystem)))
      (Resource.mk _ (DependentRandomSystem.mergeTwo _ _ _
        (DependentRandomSystem.reindex (tagCompatible_split γ layout) rightSystem)))
    ≤ ENNReal.ofReal epsilon
  rw [Resource.edist_same, DependentRandomSystem.edist_mergeTwo,
    DependentRandomSystem.edist_reindex,
    ← Resource.edist_same layout leftSystem rightSystem]
  exact close

end ResourceSystem

namespace Converter

open scoped ResourceSystem

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

/-- **Attachment along a connection** — Jost's `π^γ R` (printed p. 18) for a
converter reaching TWO interfaces at once, e.g. Fig. 2.3's π_ε^A at interface
A of `Key` and interface A of `AuthChan`.

Merge-then-attach: the two connected interfaces become one interface
providing their paired service (an isometry, `close_mergeAlong`), and the
converter is attached there.  The result's interface set is
`rest ⊕ Unit` — the untouched interfaces plus the converter's outer one, which
is Jost's `(I_P \ img(γ)) ∪ I_out`.

Total, exactly like `•[·]`: on a merged interface whose paired service is not
the converter's source, attachment is the identity. -/
@[cc_surface]
noncomputable def attachAlong [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection K rest)
    (resource : ResourceSystem S K) : ResourceSystem S (rest ⊕ Unit) :=
  converter •[Sum.inr ()] (resource.mergeAlong γ)

@[inherit_doc attachAlong]
scoped notation:73 α:74 " ••[" γ "] " R:73 => Converter.attachAlong α γ R

/-- **A γ-attachment does real work exactly when the converter's inner side
is the service the connection faces**: then the outer interface ends at the
converter's target. -/
@[cc_surface]
theorem layoutAt_attachAlong [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection K rest)
    {resource : ResourceSystem S K}
    (provides : resource.layoutAlong γ = source) :
    (converter ••[γ] resource).layoutAt (Sum.inr ()) = target :=
  ResourceSystem.layoutAt_attachAt converter (Sum.inr ()) provides

/-- **A γ-attachment that misses the service the connection faces is idle** —
totality doing real work at a connection, exactly as
`attachAt_of_not_provides` does at an interface.  What remains is the merge
itself: the two interfaces have been addressed as one, which is a
relabelling of the interface set and not an action on the resource. -/
@[cc_surface]
theorem attachAlong_of_not_provides [HasSumCode S.sig]
    {source target : S.Service} (converter : Converter S source target)
    (γ : Connection K rest) (resource : ResourceSystem S K)
    (mismatch : resource.layoutAlong γ ≠ source) :
    converter ••[γ] resource = resource.mergeAlong γ :=
  attachAt_of_not_provides converter (Sum.inr ()) _ mismatch

/-- **Eq. (4) along a connection**: a two-interface attachment is
non-expanding — merging is an isometry and attachment is 1-Lipschitz, so the
error accounting of a protocol converter that reaches two interfaces is the
same as for one that reaches one. -/
@[cc_surface]
theorem close_attachAlong [HasSumCode S.sig] {epsilon : ℝ}
    {source target : S.Service} (converter : Converter S source target)
    (γ : Connection K rest) {left right : ResourceSystem S K}
    (close : left ≈[epsilon] right) :
    (converter ••[γ] left) ≈[epsilon] (converter ••[γ] right) :=
  ResourceSystem.close_attachAt converter (Sum.inr ())
    (ResourceSystem.close_mergeAlong γ close)

end Converter

/-! ## Receipts: the algebra composes in eq.-(1) shape -/

namespace CarrierDemo

open ResourceSystem Converter
open scoped Converter ResourceSystem

/-- Two base services over `Bool` alphabets; the demo development is its
free closure so `∥` is available. -/
inductive Svc | plain | masked
  deriving DecidableEq

def baseServices : Services where
  Service := Svc
  In := fun _ => Bool
  Out := fun _ => Bool

abbrev demoServices : Services := baseServices.free

inductive Party | u | v
  deriving DecidableEq

abbrev plainLayout : demoServices.Layout Party := fun _ => .base .plain

/-- A toy deterministic box at the all-plain layout. -/
def demoBox : Machine demoServices.sig plainLayout where
  State := Unit
  init := ()
  step _ _query := some ((), (false : Bool))

noncomputable def toyAt : ResourceAt demoServices plainLayout :=
  DependentRandomSystem.ofProb
    ⟨Finsupp.single demoBox.toDDS 1, RandomSystems.Dist.isProbDist_single _⟩

noncomputable def toyR : ResourceSystem demoServices Party :=
  ResourceSystem.ofLayout toyAt

/-- The masking converter between the two base services. -/
noncomputable def mask : Converter demoServices (.base .plain) (.base .masked) :=
  Converter.ofMaps id (fun b => !b)

/-! ### A converter reaching TWO interfaces (Jost Fig. 2.3)

`KEY ∥ AUT` is now the disjoint composition of two independent copies, so
its interface set is `Party ⊕ Party`: the key resource's `u` and `v` on the
left, the authenticated channel's on the right.  Jost's π_ε^A reaches two of
them at once — *"at interface A of Key"* **and** *"at interface A of
AuthChan"* (Fig. 2.3) — which is a connection function γ, not an interface.

At the merge of those two interfaces the service is the PAIRED one, and the
converter's inner side is exactly that: it reads `Sum.inl` from the key and
writes `Sum.inr` to the channel.  `Services.free` types this directly — the
`HasSumCode` instance of `Jost/SurfacePar.lean` sets `inputEquiv` to
`Equiv.refl`, so `In (.sum a b)` **is** `In a ⊕ In b`.  The two converters
below are that idiom, and the two connections after them are Fig. 2.3's γ's. -/

/-- The bit an answer of the paired source carries, whichever component
answered. -/
def pairedBit : Bool ⊕ Bool → Bool := Sum.elim id id

/-- **π_ε^A** (Jost Fig. 2.3) on the toy alphabets: source = the PAIRED
service of the two interfaces its connection reaches, target = the outside
`masked` service.  On a plaintext bit it (1) fetches the key at the FIRST
connected interface (`Sum.inl` — "at interface A of Key"), (2) sends the
masked bit at the SECOND (`Sum.inr` — "at interface A of AuthChan"), and
answers with what the channel returned.  Two inner calls per round, on two
different resources: exactly what a converter reaching one interface cannot
express. -/
noncomputable def encA :
    Converter demoServices
      (.sum (.base .plain) (.base .plain)) (.base .masked) :=
  Converter.ofRounds
    (fun history nonempty answers =>
      match answers with
      | [] => Sum.inl (Sum.inl false)
      | key :: [] =>
          Sum.inl (Sum.inr (Bool.xor (history.getLast nonempty) (pairedBit key)))
      | _ :: sent :: _ => Sum.inr (pairedBit sent))
    (fun _ => 2)
    (by
      intro history nonempty answers
      rcases answers with _ | ⟨key, _ | ⟨sent, rest⟩⟩ <;> simp)
    ⟨2, fun _ => le_refl 2⟩

/-- **π_ε^B** (Jost Fig. 2.3), the receiving flank: it fetches the key at the
first connected interface and the ciphertext at the second, and unmasks.
Same paired source, so it too reaches two interfaces at once. -/
noncomputable def decB :
    Converter demoServices
      (.sum (.base .plain) (.base .plain)) (.base .masked) :=
  Converter.ofRounds
    (fun history nonempty answers =>
      match answers with
      | [] => Sum.inl (Sum.inl false)
      | _ :: [] => Sum.inl (Sum.inr (history.getLast nonempty))
      | key :: received :: _ =>
          Sum.inr (Bool.xor (pairedBit received) (pairedBit key)))
    (fun _ => 2)
    (by
      intro history nonempty answers
      rcases answers with _ | ⟨key, _ | ⟨received, rest⟩⟩ <;> simp)
    ⟨2, fun _ => le_refl 2⟩

/-- Coherence: total attachment on a providing layout is the part-2
attachment, bundled. -/
example :
    mask •[Party.u] toyR =
      ResourceSystem.ofLayout
        (ResourceAt.attach Party.u mask rfl toyAt) :=
  Converter.attachAt_of_provides mask Party.u rfl toyAt

/-- Totality doing real work: re-masking an already-masked interface is
the identity (its service is no longer `plain`). -/
example :
    mask •[Party.u] (mask •[Party.u] toyR) = mask •[Party.u] toyR := by
  refine Converter.attachAt_of_not_provides mask Party.u _ ?_
  rw [show toyR = ResourceSystem.ofLayout toyAt from rfl,
    Converter.attachAt_of_provides mask Party.u rfl toyAt]
  simp [ResourceSystem.layoutAt, ResourceSystem.ofLayout, Function.update]
  intro h
  injection h with h'
  exact Svc.noConfusion h'

/-- Def. 1 (i) on the toys: attachment at distinct interfaces commutes,
plainly. -/
example :
    mask •[Party.u] (mask •[Party.v] toyR) =
      mask •[Party.v] (mask •[Party.u] toyR) :=
  Converter.attachAt_comm (by decide) mask mask toyR

/-- Exact equivalence is equality. -/
example : toyR ≈[0] toyR := (ResourceSystem.close_zero_iff _ _).mpr rfl

/-! ### Fig. 2.3's two connection functions

`toyR ∥ toyR` is `[KEY, AUT]`: the left copy is the key resource, the right
copy the authenticated channel, and its interface set is `Party ⊕ Party`.
π_ε^A is wired to party `u` of both; π_ε^B to party `v` of both. -/

/-- What is left of `[KEY, AUT]` once the sender's connection is made: party
`v`'s interface at each of the two components. -/
inductive Comp | key | aut
  deriving DecidableEq

/-- **γ^A** (Jost Fig. 2.3): the sender's connection — interface `u` of the
key resource (the left component) and interface `u` of the authenticated
channel (the right one).  It leaves party `v`'s two interfaces alone. -/
def gammaU : Connection (Party ⊕ Party) Comp where
  split :=
    { toFun := fun
        | .inl .u => .inr (.inl ())
        | .inr .u => .inr (.inr ())
        | .inl .v => .inl .key
        | .inr .v => .inl .aut
      invFun := fun
        | .inr (.inl ()) => .inl .u
        | .inr (.inr ()) => .inr .u
        | .inl .key => .inl .v
        | .inl .aut => .inr .v
      left_inv := by rintro (a | a) <;> cases a <;> rfl
      right_inv := by
        rintro (a | b)
        · cases a <;> rfl
        · cases b <;> rfl }

/-- **γ^B** (Jost Fig. 2.3): the receiver's connection — the two interfaces
the sender left alone.  It leaves alone the single interface the sender's
converter produced. -/
def gammaV : Connection (Comp ⊕ Unit) Unit where
  split :=
    { toFun := fun
        | .inl .key => .inr (.inl ())
        | .inl .aut => .inr (.inr ())
        | .inr () => .inl ()
      invFun := fun
        | .inr (.inl ()) => .inl .key
        | .inr (.inr ()) => .inl .aut
        | .inl () => .inr ()
      left_inv := by
        rintro (a | b)
        · cases a <;> rfl
        · rfl
      right_inv := by
        rintro (a | b)
        · rfl
        · cases b <;> rfl }

/-- **The eq.-(1) shape composes**, with Jost's own Fig.-2.3 wiring:
`dec^{γ^B} enc^{γ^A} [KEY, AUT]`.  Each converter reaches TWO interfaces —
one of the key resource and one of the channel — so each attachment does
real work, and the constructed system has the two interfaces `A` and `B`
Fig. 2.3 draws (`Unit ⊕ Unit`), the four it started from having been
consumed two at a time. -/
noncomputable def constructedShape : ResourceSystem demoServices (Unit ⊕ Unit) :=
  decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR))

/-- The same shape, same connections, with a converter whose inner side is a
single BASE service: both attachments are idle, because a connection's
merged interface provides the PAIRED service, not a base one.  Kept as the
contrast case the move matcher must keep telling apart from
`constructedShape`. -/
noncomputable def idleShape : ResourceSystem demoServices (Unit ⊕ Unit) :=
  mask ••[gammaV] (mask ••[gammaU] (toyR ∥ toyR))

/-- The sender's attachment does real work: the merged interface provides
the paired service, which IS `encA`'s inner side, so the outer interface
ends at `masked`. -/
example :
    (encA ••[gammaU] (toyR ∥ toyR)).layoutAt (Sum.inr ()) = .base .masked :=
  Converter.layoutAt_attachAlong encA gammaU rfl

/-- …and `mask`, on the very same connection, is idle: its inner side is a
base service while the connection faces a paired one. -/
example :
    mask ••[gammaU] (toyR ∥ toyR) =
      ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) :=
  Converter.attachAlong_of_not_provides mask gammaU (toyR ∥ toyR) (by decide)

/-- **The identity converter is idle**, on a providing interface: the
memoryless converter that renames nothing is `drop_id` on the `•[i]`
spelling. -/
example :
    (Converter.ofMaps id id :
      Converter demoServices (.base .plain) (.base .plain))
        •[Party.u] toyR = toyR :=
  Converter.attachAt_id Party.u toyR

/-- …and on an interface that does *not* provide its source, where the
mismatch branch carries it instead — the statement is total. -/
example :
    (Converter.ofMaps id id :
      Converter demoServices (.base .masked) (.base .masked))
        •[Party.u] toyR = toyR :=
  Converter.attachAt_id Party.u toyR

/-- Attachment is local: masking `u` leaves `v`'s service alone. -/
example : (mask •[Party.u] toyR).layoutAt Party.v = toyR.layoutAt Party.v :=
  ResourceSystem.layoutAt_attachAt_of_ne (by decide) mask toyR

/-- info: 'RandomSystems.CC.Converter.attachAt_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAt_id

/-- info: 'RandomSystems.CC.Converter.ofMaps_eq_of_no_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.ofMaps_eq_of_no_input

/-- info: 'RandomSystems.CC.Converter.attachAt_of_no_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAt_of_no_input

/-- info: 'RandomSystems.CC.ResourceSystem.layoutAt_eq_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.layoutAt_eq_of_close

/-- info: 'RandomSystems.CC.Converter.attachAt_par_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAt_par_left

/-- info: 'RandomSystems.CC.Converter.close_par_attachAt_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.close_par_attachAt_left

/-- info: 'RandomSystems.CC.ResourceSystem.close_mergeAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.close_mergeAlong

/-- info: 'RandomSystems.CC.Converter.close_attachAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.close_attachAlong

#cc_surface_check ResourceSystem.close_zero_iff
#cc_surface_check Converter.attachAt_comm
#cc_surface_check Converter.attachAt_id
#cc_surface_check Converter.ofMaps_eq_of_no_input
#cc_surface_check Converter.attachAt_of_no_input
#cc_surface_check ResourceSystem.layoutAt_attachAt
#cc_surface_check ResourceSystem.layoutAt_attachAt_of_ne
#cc_surface_check ResourceSystem.layoutAt_eq_of_close
#cc_surface_check ResourceSystem.close_par
#cc_surface_check ResourceSystem.close_par_left
#cc_surface_check Converter.attachAt_par_left
#cc_surface_check Converter.close_par_attachAt_left
#cc_surface_check ResourceSystem.mergeAlong
#cc_surface_check ResourceSystem.layoutAlong
#cc_surface_check ResourceSystem.layoutAt_mergeAlong
#cc_surface_check ResourceSystem.close_mergeAlong
#cc_surface_check Converter.attachAlong
#cc_surface_check Converter.layoutAt_attachAlong
#cc_surface_check Converter.attachAlong_of_not_provides
#cc_surface_check Converter.close_attachAlong

end CarrierDemo

end RandomSystems.CC
