/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceCarrier
import RandomSystems.TypedInterfaceRelabel
import RandomSystems.TypedAttachRelabel
import RandomSystems.TypedTensorShuffle

/-!
# The authoring surface, part 5: renaming an interface set

Everything in parts 3–4 that changes the interface set does so *structurally*:
`∥` puts two sets side by side as `I ⊕ J`, and `••[γ]` replaces the two
interfaces a connection reaches by one, landing at `rest ⊕ Unit`.  Two terms
that a paper would call equal therefore routinely land at two different — but
canonically isomorphic — interface types: `[R,S]` at `I ⊕ J` against `[S,R]`
at `J ⊕ I`, `[[R,S],T]` against `[R,[S,T]]`, and a connection into one factor
of a parallel composition against the same connection made inside that factor.

This module supplies the operation those statements are stated through, its
one interaction law, and the first two laws that need it.

* `ResourceSystem.reindex` — **the same resource, its interfaces renamed**
  along a bijection.  Nothing about the resource changes: the boundary travels
  with the names and every interface keeps the service it provided.  It is an
  **isometry in both directions** (`close_reindex_iff`), so renaming spends no
  error and a `≈[ε]` statement may be read on either side of one.  That is
  what separates it from the other re-addressing on this surface — merging
  (`ResourceSystem.mergeAlong`) is an isometry too but is *not* invertible
  (`not_surjective_mergeBlock`) and may be used forward only.
* `Converter.attachAt_reindex` — **attaching commutes with renaming**.  A
  renaming performs no action, so there is nothing for it to interfere with;
  this is what lets a law proved at one spelling of an interface set be read
  at any other.
* `ResourceSystem.par_comm` / `par_assoc` — **`∥` is commutative and
  associative up to renaming**, with the `≈[0]` forms beside them.  Before
  the migration to disjoint interface sets these were blocked by a genuine
  re-*coding* obstruction; at disjoint interface sets nothing is left but the
  bijective shuffle.  The shuffle being available does not make the laws
  formal, though: the content is that `PFunDDS.par` is symmetric and
  associative under the swap and associator relabellings, lifted through the
  four-level tower (`RandomSystems/TypedTensorShuffle.lean`).

The connection vocabulary the γ-level algebra needs is here too, because it is
vocabulary about interface *names* rather than about behaviour:
`Connection.produced` (Jost's `I_out`), `Connection.relocate` (where a
connection leaves an interface it does not reach), `Connection.parLeft` (a
connection read on a parallel composition) and the two shuffles those force.
`Converter.attachAlong_id` closes the section: the unit law at a connection
returns the *merge*, not the resource, because a connection re-addresses even
when its converter does nothing.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource

namespace ResourceSystem

variable {S : Services} {I J : Type} [DecidableEq I] [DecidableEq J]

open scoped Converter ResourceSystem

/-- **The same resource, its interfaces renamed.**  Along a bijection of the
interface set: the interface called `rename i` afterwards is the interface
called `i` before, and it provides exactly what it provided.  A relabelling,
not an action — no converter is attached, no service is moved, and nothing is
merged. -/
@[cc_surface]
noncomputable def reindex (rename : I ≃ J) (resource : ResourceSystem S I) :
    ResourceSystem S J :=
  RandomSystems.CR18.TypedResource.Resource.relabelInterfaces rename resource

/-- A renamed interface provides what it provided under its old name. -/
@[cc_surface]
theorem layoutAt_reindex (rename : I ≃ J) (resource : ResourceSystem S I)
    (interface : I) :
    (reindex rename resource).layoutAt (rename interface) =
      resource.layoutAt interface :=
  congrArg resource.layoutAt (rename.symm_apply_apply interface)

/-- …read the other way round: the service at a new name is the service at the
old name it came from. -/
@[cc_surface]
theorem layoutAt_reindex_symm (rename : I ≃ J)
    (resource : ResourceSystem S I) (interface : J) :
    (reindex rename resource).layoutAt interface =
      resource.layoutAt (rename.symm interface) :=
  rfl

/-- **Renaming interfaces is an isometry**, in both directions: two resources
are ε-close exactly when their renamings are.  Renaming is invisible to a
distinguisher, so a `≈[ε]` statement may be read on either side of one and no
error accounting is spent crossing it.

Stated as an `↔` rather than as a one-way bound because the bijection has an
inverse — the contrast is `close_mergeAlong`, where the merge is an isometry
but not invertible and only the forward reading is available. -/
@[cc_surface]
theorem close_reindex_iff {epsilon : ℝ} (rename : I ≃ J)
    (left right : ResourceSystem S I) :
    ((reindex rename left) ≈[epsilon] (reindex rename right)) ↔
      (left ≈[epsilon] right) := by
  unfold close reindex
  rw [RandomSystems.CR18.TypedResource.Resource.edist_relabelInterfaces]

/-- The `≈[ε]` corollary an author cites: a construction statement survives a
renaming of the interface set unchanged, at the same ε. -/
@[cc_surface]
theorem close_reindex {epsilon : ℝ} (rename : I ≃ J)
    {left right : ResourceSystem S I} (close : left ≈[epsilon] right) :
    (reindex rename left) ≈[epsilon] (reindex rename right) :=
  (close_reindex_iff rename left right).mpr close

/-! ### `∥` is commutative and associative up to renaming

Jost defines `[R, S]` only at **disjoint** interface sets, so `[R,S]` and
`[S,R]` cannot be equal on the nose: they live at `I ⊕ J` and `J ⊕ I`.  What
is true — and is what a paper means when it treats `∥` as a commutative,
associative operation — is that the two differ by nothing but the names of
their interfaces.  Renaming costs no advantage (`close_reindex_iff`), so
neither law spends any of the composition theorem's error budget: the `≈[ε]`
forms below are at `ε = 0`. -/

section Shuffle

variable {K : Type} [DecidableEq K]

/-- **`∥` is commutative up to renaming**: `[R, Q]` and `[Q, R]` are the same
resource system, its interface set spelled `I ⊕ J` on one side and `J ⊕ I` on
the other.  Before the move to disjoint interface sets this was blocked by a
genuine re-*coding* obstruction — the two sides provided literally different
services at a shared interface; at disjoint interface sets nothing is left but
the bijective shuffle. -/
@[cc_surface]
theorem par_comm (left : ResourceSystem S I) (right : ResourceSystem S J) :
    left ∥ right = reindex (Equiv.sumComm J I) (right ∥ left) :=
  RandomSystems.CR18.TypedResource.Resource.tensor_comm left right

/-- **`∥` is associative up to renaming**: how a stack of three resources is
bracketed is a fact about the spelling of its interface set and nothing
else. -/
@[cc_surface]
theorem par_assoc (first : ResourceSystem S I) (second : ResourceSystem S J)
    (third : ResourceSystem S K) :
    (first ∥ second) ∥ third =
      reindex (Equiv.sumAssoc I J K).symm (first ∥ (second ∥ third)) :=
  RandomSystems.CR18.TypedResource.Resource.tensor_assoc first second third

/-- Commutativity in the papers' notation, at **zero** error: reordering a
parallel composition is free. -/
@[cc_surface]
theorem close_par_comm (left : ResourceSystem S I)
    (right : ResourceSystem S J) :
    (left ∥ right) ≈[0] reindex (Equiv.sumComm J I) (right ∥ left) :=
  (close_zero_iff _ _).mpr (par_comm left right)

/-- Associativity in the papers' notation, at **zero** error: rebracketing a
parallel composition is free. -/
@[cc_surface]
theorem close_par_assoc (first : ResourceSystem S I)
    (second : ResourceSystem S J) (third : ResourceSystem S K) :
    ((first ∥ second) ∥ third) ≈[0]
      reindex (Equiv.sumAssoc I J K).symm (first ∥ (second ∥ third)) :=
  (close_zero_iff _ _).mpr (par_assoc first second third)

end Shuffle

end ResourceSystem

namespace Converter

variable {S : Services} {I J : Type} [DecidableEq I] [DecidableEq J]

open scoped Converter ResourceSystem

/-- **Attaching commutes with renaming.**  A converter attached at `i` and
then found under the new name `rename i`, or attached at `rename i` after the
renaming: the same resource system.  Renaming moves no service and performs no
action, so there is nothing for it to interfere with — and this is what lets a
law stated at one spelling of an interface set be read at any other. -/
@[cc_surface]
theorem attachAt_reindex {source target : S.Service}
    (converter : Converter S source target) (rename : I ≃ J) (interface : I)
    (resource : ResourceSystem S I) :
    ResourceSystem.reindex rename (converter •[interface] resource) =
      converter •[rename interface] (ResourceSystem.reindex rename resource) :=
  RandomSystems.CR18.TypedResource.Resource.relabelInterfaces_act rename
    converter interface resource

end Converter

/-! ## Where a connection sends an interface

A connection consumes two interfaces and produces one.  Every *other*
interface survives, under a new name: Jost's `(I_P \ img γ) ∪ I_out` keeps it
in the first summand.  `Connection.relocate` is that renaming, made total by
sending the two consumed interfaces to the produced one — so that a single
decidable test, `γ.relocate i ≠ Sum.inr ()`, says "γ does not reach `i`". -/

namespace Connection

variable {K rest : Type}

/-- **The interface a connection produces** — Jost's `I_out`, the single outer
interface the converter provides once the connection is made.  It is the
`Sum.inr ()` of `(I_P \ img γ) ∪ I_out`, named so that statements about *which*
interface a later connection may not reach can be written without spelling a
tag. -/
@[cc_surface]
def produced (_ : Connection K rest) : rest ⊕ Unit := Sum.inr ()

/-- **Where a connection leaves an interface.**  An interface the connection
does not reach keeps its own slot, `Sum.inl` of its name in `rest`; the two it
does reach are consumed, and both are sent to the connection's single outer
interface `Sum.inr ()`.  So `γ.relocate i ≠ Sum.inr ()` is exactly *`i` is not
in the image of γ*. -/
@[cc_surface]
def relocate (γ : Connection K rest) (interface : K) : rest ⊕ Unit :=
  Sum.map id (fun _ => ()) (γ.split interface)

@[simp]
theorem relocate_untouched (γ : Connection K rest) (name : rest) :
    γ.relocate (γ.untouched name) = Sum.inl name := by
  show Sum.map id (fun _ => ()) (γ.split (γ.split.symm (Sum.inl name))) =
    Sum.inl name
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem relocate_first (γ : Connection K rest) :
    γ.relocate γ.first = Sum.inr () := by
  show Sum.map id (fun _ => ())
    (γ.split (γ.split.symm (Sum.inr (Sum.inl ())))) = Sum.inr ()
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem relocate_second (γ : Connection K rest) :
    γ.relocate γ.second = Sum.inr () := by
  show Sum.map id (fun _ => ())
    (γ.split (γ.split.symm (Sum.inr (Sum.inr ())))) = Sum.inr ()
  rw [Equiv.apply_symm_apply]
  rfl

/-- **An interface a connection does not reach has a name among the survivors**,
and `relocate` is that name.  The decidable side condition
`γ.relocate i ≠ Sum.inr ()` therefore carries all the information the
interface-level laws need about "`i` is outside `img γ`". -/
@[cc_surface]
theorem exists_untouched_of_relocate_ne (γ : Connection K rest) {interface : K}
    (avoids : γ.relocate interface ≠ Sum.inr ()) :
    ∃ name : rest, interface = γ.untouched name ∧
      γ.relocate interface = Sum.inl name := by
  rcases split : γ.split interface with name | reached
  · refine ⟨name, ?_, ?_⟩
    · show interface = γ.split.symm (Sum.inl name)
      rw [← split, Equiv.symm_apply_apply]
    · show Sum.map id (fun _ => ()) (γ.split interface) = Sum.inl name
      rw [split]
      rfl
  · refine absurd ?_ avoids
    show Sum.map id (fun _ => ()) (γ.split interface) = Sum.inr ()
    rw [split]
    rfl

/-! ### A connection into one factor of a parallel composition -/

/-- The bijection between the two ways of writing the same interface set when
a connection is made inside the **left** factor of `[R, T]`: doing it inside
the factor leaves `(rest ⊕ Unit) ⊕ J`, doing it on the composite leaves
`(rest ⊕ J) ⊕ Unit`.  The same interfaces, two spellings. -/
def outerShuffle (rest J : Type) : (rest ⊕ Unit) ⊕ J ≃ (rest ⊕ J) ⊕ Unit :=
  (Equiv.sumAssoc rest Unit J).trans
    ((Equiv.sumCongr (Equiv.refl rest) (Equiv.sumComm Unit J)).trans
      (Equiv.sumAssoc rest J Unit).symm)

/-- The bijection with the connection's two-interface block in place of its
outer interface — the shuffle the *split* of `[R, T]` factors through. -/
def blockShuffle (rest J : Type) :
    (rest ⊕ (Unit ⊕ Unit)) ⊕ J ≃ (rest ⊕ J) ⊕ (Unit ⊕ Unit) :=
  (Equiv.sumAssoc rest (Unit ⊕ Unit) J).trans
    ((Equiv.sumCongr (Equiv.refl rest) (Equiv.sumComm (Unit ⊕ Unit) J)).trans
      (Equiv.sumAssoc rest J (Unit ⊕ Unit)).symm)

/-- **A connection into the left factor, read on the composite.**  Jost's `γ`
lands in `R`'s interfaces; on `[R, T]` it reaches the same two, now
`Sum.inl`-tagged, and leaves alone everything it left alone in `R` together
with the whole of `T`. -/
@[cc_surface]
def parLeft {I rest : Type} (γ : Connection I rest) (J : Type) :
    Connection (I ⊕ J) (rest ⊕ J) where
  split := (Equiv.sumCongr γ.split (Equiv.refl J)).trans (blockShuffle rest J)

@[simp]
theorem parLeft_first {I rest : Type} (γ : Connection I rest) (J : Type) :
    (γ.parLeft J).first = Sum.inl γ.first :=
  rfl

@[simp]
theorem parLeft_second {I rest : Type} (γ : Connection I rest) (J : Type) :
    (γ.parLeft J).second = Sum.inl γ.second :=
  rfl

@[simp]
theorem parLeft_untouched_inl {I rest : Type} (γ : Connection I rest)
    (J : Type) (name : rest) :
    (γ.parLeft J).untouched (Sum.inl name) = Sum.inl (γ.untouched name) :=
  rfl

@[simp]
theorem parLeft_untouched_inr {I rest : Type} (γ : Connection I rest)
    (J : Type) (interface : J) :
    (γ.parLeft J).untouched (Sum.inr interface) = Sum.inr interface :=
  rfl

end Connection

/-! ## The unit law at a connection

`α ••[γ] R` is a re-addressing followed by an action.  When the converter is
the identity there is no action left — but the re-addressing stays, because it
changed the interface set.  So the connection's unit law does not return `R`;
it returns the merge, and that is the honest statement. -/

namespace Converter

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

open scoped ResourceSystem

/-- **The identity converter at a connection leaves exactly the merge.**  The
γ-level companion of `Converter.attachAt_id`: attaching the memoryless
converter that renames nothing along a connection performs no action, so what
remains is the re-addressing the connection performed — the two interfaces it
reaches, addressed as one.  Total, like `attachAt_id`: no hypothesis that the
connection faces the converter's source. -/
@[cc_surface]
theorem attachAlong_id [HasSumCode S.sig] {service : S.Service}
    (γ : Connection K rest) (resource : ResourceSystem S K) :
    (Converter.ofMaps id id : Converter S service service) ••[γ] resource =
      resource.mergeAlong γ :=
  Converter.attachAt_id (Sum.inr ()) (resource.mergeAlong γ)

end Converter

/-! ## Receipts -/

/-- info: 'RandomSystems.CC.ResourceSystem.close_reindex_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.close_reindex_iff

/-- info: 'RandomSystems.CC.Connection.exists_untouched_of_relocate_ne' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Connection.exists_untouched_of_relocate_ne

/-- info: 'RandomSystems.CC.ResourceSystem.par_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.par_comm

/-- info: 'RandomSystems.CC.ResourceSystem.par_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.par_assoc

/-- info: 'RandomSystems.CC.Converter.attachAt_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAt_reindex

/-- info: 'RandomSystems.CC.Converter.attachAlong_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAlong_id

#cc_surface_check ResourceSystem.reindex
#cc_surface_check ResourceSystem.layoutAt_reindex
#cc_surface_check ResourceSystem.layoutAt_reindex_symm
#cc_surface_check ResourceSystem.close_reindex_iff
#cc_surface_check ResourceSystem.close_reindex
#cc_surface_check ResourceSystem.par_comm
#cc_surface_check ResourceSystem.par_assoc
#cc_surface_check ResourceSystem.close_par_comm
#cc_surface_check ResourceSystem.close_par_assoc
#cc_surface_check Converter.attachAt_reindex
#cc_surface_check Connection.produced
#cc_surface_check Connection.relocate
#cc_surface_check Converter.attachAlong_id
#cc_surface_check Connection.exists_untouched_of_relocate_ne
#cc_surface_check Connection.parLeft

end RandomSystems.CC
