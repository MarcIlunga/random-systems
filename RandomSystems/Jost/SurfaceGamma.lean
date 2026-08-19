/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceMergeLocality
import RandomSystems.Jost.SurfaceMergePar

/-!
# The authoring surface, part 6: the algebra at a connection

`α •[i] R` has an algebra — attachments at distinct interfaces commute
(`Converter.attachAt_comm`), and one landing in a factor of `[R, T]` passes the
other factor through (`Converter.attachAt_par_left`).  This module gives the
same two laws at Jost's connection function γ, where `α ••[γ] R` reaches TWO
interfaces at once.

**The reading that makes both work.**  `α ••[γ] R` is *not* one operation: it
is a **re-addressing** followed by an **action**.  The re-addressing is
`R.mergeAlong γ` — the two interfaces γ reaches, addressed as one — and the
action is an ordinary `•[·]` at the single interface the connection produced
(`γ.produced`).  The two halves behave completely differently under the
algebra:

* the *action* half commutes exactly as `•[i]` does;
* the *re-addressing* half cannot move at all, because it **changes the
  interface set**, and an operation that changes the interface set has no
  order to be exchanged with.

So the γ-level laws are the interface-level laws with the merges frozen in
place.  That is the honest content of both statements below, and it is why
neither is symmetric in the way the interface-level ones are.

* `Converter.attachAlong_comm` (Jost Prop. 2.2.3, clause 1 at γ) — a plain
  equality, no transport.  The side condition is Jost's own *`img γ₂` misses
  `img γ₁`*, and at the type level it says: γ₂ must not reach the one interface
  γ₁ produced.
* `Converter.attachAlong_par_left` (Jost Prop. 2.2.3, clause 2 at γ) — an
  equality up to one **explicit renaming**, and here the renaming is not
  avoidable: the two sides genuinely name the same interfaces differently,
  `(rest ⊕ J) ⊕ Unit` against `(rest ⊕ Unit) ⊕ J`.  Renaming costs no
  advantage, so the `≈[ε]` corollary `Converter.close_attachAlong_par_left`
  carries the same ε as its interface-level twin.

The two kernel facts underneath are `ResourceSystem.mergeAlong_attachAt_untouched`
(`Jost/SurfaceMergeLocality.lean` — merging is *local*) and
`ResourceSystem.mergeAlong_par_left` (`Jost/SurfaceMergePar.lean` — merging
inside a factor is merging the factor); the third ingredient,
`Converter.attachAt_reindex` (`Jost/SurfaceShuffle.lean`), is what lets an
action cross a renaming.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open scoped Converter ResourceSystem

namespace ResourceSystem

variable {S : Services} {K rest : Type} [DecidableEq K] [DecidableEq rest]

/-- **Merging is local**, addressed through `Connection.relocate`: a converter
attached anywhere outside `img γ` may be attached before or after the merge,
and afterwards it sits where γ left that interface.  The `relocate` spelling is
what makes the side condition a single decidable test — `γ.relocate i` is the
connection's produced interface exactly when γ reaches `i`. -/
@[cc_surface]
theorem mergeAlong_attachAt [HasSumCode S.sig] (γ : Connection K rest)
    (interface : K) (avoids : γ.relocate interface ≠ γ.produced)
    {source target : S.Service} (converter : Converter S source target)
    (resource : ResourceSystem S K) :
    (converter •[interface] resource).mergeAlong γ =
      converter •[γ.relocate interface] (resource.mergeAlong γ) := by
  obtain ⟨name, rfl, relocated⟩ :=
    Connection.exists_untouched_of_relocate_ne γ avoids
  rw [relocated]
  exact mergeAlong_attachAt_untouched γ name converter resource

end ResourceSystem

namespace Converter

/-! ## Jost Proposition 2.2.3, clause 1, at a connection -/

variable {S : Services} {K rest rest₂ : Type}
  [DecidableEq K] [DecidableEq rest] [DecidableEq rest₂]

/-- **Two connections commute when their images are disjoint** (Jost
Prop. 2.2.3, clause 1, printed p. 18) — a plain equality, no transport.

The type-level reading of Jost's side condition.  `α ••[γ₁] R` lives at
`(I_P \ img γ₁) ∪ I_out`, so a second connection γ₂ is a connection *on that
set*, and "γ₂ avoids γ₁'s image" is not a statement about `I_P` at all: the
interfaces γ₁ consumed are gone, and what γ₂ must miss is the single interface
γ₁ **produced**.  That is `γ₂.relocate γ₁.produced ≠ γ₂.produced`, one
decidable test.

What commutes is the two converters' **actions**.  γ₁'s re-addressing stays
where it is — the merge changed the interface set, so it has no order to be
exchanged with — and on the right `α` is found at the ordinary interface γ₂
left for it, `γ₂.relocate γ₁.produced`.  Read the equation as: *whether α acts
before or after β is immaterial; only the order of the two re-addressings is
forced.* -/
@[cc_surface]
theorem attachAlong_comm [HasSumCode S.sig]
    {source₁ target₁ source₂ target₂ : S.Service}
    (inner : Converter S source₁ target₁) (outer : Converter S source₂ target₂)
    (γ₁ : Connection K rest) (γ₂ : Connection (rest ⊕ Unit) rest₂)
    (avoids : γ₂.relocate γ₁.produced ≠ γ₂.produced)
    (resource : ResourceSystem S K) :
    outer ••[γ₂] (inner ••[γ₁] resource) =
      inner •[γ₂.relocate γ₁.produced]
        (outer ••[γ₂] (resource.mergeAlong γ₁)) := by
  show outer •[γ₂.produced]
      ((inner •[γ₁.produced] (resource.mergeAlong γ₁)).mergeAlong γ₂) = _
  rw [ResourceSystem.mergeAlong_attachAt γ₂ γ₁.produced avoids inner
    (resource.mergeAlong γ₁)]
  exact Converter.attachAt_comm (Ne.symm avoids) outer inner _

/-! ## Jost Proposition 2.2.3, clause 2, and Theorem 2.2.5 (2), at a connection -/

variable {I J : Type} [DecidableEq I] [DecidableEq J]

/-- **A connection landing wholly in one factor passes the other through**
(Jost Prop. 2.2.3, clause 2, printed p. 18, at γ): `π^γ [R, T] = [π^γ R, T]`,
where γ reaches two interfaces of `R` only.

Unlike its interface-level twin `Converter.attachAt_par_left`, this one is an
equality **up to an explicit renaming**, and the renaming is not an artefact:
made on the composite, the connection leaves `(rest ⊕ J) ⊕ Unit` — the
survivors of `R`, then all of `T`, then the converter's outer interface; made
inside the factor and composed afterwards, it leaves `(rest ⊕ Unit) ⊕ J`.  The
same interfaces, two orders of writing them, related by
`Connection.outerShuffle`.  Renaming costs nothing (`close_reindex_iff`), which
is why the `≈[ε]` corollary below spends no error on it. -/
@[cc_surface]
theorem attachAlong_par_left [HasSumCode S.sig] {source target : S.Service}
    (converter : Converter S source target) (γ : Connection I rest)
    (left : ResourceSystem S I) (right : ResourceSystem S J) :
    converter ••[γ.parLeft J] (left ∥ right) =
      ResourceSystem.reindex (Connection.outerShuffle rest J)
        ((converter ••[γ] left) ∥ right) := by
  show converter •[Sum.inr ()]
    ((left ∥ right).mergeAlong (γ.parLeft J)) = _
  rw [ResourceSystem.mergeAlong_par_left γ left right,
    show (converter ••[γ] left) ∥ right =
        converter •[Sum.inl (Sum.inr ())] ((left.mergeAlong γ) ∥ right) from
      (Converter.attachAt_par_left converter (Sum.inr ())
        (left.mergeAlong γ) right).symm,
    Converter.attachAt_reindex converter (Connection.outerShuffle rest J)
      (Sum.inl (Sum.inr ())) ((left.mergeAlong γ) ∥ right)]
  rfl

/-- **Jost Theorem 2.2.5 (2) at a connection.**  Jost's proof is one line —
*"the second property follows from Proposition 2.2.3:
`π[R,T] = [πR,T] ⊆ [S,T]`"* — and this is that line for a converter that
reaches two interfaces: rewrite by clause 2, compose in parallel with the
untouched `T` at no extra error (eq. (3) with `0` on the right flank), and
rename the interface set at no error at all.

A construction statement for `R` therefore yields one for `[R, T]` with the
same ε and the same protocol, exactly as in the one-interface case. -/
@[cc_surface]
theorem close_attachAlong_par_left [HasSumCode S.sig] {epsilon : ℝ}
    (nonneg : 0 ≤ epsilon) {source target : S.Service}
    (converter : Converter S source target) (γ : Connection I rest)
    {assumed : ResourceSystem S I} {ideal : ResourceSystem S (rest ⊕ Unit)}
    (other : ResourceSystem S J)
    (construction : (converter ••[γ] assumed) ≈[epsilon] ideal) :
    (converter ••[γ.parLeft J] (assumed ∥ other)) ≈[epsilon]
      ResourceSystem.reindex (Connection.outerShuffle rest J) (ideal ∥ other) := by
  rw [attachAlong_par_left]
  exact ResourceSystem.close_reindex (Connection.outerShuffle rest J)
    (ResourceSystem.close_par_left nonneg other construction)

end Converter

/-! ## Receipts -/

/-- info: 'RandomSystems.CC.ResourceSystem.mergeAlong_attachAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResourceSystem.mergeAlong_attachAt

/-- info: 'RandomSystems.CC.Converter.attachAlong_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAlong_comm

/-- info: 'RandomSystems.CC.Converter.attachAlong_par_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.attachAlong_par_left

/-- info: 'RandomSystems.CC.Converter.close_attachAlong_par_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Converter.close_attachAlong_par_left

#cc_surface_check ResourceSystem.mergeAlong_attachAt
#cc_surface_check Converter.attachAlong_comm
#cc_surface_check Converter.attachAlong_par_left
#cc_surface_check Converter.close_attachAlong_par_left

end RandomSystems.CC
