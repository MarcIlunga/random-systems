/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfacePar
import RandomSystems.Jost.SurfaceCarrier

/-!
# The authoring surface, part 4: single-world resources meet the algebra

`Interfaces` (one signature per interface, `Jost/Surface.lean`) and
`Services` (a development's alphabet pairs, `Jost/SurfaceAttach.lean`) were
built in separate passes; this module connects them so a single-world
resource feeds `∥` and `attach` without re-declaration.  Since `∥` composes
at **disjoint** interface sets it needs no coding, so `Resource.par` is
`ResourceAt.par` directly; the free-closure embedding below is what a
development needs when a converter reaches *two* interfaces at once (the
merge coding — `Jost/SurfacePar.lean`).

The load-bearing observation is that the connection is DEFINITIONAL: an
interface declaration IS the one-service-per-interface development
(`Interfaces.services`), its boundary IS the identity layout, and the free
closure's base layout carries definitionally the same query and answer
alphabets.  What is *not* definitional is the carrier index: `Resource F`
and its image in the free closure live over different signature universes
(`F.Iface` vs `SumService F.Iface` codes), so the embedding into the free
closure is a genuine map — built here at every level (deterministic, law,
resource) with the quotient step discharged through metric full
abstraction, and proven to be an isometry.

`Resource.par` gives Fig. 2.1's `[R, S]` directly on two single-world
resources over the same interface declaration, at the disjoint union of the
two interface sets, with eq. (3) restated against the original resources.

Cross-interface-set padding (`Interfaces.pad` — Jost's `[R, S]` over
*disjoint* interface sets, each side inert at the other's interfaces) is
delivered at the interface/realization level; its resource-level embedding
is the identified remaining wiring (see the docstring at the end).
-/

namespace RandomSystems.CC

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource

/-! ## 1. An interface declaration IS a one-service-per-interface development -/

/-- The development whose services are exactly `F`'s interfaces. -/
def Interfaces.services (F : Interfaces) : Services where
  Service := F.Iface
  In := F.In
  Out := F.Out

/-- The identity layout: each interface provides its own service. -/
abbrev Interfaces.selfLayout (F : Interfaces) :
    (F.services).Layout F.Iface := fun interface => interface

/-- **The bridge is definitional**: a single-world resource is literally a
resource of the one-service-per-interface development at the identity
layout. -/
theorem resource_eq_resourceAt (F : Interfaces) :
    Resource F = ResourceAt F.services F.selfLayout :=
  rfl

/-! ## 2. Embedding into the free closure

The base layout of the free closure carries definitionally the same query
and answer alphabets, but the signature universes differ (`F.Iface` vs
`SumService F.Iface` codes), so this is a genuine map: repackage the
deterministic system (fields transfer by definitional equality), push the
law forward, and descend to the quotient through metric full
abstraction. -/

/-- The base layout in the free closure: interface `i` provides the base
service `.base i`. -/
abbrev Interfaces.freeLayout (F : Interfaces) :
    (F.services.free).Layout F.Iface := fun interface => .base interface

/-- Deterministic embedding into the free closure: every field transfers
definitionally (the base-service alphabets reduce to `F`'s). -/
def Interfaces.embedFreeDDS (F : Interfaces)
    (system : DependentDDS F.sig F.bnd) :
    DependentDDS (F.services.free).sig F.freeLayout where
  domain := system.domain
  empty_not_mem := system.empty_not_mem
  prefix_closed := system.prefix_closed
  output := system.output

/-- Flattening commutes with the deterministic embedding — definitionally. -/
theorem Interfaces.flatten_embedFreeDDS (F : Interfaces)
    (system : DependentDDS F.sig F.bnd) :
    DependentDDS.flatten (F.embedFreeDDS system) = DependentDDS.flatten system :=
  rfl

/-- Law-level embedding into the free closure. -/
noncomputable def Interfaces.embedFreeLaw (F : Interfaces)
    (law : DependentPDS F.sig F.bnd) :
    DependentPDS (F.services.free).sig F.freeLayout :=
  Dist.fTransform F.embedFreeDDS law

/-- Flattening sees through the law-level embedding. -/
theorem Interfaces.flatten_embedFreeLaw (F : Interfaces)
    (law : DependentPDS F.sig F.bnd) :
    DependentPDS.flatten (F.embedFreeLaw law) = DependentPDS.flatten law := by
  unfold Interfaces.embedFreeLaw DependentPDS.flatten
  rw [Dist.fTransform_comp]
  exact congrArg (fun f => Dist.fTransform f law)
    (funext fun system => F.flatten_embedFreeDDS system)

/-- The embedded law of a normalized law is normalized. -/
theorem Interfaces.embedFreeLaw_isProbDist (F : Interfaces)
    {law : DependentPDS F.sig F.bnd} (normalized : law.isProbDist) :
    (F.embedFreeLaw law).isProbDist :=
  (Dist.isProbDist_fTransform _ normalized.nonNeg).mpr normalized

/-- **Resource-level embedding into the free closure.**  Well-defined on
behaviors because flattening sees through the embedding and typed
contextual equivalence is strict equivalence of the flattenings (metric
full abstraction). -/
noncomputable def Resource.embedFree {F : Interfaces} :
    Resource F → ResourceAt F.services.free F.freeLayout :=
  Quotient.lift
    (fun prob => DependentRandomSystem.ofProb
      ⟨F.embedFreeLaw prob.val, F.embedFreeLaw_isProbDist prob.property⟩)
    (by
      intro P Q equivalent
      refine Quotient.sound ?_
      show DependentPDS.ContextuallyEquivalent _ _
      rw [DependentPDS.contextually_equivalent_iff_flatten_equivalent,
        F.flatten_embedFreeLaw, F.flatten_embedFreeLaw]
      exact (DependentPDS.contextually_equivalent_iff_flatten_equivalent
        P.val Q.val).mp equivalent)

@[simp]
theorem Resource.embedFree_sampleInit {F : Interfaces} {Omega : Type*}
    (family : Omega → F.Realization) (seed : Dist Omega)
    (normalized : seed.isProbDist) :
    (Resource.sampleInit family seed normalized).embedFree =
      DependentRandomSystem.ofProb
        ⟨F.embedFreeLaw (Machine.lawOf family seed normalized).val,
          F.embedFreeLaw_isProbDist (Machine.lawOf family seed normalized).property⟩ :=
  rfl

/-- **The embedding is an isometry**: behavioral distance is computed on the
flattenings, and the embedding does not move them.  (Kernel form; the
surface statement is `Resource.close_embedFree` below.) -/
theorem Resource.edist_embedFree {F : Interfaces} (left right : Resource F) :
    edist left.embedFree right.embedFree = edist left right := by
  refine Quotient.inductionOn₂ left right fun P Q => ?_
  show DependentPDS.contextualEDist (F.embedFreeLaw P.val) (F.embedFreeLaw Q.val) =
    DependentPDS.contextualEDist P.val Q.val
  rw [DependentPDS.contextual_edist_eq_max_edist_flatten,
    DependentPDS.contextual_edist_eq_max_edist_flatten,
    F.flatten_embedFreeLaw, F.flatten_embedFreeLaw]
  rfl

open scoped ResourceSystem in
/-- The embedding preserves closeness in both directions (it is an
isometry): single-world resources are ε-close **iff** their free-closure
images are — so nothing about distinguishability is gained or lost by
moving to the algebra's world. -/
@[cc_surface]
theorem Resource.close_embedFree {F : Interfaces} {epsilon : ℝ}
    (left right : Resource F) :
    (left.embedFree ≈[epsilon] right.embedFree) ↔ (left ≈[epsilon] right) := by
  unfold ResourceSystem.close
  rw [Resource.edist_embedFree]

/-! ## 3. `[R, S]` on single-world resources -/

/-- Fig. 2.1's `[R, S]` for two resources over one interface declaration:
their interface sets side by side, each interface providing exactly what it
provided in its own copy.  No free closure is involved — the disjoint form of
`∥` needs no alphabet coding at all (`Jost/SurfacePar.lean`). -/
noncomputable def Resource.par {F : Interfaces} (left right : Resource F) :
    ResourceAt F.services (Sum.elim F.selfLayout F.selfLayout) :=
  ResourceAt.par (S := F.services) (layoutL := F.selfLayout)
    (layoutR := F.selfLayout) left right

@[inherit_doc] scoped infixr:70 " ∥ " => Resource.par

/-- Maurer11 eq. (3) for single-world resources: parallel composition does
not expand behavioral distance beyond the sum of the components'.  (Kernel
form; the surface statement is `Resource.close_par` below.) -/
theorem Resource.edist_par_le {F : Interfaces}
    (leftA leftB rightA rightB : Resource F) :
    edist (leftA ∥ rightA) (leftB ∥ rightB) ≤
      edist leftA leftB + edist rightA rightB :=
  ResourceAt.edist_par_le (S := F.services) leftA leftB rightA rightB

open scoped ResourceSystem in
/-- **Eq. (3)** (Maurer11 Def. 2) for single-world resources, in the
papers' notation: parallel composition is non-expanding against the
original resources, through the embedding isometry. -/
@[cc_surface]
theorem Resource.close_par {F : Interfaces} {epsilonL epsilonR : ℝ}
    (nonnegL : 0 ≤ epsilonL) (nonnegR : 0 ≤ epsilonR)
    {leftA leftB rightA rightB : Resource F}
    (closeL : leftA ≈[epsilonL] leftB) (closeR : rightA ≈[epsilonR] rightB) :
    (leftA ∥ rightA) ≈[epsilonL + epsilonR] (leftB ∥ rightB) := by
  unfold ResourceSystem.close at *
  calc edist (leftA ∥ rightA) (leftB ∥ rightB)
      ≤ edist leftA leftB + edist rightA rightB :=
        Resource.edist_par_le leftA leftB rightA rightB
    _ ≤ ENNReal.ofReal epsilonL + ENNReal.ofReal epsilonR :=
        add_le_add closeL closeR
    _ = ENNReal.ofReal (epsilonL + epsilonR) :=
        (ENNReal.ofReal_add nonnegL nonnegR).symm

/-! ## 4. Cross-interface-set padding -/

/-- Jost's disjoint-union reading of `[R, S]`, boundary half: extend an
interface declaration by a foreign interface set at which the resource is
inert — the foreign inputs are `Empty`, so no query can ever be addressed
there. -/
def Interfaces.pad (F : Interfaces) (Foreign : Type) [DecidableEq Foreign] :
    Interfaces where
  Iface := F.Iface ⊕ Foreign
  In := Sum.elim F.In fun _ => Empty
  Out := Sum.elim F.Out fun _ => Empty

/-- Pad a realization: native queries step as before; foreign queries
cannot be formed (`Empty` input), so the clause is vacuous. -/
def Interfaces.padRealization (F : Interfaces) (Foreign : Type)
    [DecidableEq Foreign] (realization : F.Realization) :
    (F.pad Foreign).Realization where
  State := realization.State
  init := realization.init
  step state query :=
    match query with
    | ⟨.inl interface, input⟩ => realization.step state ⟨interface, input⟩
    | ⟨.inr _, input⟩ => input.elim

/-- Padded resources at the law level: the padded family under the same
seed law. -/
noncomputable def Resource.padSampleInit (F : Interfaces) (Foreign : Type)
    [DecidableEq Foreign] {Omega : Type*} (family : Omega → F.Realization)
    (seed : Dist Omega) (normalized : seed.isProbDist) :
    Resource (F.pad Foreign) :=
  Resource.sampleInit (fun omega => F.padRealization Foreign (family omega))
    seed normalized

/-! **Identified remaining wiring** (not discharged here, stated precisely):
the boundary-abstract embedding `Resource F → Resource (F.pad Foreign)` for
an *arbitrary* resource (not presented by a family).  Unlike the free-closure
embedding above, the padded query alphabet `Σ (j : F.Iface ⊕ Foreign), …` is
*equivalent* but not definitionally equal to `Σ (i : F.Iface), F.In i`, so
the deterministic transport is a relabelling, and the quotient descent needs
the padded analogue of `TypedParallel.lean`'s defining equation — a lemma
`flatten (padDDS s) = PFunPDS.relabel e f (flatten s)` for the evident query
and answer equivalences — after which `StrictContext.equivalent_relabel` and
`maxEDist_relabel` transport contextual equivalence and the metric exactly
as the parallel case does.  For resources authored on the surface
(families of realizations), `Resource.padSampleInit` above already covers
the use case without that machinery. -/

/-! ## 5. Demo: the showcase counter, composed with itself -/

namespace BridgeDemo

inductive CtrIface | user | audit
  deriving DecidableEq

inductive UserIn | ping
inductive AuditIn | read

def ctr : Interfaces where
  Iface := CtrIface
  In := fun | .user => UserIn | .audit => AuditIn
  Out := fun | .user => Unit | .audit => Nat

noncomputable def counterA : Resource ctr :=
  Resource.ofState (0 : Nat) fun n query =>
    match query with
    | ⟨.user, .ping⟩ => some (n + 1, ())
    | ⟨.audit, .read⟩ => some (n, n)

/-- Two independent counters side by side — `[R, R]`, on the disjoint union
of the two interface sets (four interfaces, two per copy). -/
noncomputable def twoCounters := counterA ∥ counterA

/-- The composite is a resource at the disjoint-union layout; distance to
itself is zero — a smoke check that the metric instances line up. -/
example : edist twoCounters twoCounters = 0 := by simp

end BridgeDemo

end RandomSystems.CC
