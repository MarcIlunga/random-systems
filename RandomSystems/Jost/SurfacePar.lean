/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceAttach
import RandomSystems.TypedTensor
import RandomSystems.Jost.SurfaceLint

/-!
# The authoring surface, part 3: parallel composition at disjoint interface sets

Jost's `[R, S]` (§2.2.2, printed p. 17) composes resources whose **interface
sets are disjoint**: the composite "provides each party access to the
corresponding interfaces of all subsystems", and its interface set is the
union `⋃ᵢ I_i`.  That is the operation this module surfaces:

```
R : ResourceAt S layoutL   S : ResourceAt S layoutR
------------------------------------------------------
      R ∥ S : ResourceAt S (Sum.elim layoutL layoutR)
```

over `I ⊕ J` — and on the bundled carrier of part 4,
`ResourceSystem S I → ResourceSystem S J → ResourceSystem S (I ⊕ J)`.

**The notation.**  Jost writes `[R, S]`; `[·, ·]` is list syntax in Lean, so
the operation is rendered `∥`, which is Maurer11 §4.4 eq. (3)'s own notation
for it (`d(R ∥ R', S ∥ S') ≤ d(R,S) + d(R',S')` — `close_par` below).  The
two spellings name one operation; `∥` is what the reader sees and `[R, S]`
is what the thesis prints.

## The carrier is index-varying, and Maurer11 Def. 1 is untouched

Parallel composition changes the interface set, so the surface's `Φ` is a
*family* `I ↦ ResourceSystem S I` rather than one set with operations.  This
is not in tension with Maurer11 Def. 1.  Definition 1 asks that `Φ` be
closed under **converter attachment**, and fn. 9's *"the resulting system is
again a resource with the same interface set"* is a constraint on
attachment — which on this surface is still an endo-operation
`Converter.attachAt : ResourceSystem S I → ResourceSystem S I` (part 4,
total).  Parallel composition is never asked to stay inside one `Φ`: Jost
defines it only across disjoint interface sets, so changing the index is
its definition, not a defect of the encoding.  Relatedly, the "same
interface set" side condition of `d(R, S)` is a *theorem* on the bundled
carrier rather than a convention — `ResourceSystem.layoutAt_eq_of_close`
(part 4): two resource systems at any finite distance necessarily agree on
layout, differing layouts sitting at `⊤`.

## What the disjoint form saves, and where the coding went

The merged reading of `∥` — every interface keeps its owner and now provides
*both* components' services — needs an alphabet coding at each shared
interface (`HasSumCode`).  The disjoint form needs none: the composite's
boundary is `Sum.elim layoutL layoutR`, whose fibre at `Sum.inl i` **is**
`layoutL i` by iota (`TypedTensor.lean`'s module header).  Moreover the
decomposition is unique (`tensor_inj`) where the merged one has to appeal to
an axiom of the coding class.

`SumService`, `Services.free` and the `HasSumCode` instance below are
therefore **not** what `∥` is built from any more.  They keep a role, and it
is the one they are actually for: they are the coding for **merging** a
block of interfaces into one — the operation an n-ary converter needs, since
a converter reaching two interfaces at once is a unary converter at their
merge (`Converter.attachAlong`, part 4, and `DependentDDS.mergeTwo`).  A
development whose converters reach more than one interface at a time
declares its resources over `S.free`, exactly as before; what changed is
*why*.

Merging is an isometry and injective, but — unlike a bijective re-indexing —
it is **not invertible** (`not_surjective_mergeBlock`): the merged boundary
admits resources answering a block query on the wrong side of the coded sum.
Nothing here uses it backwards.

The operation itself and its law are the kernel's
(`DependentRandomSystem.tensor`, `edist_tensor_le` — Maurer11 eq. (3) on the
contextual fibres); this module only surfaces them.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource

/-- Service names freely closed under pairing — the vocabulary a development
needs when one converter reaches **two** interfaces at once, since such a
converter is a unary converter at the merge of the two, whose service is the
paired one. -/
@[cc_surface]
inductive SumService (base : Type) : Type
  | base (service : base)
  | sum (left right : SumService base)
  deriving DecidableEq

namespace SumService

variable {S : Services}

/-- Inputs of a merged service: tagged sums of the merged interfaces'. -/
@[cc_surface]
def inputs (S : Services) : SumService S.Service → Type
  | .base service => S.In service
  | .sum left right => inputs S left ⊕ inputs S right

/-- Outputs of a merged service: tagged sums of the merged interfaces'. -/
@[cc_surface]
def outputs (S : Services) : SumService S.Service → Type
  | .base service => S.Out service
  | .sum left right => outputs S left ⊕ outputs S right

end SumService

/-- The free sum-closure of a development's services: same base names
(embedded via `.base`), paired services carry tagged-sum alphabets.  A
development whose converters reach several interfaces at once declares its
resources over `S.free`, so that the merge of any two interfaces has a
service to land on. -/
@[cc_surface]
def Services.free (S : Services) : Services where
  Service := SumService S.Service
  In := SumService.inputs S
  Out := SumService.outputs S

/-- The merge obligations of the free closure are definitional: the paired
service's alphabets **are** the tagged sums, so the coding a merge needs is
`Equiv.refl` and constructor injectivity — declared once, here, for every
development. -/
instance (S : Services) : HasSumCode (S.free).sig where
  sumCode := SumService.sum
  inputEquiv _ _ := Equiv.refl _
  outputEquiv _ _ := Equiv.refl _
  sumCode_inj paired := by
    injection paired with left right
    exact ⟨left, right⟩

namespace ResourceAt

variable {S : Services} {I J : Type} [DecidableEq I] [DecidableEq J]

/-- **`[R, S]`** (Jost §2.2.2, printed p. 17; Fig. 2.1), rendered `∥`
(Maurer11 eq. (3)'s notation for the same operation — `[·,·]` is list
syntax): two resources with **disjoint** interface sets, side by side.  Each
interface of the composite is an interface of exactly one component and
provides exactly what it provided there.  Well-defined on behaviors by the
kernel's congruence. -/
@[cc_surface]
noncomputable def par {layoutL : S.Layout I} {layoutR : S.Layout J}
    (left : ResourceAt S layoutL) (right : ResourceAt S layoutR) :
    ResourceAt S (Sum.elim layoutL layoutR) :=
  DependentRandomSystem.tensor left right

@[inherit_doc] scoped infixr:70 " ∥ " => ResourceAt.par

/-- Parallel composition does not expand behavioral distance beyond the
sum of the components' (Maurer11 eq. (3)): the parallel face of the
composition theorem's error accounting.

**Demoted** (Maurer standard): states the raw metric projection; the
papers write `≈_ε`.  Surface successor: `ResourceAt.close_par` (eq. (3)
in `≈[ε]` — `Jost/SurfaceCarrier.lean`). -/
@[cc_surface_demoted]
theorem edist_par_le {layoutL : S.Layout I} {layoutR : S.Layout J}
    (leftA leftB : ResourceAt S layoutL)
    (rightA rightB : ResourceAt S layoutR) :
    edist (leftA ∥ rightA) (leftB ∥ rightB) ≤
      edist leftA leftB + edist rightA rightB :=
  DependentRandomSystem.edist_tensor_le leftA leftB rightA rightB

end ResourceAt

end RandomSystems.CC
