/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS
import RandomSystems.StepConverter

/-!
# The resource view: what a converter interacts with

CR18 Def 3.9 connects a converter's inner interface to `s⊥` (Def 3.3), never
to `s` itself: the object a converter interacts with is the **resource view**
`⟦S⟧ := S⊥` — a *fully defined* `(X, Y∪{⊥})`-system, total on every nonempty
history.  This module records the three facts that make "converters interact
with resources" precise:

* **Nothing is lost** (`fullyDefined_inj`): `S` is recoverable from `S⊥`, so
  the resource view is an *embedding* `DDS X Y ↪ Res X Y`.  `dom S` is
  recovered as the histories along which `S⊥` answers `some` at every
  nonempty prefix (validity makes `keptPrefix` the identity along such
  chains), and the outputs are the `some`-values.
* **Application factors** (`DDC.apply_congr_resourceView`): `α ·ᶜ S` depends
  on `S` only through `S⊥` — structurally, `connStep` reads only
  `output S⊥`.
* **A DDS is a single-interface resource** (`unitResourceEquiv`): CR18
  Def 3.5 resources with interface set `Unit` are exactly `(X,Y)`-DDSs, by
  reindexing histories along `List X ≅ List (Unit × X)`.

At the probabilistic level nothing new happens, by design: the resource view
and converter application push forward along `Dist.fTransform` (CR18 Def 3.17
composition = pushforward of the deterministic apply over the independent
product), preserving probability mass — *applying a converter to a random
system simply creates a random system*.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v w z

namespace PFunDDS

open scoped PFunDDS

variable {X : Type z} {Y : Type v}

/-- Membership in `S` at an extended history, read off the resource view: the
answers of `S` are exactly the `some`-answers of `S⊥` (along live histories). -/
theorem mem_iff_output_fullyDefined (S : DDS X Y) (l : List X) (x : X)
    (hl : l ∈ dom S ∨ l = []) (y : Y) :
    y ∈ S.1 (l ++ [x]) ↔
      output (S⊥) (l ++ [x]) (by rw [dom_fullyDefined]; simp) = some y := by
  constructor
  · intro hy
    have hmem : l ++ [x] ∈ dom S := Part.dom_iff_mem.mpr ⟨y, hy⟩
    rw [output_fullyDefined_append_of_mem S l x hl hmem]
    exact congrArg some (Part.mem_unique (Part.get_mem _) hy)
  · intro hout
    obtain ⟨hmem, hy⟩ := mem_of_output_fullyDefined_append_eq_some S l x hl hout
    rw [← hy]
    exact Part.get_mem _

/-- **The resource view loses nothing**: a DDS is recoverable from its fully
defined completion, so `⟦·⟧ = (·)⊥` embeds systems into single-interface
resources.  (Converse of the factoring: since `α ·ᶜ S` reads only `S⊥`, and
`S⊥` determines `S`, converters interact with exactly the information a
system carries.) -/
theorem fullyDefined_inj {S T : DDS X Y} (h : S⊥ = T⊥) : S = T := by
  have hout : ∀ (l : List X) (hlS : l ∈ dom (S⊥)) (hlT : l ∈ dom (T⊥)),
      output (S⊥) l hlS = output (T⊥) l hlT := by
    intro l hlS hlT
    have hpart : (S⊥).1 l = (T⊥).1 l := by rw [h]
    exact Part.mem_unique (hpart ▸ Part.get_mem hlS) (Part.get_mem hlT)
  apply Subtype.ext
  funext l
  induction l using List.reverseRecOn with
  | nil =>
      apply Part.ext
      intro y
      constructor
      · intro hy
        exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩ : [] ∈ dom S) (empty_not_mem S)
      · intro hy
        exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩ : [] ∈ dom T) (empty_not_mem T)
  | append_singleton l' x IH =>
      by_cases hl' : l' ∈ dom S ∨ l' = []
      · have hl'T : l' ∈ dom T ∨ l' = [] := by
          rcases hl' with hmem | rfl
          · left
            show (T.1 l').Dom
            rw [← IH]
            exact hmem
          · right; rfl
        apply Part.ext
        intro y
        rw [mem_iff_output_fullyDefined S l' x hl' y,
          mem_iff_output_fullyDefined T l' x hl'T y,
          hout (l' ++ [x]) (by rw [dom_fullyDefined]; simp)
            (by rw [dom_fullyDefined]; simp)]
      · have hl'ne : l' ≠ [] := fun hnil => hl' (Or.inr hnil)
        have hl'S : l' ∉ dom S := fun hmem => hl' (Or.inl hmem)
        have hnotS : l' ++ [x] ∉ dom S := fun hmem =>
          hl'S (prefix_closed S ⟨[x], rfl⟩ hl'ne hmem)
        have hnotT : l' ++ [x] ∉ dom T := fun hmem => by
          refine hl'S ?_
          show (S.1 l').Dom
          rw [IH]
          exact prefix_closed T ⟨[x], rfl⟩ hl'ne hmem
        apply Part.ext
        intro y
        constructor
        · intro hy
          exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩ : l' ++ [x] ∈ dom S) hnotS
        · intro hy
          exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩ : l' ++ [x] ∈ dom T) hnotT

/-- The resource view as an injection. -/
theorem fullyDefined_injective :
    Function.Injective (fullyDefined : DDS X Y → DDS X (Option Y)) :=
  fun _ _ h => fullyDefined_inj h

/-! ### CR18 Definition 3.5, single interface: a DDS *is* a resource -/

/-- A DDS as a CR18 Def 3.5 resource with the single interface `()`:
reindex histories along `List (Unit × X) → List X`. -/
def toUnitResource (S : DDS X Y) : Resource Unit X Y :=
  ⟨fun l => S.1 (l.map Prod.snd), by
    refine ⟨fun h => empty_not_mem S h, ?_⟩
    intro l₁ l₂ hpre hne hdom
    exact prefix_closed S (hpre.map Prod.snd)
      (fun hnil => hne (List.map_eq_nil_iff.mp hnil)) hdom⟩

/-- A single-interface resource as a DDS: reindex histories along
`List X → List (Unit × X)`. -/
def ofUnitResource (R : Resource Unit X Y) : DDS X Y :=
  ⟨fun l => R.1 (l.map fun x => ((), x)), by
    refine ⟨fun h => empty_not_mem R h, ?_⟩
    intro l₁ l₂ hpre hne hdom
    exact prefix_closed R (hpre.map _)
      (fun hnil => hne (List.map_eq_nil_iff.mp hnil)) hdom⟩

/-- **A DDS is exactly a single-interface resource** (CR18 Def 3.5 with
`I = Unit`): the reindexing maps are mutually inverse. -/
def unitResourceEquiv : DDS X Y ≃ Resource Unit X Y where
  toFun := toUnitResource
  invFun := ofUnitResource
  left_inv S := by
    apply Subtype.ext
    funext l
    show S.1 ((l.map fun x => ((), x)).map Prod.snd) = S.1 l
    rw [List.map_map]
    simp [Function.comp_def]
  right_inv R := by
    apply Subtype.ext
    funext l
    show R.1 ((l.map Prod.snd).map fun x => ((), x)) = R.1 l
    rw [List.map_map]
    have : ((fun x => ((), x)) ∘ Prod.snd : Unit × X → Unit × X) = id := by
      funext p
      cases p with
      | mk u x => cases u; rfl
    rw [this, List.map_id]

end PFunDDS

namespace PFunConverter

namespace DDC

open scoped PFunDDS

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- **Converter application factors through the resource view** (CR18 Def 3.9
reads the system only via Def 3.3's `s⊥`): systems with the same resource
view receive converters identically.  Structurally, `connStep` mentions the
system only as `output S⊥`; with `fullyDefined_inj` the hypothesis already
forces `S = T`, which is exactly the sense in which the resource view is the
*whole* interaction-relevant content of a system. -/
theorem apply_congr_resourceView (α : DDC U V X Y) {S T : PFunDDS.DDS X Y}
    (h : S⊥ = T⊥) : (α ·ᶜ S) = (α ·ᶜ T) := by
  rw [PFunDDS.fullyDefined_inj h]

end DDC

end PFunConverter

/-! ### Probabilistic lifts: converter application creates a random system -/

section Probabilistic

open PFunConverter
open scoped PFunConverter.DDC

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-- A deterministic converter applied to a probabilistic system: the
pushforward of the deterministic Def 3.9 apply.  *Applying a converter simply
creates a random system.* -/
noncomputable def PFunPDS.applyDDC (α : DDC U V X Y) (S : PFunPDS X Y) :
    PFunPDS U V :=
  Dist.fTransform (fun s => α ·ᶜ s) S

/-- Deterministic-converter application preserves probability mass (for a
non-negative law; over the signed carrier the unconditional `↔` is false). -/
theorem PFunPDS.isProbDist_applyDDC_iff (α : DDC U V X Y)
    {S : PFunPDS X Y} (hS : S.NonNeg) :
    (PFunPDS.applyDDC α S).isProbDist ↔ S.isProbDist := by
  unfold PFunPDS.applyDDC
  exact Dist.isProbDist_fTransform _ hS

/-- CR18 Definition 3.17 composition, law level: a probabilistic converter
applied to an independent probabilistic system is the pushforward of the
deterministic apply over the product law. -/
noncomputable def PFunPDC.apply (A : PFunPDC U V X Y) (S : PFunPDS X Y) :
    PFunPDS U V :=
  Dist.fTransform (fun p : DDC U V X Y × PFunDDS.DDS X Y => p.1 ·ᶜ p.2)
    (Dist.prod A S)

/-- Probabilistic-converter application preserves probability mass. -/
theorem PFunPDC.apply_isProbDist {A : PFunPDC U V X Y} {S : PFunPDS X Y}
    (hA : A.isProbDist) (hS : S.isProbDist) :
    (PFunPDC.apply A S).isProbDist := by
  unfold PFunPDC.apply
  exact Dist.fTransform_isProbDist _ (Dist.prod_isProbDist A S hA hS)

/-- **Converter on a random function** (law-level realization transport): if a deterministic
converter carries every `⌜f⌝` to `⌜F f⌝`, it carries the random function of `Df` to the random
function of the pushforward `F Df` — CR18 Def 3.17 composition is a pushforward of the
per-realization equation. -/
theorem PFunPDS.applyDDC_ofFunDist (α : DDC U V X Y) {F : (X → Y) → U → V}
    (hα : ∀ f, (α ·ᶜ PFunDDS.functionEvaluator f) = PFunDDS.functionEvaluator (F f))
    (Df : Dist (X → Y)) :
    PFunPDS.applyDDC α (PFunPDS.ofFunDist Df)
      = PFunPDS.ofFunDist (Dist.fTransform F Df) := by
  unfold PFunPDS.applyDDC PFunPDS.ofFunDist
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  congr 1
  funext f
  exact hα f

/-- **Simple converter on a random function**: pushing a random function
through the simple converter `(c, d)` yields the random function of the
composed functions — the probabilistic form of the recovery theorem
`(simple c d) S = d ∘ S ∘ c`. -/
theorem PFunPDS.applyDDC_simple_ofFunDist (c : U → X) (d : Y → V)
    (Df : Dist (X → Y)) :
    PFunPDS.applyDDC (DDC.simple c d) (PFunPDS.ofFunDist Df)
      = PFunPDS.ofFunDist (Dist.fTransform (fun f u => d (f (c u))) Df) :=
  PFunPDS.applyDDC_ofFunDist (DDC.simple c d) (DDC.simple_functionEvaluator c d) Df

end Probabilistic

end RandomSystems.CR18
