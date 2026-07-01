/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.CR18.DDS

/-!
# CR18 History Morphisms (`HistMap`) and the `comap`/`mapOutput` algebra

This module introduces the *equational* (purely functional) combinator core that
the converter-algebra of CR18 is re-expressed on top of. It replaces the previous
operational, driver-based encoding of converter application with Maurer's
equational style: every operation `op` on systems is defined by a *defining
equation* of the form

> `(op s)` on the input history `l` equals (a component of) `s` evaluated on a
> *derived* history `T(l)`.

The single one-time combinator that captures "evaluate `s` on a derived history"
is `DDS.comap T s`, where `T : HistMap A B` is a partial, prefix-monotone
history morphism `List A ⇀ List B`. Concretely:

* **Cascade** `s ⊲ t = t ⟦ yHistory s ⟧` is `DDS.comap (yHistory-as-HistMap s) t`:
  the derived `Y`-history is `(s(x₁), s(x₁,x₂), …, s(x₁…xₖ))`.
* **Attachment** `αⁱs` evaluates `s` on the *α-translated* outer history, which is
  again a `HistMap` (the `translate` scan).

The well-formedness obligations (`prefix_closed`, `nonempty_input`) for these
operations are then discharged **once and for all** here, on `comap`, from the
three structural fields of `HistMap` (prefix-closed defined set, prefix
monotonicity, nonempty preservation). Downstream operations inherit them for free
by exhibiting the appropriate `HistMap`; no operation re-proves a domain law.

## `HistMap` conventions

A `HistMap A B` is a *partial prefix-monotone history morphism*. Its `defined`
set obeys exactly the CR18 `DDS`-domain discipline:

* `[] ∉ defined` (the empty history is never in the morphism domain — matching
  `DDS.nonempty_input`, and making `DDS.comap` exclude `[]` automatically);
* `defined` is closed under *nonempty* prefixes (matching `DDS.prefix_closed`);
* `map` is **prefix monotone**: `l₁ <+: l₂` with both defined gives
  `map l₁ <+: map l₂`;
* `map` is **nonempty preserving**: a defined (hence nonempty) `l` maps to a
  nonempty `map l`.

These three facts are precisely what `DDS.comap`'s `prefix_closed`/
`nonempty_input` proofs consume.
-/

namespace RandomSystems.CR18

universe u v w

variable {A : Type u} {B : Type v} {Y Z : Type*}

/-- A **partial prefix-monotone history morphism** `List A ⇀ List B`.

This is the one-time combinator datum on top of which the entire CR18 converter
algebra (cascade, attachment) is re-expressed equationally. The fields encode the
same domain discipline as `DDS`:

* `defined`   — the morphism domain, a prefix-closed subset of `List A` with
                `[] ∉ defined`;
* `map`       — the morphism action on a defined history, producing a `List B`;
* `nonempty_defined`, `prefix_closed_defined` — the `DDS`-style domain laws on
                `defined`;
* `map_prefix` — **prefix monotonicity** of `map`;
* `map_nonempty` — **nonempty preservation** of `map`.

The two monotonicity/nonemptiness fields are exactly what is needed to push a
`comap` domain membership down to nonempty prefixes. -/
structure HistMap (A : Type u) (B : Type v) where
  /-- The morphism domain: a prefix-closed subset of `List A` not containing `[]`. -/
  defined : Set (List A)
  /-- The empty history is never in the morphism domain. -/
  nonempty_defined : [] ∉ defined
  /-- The morphism domain is closed under nonempty prefixes. -/
  prefix_closed_defined :
    ∀ {l₁ l₂ : List A}, l₁ <+: l₂ → l₁ ≠ [] → l₂ ∈ defined → l₁ ∈ defined
  /-- The action of the morphism on a defined history. -/
  map : (l : List A) → l ∈ defined → List B
  /-- Prefix monotonicity: the morphism takes prefixes to prefixes. -/
  map_prefix :
    ∀ {l₁ l₂ : List A} (h₁ : l₁ ∈ defined) (h₂ : l₂ ∈ defined),
      l₁ <+: l₂ → map l₁ h₁ <+: map l₂ h₂
  /-- Nonempty preservation: a defined (hence nonempty) history has a nonempty
  image. -/
  map_nonempty :
    ∀ {l : List A} (h : l ∈ defined), map l h ≠ []

namespace HistMap

variable {A : Type u} {B : Type v} {C : Type w}

/-- The identity history morphism on `List A`, defined on every nonempty history. -/
def id (A : Type u) : HistMap A A where
  defined := {l | l ≠ []}
  nonempty_defined := fun h => h rfl
  prefix_closed_defined := fun {_ _} _ hne _ => hne
  map := fun l _ => l
  map_prefix := fun {_ _} _ _ hp => hp
  map_nonempty := fun {_} h => h

@[simp]
theorem id_map (A : Type u) (l : List A) (h : l ∈ (id A).defined) :
    (id A).map l h = l := rfl

@[simp]
theorem id_defined (A : Type u) (l : List A) :
    l ∈ (id A).defined ↔ l ≠ [] := Iff.rfl

/-- Composition of history morphisms `T₂ ∘ T₁ : List A ⇀ List C`, applying `T₁`
first and then `T₂`. A history is defined for the composite when it is defined for
`T₁` and its `T₁`-image is defined for `T₂`. -/
def comp (T₂ : HistMap B C) (T₁ : HistMap A B) : HistMap A C where
  defined := {l | ∃ h : l ∈ T₁.defined, T₁.map l h ∈ T₂.defined}
  nonempty_defined := by
    rintro ⟨h, _⟩
    exact T₁.nonempty_defined h
  prefix_closed_defined := by
    rintro l₁ l₂ hprefix hne ⟨h₂, h₂'⟩
    have h₁ : l₁ ∈ T₁.defined := T₁.prefix_closed_defined hprefix hne h₂
    refine ⟨h₁, ?_⟩
    exact T₂.prefix_closed_defined (T₁.map_prefix h₁ h₂ hprefix)
      (T₁.map_nonempty h₁) h₂'
  map := fun l h => T₂.map (T₁.map l h.choose) h.choose_spec
  map_prefix := by
    rintro l₁ l₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ hprefix
    exact T₂.map_prefix _ _ (T₁.map_prefix h₁ h₂ hprefix)
  map_nonempty := by
    rintro l ⟨_h, h'⟩
    exact T₂.map_nonempty h'

@[simp]
theorem comp_defined (T₂ : HistMap B C) (T₁ : HistMap A B) (l : List A) :
    l ∈ (T₂.comp T₁).defined ↔ ∃ h : l ∈ T₁.defined, T₁.map l h ∈ T₂.defined :=
  Iff.rfl

/-- Defining equation for the composite morphism's action: it is `T₂` applied to
the `T₁`-image, witnessed by the composite-membership proof. -/
theorem comp_map (T₂ : HistMap B C) (T₁ : HistMap A B) (l : List A)
    (h : l ∈ (T₂.comp T₁).defined) (h₁ : l ∈ T₁.defined)
    (h₂ : T₁.map l h₁ ∈ T₂.defined) :
    (T₂.comp T₁).map l h = T₂.map (T₁.map l h₁) h₂ := by
  -- `map` uses `h.choose`/`h.choose_spec`, which differ from `h₁`/`h₂` only by
  -- proof irrelevance of the in-domain witnesses, so the two sides are
  -- definitionally equal.
  rfl

end HistMap

namespace DDS

variable {A : Type u} {B : Type v}

/-- **The one-time combinator.** Precompose a `DDS B Y` with a history morphism
`T : HistMap A B`, yielding a `DDS A Y`. This is the equational core on which the
CR18 converter algebra is built: a history `l` is in the domain exactly when it is
in `T.defined` and its `T`-image is in `s.dom`, and the response is `s` evaluated
on that derived history.

The well-formedness obligations are discharged **here, once**, from the
`HistMap` structure: `prefix_closed` from `T.prefix_closed_defined` +
`T.map_prefix` + `T.map_nonempty` + `s.prefix_closed`, and `nonempty_input` from
`T.nonempty_defined`. -/
def comap (T : HistMap A B) (s : DDS B Y) : DDS A Y where
  dom := {l | ∃ h : l ∈ T.defined, T.map l h ∈ s.dom}
  nonempty_input := by
    rintro ⟨h, _⟩
    exact T.nonempty_defined h
  prefix_closed := by
    rintro l₁ l₂ hprefix hne ⟨h₂, h₂'⟩
    have h₁ : l₁ ∈ T.defined := T.prefix_closed_defined hprefix hne h₂
    refine ⟨h₁, ?_⟩
    exact s.prefix_closed (T.map_prefix h₁ h₂ hprefix) (T.map_nonempty h₁) h₂'
  respond := fun l h => s.respond (T.map l h.choose) h.choose_spec

/-- Domain characterization for `comap`. -/
@[simp]
theorem comap_dom (T : HistMap A B) (s : DDS B Y) (l : List A) :
    l ∈ (comap T s).dom ↔ ∃ h : l ∈ T.defined, T.map l h ∈ s.dom :=
  Iff.rfl

/-- **Defining output equation for `comap`** (`@[simp]`): the output of `comap T s`
on a history `l` is `s`'s output on the derived history `T.map l _`, for any
in-domain witnesses. This is the equational law every derived operation reads its
output equation off of. -/
@[simp]
theorem comap_output (T : HistMap A B) (s : DDS B Y) (l : List A)
    (h : l ∈ (comap T s).dom) (hT : l ∈ T.defined) (hs : T.map l hT ∈ s.dom) :
    (comap T s).output l h = s.output (T.map l hT) hs := by
  -- `respond` uses `h.choose`/`h.choose_spec`; reconcile with `hT`/`hs` by proof
  -- irrelevance of the in-domain witnesses (both sides definitionally equal).
  rfl

/-- **Functoriality of `comap`** (`comap_comp`): precomposing with a composite
history morphism is the same as precomposing twice. This is the equational law
behind associativity-style rewrites (and the engine of `attachAt_comm`). -/
theorem comap_comp (T₁ : HistMap A B) {C : Type w} (T₂ : HistMap B C)
    (s : DDS C Y) :
    comap T₁ (comap T₂ s) = comap (T₂.comp T₁) s := by
  apply DDS.ext
  · ext l
    constructor
    · rintro ⟨h₁, h₂, hs⟩
      exact ⟨⟨h₁, h₂⟩, hs⟩
    · rintro ⟨⟨h₁, h₂⟩, hs⟩
      exact ⟨h₁, h₂, hs⟩
  · intro l h h'
    -- both sides are `s.respond` on the doubly-derived history; reduce by the
    -- defining output equations and proof irrelevance.
    have h₁ : l ∈ T₁.defined := h.choose
    have h₂ : T₁.map l h₁ ∈ T₂.defined := h.choose_spec.choose
    have hs : T₂.map (T₁.map l h₁) h₂ ∈ s.dom := h.choose_spec.choose_spec
    have hcomp : l ∈ (T₂.comp T₁).defined := ⟨h₁, h₂⟩
    have hsc : (T₂.comp T₁).map l hcomp ∈ s.dom := by
      rw [HistMap.comp_map T₂ T₁ l hcomp h₁ h₂]; exact hs
    rw [comap_output T₁ (comap T₂ s) l h h₁ ⟨h₂, hs⟩,
        comap_output T₂ s _ ⟨h₂, hs⟩ h₂ hs,
        comap_output (T₂.comp T₁) s l h' hcomp hsc]
    -- LHS history `T₂.map (T₁.map l h₁) h₂` and RHS `(T₂.comp T₁).map l hcomp`
    -- are definitionally equal (`comp_map`), so the two `s.output` calls agree.
    rfl

/-- Postcompose a `DDS A Y` with a pure output map `f : Y → Z`. Trivial: same
domain, `f` applied to each response. -/
def mapOutput (f : Y → Z) (s : DDS A Y) : DDS A Z where
  dom := s.dom
  nonempty_input := s.nonempty_input
  prefix_closed := s.prefix_closed
  respond := fun l h => f (s.respond l h)

@[simp]
theorem mapOutput_dom (f : Y → Z) (s : DDS A Y) :
    (mapOutput f s).dom = s.dom := rfl

/-- **Defining output equation for `mapOutput`** (`@[simp]`). -/
@[simp]
theorem mapOutput_output (f : Y → Z) (s : DDS A Y) (l : List A)
    (h : l ∈ (mapOutput f s).dom) :
    (mapOutput f s).output l h = f (s.output l h) := rfl

/-- `mapOutput` commutes with `comap`: precomposing then postcomposing equals
postcomposing then precomposing. (Used in `attachAt_comm` to slide the output map
through the derived-history precomposition.) -/
theorem mapOutput_comap (f : Y → Z) (T : HistMap A B) (s : DDS B Y) :
    mapOutput f (comap T s) = comap T (mapOutput f s) := by
  apply DDS.ext
  · rfl
  · intro l h h'
    have hT : l ∈ T.defined := h'.choose
    have hs : T.map l hT ∈ (mapOutput f s).dom := h'.choose_spec
    -- `hs : T.map l hT ∈ (mapOutput f s).dom = s.dom`.
    have hs' : T.map l hT ∈ s.dom := hs
    rw [mapOutput_output f (comap T s) l h,
        comap_output T s l h hT hs',
        comap_output T (mapOutput f s) l h' hT hs,
        mapOutput_output f s (T.map l hT) hs']

end DDS

/-!
## SCAN-shaped history morphisms

The history morphisms arising in CR18 (`yHistory` for cascade, `translate` for
attachment) are all **scans**: a left fold over the input history that, at each
step, *appends* a (possibly state- and `DDS`-output-dependent) chunk to the
running output, threading a state. The crucial structural facts — prefix
monotonicity and nonempty preservation — hold for *every* scan of this shape,
proved here once.

We package a scan by:
* a `defined` set with the `DDS`-domain discipline (supplied by the instantiating
  operation, e.g. `s.dom` for cascade);
* a per-prefix *output chunk* `chunk : (l) → l ∈ defined → List B` that is the
  image of the prefix of length `|l|` — i.e. the scan's running output after
  consuming `l`. The two structural laws are then stated directly on `chunk`:
  `chunk` is prefix-monotone and maps nonempty histories to nonempty outputs.

In practice the instantiating operation already has a per-prefix output list
(`yHistory s l h` for cascade; the translated outer history for attachment) and
the only work is to prove these two laws for it. `ofScan` is the constructor that
turns those two proofs plus the `defined` discipline into a `HistMap`. The
existing `DDS.yHistory` dependent-prefix-outputs pattern is the canonical model.
-/

namespace HistMap

variable {A : Type u} {B : Type v}

/-- Build a `HistMap` from scan data: a prefix-closed `defined` set together with
a per-prefix output chunk that is prefix-monotone and nonempty-preserving. This
is the single constructor through which `yHistory` (cascade) and `translate`
(attachment) become history morphisms; it discharges the `HistMap` fields from
the two scan laws. -/
def ofScan (defined : Set (List A))
    (nonempty_defined : [] ∉ defined)
    (prefix_closed_defined :
      ∀ {l₁ l₂ : List A}, l₁ <+: l₂ → l₁ ≠ [] → l₂ ∈ defined → l₁ ∈ defined)
    (chunk : (l : List A) → l ∈ defined → List B)
    (chunk_prefix :
      ∀ {l₁ l₂ : List A} (h₁ : l₁ ∈ defined) (h₂ : l₂ ∈ defined),
        l₁ <+: l₂ → chunk l₁ h₁ <+: chunk l₂ h₂)
    (chunk_nonempty :
      ∀ {l : List A} (h : l ∈ defined), chunk l h ≠ []) :
    HistMap A B where
  defined := defined
  nonempty_defined := nonempty_defined
  prefix_closed_defined := prefix_closed_defined
  map := chunk
  map_prefix := chunk_prefix
  map_nonempty := chunk_nonempty

@[simp]
theorem ofScan_defined (defined : Set (List A)) (hd) (hpc)
    (chunk : (l : List A) → l ∈ defined → List B) (hcp) (hcn) (l : List A) :
    l ∈ (ofScan defined hd hpc chunk hcp hcn).defined ↔ l ∈ defined := Iff.rfl

@[simp]
theorem ofScan_map (defined : Set (List A)) (hd) (hpc)
    (chunk : (l : List A) → l ∈ defined → List B) (hcp) (hcn)
    (l : List A) (h : l ∈ (ofScan defined hd hpc chunk hcp hcn).defined) :
    (ofScan defined hd hpc chunk hcp hcn).map l h = chunk l h := rfl

end HistMap

end RandomSystems.CR18
