/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.LiftingExample

/-!
# Permanent regression gate for the construction notation surface

Every statement here is a *usability* receipt, not a mathematical one: each
`example` asserts that a paper-shaped phrase **elaborates** with the arguments a
reader would naturally write, and with none of the plumbing tokens the layer
exists to hide.  A regression shows up as a build failure in this file rather
than as a slow drift towards hand-written `Pi.mulSingle` tuples in model files.

The four defects this gate pins, and what was actually true of each:

* **(a) approximate lifting for bare converters — was REAL, now fixed.**
  `AbstractCrypto.ApproximatelyConstructs` demanded `[Monoid M] [MulAction M Φ]`
  purely because of the ambient `variable` line, while its body uses only
  `HasReduction.Red` (a bare relation) and `Relaxation.eball` (metric on `Φ`
  only).  A `Primitive` is not a monoid and has no reason to be, so the exact
  form `⟪R⟫ —[flip]→ ⟪S⟫` accepted a bare converter while the approximate form
  failed with `failed to synthesize Monoid (Primitive …)`.  The fix took the
  hypothesis actually used, `[HasReduction (Set Φ) M]`.

* **(b) packing coercion — was REAL, now fixed.**  60+ sites across ten modules
  spelled `⟨boundary, ofProb S⟩` by hand although the boundary is already
  determined by the law's type; `instCoeTCProbResource` recovers it.

* **(c) glyph collision — NOT a defect.**  `RandomSystemsCC.CR18`'s
  `—[c; ε]→` and `AbstractCrypto`'s `—[π; ε]→` do share a glyph sequence and a
  precedence, but they are *not* ambiguous in practice: the two take different
  argument types (`Resource U`/`ℝ`/`DDConverter` versus `Set Φ`/`ℝ≥0∞`/`M`), so
  at most one elaborates for any given term.  Opening both scopes at once —
  which the last check below does, and which `CBC.lean` was believed to be
  avoiding — is fine.  The RS-side `constructs` also already delegates to
  `AbstractCrypto.ApproximatelyConstructs`, so it introduces no second notion.

* **(d) `⇂` unused — was REAL, now discharged.**  The last fully-qualified
  `AbstractCrypto.patternAttach` in the tree is gone.
-/

namespace RandomSystemsCC.NotationChecks

open AbstractCrypto RandomSystems.CR18.TypedResource RandomSystemsCC.TypedFinite
open scoped AbstractCrypto
open RandomSystemsCC.LiftingExample (bitSig)

local notation "flip'" => RandomSystemsCC.LiftingExample.flip

/-! ### (a) Both construction forms take a **bare** `Primitive` -/

/-- Exact construction, bare converter — no `Pi.mulSingle`, no `.toProtocol`. -/
example (R : Phi Unit bitSig) : Prop := ⟪R⟫ —[flip']→ ⟪flip' • R⟫

/-- Approximate construction, bare converter.  This is the form that could not
elaborate before the `ApproximatelyConstructs` generalization. -/
example (R : Phi Unit bitSig) : Prop := ⟪R⟫ —[flip'; 0]→ ⟪flip' • R⟫

/-- …and at a symbolic radius, so the fix is not an artefact of `ε = 0`. -/
example (R : Phi Unit bitSig) (ε : ENNReal) : Prop :=
  ⟪R⟫ —[flip'; ε]→ ⟪flip' • R⟫

/-- The approximate form at radius `0` is implied by the exact one, so the two
spellings agree where they overlap rather than merely both parsing. -/
example (R : Phi Unit bitSig) (exact : ⟪R⟫ —[flip']→ ⟪flip' • R⟫) :
    ⟪R⟫ —[flip'; 0]→ ⟪flip' • R⟫ :=
  fun x hx => Relaxation.mem_eball_iff.mpr ⟨x, exact hx, by simp⟩

/-! ### (b) A law at a known boundary packs itself -/

/-- No `⟨boundary, ofProb …⟩`: the boundary comes from the law's own type. -/
example {I : Type} {U : SignatureUniverse} [DecidableEq I] [DecidableEq U.Code]
    {boundary : Boundary U I} (law : DependentPDS.Prob U boundary) :
    Resource I U := law

/-- The packing is transparent in both components. -/
example {I : Type} {U : SignatureUniverse} [DecidableEq I] [DecidableEq U.Code]
    {boundary : Boundary U I} (law : DependentPDS.Prob U boundary) :
    (law : Resource I U).boundary = boundary := by simp

/-! ### (d) The interface-pattern restriction reads as in the papers -/

/-- `π ⇂ P` rather than `AbstractCrypto.patternAttach P π`, and the notation
means exactly that — pinned by `rfl`, not merely parsed. -/
example {I : Type} {Γ : I → Type} [∀ i, Monoid (Γ i)] (π : ∀ i, Γ i)
    (P : Set I) : (π ⇂ P) = patternAttach P π := rfl

/-! ### (c) Both scopes open at once is not ambiguous

This whole file already has `open scoped AbstractCrypto` alongside the
`RandomSystemsCC.CR18` scope that `⟪·⟫`/`—[·]→` come from, and every check
above elaborates.  The remaining receipt is that AC's *own* `—[π; ε]→` still
resolves for genuine specification-level arguments in the same scope. -/

example {M Φ : Type} [Monoid M] [MulAction M Φ] [PseudoEMetricSpace Φ]
    (π : M) (ε : ENNReal) (R S : Set Φ) : Prop := R —[π; ε]→ S

end RandomSystemsCC.NotationChecks
