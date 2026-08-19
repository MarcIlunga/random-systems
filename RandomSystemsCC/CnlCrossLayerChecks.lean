/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.ControlledNaturalLanguage

/-!
# Cross-layer regression for the two controlled-language layers

The estate has **two** controlled-language layers — `AbstractCrypto`'s
(`CryptoControlledNaturalLanguage`) and this package's
(`RandomSystemsCC.ControlledNaturalLanguage`, which imports it) — each with its
own table of English words promoted to parser atoms.  Until this file, each
layer tested only *itself*, so nothing checked that a sentence from the lower
layer still parses in a file that has the upper layer in scope.  It did not.

**The defect.**  A word used as a parser atom anywhere in the combined system is
a *token* everywhere downstream, and a token can never be matched by `ident`.
This package's Condition-C sentences spell `"We" "apply" "the" …`, promoting
`the` to a token; `AbstractCrypto`'s `cnlReplaceProtocol`, `cnlUseSimulator` and
`cnlParallelContext` took that same word as `theWord:ident` and validated it
afterwards with `expectWord`.  Downstream of this package's CNL those three
sentences therefore could not parse *at all* — not a wrong elaboration, a parse
error.  Measured, the words that actually collide are exactly three — `the`,
`we` and `obtain` — and the fix is for `AbstractCrypto` to spell those as the
atoms they already are downstream.  No prose changed in either layer.

The fix is deliberately **minimal, and driven by build failures rather than by
the containment computation**.  Five words are both atoms here and `ident`s
there (`the`, `we`, `obtain`, `follows`, `protocol`), but promoting `follows`
or `protocol` breaks working code — `TypedConstructChecks.lean` binds both as
ordinary identifiers, and `protocol` is about as natural an identifier as this
domain has.  Promoting a word is not free: it spends that word globally.  So
only the words whose absence actually breaks a parse were promoted.

**Why one layer could not have caught it.**  `AbstractCrypto`'s own test file
exercises all three sentences and passes, because in that file this package's
CNL is not imported and `the` is still an ordinary identifier.  The failure
exists only in the *union*, which is exactly what this file is.

**A live constraint this file also pins.**  Promoting an English word to an atom
costs its use as a Lean identifier downstream.  This package's CNL currently
spends, among others, `real`, `ideal`, `bound`, `event`, `game` and `the`.  The
binders below are named `realRes`/`idealRes` for that reason — `real` and
`ideal` are *tokens* here, and `(real ideal : Phi)`, which is what
`AbstractCrypto`'s own tests write, is a parse error in this file.  That is a
deliberate cost, not a bug, but it is a cost that grows with every new sentence
and is invisible to a single-layer gate.
-/

namespace RandomSystemsCC.CnlCrossLayerChecks

open AbstractCrypto
open scoped AbstractCrypto CryptoControlledNaturalLanguage

variable {I : Type} [DecidableEq I] {Gamma : I → Type} [∀ i, Monoid (Gamma i)]
  {Phi : Type} [PseudoEMetricSpace Phi] [MulAction (∀ i, Gamma i) Phi]

/-- `cnlUseSimulator`, in scope with this package's CNL. -/
example (protocol simulator : ∀ i, Gamma i)
    (simulators : Submonoid (∀ i, Gamma i)) (realRes idealRes : Phi)
    (error : ENNReal) (simulatorMembership : simulator ∈ simulators)
    (distanceBound : edist (protocol • realRes) (simulator • idealRes) ≤ error) :
    ⟪realRes⟫ —[protocol; error]→ (⟪idealRes⟫ ^⋆[simulators]) := by
  We use simulator to prove the construction
  · exact simulatorMembership
  · exact distanceBound

omit [PseudoEMetricSpace Phi] in
/-- `cnlReplaceProtocol`, in scope with this package's CNL. -/
example {protocol protocol' : ∀ i, Gamma i}
    {realSpec idealSpec : Set Phi} (protocolEquation : protocol = protocol')
    (construction : realSpec —[protocol]→ idealSpec) :
    realSpec —[protocol']→ idealSpec := by
  Replacing the protocol in construction using protocolEquation,
    we obtain the required construction

/-- `cnlParallelContext`, both sides, in scope with this package's CNL. -/
example [Par (∀ i, Gamma i)] [Par Phi]
    [SMulParClass (∀ i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : ∀ i, Gamma i} {realSpec idealSpec context : Set Phi}
    {error : ENNReal}
    (construction : realSpec —[protocol; error]→ idealSpec) :
    realSpec ∥ context —[protocol ∥ 1; error]→ idealSpec ∥ context := by
  With context as the right parallel context,
    the construction follows from construction

example [Par (∀ i, Gamma i)] [Par Phi]
    [SMulParClass (∀ i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : ∀ i, Gamma i} {realSpec idealSpec context : Set Phi}
    {error : ENNReal}
    (construction : realSpec —[protocol; error]→ idealSpec) :
    context ∥ realSpec —[1 ∥ protocol; error]→ context ∥ idealSpec := by
  With context as the left parallel context,
    the construction follows from construction

end RandomSystemsCC.CnlCrossLayerChecks
