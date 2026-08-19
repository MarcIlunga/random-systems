/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite

/-!
# A minimal worked example: declare at RS, prove by lifting to AC

The methodology the FROST development should follow, in miniature.  We
**declare the concrete objects at the random-systems level** — a signature,
a resource, a converter — and then **prove a construction statement by
lifting to Abstract Cryptography**: because `RandomSystemsCC.TypedFinite`
instantiates AC's monoid/action/metric contract, AC's construction calculus
(`constructs_singleton_iff`, `Constructs.trans`, …) applies to the concrete
RS objects for free.

The statements read as **algebra**, as in the papers: a converter `flip`, a
resource `R`, the applied converter `flip.toProtocol • R`, and the
construction `⟪R⟫ —[flip.toProtocol]→ ⟪…⟫`.  The RS→AC embedding of a local
converter (`Primitive.toProtocol`, the paper's `αⁱ`) hides the
tuple/monoid plumbing; the raw `.act` never appears in a statement.

The division of labor:

* the **RS level** owns the concrete object and the one genuine behavioral
  fact (`flip.toProtocol • R = …`; for a real scheme this is a coupling or
  program-equivalence proof);
* the **AC level** owns the construction *predicate* and its *calculus*
  (`⟪·⟫ —[·]→ ⟪·⟫`, and composition).

Nothing is assumed: the construction is *discharged* from the RS behavioral
fact via an AC lemma.
-/

namespace RandomSystemsCC.LiftingExample

open AbstractCrypto
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto

/-- **RS level.**  A one-interface bit-oracle signature. -/
abbrev bitSig : SignatureUniverse where
  Code := Unit
  input _ := Bool
  output _ := Bool

instance : DecidableEq bitSig.Code := inferInstanceAs (DecidableEq Unit)

/-- **RS level.**  The output-negating converter, a genuine `Primitive`. -/
def flip : Primitive Unit bitSig () :=
  Primitive.ofFunctions () () id (fun b => !b)

/-- **RS behavioral fact**, stated as algebra with a *bare* converter:
applying `flip` to a resource is its native action, `flip • R = flip.act R`.
No embedding is written — the `SMul` instance lifts it.  (For a real scheme
the right-hand side would be a *named ideal resource* and this a coupling
proof; here it is the action's defining equation.) -/
theorem flip_apply (R : Phi Unit bitSig) : flip • R = flip.act R := rfl

/-- **Lifted to AC**, as a construction, again with a bare converter: `flip`
constructs `flip · R` from `R`.  The coercion lifts `flip` into the
construction notation automatically, and the AC lemma
`constructs_singleton_iff` discharges the predicate from the native
action — no embedding, no `.act`, no tuple plumbing in the statement. -/
theorem flip_constructs (R : Phi Unit bitSig) :
    ⟪R⟫ —[flip]→ ⟪flip • R⟫ :=
  constructs_singleton_iff.mpr (coe_primitive_smul flip R)

end RandomSystemsCC.LiftingExample
