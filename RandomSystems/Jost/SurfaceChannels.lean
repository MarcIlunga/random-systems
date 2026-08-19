/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Systems
import RandomSystems.Jost.Surface
import RandomSystems.Jost.SurfaceNames

/-!
# The channel calculus: MaRuTa12 §1.3's five resources, under their glyphs

The Maurer school names channels by symbols — MaRuTa12 §1.3, "using the
notation of [24]":

* `—→`   an *insecure channel*: leaks the complete messages at `E`, and
  allows `E` to delete, change, or inject messages;
* `•—→`  an *authenticated channel*: leaks the complete messages; `E` only
  forwards or deletes;
* `—→•`  a *confidential channel*: leaks only the length, but allows
  delete, change, inject;
* `•—→•` a *secure channel*: leaks only the length, forward-or-delete only;
* `•══•` a *shared secret key*: the same uniformly random value at `A` and
  `B`, nothing at `E`.

"The intuitive interpretation of the symbol `•` is that the capabilities
at the marked side are provided exclusively to that party."

These five are declared here as surface resources with the glyphs as their
`cc_display` names, LaTeX forms for the exporter, and `role assumed` —
Maurer11's palette colors assumed resources blue in equations.

Provenance: the authenticated and secure channels ARE the tree's existing
boxes (`JostFigure22.authChan`, `Jost226.secChan`) — reused, not
re-authored; the insecure and confidential channels add `inject` to Eve's
alphabet; the shared key is the surface (one-code-per-interface)
presentation of Fig. 2.2's `Key` (whose kernel twin,
`JostFigure22.keyMachine`, uses a shared signature code and thus lives
below the `Interfaces` surface).  All channels are multiple-use
(MaRuTa12 §2.4's "several (arbitrarily interleaved) interactions"), with
Jost's free interface `F` carrying honest delivery as in Fig. 2.2.
Lengths are kept abstract as `len : M → L`, as in `Jost/Systems.lean`.
-/

namespace RandomSystems.CC.Channels

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.TypedResource.JostFigure22
open RandomSystems.CR18.TypedResource.Jost226 (secOut secChan)

/-! ## Interface declarations -/

/-- The channel boundary of Fig. 2.2 over message space `M`: `A` sends,
`B` receives, `E` leaks/delivers, `F` delivers. -/
def channelInterfaces (M : Type) : Interfaces where
  Iface := Iface
  In := chanIn M
  Out := chanOut M

/-- Eve's alphabet at a *malleable* channel: read, deliver, or inject an
arbitrary message — the delete/change/inject capabilities of `—→` and
`—→•`.  (Change = inject after leak; delete = never deliver.) -/
inductive MalleableEveIn (M : Type)
  | leak (index : Nat)
  | deliver (index : Nat)
  | inject (message : M)

/-- Inputs of a malleable channel: as Fig. 2.2, with Eve's alphabet
extended by `inject`. -/
def malleableIn (M : Type) : Iface → Type
  | .A => SenderIn M
  | .B => ReceiverIn
  | .E => MalleableEveIn M
  | .F => FreeIn

/-- The insecure-channel boundary: malleable, and Eve's leak returns the
complete message. -/
def insecureInterfaces (M : Type) : Interfaces where
  Iface := Iface
  In := malleableIn M
  Out := chanOut M

/-- The confidential-channel boundary: malleable, but Eve's leak returns
only the length. -/
def confidentialInterfaces (M L : Type) : Interfaces where
  Iface := Iface
  In := malleableIn M
  Out := secOut M L

/-- The secure-channel boundary: Fig. 2.2 inputs, Eve sees lengths only. -/
def secureInterfaces (M L : Type) : Interfaces where
  Iface := Iface
  In := chanIn M
  Out := secOut M L

/-- The shared-key boundary: two fetch interfaces.  (The kernel `Key` of
Fig. 2.2 shares one signature code between them; at the one-code-per-
interface surface the two interfaces simply carry equal alphabets.) -/
def keyInterfaces (K : Type) : Interfaces where
  Iface := KeyIface
  In := fun _ => FetchIn
  Out := fun _ => K

/-! ## The five resources -/

/-- `—→`: the insecure channel.  Leaks complete messages; Eve may deliver
a sent message, inject her own, or never deliver (delete). -/
@[cc_display "—→", cc_latex "\\longrightarrow", cc_role assumed]
noncomputable def insecureChannel (M : Type) :
    Resource (insecureInterfaces M) :=
  Resource.ofState (⟨[], none⟩ : ChanLog M) fun state query =>
    match query with
    | ⟨.A, .send m⟩ => some ({ state with log := state.log ++ [m] }, .ok)
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ => some (state, .leaked (logLookup state.log i))
    | ⟨.E, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)
    | ⟨.E, .inject m⟩ => some ({ state with delivered := some m }, .ok)
    | ⟨.F, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)

/-- `•—→`: the authenticated channel — Fig. 2.2's `AuthChan`, reused
verbatim.  Leaks complete messages; Eve only forwards or deletes. -/
@[cc_display "•—→", cc_latex "{\\bullet}\\!\\longrightarrow",
  cc_role assumed]
noncomputable def authenticatedChannel (M : Type) :
    Resource (channelInterfaces M) :=
  Resource.ofRealization (authChan M)

/-- `—→•`: the confidential channel.  Eve sees only lengths but may
deliver, inject, or delete. -/
@[cc_display "—→•", cc_latex "\\longrightarrow\\!{\\bullet}",
  cc_role assumed]
noncomputable def confidentialChannel {M L : Type} (len : M → L) :
    Resource (confidentialInterfaces M L) :=
  Resource.ofState (⟨[], none⟩ : ChanLog M) fun state query =>
    match query with
    | ⟨.A, .send m⟩ => some ({ state with log := state.log ++ [m] }, .ok)
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ => some (state, .leaked ((logLookup state.log i).map len))
    | ⟨.E, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)
    | ⟨.E, .inject m⟩ => some ({ state with delivered := some m }, .ok)
    | ⟨.F, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)

/-- `•—→•`: the secure channel — `Jost226.secChan`, reused verbatim.
Eve sees only lengths and only forwards or deletes. -/
@[cc_display "•—→•",
  cc_latex "{\\bullet}\\!\\longrightarrow\\!{\\bullet}", cc_role assumed]
noncomputable def secureChannel {M L : Type} (len : M → L) :
    Resource (secureInterfaces M L) :=
  Resource.ofRealization (secChan len)

/-- The deterministic fibre of the shared key at a fixed sampled value. -/
def keyBox (K : Type) (k : K) : (keyInterfaces K).Realization where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨_, .fetch⟩ => some ((), k)

/-- `•══•`: the shared secret key — the same uniformly random value at
both interfaces, nothing for Eve (she has no interface here at all, the
strongest reading of the exclusivity dots). -/
@[cc_display "•══•", cc_latex "{\\bullet}\\!=\\!\\!=\\!{\\bullet}",
  cc_role assumed]
noncomputable def sharedKey (K : Type) [Fintype K] [Nonempty K] :
    Resource (keyInterfaces K) :=
  Resource.sampleInit (keyBox K) (Dist.uniform K)

end RandomSystems.CC.Channels
