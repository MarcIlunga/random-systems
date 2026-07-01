/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.CR18.DDS
import RandomSystems.CR18.DDE
import RandomSystems.CR18.PDS
import RandomSystems.CR18.Behavior

open RandomSystems (Dist)

/-!
# CR18 Definition 3.22 — Monotone Binary Output, DDG, and PDG

This module formalizes CR18 Definition 3.22 (Maurer's lecture notes,
"Cryptography: Random Systems"):

> **Definition 3.22.**  For a `(X, Y × {0, 1})`-DDS `g` the binary component
> `aᵢ` of the output `(yᵢ, aᵢ)` is called a **monotone binary output (MBO)**
> if `aᵢ = 1` implies `aⱼ = 1` for `j ≥ i`.  Such a DDS `g` with MBO is also
> called a **deterministic discrete `(X, Y)`-game (DDG)**.

Additionally:

* A **probabilistic discrete game (PDG)** (called "probabilistic discrete game"
  in CR18's running prose after Definition 3.22) is a `PDS (X, Y × Bool)`
  whose binary component is monotone — i.e., a random variable over DDGs.

* A **deterministic winner** `w` for an `(X, Y)`-game `g` is a
  `(Y, X)`-DDE (Definition 3.23; winner sees outputs but not the MBO bits).

## Relation to `ConditionBased.lean`

The legacy `RandomSystems.TranscriptCondition` in
`RandomSystems/ConditionBased.lean` captures a *monotone condition* (predicate
on transcripts that is monotone in the number of rounds).  The MBO property is
the *per-output* incarnation of monotonicity: the bit component of a DDS output
is monotone along the interaction sequence.  `DDG.IsMBO` is the game-native
equivalent at the DDS level.

## Conventions

* Output `Y × Bool`: `Bool` represents `{0, 1}`, `false = 0`, `true = 1`.
* The DDE type `RandomSystems.CR18.DDE X Y` (from `CR18.DDE`) is reused
  directly for winners (Def 3.23: a winner is a `(Y, X)`-DDE).
* All definitions follow the partial-function `DDS` model from `CR18.DDS`.
-/

namespace RandomSystems.CR18

/-! ## MBO predicate on DDS output sequences -/

/-- CR18 Definition 3.22: the binary component sequence extracted from a
sequence of `Y × Bool` outputs.

Given an output history `[(y₁, a₁), (y₂, a₂), ...]`, this extracts
`[a₁, a₂, ...]`. -/
def binaryComponents {Y : Type*} (outs : List (Y × Bool)) : List Bool :=
  outs.map Prod.snd

/-- CR18 Definition 3.22: a list of bits is **monotone** (in the MBO sense) if
`aᵢ = true` implies `aⱼ = true` for all `j ≥ i`.

Equivalently: once the sequence contains `true`, all subsequent bits are also
`true`. -/
def BitSeq.IsMonotone (bits : List Bool) : Prop :=
  ∀ (i j : ℕ) (hi : i < bits.length) (hj : j < bits.length),
    i ≤ j →
    bits[i] = true →
    bits[j] = true

/-- CR18 Definition 3.22: the MBO predicate on a `(X, Y × Bool)`-DDS.

The DDS `g` has a **monotone binary output (MBO)** if, for every input sequence
in the domain, the sequence of binary components of the outputs is monotone:
once some output has bit `1 = true`, all later outputs also carry bit `1`. -/
def DDS.IsMBO {X Y : Type*} (g : DDS X (Y × Bool)) : Prop :=
  ∀ (l : List X) (_ : l ∈ g.dom)
    (i j : ℕ) (_ : i ≤ j) (_ : j < l.length),
    (∃ (li : l.take (i + 1) ∈ g.dom),
        (g.respond (l.take (i + 1)) li).2 = true) →
    ∃ (lj : l.take (j + 1) ∈ g.dom),
        (g.respond (l.take (j + 1)) lj).2 = true

/-! ## DDG: Deterministic Discrete Game -/

/-- CR18 Definition 3.22: a **deterministic discrete `(X, Y)`-game (DDG)** is a
`(X, Y × Bool)`-DDS whose binary output component is monotone.

Maurer: "Such a DDS `g` with MBO is also called a deterministic discrete
`(X, Y)`-game (DDG)." -/
structure DDG (X Y : Type*) where
  /-- The underlying `(X, Y × Bool)`-DDS. -/
  toSystem : DDS X (Y × Bool)
  /-- The binary output component is monotone. -/
  mbo : toSystem.IsMBO

namespace DDG

variable {X Y : Type*}

/-- The coercion from a DDG to its underlying DDS. -/
instance : CoeTC (DDG X Y) (DDS X (Y × Bool)) where
  coe g := g.toSystem

/-- Convenience: the regular output `yᵢ` at an in-domain input history. -/
def regularOutput (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) : Y :=
  (g.toSystem.respond l hl).1

/-- Convenience: the binary output `aᵢ` at an in-domain input history. -/
def binaryOutput (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) : Bool :=
  (g.toSystem.respond l hl).2

/-- The MBO property reformulated using `binaryOutput` for readability.

Once `aᵢ = true` for some prefix, all longer prefixes also have `aⱼ = true`. -/
theorem mbo_binaryOutput (g : DDG X Y)
    (l : List X) (hl : l ∈ g.toSystem.dom)
    (i j : ℕ) (hij : i ≤ j) (hj : j < l.length)
    (hi_dom : l.take (i + 1) ∈ g.toSystem.dom)
    (ha_i : g.binaryOutput (l.take (i + 1)) hi_dom = true) :
    ∃ hj_dom : l.take (j + 1) ∈ g.toSystem.dom,
        g.binaryOutput (l.take (j + 1)) hj_dom = true :=
  g.mbo l hl i j hij hj ⟨hi_dom, ha_i⟩

/-- A DDG is "won" on input history `l` if the binary output at `l` is `true`. -/
def IsWon (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) : Prop :=
  g.binaryOutput l hl = true

end DDG

/-! ## Winner for a DDG (Definition 3.23) -/

/-- CR18 Definition 3.23: a **deterministic winner** `w` for an `(X, Y)`-DDG `g`
is a `(Y, X)`-DDE — a deterministic discrete environment for the game `g`.

Maurer: "A (deterministic) winner `w` for an `(X, Y)`-game `g` is a discrete
`(Y, X)`-environment (DDE, see Definition 3.16)."

Note: the winner sees only the `Y`-component of the output `(yᵢ, aᵢ)` — the
MBO bit `aᵢ` is *not* returned to the winner.  Since the game has input
alphabet `X` and (visible) output alphabet `Y`, the winner is a `(Y, X)`-DDE:
it consumes `Y`-outputs and produces `X`-inputs.  In CR18.DDE notation, this
is `DDE X Y` (type `List (Option Y) → Option X`). -/
abbrev Winner (X Y : Type*) : Type _ := DDE X Y

namespace Winner

variable {X Y : Type*}

/-- Project a `(X, Y × Bool)`-DDS to a `(X, Y)`-DDS by dropping the Bool
component from every output.  This is the interface the winner sees: it
receives only the `Y` part, not the MBO bit. -/
def projectGame (g : DDG X Y) : DDS X Y where
  dom := g.toSystem.dom
  nonempty_input := g.toSystem.nonempty_input
  prefix_closed := g.toSystem.prefix_closed
  respond := fun l hl => (g.toSystem.respond l hl).1

/-- Bridge instance: `(projectGame g).dom` is definitionally `g.toSystem.dom`, so a decidable
membership for the latter transports to the former.  Fixes instance synthesis at the
`projectGame`-transcript sites. -/
instance projectGame_decidableDom (g : DDG X Y)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)] :
    DecidablePred (fun l : List X => l ∈ (projectGame g).dom) :=
  inferInstanceAs (DecidablePred (fun l : List X => l ∈ g.toSystem.dom))

/-- CR18 Definition 3.22 (prose): the winner wins game `g` if the binary output
becomes `true` for some round in the interaction transcript.

Maurer: "Winner `w` wins game `g` if `aᵢ = 1` for some `i ≥ 1`."

We run the winner against the *projected* DDS (which only reveals the `Y`
component of each output), then check the *full* game's MBO bits at those
same input prefixes. -/
def Wins (w : Winner X Y) (g : DDG X Y)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  let t := DDE.transcript (projectGame g) w fuel
  ∃ (i : ℕ) (_ : i < t.inputs.length)
    (hdom : t.inputs.take (i + 1) ∈ g.toSystem.dom),
      g.binaryOutput (t.inputs.take (i + 1)) hdom = true

end Winner

/-! ## Probabilistic Discrete Game (PDG) -/

/-- CR18 Definition 3.22 (probabilistic analogue): a **probabilistic discrete
`(X, Y)`-game (PDG)** is a probabilistic discrete system (PDS) with MBO.

Maurer: "A probabilistic discrete game `G` is now a probabilistic discrete
system (PDS, see Definition 3.14) with MBO."

We model this as a `Dist` (finite-support sub-distribution, LM20 Def 1) over
DDGs: the random variable ranges over deterministic discrete games, each of
which already carries the MBO invariant. -/
abbrev PDG (X : Type*) (Y : Type*) : Type _ :=
  Dist (DDG X Y)

namespace PDG

variable {X Y : Type*}

/-- Embed a deterministic DDG as the degenerate PDG concentrated at that game. -/
noncomputable def pure (g : DDG X Y) : PDG X Y :=
  Finsupp.single g 1

/-- Alias for the canonical embedding. -/
noncomputable abbrev ofDDG (g : DDG X Y) : PDG X Y :=
  pure g

/-- The underlying PDS of a PDG, obtained by pushing forward along the DDG's
DDS projection. -/
noncomputable def toPDS [DecidableEq (DDS X (Y × Bool))] (G : PDG X Y) :
    PDS X (Y × Bool) :=
  Dist.fTransform DDG.toSystem G

/-- The degenerate PDG concentrated at `g` has the same underlying PDS as
`PDS.pure g.toSystem`. -/
theorem toPDS_pure [DecidableEq (DDS X (Y × Bool))] (g : DDG X Y) :
    (pure g).toPDS = PDS.pure g.toSystem := by
  classical
  simp only [toPDS, pure, PDS.pure, Dist.fTransform]
  rw [Finsupp.sum_single_index (by simp)]

end PDG

/-! ## Relation to `RandomSystems.TranscriptCondition`

The legacy `RandomSystems.TranscriptCondition` in `ConditionBased.lean`
defines a predicate on (finite, total) transcripts `Fin q → X × Y` that is
"monotone" in the sense that it holds for all prefixes.  The MBO property here
is the analogous notion at the CR18 DDS level: the binary output bit is once set
to `true`, it stays `true`.

Both capture the same intuition — a "bad event that, once triggered, stays
triggered" — but operate at different levels of the framework:
- `TranscriptCondition` works on total fixed-length transcripts for the legacy
  `RandomSystems.DDS X Y q` model.
- `DDS.IsMBO` / `DDG` works on partial-function `CR18.DDS` systems with
  variable-length interactions.

No direct bridge is provided here because the two system models (`RandomSystems.DDS`
and `RandomSystems.CR18.DDS`) use incompatible transcript types; the conceptual
relation is documented rather than formalized.
-/

end RandomSystems.CR18

/-!
## P9 — Multi-Game MBOs: Hidden vs. Visible

CR18 §3.7.1 (prose after Definition 3.22):

> "for so-called multi-games, the natural generalization where the game has
> several MBO's, it does matter whether these bits are (or are not) hidden
> from the winner."

A **multi-game** with `k` subgames is a `(X, Y × (Fin k → Bool))`-DDS in
which all `k` binary-component sequences are monotone (each is an MBO).  A
winner interacting with a multi-game may either:

* **Not** see the MBO bits — the winner's interface exposes only `Y`
  (hidden-MBO winner, `HiddenWinner`); or
* **See** all MBO bits — the winner's interface exposes `Y × (Fin k → Bool)`
  (visible-MBO winner, `VisibleWinner`).

For a single subgame (`k = 1`) this recovers the ordinary DDG / Winner from
Definition 3.22 / 3.23.  The `DDG X Y` already embodies the k=1 case; the
multi-game generalises to arbitrary `k`.
-/

namespace RandomSystems.CR18

/-! ### Multi-game MBO predicate -/

/-- CR18 §3.7.1 (P9): the `j`-th binary component sequence of a
`(X, Y × (Fin k → Bool))`-DDS is monotone (is an MBO). -/
def DDS.IsComponentMBO {X Y : Type*} {k : ℕ}
    (g : DDS X (Y × (Fin k → Bool))) (j : Fin k) : Prop :=
  ∀ (l : List X) (_ : l ∈ g.dom)
    (i₁ i₂ : ℕ) (_ : i₁ ≤ i₂) (_ : i₂ < l.length),
    (∃ h₁ : l.take (i₁ + 1) ∈ g.dom,
        (g.respond (l.take (i₁ + 1)) h₁).2 j = true) →
    ∃ h₂ : l.take (i₂ + 1) ∈ g.dom,
        (g.respond (l.take (i₂ + 1)) h₂).2 j = true

/-- CR18 §3.7.1 (P9): **all** `k` binary component sequences are MBOs. -/
def DDS.IsMultiMBO {X Y : Type*} {k : ℕ}
    (g : DDS X (Y × (Fin k → Bool))) : Prop :=
  ∀ j : Fin k, g.IsComponentMBO j

/-! ### Multi-game structure (DDG with k MBOs) -/

/-- CR18 §3.7.1 (P9): a **deterministic discrete multi-game** with `k`
subgames — a `(X, Y × (Fin k → Bool))`-DDS in which every binary component
sequence is a monotone binary output.

* `k = 0`: vacuously any DDS (no winning conditions)
* `k = 1`: isomorphic to the single-game `DDG X Y` (see `DDG.toMultiGame`)
* `k ≥ 2`: genuine multi-game -/
structure MultiGame (X Y : Type*) (k : ℕ) where
  /-- The underlying `(X, Y × (Fin k → Bool))`-DDS. -/
  toSystem : DDS X (Y × (Fin k → Bool))
  /-- All k binary component sequences are monotone. -/
  multiMBO : toSystem.IsMultiMBO

namespace MultiGame

variable {X Y : Type*} {k : ℕ}

/-- Coercion to the underlying DDS. -/
instance : CoeTC (MultiGame X Y k) (DDS X (Y × (Fin k → Bool))) where
  coe g := g.toSystem

/-- The regular (`Y`-component) output at an in-domain history. -/
def regularOutput (g : MultiGame X Y k) (l : List X)
    (hl : l ∈ g.toSystem.dom) : Y :=
  (g.toSystem.respond l hl).1

/-- The `j`-th MBO bit at an in-domain history. -/
def mboOutput (g : MultiGame X Y k) (j : Fin k) (l : List X)
    (hl : l ∈ g.toSystem.dom) : Bool :=
  (g.toSystem.respond l hl).2 j

/-- Subgame `j` is won at history `l`. -/
def IsWon (g : MultiGame X Y k) (j : Fin k) (l : List X)
    (hl : l ∈ g.toSystem.dom) : Prop :=
  g.mboOutput j l hl = true

/-- Embed a single-game `DDG X Y` as a `MultiGame X Y 1`. -/
def ofDDG (g : DDG X Y) : MultiGame X Y 1 where
  toSystem := {
    dom            := g.toSystem.dom
    nonempty_input := g.toSystem.nonempty_input
    prefix_closed  := g.toSystem.prefix_closed
    respond        := fun l hl =>
      let (y, a) := g.toSystem.respond l hl
      (y, fun _ => a)
  }
  multiMBO := fun _ l hl i j hij hj ⟨hi_dom, ha⟩ => by
    -- The unique MBO component is the same as the DDG's MBO
    obtain ⟨hj_dom, hbj⟩ := g.mbo l hl i j hij hj ⟨hi_dom, ha⟩
    exact ⟨hj_dom, hbj⟩

end MultiGame

/-! ### Hidden-MBO winner (§3.7.1) -/

/-- CR18 §3.7.1 (P9): a **hidden-MBO winner** for a `MultiGame X Y k` is a
`(Y, X)`-DDE — identical to the single-game winner.

"Hidden" means the winner's interface exposes only the regular output `Y`,
not the `k` MBO bits.  This is the natural generalisation of Definition 3.23:
the MBO bits are at a "special interface" invisible to the winner. -/
abbrev HiddenWinner (X Y : Type*) : Type _ := DDE X Y

namespace HiddenWinner

variable {X Y : Type*} {k : ℕ}

/-- Project a `MultiGame` to a `(X, Y)`-DDS by dropping all MBO bits from
the output — this is the interface seen by a hidden-MBO winner. -/
def projectMultiGame (g : MultiGame X Y k) : DDS X Y where
  dom            := g.toSystem.dom
  nonempty_input := g.toSystem.nonempty_input
  prefix_closed  := g.toSystem.prefix_closed
  respond        := fun l hl => (g.toSystem.respond l hl).1

/-- Bridge instance: `(projectMultiGame g).dom` is definitionally `g.toSystem.dom`, so decidable
membership transports.  Fixes instance synthesis at the `projectMultiGame`-transcript sites. -/
instance projectMultiGame_decidableDom (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)] :
    DecidablePred (fun l : List X => l ∈ (projectMultiGame g).dom) :=
  inferInstanceAs (DecidablePred (fun l : List X => l ∈ g.toSystem.dom))

/-- A hidden-MBO winner wins subgame `j` if the `j`-th MBO bit becomes `true`
for some round.  The winner is run against the projected DDS (sees only `Y`),
and we check the full game's MBO bits at those input prefixes. -/
def Wins (w : HiddenWinner X Y) (g : MultiGame X Y k) (j : Fin k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  let t := DDE.transcript (projectMultiGame g) w fuel
  ∃ (i : ℕ) (_ : i < t.inputs.length)
    (hdom : t.inputs.take (i + 1) ∈ g.toSystem.dom),
      g.mboOutput j (t.inputs.take (i + 1)) hdom = true

/-- A hidden-MBO winner wins **at least one** subgame (OR-combination). -/
def WinsAny (w : HiddenWinner X Y) (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  ∃ j : Fin k, Wins w g j fuel

/-- A hidden-MBO winner wins **all** subgames (AND-combination). -/
def WinsAll (w : HiddenWinner X Y) (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  ∀ j : Fin k, Wins w g j fuel

end HiddenWinner

/-! ### Visible-MBO winner (§3.7.1) -/

/-- CR18 §3.7.1 (P9): a **visible-MBO winner** for a `MultiGame X Y k` is a
`(Y × (Fin k → Bool), X)`-DDE.

"Visible" means the winner receives the full output `(y, a₁, …, aₖ)` at each
round — the MBO bits are **not** hidden.  Maurer notes this distinction only
matters for multi-games:

> "for so-called multi-games … it does matter whether these bits are (or are
> not) hidden from the winner."

Note: even with hidden MBOs, "a DDG can of course be defined in a way that the
regular outputs `yᵢ` contain information about `aᵢ`" — hiding is about the
*interface*, not the information content of `yᵢ`. -/
abbrev VisibleWinner (X Y : Type*) (k : ℕ) : Type _ :=
  DDE X (Y × (Fin k → Bool))

namespace VisibleWinner

variable {X Y : Type*} {k : ℕ}

/-- A visible-MBO winner is run directly against the full `(X, Y × (Fin k →
Bool))`-DDS — it sees both the regular output and all MBO bits. -/
def Wins (w : VisibleWinner X Y k) (g : MultiGame X Y k) (j : Fin k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  let t := DDE.transcript g.toSystem w fuel
  ∃ (i : ℕ) (_ : i < t.inputs.length)
    (hdom : t.inputs.take (i + 1) ∈ g.toSystem.dom),
      g.mboOutput j (t.inputs.take (i + 1)) hdom = true

/-- A visible-MBO winner wins **at least one** subgame. -/
def WinsAny (w : VisibleWinner X Y k) (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  ∃ j : Fin k, Wins w g j fuel

/-- A visible-MBO winner wins **all** subgames. -/
def WinsAll (w : VisibleWinner X Y k) (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) : Prop :=
  ∀ j : Fin k, Wins w g j fuel

end VisibleWinner

/-! ### Relationship: hidden vs. visible winner

A visible-MBO winner can simulate a hidden-MBO winner (it can ignore the extra
bits), but not vice versa.  We state this as a definitional embedding.
-/

/-- Every hidden-MBO winner can be lifted to a visible-MBO winner by having
the visible interface pass only the `Y` component of each output to the
underlying hidden winner's DDE. -/
def HiddenWinner.toVisible {X Y : Type*} {k : ℕ}
    (w : HiddenWinner X Y) : VisibleWinner X Y k :=
  -- The visible winner receives `Option (Y × (Fin k → Bool))` outputs;
  -- it strips the MBO bits and forwards only the `Y` part to `w`.
  fun history => w (history.map (Option.map Prod.fst))

/-- Projecting away the MBO bits commutes with the `⊥`-completion of
Definition 3.3: the fully defined completion of the projected multi-game
outputs exactly the `Y`-component of the full game's completed output. -/
private theorem projectMultiGame_fullyDefined_output {X Y : Type*} {k : ℕ}
    (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (l : List X)
    (h : l ∈ (DDS.fullyDefined (HiddenWinner.projectMultiGame g)).dom)
    (h' : l ∈ (DDS.fullyDefined g.toSystem).dom) :
    (DDS.fullyDefined (HiddenWinner.projectMultiGame g)).output l h =
      Option.map Prod.fst ((DDS.fullyDefined g.toSystem).output l h') := by
  have hdom : (HiddenWinner.projectMultiGame g).dom = g.toSystem.dom := rfl
  have hkept : DDS.keptPrefix (HiddenWinner.projectMultiGame g) l.dropLast =
      DDS.keptPrefix g.toSystem l.dropLast := by
    simp only [DDS.keptPrefix, hdom]
  simp only [DDS.fullyDefined_output, hkept, hdom]
  split
  · rfl
  · rfl

/-- Lockstep invariant for the hidden/visible transcript drivers: whenever the
accumulated prefixes agree on inputs and on `Prod.fst`-projected outputs, the
lifted visible winner (run against the full multi-game) and the underlying
hidden winner (run against the projected game) produce the same inputs. -/
private theorem toVisible_runTranscript_inputs {X Y : Type*} {k : ℕ}
    (w : HiddenWinner X Y) (g : MultiGame X Y k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)] :
    ∀ (fuel : ℕ) (tv : DDE.TranscriptPrefix X (Y × (Fin k → Bool)))
      (th : DDE.TranscriptPrefix X Y),
      tv.inputs = th.inputs →
      tv.outputs.map (Option.map Prod.fst) = th.outputs →
      (DDE.runTranscript g.toSystem (HiddenWinner.toVisible w) fuel tv).inputs =
        (DDE.runTranscript (HiddenWinner.projectMultiGame g) w fuel th).inputs := by
  intro fuel
  induction fuel with
  | zero =>
      intro tv th hin _
      simpa [DDE.runTranscript] using hin
  | succ n ih =>
      rintro ⟨tvi, tvo⟩ ⟨thi, tho⟩ hin hout
      dsimp only at hin hout
      subst hin
      subst hout
      have hvis : HiddenWinner.toVisible (k := k) w tvo =
          w (tvo.map (Option.map Prod.fst)) := rfl
      cases hw : w (tvo.map (Option.map Prod.fst)) with
      | none =>
          have h₁ : DDE.runTranscript g.toSystem (HiddenWinner.toVisible w)
              (n + 1) ⟨tvi, tvo⟩ = ⟨tvi, tvo⟩ :=
            DDE.runTranscript_halting_clause _ _ ⟨tvi, tvo⟩ n hw
          have h₂ : DDE.runTranscript (HiddenWinner.projectMultiGame g) w
              (n + 1) ⟨tvi, tvo.map (Option.map Prod.fst)⟩ =
              ⟨tvi, tvo.map (Option.map Prod.fst)⟩ :=
            DDE.runTranscript_halting_clause _ _
              ⟨tvi, tvo.map (Option.map Prod.fst)⟩ n hw
          rw [h₁, h₂]
      | some x =>
          simp only [DDE.runTranscript, hvis, hw]
          refine ih _ _ rfl ?_
          have hdom : tvi ++ [x] ∈ (DDS.fullyDefined g.toSystem).dom := by
            simp [DDS.fullyDefined]
          simp only [DDE.extendWithInput, List.map_append, List.map_cons,
            List.map_nil]
          rw [projectMultiGame_fullyDefined_output g (tvi ++ [x]) _ hdom]

/-- Winning a multi-game as a hidden winner is equivalent to winning it as
the lifted visible winner (which ignores the MBO bits in the visible outputs).

This captures "hidden = visible that ignores the MBO bits": both run the same
DDE logic on the `Y` component of each output, so the input sequences produced
are identical, and hence the same MBO bits are triggered at the same rounds. -/
theorem HiddenWinner.toVisible_wins_iff {X Y : Type*} {k : ℕ}
    (w : HiddenWinner X Y) (g : MultiGame X Y k) (j : Fin k)
    [DecidablePred (fun l : List X => l ∈ g.toSystem.dom)]
    (fuel : ℕ) :
    w.toVisible.Wins g j fuel ↔ w.Wins g j fuel := by
  have hinputs :
      (DDE.transcript g.toSystem (HiddenWinner.toVisible w) fuel).inputs =
        (DDE.transcript (HiddenWinner.projectMultiGame g) w fuel).inputs :=
    toVisible_runTranscript_inputs w g fuel DDE.TranscriptPrefix.empty
      DDE.TranscriptPrefix.empty rfl rfl
  simp only [VisibleWinner.Wins, HiddenWinner.Wins]
  rw [hinputs]

/-! ## Discrete Distinguisher (DDD) — Definition 3.24 -/

/-- CR18 Definition 3.24: the possible outputs of one step of a discrete
distinguisher.

A DDD is like a DDE but with *two* stop symbols `⊣₀` and `⊣₁` instead of one.
At each step the distinguisher either:
- sends a query `x` to the system and continues, or
- emits a stop symbol `⊣ᵢ` (indexed by `i : Bool`, `false = 0`, `true = 1`).
-/
inductive DDDStep (X : Type*)
  /-- Send query `x` to the system and continue the interaction. -/
  | query (x : X) : DDDStep X
  /-- Emit stop symbol `⊣ᵢ` and halt; `i = false` is `⊣₀`, `i = true` is `⊣₁`. -/
  | stop  (i : Bool) : DDDStep X
  deriving DecidableEq

namespace DDDStep

variable {X : Type*}

/-- The stop index as a natural number (0 or 1). -/
def stopIndex : DDDStep X → ℕ
  | stop i  => i.toNat
  | query _ => 0

/-- `true` iff this step is a stop (either stop symbol). -/
def isStop : DDDStep X → Bool
  | stop _  => true
  | query _ => false

end DDDStep

/-- CR18 Definition 3.24: a **(deterministic) discrete distinguisher for
`(X, Y)`-systems (DDD)** is an environment with two stop symbols `⊣₀` and `⊣₁`.

At each step, given the output history `(y₁, …, yᵢ₋₁)` seen so far, the DDD
either sends a new query `xᵢ ∈ X` to the system, or emits one of the two stop
symbols `⊣₀` / `⊣₁` and halts.

We model the history as `List (Option Y)` (matching `DDE`; `none = ⊥` means the
system did not reply), and each step as a `DDDStep X`.

Maurer: "A (deterministic) discrete distinguisher for (X, Y)-system (DDD) is
an environment `d` for (X, Y)-systems which, when it stops, also outputs a bit.
… it is an environment with two stop symbols `⊣₀` and `⊣₁`. The output of `d`
for system `s` is equal to the index of the stopping symbol. If `d` does not
stop … then the output is defined to be 0." -/
def DDD (X Y : Type*) := List (Option Y) → DDDStep X

namespace DDD

variable {X Y : Type*}

/-- The DDD stops with symbol `⊣ᵢ` after seeing history `l`. -/
def StopsAt (d : DDD X Y) (l : List (Option Y)) (i : Bool) : Prop :=
  d l = DDDStep.stop i

/-- The DDD emits a stop symbol (for some index) after seeing history `l`. -/
def Stops (d : DDD X Y) (l : List (Option Y)) : Prop :=
  (d l).isStop = true

/-- The first step taken by the DDD before seeing any system output. -/
def firstStep (d : DDD X Y) : DDDStep X := d []

/-! ### Fuel-bounded execution against a DDS -/

/-- Running state of a DDD interacting with a `(X, Y)`-DDS.

Records the accumulated input/output histories and whether the DDD has halted,
in the same spirit as `DDE.TranscriptPrefix`. -/
structure Transcript (X Y : Type*) where
  /-- The inputs sent to the system so far. -/
  inputs  : List X
  /-- The outputs received from the system (`Option Y` as in CR18). -/
  outputs : List (Option Y)
  /-- `some i` once the DDD has halted with stop symbol `⊣ᵢ`; `none` = running. -/
  halted  : Option Bool

/-- The initial empty transcript before any interaction. -/
def Transcript.empty : Transcript X Y where
  inputs  := []
  outputs := []
  halted  := none

/-- Fuel-bounded execution of `d` against `s`, starting from transcript `t`.

Each step either:
- halts immediately if already halted (returns `t` unchanged), or
- evaluates `d t.outputs`:
  * `stop i` → records `halted := some i` and returns;
  * `query x` → appends `x` to inputs, evaluates `s⊥`, appends the result to
    outputs, and recurses with one less unit of fuel. -/
def run (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (d : DDD X Y) : ℕ → Transcript X Y → Transcript X Y
  | 0,     t => t
  | n + 1, t =>
      if t.halted.isSome then t
      else match d t.outputs with
        | DDDStep.stop i  => { t with halted := some i }
        | DDDStep.query x =>
            let inputs' := t.inputs ++ [x]
            let y := (DDS.fullyDefined s).output inputs' (by
              simp [DDS.fullyDefined, inputs'])
            run s d n
              { inputs  := inputs'
                outputs := t.outputs ++ [y]
                halted  := none }

/-- CR18 Definition 3.24: execute `d` against `s` for up to `fuel` steps. -/
def exec (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (d : DDD X Y) (fuel : ℕ) : Transcript X Y :=
  run s d fuel Transcript.empty

/-- CR18 Definition 3.24: **the output of `d` for system `s`**.

Returns the index (0 or 1) of the stop symbol `⊣ᵢ` emitted by `d`.
If `d` does not stop within `fuel` steps, returns 0 (Maurer's default). -/
def output (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (d : DDD X Y) (fuel : ℕ) : ℕ :=
  match (exec s d fuel).halted with
  | some i => i.toNat
  | none   => 0

/-- Embed a DDD as a plain `DDE` by conflating both stop symbols into one `⊣`.

This forgets the stop-index but is useful for relating DDDs to the existing DDE
transcript infrastructure (e.g., `DDE.transcript`). -/
def toDDE (d : DDD X Y) : DDE X Y := fun outs =>
  match d outs with
  | DDDStep.query x => some x
  | DDDStep.stop _  => none

/-! ### Basic lemmas -/

/-- If `d` stops at history `l` with index `i`, then `toDDE d` stops at `l`. -/
theorem toDDE_stops_of_stop (d : DDD X Y) (l : List (Option Y)) (i : Bool)
    (h : d.StopsAt l i) : d.toDDE l = none := by
  simp [toDDE, StopsAt] at *
  rw [h]

/-- With zero fuel the DDD has no time to run; output defaults to 0. -/
@[simp]
theorem output_zero_fuel (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (d : DDD X Y) : output s d 0 = 0 := by
  simp [output, exec, run, Transcript.empty]

/-- If the DDD immediately stops with `⊣ᵢ` on the empty history, running it for
any positive amount of fuel returns `i.toNat`. -/
theorem output_of_immediate_stop (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)]
    (d : DDD X Y) (i : Bool) (h : d.StopsAt [] i) (fuel : ℕ) (hfuel : 0 < fuel) :
    output s d fuel = i.toNat := by
  cases fuel with
  | zero  => omega
  | succ n =>
    simp [output, exec, run, Transcript.empty, StopsAt] at *
    rw [show d [] = DDDStep.stop i from h]

end DDD

end RandomSystems.CR18

/-!
## CR18 Definition 4.5 — Game as a G-valued Random Variable

CR18 §4.5.1 gives the Chapter 4 instantiation of the abstract problem/solver
framework (Definition 4.2) to games.

> **Definition 4.5.** A game **G** is a **G**-valued random variable over G,
> a winner **W** is a **W**-valued random variable, the performance set is
> Ω = [0, 1], and the performance of **W** for game **G** is the winning
> probability, i.e.,
>
>   **G**(**W**) := Pr[ω(**W**, **G**) = 1].

Here:
* `G` is an arbitrary type of (deterministic) games — in the running example,
  `DDG X Y`, but Definition 4.5 is stated for any abstract `G`.
* `W` is an arbitrary type of (deterministic) winners.
* `ω : W → G → Bool` is the winning predicate (`ω(w, g) = 1` iff `w` wins `g`).
* A game **G** is a `Dist G` (a G-valued random variable, sub-distribution).
* A winner **W** is a `Dist W` (a W-valued random variable).
* The performance (winning probability) is `∑ w g, W(w) * G(g) * ω(w,g)`.

Multi-games (k subgames, winning predicates ω₁, …, ωₖ) are also covered here.
-/

namespace RandomSystems.CR18

namespace Def45

/-! ### Abstract winning predicate and game type -/

/-- CR18 §4.5.1: a **game structure** bundles an abstract set of games `G`,
an abstract set of winners `W`, and a winning predicate `ω : W → G → Bool`.

Maurer: "we consider a setting with a set G of (deterministic) games and a
set W of (deterministic) winners, and a function ω : W × G → {0,1}." -/
structure GameStructure where
  /-- Type of deterministic games. -/
  Game   : Type*
  /-- Type of deterministic winners. -/
  Winner : Type*
  /-- Winning predicate: `win w g = true` iff `w` wins `g`. -/
  win    : Winner → Game → Bool

namespace GameStructure

/-! ### Probabilistic game (G-valued random variable) -/

/-- CR18 Definition 4.5: a **probabilistic game** is a random variable over
deterministic games, i.e., a `Dist` (finite-support sub-distribution) over
`gs.Game`.

Maurer: "A game **G** is a **G**-valued random variable over G." -/
def ProbGame (gs : GameStructure) : Type* := Dist gs.Game

/-- CR18 Definition 4.5: a **probabilistic winner** is a random variable over
deterministic winners, i.e., a `Dist` over `gs.Winner`.

Maurer: "a winner **W** is a **W**-valued random variable." -/
def ProbWinner (gs : GameStructure) : Type* := Dist gs.Winner

/-! ### Winning probability (the performance function) -/

/-- CR18 Definition 4.5: the **winning probability** of probabilistic winner
**W** against probabilistic game **G**.

Maurer: "the performance of **W** for game **G** is the winning probability,
i.e., **G**(**W**) := Pr[ω(**W**, **G**) = 1]."

Since **W** and **G** are independent, the joint probability is:
  Pr[ω(W, G) = 1] = ∑ w g, W(w) · G(g) · [ω(w,g) = 1]

In the `Dist` (`Finsupp`) model this is the nested `Finsupp.sum` over the finite
supports of `W` and `G`: draw `w ← W` and `g ← G` independently, then evaluate
`ω(w, g)`. -/
noncomputable def winProb (gs : GameStructure)
    (W : Dist gs.Winner) (G : Dist gs.Game) : NNReal :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * if gs.win w g then 1 else 0

/-- `winProb` is bounded above by 1 (it is a probability) for probability
distributions `W`, `G`.

The probability-distribution hypotheses are stated `Fintype`-free as Finsupp
total masses `= 1` (the LM20 `Dist` weight, see `Dist.weight_eq_finsupp_sum`);
this is needed because concrete game types (`DDG X Y`) are infinite.  For
`Fintype` carriers the hypotheses are equivalent to `isProbDist`. -/
theorem winProb_le_one (gs : GameStructure)
    (W : Dist gs.Winner) (G : Dist gs.Game)
    (hW : W.sum (fun _ p => p) = 1) (hG : G.sum (fun _ p => p) = 1) :
    gs.winProb W G ≤ 1 := by
  -- Bound the indicator `if win w g then 1 else 0 ≤ 1` so each inner term
  -- `wp * gp * (if …) ≤ wp * gp`, then the double sum collapses to
  -- the product of the total masses `1 * 1 = 1` via `Finsupp.mul_sum`.
  rw [GameStructure.winProb]
  have hinner :
      (Finsupp.sum W fun w wp =>
          G.sum fun g gp => wp * gp * if gs.win w g then 1 else 0) ≤
        Finsupp.sum W fun _ wp => wp := by
    apply Finsupp.sum_le_sum
    intro w _
    have hb :
        (Finsupp.sum G fun g gp => W w * gp * if gs.win w g then 1 else 0) ≤
          Finsupp.sum G fun _ gp => W w * gp := by
      apply Finsupp.sum_le_sum
      intro g _
      split <;> simp
    calc (Finsupp.sum G fun g gp => W w * gp * if gs.win w g then 1 else 0)
        ≤ Finsupp.sum G fun _ gp => W w * gp := hb
      _ = W w * Finsupp.sum G fun _ gp => gp := by rw [Finsupp.mul_sum]
      _ = W w := by rw [hG, mul_one]
  calc (Finsupp.sum W fun w wp =>
          G.sum fun g gp => wp * gp * if gs.win w g then 1 else 0)
      ≤ Finsupp.sum W fun _ wp => wp := hinner
    _ = 1 := hW

/-- `winProb` is non-negative (trivially, since it is an `NNReal`). -/
theorem winProb_nonneg (gs : GameStructure)
    (W : Dist gs.Winner) (G : Dist gs.Game) :
    0 ≤ gs.winProb W G := zero_le _

/-- Embed a deterministic game as the degenerate probabilistic game
concentrated at that game (point-mass distribution). -/
noncomputable def ProbGame.pure {gs : GameStructure} (g : gs.Game) : gs.ProbGame :=
  Finsupp.single g 1

/-- Embed a deterministic winner as the degenerate probabilistic winner
concentrated at that winner. -/
noncomputable def ProbWinner.pure {gs : GameStructure} (w : gs.Winner) : gs.ProbWinner :=
  Finsupp.single w 1

/-- For a degenerate game concentrated at `g` and a degenerate winner
concentrated at `w`, the winning probability equals `ω(w, g)` (0 or 1). -/
@[simp]
theorem winProb_pure_pure (gs : GameStructure) (w : gs.Winner) (g : gs.Game) :
    gs.winProb (Finsupp.single w 1) (Finsupp.single g 1) =
      if gs.win w g then 1 else 0 := by
  classical
  simp only [winProb]
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_single_index (by simp)]
  simp

end GameStructure

/-! ### Multi-game extension (§4.5.1)

CR18 §4.5.1: "A more general setting is when a game consists of several
(say k) subgames, i.e., when there are k functions ω₁, …, ωₖ with
ωᵢ : W × G → {0,1}, where ωᵢ(w,g) = 1 is interpreted as w winning the
i-th subgame of g. Such a game g (or the probabilistic counter-part G) is
called a **multi-game**."
-/

/-- CR18 §4.5.1: a **multi-game structure** bundles sets G and W with k
winning predicates ω₁, …, ωₖ.  The single-game case (`k = 1`) recovers
`GameStructure` up to `Fin 1`. -/
structure MultiGameStructure (k : ℕ) where
  /-- Type of deterministic games. -/
  Game   : Type*
  /-- Type of deterministic winners. -/
  Winner : Type*
  /-- The `k` winning predicates: `win j w g = true` iff `w` wins subgame `j`. -/
  win    : Fin k → Winner → Game → Bool

namespace MultiGameStructure

variable {k : ℕ}

/-- Probabilistic multi-game: a `Dist` over deterministic games. -/
def ProbGame (mgs : MultiGameStructure k) : Type* := Dist mgs.Game

/-- Probabilistic winner for a multi-game: a `Dist` over deterministic winners. -/
def ProbWinner (mgs : MultiGameStructure k) : Type* := Dist mgs.Winner

/-- CR18 §4.5.1: winning probability for subgame `j`. -/
noncomputable def winProb (mgs : MultiGameStructure k) (j : Fin k)
    (W : Dist mgs.Winner) (G : Dist mgs.Game) : NNReal :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * if mgs.win j w g then 1 else 0

/-- CR18 Definition 4.6 (OR-game): `w` wins `g∨` iff `w` wins at least one
subgame of `g`.

Maurer: "g∨ … the game corresponding to the logical OR of the k subgames,
i.e., the game of winning at least one of the games:
  ω(w, g∨) = ⋁ᵢ ωᵢ(w, g)." -/
def winOR (mgs : MultiGameStructure k) (w : mgs.Winner) (g : mgs.Game) : Bool :=
  decide (∃ j : Fin k, mgs.win j w g = true)

/-- CR18 Definition 4.6 (AND-game): `w` wins `g∧` iff `w` wins all subgames.

Maurer: "g∧ … the game corresponding to the logical AND of the k subgames,
i.e., the game of winning all of the games:
  ω(w, g∧) = ⋀ᵢ ωᵢ(w, g)."

Edge cases:
* `k = 0`: vacuously `true` (empty AND); the winner trivially wins the empty game.
* `k = 1`: reduces to the single winning predicate `ω₀(w, g)`.
-/
def winAND (mgs : MultiGameStructure k) (w : mgs.Winner) (g : mgs.Game) : Bool :=
  decide (∀ j : Fin k, mgs.win j w g = true)

/-- CR18 P5: `winAND` returns `true` iff the winner wins every subgame.

This is the characteristic property of the AND-game:
  `ω(w, g∧) = true  ↔  ∀ j, ωⱼ(w, g) = true`. -/
@[simp]
theorem winAND_true_iff (mgs : MultiGameStructure k) (w : mgs.Winner) (g : mgs.Game) :
    mgs.winAND w g = true ↔ ∀ j : Fin k, mgs.win j w g = true := by
  simp [winAND]

/-- CR18 P5: `winAND` returns `false` iff there exists a subgame the winner loses. -/
theorem winAND_false_iff (mgs : MultiGameStructure k) (w : mgs.Winner) (g : mgs.Game) :
    mgs.winAND w g = false ↔ ∃ j : Fin k, mgs.win j w g = false := by
  simp [winAND, decide_eq_false_iff_not, not_forall]

/-- The OR-game as a `GameStructure`. -/
def toGameStructureOR (mgs : MultiGameStructure k) : GameStructure where
  Game   := mgs.Game
  Winner := mgs.Winner
  win    := mgs.winOR

/-- The AND-game as a `GameStructure` (CR18 Definition 4.6, P5).

The winning predicate of the AND-game is `winAND`. -/
def toGameStructureAND (mgs : MultiGameStructure k) : GameStructure where
  Game   := mgs.Game
  Winner := mgs.Winner
  win    := mgs.winAND

/-- CR18 P5: the AND-game's winning predicate is `winAND` (definitionally). -/
@[simp]
theorem toGameStructureAND_win (mgs : MultiGameStructure k) :
    mgs.toGameStructureAND.win = mgs.winAND := rfl

/-- CR18 P5: the winning probability for the AND-game (winning ALL subgames).

The winning probability of the AND-game is at most the winning probability of
every individual subgame:
  **G**∧(**W**) ≤ **G**ⱼ(**W**) for each j.

This reflects the CR18 prose (§4.9.1):
  "one cannot win both games with probability better than βγ." -/
noncomputable def winProbAND (mgs : MultiGameStructure k)
    (W : Dist mgs.Winner) (G : Dist mgs.Game) : NNReal :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * if mgs.winAND w g then 1 else 0

/-- CR18 P5: `winProbAND` equals the winning probability of `toGameStructureAND`. -/
@[simp]
theorem winProbAND_eq (mgs : MultiGameStructure k)
    (W : Dist mgs.Winner) (G : Dist mgs.Game) :
    mgs.winProbAND W G = GameStructure.winProb mgs.toGameStructureAND W G := by
  -- Both sides are definitionally equal after unfolding
  rfl

/-- CR18 P5: AND-winning probability is bounded above by each subgame's winning
probability.

For each subgame index `j`, if a winner has winning probability `p` for the
AND-game, they have winning probability ≥ `p` for subgame `j` alone. -/
theorem winProbAND_le_winProb (mgs : MultiGameStructure k) (j : Fin k)
    (W : Dist mgs.Winner) (G : Dist mgs.Game) :
    mgs.winProbAND W G ≤ mgs.winProb j W G := by
  -- Both sides are nested `Finsupp.sum`s differing only in the indicator:
  -- `winAND w g` vs `win j w g`.  Since `winAND w g = true → win j w g = true`,
  -- the AND indicator is ≤ the subgame-`j` indicator pointwise, so each inner
  -- term is bounded, and `Finsupp.sum_le_sum` lifts this to the double sum.
  unfold winProbAND winProb
  apply Finsupp.sum_le_sum
  intro w _
  apply Finsupp.sum_le_sum
  intro g _
  gcongr
  split
  · rename_i h
    have hj : mgs.win j w g = true := (winAND_true_iff mgs w g).mp h j
    simp [hj]
  · simp

/-- A single-game structure is a degenerate multi-game structure with `k = 1`. -/
def ofGameStructure (gs : GameStructure) : MultiGameStructure 1 where
  Game   := gs.Game
  Winner := gs.Winner
  win    := fun _ => gs.win

/-- CR18 P5: for k=0, the AND-game is trivially won (empty conjunction is true). -/
theorem winAND_zero_eq_true (mgs : MultiGameStructure 0) (w : mgs.Winner) (g : mgs.Game) :
    mgs.winAND w g = true := by
  simp [winAND]

/-- CR18 P5: AND and OR coincide for a single subgame (k=1). -/
theorem winAND_eq_winOR_of_one (mgs : MultiGameStructure 1) (w : mgs.Winner) (g : mgs.Game) :
    mgs.winAND w g = mgs.winOR w g := by
  simp [winAND, winOR]

end MultiGameStructure

end Def45

end RandomSystems.CR18

/-!
## CR18 Definition 4.7 — Distinction Problem

CR18 §4.5.2 (Maurer's lecture notes, "Cryptography: Random Systems"):

> **Setting.** A set O of objects, a set D of (deterministic) distinguishers, and
> a function `κ : D × O → {0, 1}` (the decision function).
>
> **Definition 4.7.** A *distinction problem* is a pair `(S₀, S₁)` of O-valued
> random variables (distributions), and will be denoted as `⟨S₀ | S₁⟩`.
> A *distinguisher* **D** is a D-valued random variable.
> The *performance* of **D** for distinction problem `⟨S₀ | S₁⟩` is
>
>   `⟨S₀ | S₁⟩(D) := Δ_D(S₀, S₁) = Pr^{D·S₁}[κ(D, S₁) = 1] − Pr^{D·S₀}[κ(D, S₀) = 1]`

### Lean representation

* An `O`-valued random variable is a `Dist O` (sub-distribution, LM20 Def 1).
* A `D`-valued random variable (probabilistic distinguisher) is a `Dist D`.
* The setting parameters are bundled in `DistinctionStructure`: the types `O`
  and `D`, and the decision function `κ : D → O → Bool`.
* `DistinctionProblem` is a `Dist O × Dist O` (the pair `(S₀, S₁)`) — i.e. a
  *pair of PDS* when `O` is a DDS type.
* The performance function `DistinctionStructure.performance` computes
  `Δ_D(S₀, S₁)` as a real number.
-/

namespace RandomSystems.CR18

namespace Def47

/-! ### Setting parameters (§4.5.2) -/

/-- CR18 §4.5.2: the **distinction structure** — the setting parameters for
a distinction problem.

Maurer: "we consider a setting with a set O of objects, a set D of
(deterministic) distinguishers, and a function κ : D × O → {0, 1}." -/
structure DistinctionStructure where
  /-- Type of objects. -/
  O : Type*
  /-- Type of deterministic distinguishers. -/
  D : Type*
  /-- Decision function: `κ d o = true` iff distinguisher `d` outputs 1 on object `o`. -/
  κ : D → O → Bool

namespace DistinctionStructure

/-! ### The distinction problem -/

/-- CR18 Definition 4.7: a **distinction problem** `⟨S₀ | S₁⟩` is a pair of
O-valued random variables (distributions).

Maurer: "A distinction problem is a pair (S₀, S₁) of O-valued random
variables (or, more precisely, distributions)."

In our model each `Sᵢ` is a `Dist ds.O` (finite-support sub-distribution, LM20
Def 1), so a distinction problem is a *pair of `Dist`* — exactly a pair of PDS
when `ds.O` is a DDS type. -/
abbrev DistinctionProblem (ds : DistinctionStructure) : Type* :=
  Dist ds.O × Dist ds.O

/-- CR18 Definition 4.7: a **probabilistic distinguisher** **D** is a
D-valued random variable.

Maurer: "A distinguisher D is a D-valued random variable." -/
abbrev ProbDistinguisher (ds : DistinctionStructure) : Type* :=
  Dist ds.D

/-! ### Performance function -/

/-- CR18 Definition 4.7: the **per-distinguisher advantage** of a
*deterministic* distinguisher `d` for distinction problem `⟨S₀ | S₁⟩`.

This is the signed quantity:
  `Δ_d(S₀, S₁) := Pr^{d·S₁}[κ(d, S₁) = 1] − Pr^{d·S₀}[κ(d, S₀) = 1]`

Both expectations are over the independent O-valued distributions `S₀` and `S₁`.
Since `d` is deterministic, the probabilities reduce to a `Finsupp.sum` over the
support of each distribution (`NNReal` masses coerced into `Real`). -/
noncomputable def advantageDet (ds : DistinctionStructure)
    (d : ds.D) (S₀ S₁ : Dist ds.O) : Real :=
  (S₁.sum fun o w => (w : Real) * if ds.κ d o then 1 else 0) -
  (S₀.sum fun o w => (w : Real) * if ds.κ d o then 1 else 0)

/-- CR18 Definition 4.7: the **performance** of a *probabilistic* distinguisher
**D** (a D-valued random variable) for distinction problem `⟨S₀ | S₁⟩`.

Maurer: "the performance of D for distinction problem ⟨S₀ | S₁⟩ is
  ⟨S₀ | S₁⟩(D) := Δ_D(S₀, S₁)
               = Pr^{D·S₁}[κ(D, S₁) = 1] − Pr^{D·S₀}[κ(D, S₀) = 1]"

Since **D** and **S** are independent, the joint probability is:
  `Pr^{D·Sᵢ}[κ(D, Sᵢ) = 1] = ∑ d o, D(d) · Sᵢ(o) · [κ(d, o) = 1]`
(here a nested `Finsupp.sum` over the supports of `D` and `Sᵢ`).
-/
noncomputable def performance (ds : DistinctionStructure)
    (prob : ds.DistinctionProblem) (D : ds.ProbDistinguisher) : Real :=
  let ⟨S₀, S₁⟩ := prob
  (D.sum fun d dw => S₁.sum fun o ow =>
      (dw : Real) * (ow : Real) * if ds.κ d o then 1 else 0) -
  (D.sum fun d dw => S₀.sum fun o ow =>
      (dw : Real) * (ow : Real) * if ds.κ d o then 1 else 0)

/-! ### Basic properties -/

/-- The performance of a deterministic distinguisher (point-mass on `d`) for a
distinction problem equals the per-distinguisher advantage `advantageDet`. -/
@[simp]
theorem performance_pure (ds : DistinctionStructure)
    (d : ds.D) (S₀ S₁ : Dist ds.O) :
    ds.performance (S₀, S₁) (Finsupp.single d 1) = ds.advantageDet d S₀ S₁ := by
  -- Collapse each outer `Finsupp.sum` over the point-mass `Finsupp.single d 1`
  -- to its single term at `d` (with weight `1`), matching `advantageDet`.
  classical
  simp only [performance, advantageDet]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp

/-- The performance is antisymmetric: swapping `S₀` and `S₁` negates the
performance.

This mirrors CR18's signed `Δ_D(S₀, S₁) = −Δ_D(S₁, S₀)`. -/
theorem performance_neg_of_swap (ds : DistinctionStructure)
    (prob : ds.DistinctionProblem) (D : ds.ProbDistinguisher) :
    ds.performance (prob.2, prob.1) D = - ds.performance prob D := by
  obtain ⟨S₀, S₁⟩ := prob
  simp only [performance]
  ring

/-- The performance of a *trivial* distinguisher — one that always outputs 0
(never outputs 1) — is 0, regardless of the distinction problem. -/
theorem performance_zero_distinguisher (ds : DistinctionStructure)
    (S₀ S₁ : Dist ds.O) (D : ds.ProbDistinguisher)
    (hκ : ∀ d : ds.D, ∀ o : ds.O, ds.κ d o = false) :
    ds.performance (S₀, S₁) D = 0 := by
  simp [performance, hκ]

end DistinctionStructure

end Def47

end RandomSystems.CR18

/-!
## CR18 Definition 4.8 — Bit-Guessing Problem

CR18 §4.5.3 (Maurer's lecture notes, "Cryptography: Random Systems"):

> **Setting.** A set O of objects, a set D of (deterministic) distinguishers
> (also called *bit-guessers*), and a function `κ : D × O → {0, 1}`.
>
> **Definition 4.8.** A *bit-guessing problem* is a pair — an `O × {0, 1}`-valued
> random variable `(S, B)` — and is denoted as `[S; B]`.
> A *distinguisher* (or *bit-guesser*) **D** is a D-valued random variable.
> The *performance* of **D** for bit-guessing problem `[S; B]` is, *as literally
> printed in CR18 (Definition 4.8, and Definition 2.9)*:
>
>   `[S; B](D) := Λ_D(S, B) = 2 · Pr_{D·(S,B)}[κ(D, S) = B] − 1/2`
>
> **This printed formula is wrong (typo in the notes).**  We use the corrected
> form (see DEVIATION marker on `advantageDet`):
>
>   `[S; B](D) := Λ_D(S, B) = 2 · (Pr_{D·(S,B)}[κ(D, S) = B] − 1/2)`
>                           = 2 · Pr_{D·(S,B)}[κ(D, S) = B] − 1`
>
> The performance lies in `[−1, 1]`: performance `1` means D always guesses
> correctly (`Pr = 1`); performance `−1` means D never guesses correctly
> (`Pr = 0`).  These anchors hold only for the `−1` version; the printed
> `−1/2` version would give the range `[−1/2, 3/2]`, contradicting Maurer's
> own stated range and the Lemma 2.3 proof chain (see DEVIATIONS log).
>
> Note: `(S, B)` is modeled as a *single* `Dist (O × Bool)` — the correlation
> between the object and the hidden bit is captured in the joint distribution.

### Lean representation

* `O × Bool` is the joint type of `(S, B)`.
* A `(O × Bool)`-valued random variable is a `Dist (O × Bool)`.
* A `D`-valued probabilistic distinguisher is a `Dist D`.
* The setting parameters are bundled in `BitGuessingStructure`.
* `BitGuessingProblem` is a `Dist (O × Bool)` (the joint `(S, B)`).
* `BitGuessingStructure.performance` computes `Λ_D(S, B)` as a real number.
-/

namespace RandomSystems.CR18

namespace Def48

/-! ### Setting parameters (§4.5.3) -/

/-- CR18 §4.5.3: the **bit-guessing structure** — the setting parameters for
a bit-guessing problem.

Maurer: "we consider a setting with a set O of objects, a set D of
(deterministic) distinguishers, and a function κ : D × O → {0, 1}."

This is the same setting as `Def47.DistinctionStructure` — the distinction is
in *how* the problem and performance are defined, not in the parameters. -/
structure BitGuessingStructure where
  /-- Type of objects (the "system" side). -/
  O : Type*
  /-- Type of deterministic distinguishers (bit-guessers). -/
  D : Type*
  /-- Decision function: `κ d o = true` iff distinguisher `d` outputs 1 on object `o`. -/
  κ : D → O → Bool

namespace BitGuessingStructure

/-! ### The bit-guessing problem -/

/-- CR18 Definition 4.8: a **bit-guessing problem** `[S; B]` is an
`O × Bool`-valued random variable.

Maurer: "A bit-guessing problem is a pair [—] an O × {0,1}-valued random
variable (S, B), and is denoted as [S; B]."

The joint distribution `Dist (O × Bool)` captures the correlation between
the object `S` and the hidden bit `B`. -/
abbrev BitGuessingProblem (bgs : BitGuessingStructure) : Type* :=
  Dist (bgs.O × Bool)

/-- CR18 Definition 4.8: a **probabilistic bit-guesser** **D** is a
D-valued random variable.

Maurer: "A distinguisher (or bit-guesser) D is a D-valued random variable." -/
abbrev ProbBitGuesser (bgs : BitGuessingStructure) : Type* :=
  Dist bgs.D

/-! ### Performance function -/

-- DEVIATION FROM CR18 (Definition 4.8): the notes literally print
-- `Λ_D(S,B) = 2 · Pr[κ(D,S)=B] − 1/2` (mirrored verbatim from Definition 2.9
-- and the IND-CPA discussion).  That printed constant `−1/2` is a typo: it
-- yields the range `[−1/2, 3/2]`, contradicting (i) Maurer's own assertion that
-- the performance "is between −1 and 1", (ii) the explicit anchors "performance
-- 1 ⇔ Pr = 1" / "performance −1 ⇔ Pr = 0", and (iii) the Lemma 2.3 proof, whose
-- chain `2·(½a+½b) − c = Δ_D(S₀,S₁)` only closes for `c = 1`.  The intended
-- definition is the standard calibrated advantage `2·(Pr − 1/2) = 2·Pr − 1`,
-- which is what we implement here.
/-- CR18 Definition 4.8: the **per-distinguisher advantage** of a
*deterministic* bit-guesser `d` for bit-guessing problem `[S; B]`.

We use the corrected calibration (see DEVIATION note above; the printed `−1/2`
is a typo):
  `Λ_d(S, B) := 2 · (Pr_{(s,b) ∼ (S,B)}[κ(d, s) = b] − 1/2)`
             = 2 · Pr_{(s,b) ∼ (S,B)}[κ(d, s) = b] − 1`

Expanded:
  `Λ_d(S, B) = 2 · (∑ (o,b), (S,B)(o,b) · [κ(d,o) = b]) − 1`

Since `κ(d, o) ∈ Bool` and `b ∈ Bool`, the indicator `[κ(d,o) = b]` is 1
when they match and 0 otherwise. -/
noncomputable def advantageDet (bgs : BitGuessingStructure)
    (d : bgs.D) (SB : Dist (bgs.O × Bool)) : Real :=
  2 * (SB.sum fun ob w => (w : Real) *
        if bgs.κ d ob.1 = ob.2 then 1 else 0) - 1

/-- CR18 Definition 4.8: the **performance** of a *probabilistic* bit-guesser
**D** (a D-valued random variable) for bit-guessing problem `[S; B]`.

Maurer (Definition 4.8) literally prints
  `[S; B](D) := Λ_D(S, B) = 2 · Pr_{D·(S,B)}[κ(D, S) = B] − 1/2`,
but the constant `−1/2` is a typo (see the DEVIATION note on `advantageDet`).
We use the corrected, calibrated form:
  `[S; B](D) := 2 · (Pr_{D·(S,B)}[κ(D, S) = B] − 1/2) = 2 · Pr − 1`.

Since **D** and **(S, B)** are independent, the joint probability is:
  `Pr_{D·(S,B)}[κ(D,S) = B] = ∑ d (o,b), D(d) · (S,B)(o,b) · [κ(d,o) = b]`
-/
noncomputable def performance (bgs : BitGuessingStructure)
    (SB : bgs.BitGuessingProblem) (D : bgs.ProbBitGuesser) : Real :=
  2 * (D.sum fun d dw => SB.sum fun ob ow =>
        (dw : Real) * (ow : Real) *
        if bgs.κ d ob.1 = ob.2 then 1 else 0) - 1

/-! ### Basic properties -/

/-- The performance of a deterministic bit-guesser (point-mass on `d`) for a
bit-guessing problem equals the per-distinguisher advantage `advantageDet`. -/
@[simp]
theorem performance_pure (bgs : BitGuessingStructure)
    (d : bgs.D) (SB : Dist (bgs.O × Bool)) :
    bgs.performance SB (Finsupp.single d 1) = bgs.advantageDet d SB := by
  -- Collapse the outer `Finsupp.sum` over the point-mass `Finsupp.single d 1`
  -- to its single term at `d` (with weight `1`), matching `advantageDet`.
  classical
  simp only [performance, advantageDet]
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- Performance lies in `[−1, 1]`: at least `−1` and at most `1`.
Maurer: "The performance [S; B](D) is between −1 and 1." -/
theorem performance_le_one (bgs : BitGuessingStructure)
    (SB : bgs.BitGuessingProblem) (D : bgs.ProbBitGuesser)
    [Fintype bgs.D] [Fintype (bgs.O × Bool)]
    (hD : D.isProbDist) (hSB : SB.isProbDist) :
    bgs.performance SB D ≤ 1 := by
  -- The performance is `2 * S - 1` where `S` is the real-valued double
  -- `Finsupp.sum` of `D(d) · SB(ob) · [κ d ob.1 = ob.2]`.  Bounding the
  -- indicator by `1`, the inner sum is `≤ D(d) · ∑ SB = D(d) · 1`, and the
  -- outer sum is `≤ ∑ D = 1`.  So `S ≤ 1` and `2 * S - 1 ≤ 1`.  This mirrors
  -- `GameStructure.winProb_le_one`, lifted to `ℝ` through the `NNReal` casts.
  rw [BitGuessingStructure.performance]
  have hSBsum : (Finsupp.sum SB fun _ ow => (ow : ℝ)) = 1 := by
    have hcoe : (Finsupp.sum SB fun _ ow => (ow : ℝ)) =
        ((SB.weight : NNReal) : ℝ) := by
      rw [Dist.weight_eq_finsupp_sum]
      simp [Finsupp.sum, NNReal.coe_sum]
    rw [hcoe, hSB, NNReal.coe_one]
  have hDsum : (Finsupp.sum D fun _ dw => (dw : ℝ)) = 1 := by
    have hcoe : (Finsupp.sum D fun _ dw => (dw : ℝ)) =
        ((D.weight : NNReal) : ℝ) := by
      rw [Dist.weight_eq_finsupp_sum]
      simp [Finsupp.sum, NNReal.coe_sum]
    rw [hcoe, hD, NNReal.coe_one]
  have hS : (Finsupp.sum D fun d dw => Finsupp.sum SB fun ob ow =>
        (dw : ℝ) * (ow : ℝ) * if bgs.κ d ob.1 = ob.2 then 1 else 0) ≤ 1 := by
    calc (Finsupp.sum D fun d dw => Finsupp.sum SB fun ob ow =>
              (dw : ℝ) * (ow : ℝ) * if bgs.κ d ob.1 = ob.2 then 1 else 0)
        ≤ Finsupp.sum D fun _ dw => (dw : ℝ) := by
          apply Finsupp.sum_le_sum
          intro d _
          calc (Finsupp.sum SB fun ob ow =>
                    (D d : ℝ) * (ow : ℝ) * if bgs.κ d ob.1 = ob.2 then 1 else 0)
              ≤ Finsupp.sum SB fun _ ow => (D d : ℝ) * (ow : ℝ) := by
                apply Finsupp.sum_le_sum
                intro ob _
                have hnn : (0 : ℝ) ≤ (D d : ℝ) * (SB ob : ℝ) :=
                  mul_nonneg (D d).coe_nonneg (SB ob).coe_nonneg
                split
                · simp
                · simpa using hnn
            _ = (D d : ℝ) * Finsupp.sum SB fun _ ow => (ow : ℝ) := by
                rw [Finsupp.mul_sum]
            _ = (D d : ℝ) := by rw [hSBsum, mul_one]
      _ = 1 := hDsum
  linarith

theorem neg_one_le_performance (bgs : BitGuessingStructure)
    (SB : bgs.BitGuessingProblem) (D : bgs.ProbBitGuesser) :
    -1 ≤ bgs.performance SB D := by
  -- The performance is `2 * S - 1` where `S` is the double `Finsupp.sum` of the
  -- nonnegative terms `D(d) · SB(ob) · [κ d ob.1 = ob.2]`.  Each term is a
  -- product of nonnegative reals (NNReal casts) times an indicator in `{0, 1}`,
  -- so `0 ≤ S` by `Finsupp.sum_nonneg`, hence `2 * S - 1 ≥ -1`.  This mirrors
  -- the nonnegativity branch of `performance_le_one`.
  rw [BitGuessingStructure.performance]
  have hS : (0 : ℝ) ≤ Finsupp.sum D fun d dw =>
      Finsupp.sum SB fun ob ow =>
        (dw : ℝ) * (ow : ℝ) * if bgs.κ d ob.1 = ob.2 then 1 else 0 := by
    apply Finsupp.sum_nonneg
    intro d _
    apply Finsupp.sum_nonneg
    intro ob _
    have hnn : (0 : ℝ) ≤ (D d : ℝ) * (SB ob : ℝ) :=
      mul_nonneg (D d).coe_nonneg (SB ob).coe_nonneg
    split
    · simpa using hnn
    · simp
  linarith

/-- The performance of a *trivial* guesser — one that always outputs the same
value regardless of the object — takes a value that depends only on the
marginal distribution of `B`.

If `κ d o = false` for all `d, o` (the guesser always outputs 0), the
advantage is `2 · Pr[B = false] − 1`, i.e., negative when `B = true` is more
likely. -/
theorem performance_constant_zero_guesser (bgs : BitGuessingStructure)
    (SB : bgs.BitGuessingProblem) (D : bgs.ProbBitGuesser)
    (hκ : ∀ d : bgs.D, ∀ o : bgs.O, bgs.κ d o = false) :
    bgs.performance SB D =
      2 * (D.sum fun _ dw => SB.sum fun ob ow =>
            (dw : Real) * (ow : Real) * if ob.2 = false then 1 else 0) - 1 := by
  -- The hypothesis `hκ` rewrites every guess `κ d ob.1` to `false`, so the
  -- indicator `[κ d ob.1 = ob.2]` becomes `[false = ob.2]`; `eq_comm` flips it
  -- to `[ob.2 = false]` to match the statement's RHS.
  simp only [performance, hκ]
  simp only [eq_comm]

end BitGuessingStructure

end Def48

end RandomSystems.CR18

/-!
## CR18 Definition 4.9 — Independent Copies X^q

CR18 §4.7.1 (Maurer's lecture notes, "Cryptography: Random Systems"):

> **Definition 4.9.** For an X-random variable X, we denote by **X^q** the
> X^q-random variable consisting of q **independent copies** of X. More
> precisely, **X^q** = (X₁, …, Xq) where X₁, …, Xq are independent and each
> Xᵢ has the same (marginal) probability distribution as X. Moreover, we
> denote by ⟨X⟩ the X^∞-random variable consisting of a countable number of
> independent copies of X.

### Lean representation

* An `X`-random variable is a `Dist α` (a finite-support sub-distribution over
  some type `α`).
* `X^q` is modelled as `Dist (Fin q → α)`: a distribution over q-tuples whose
  components are independently sampled from `X`.
* The `q`-fold independent-product measure is constructed by recursion on `q`
  using the `Dist` bind (a nested `Finsupp.sum`): draw each component
  independently from `X`.
* The infinite countable case `⟨X⟩` is left as a propositional characterisation
  (`IsIndependentCopiesFamily`) rather than a concrete `Dist`, since `α^∞`
  is uncountable for non-singleton `α` and lies outside discrete distribution
  theory (Maurer notes this in footnote 24).
-/

namespace RandomSystems.CR18

namespace Def49

/-! ### q-fold independent product of a `Dist` -/

/-- CR18 Definition 4.9: **q independent copies** of an `α`-valued random
variable `X : Dist α`.

We construct the product measure on `Fin q → α` by recursion on `q`, sampling
each component independently from `X` via the `Dist` bind (a nested
`Finsupp.sum`):

* `q = 0`: the unique empty tuple, as a point mass `Finsupp.single Fin.elim0 1`.
* `q = n + 1`: draw `x₀ ← X` (mass `wx`), draw `rest ← independentCopies n X`
  (mass `wr`), and place mass `wx * wr` on the tuple that maps `0 ↦ x₀` and each
  successor `i.succ ↦ rest i`.

This matches CR18: each `Xᵢ` is an independent draw with the same marginal
distribution as `X`. `DecidableEq` instances are needed to form the point
masses (`Finsupp.single`) in the bind. -/
noncomputable def independentCopies {α : Type*} [DecidableEq α] :
    (q : ℕ) → Dist α → Dist (Fin q → α)
  | 0,     _ => Finsupp.single Fin.elim0 1
  | q + 1, X =>
      X.sum fun x₀ wx =>
        (independentCopies q X).sum fun rest wr =>
          Finsupp.single (Fin.cons x₀ rest) (wx * wr)

/-- The zero-fold independent product is the point mass on the empty tuple. -/
@[simp]
theorem independentCopies_zero {α : Type*} [DecidableEq α] (X : Dist α) :
    independentCopies 0 X = Finsupp.single Fin.elim0 1 :=
  rfl

/-- The product formula for `independentCopies`: the mass of tuple `a`
factors as the product of the individual marginal masses.

Maurer: "X₁, …, Xq are independent and each Xᵢ has the same marginal
distribution as X." -/
theorem independentCopies_apply {α : Type*} (q : ℕ) (X : Dist α)
    [DecidableEq α] (a : Fin q → α) :
    independentCopies q X a = ∏ i : Fin q, X (a i) := by
  induction q with
  | zero =>
      simp only [independentCopies, Finset.univ_eq_empty, Finset.prod_empty]
      rw [Finsupp.single_apply]
      exact if_pos (Subsingleton.elim _ _)
  | succ n ih =>
      classical
      -- Mirror of `RandomSystems.Dist.prod_apply`: expand the nested
      -- `Finsupp.sum` of point masses, then collapse each layer with
      -- `Finsupp.sum_eq_single`, and fold back via `Fin.prod_univ_succ`.
      have hcons : ∀ (x₀ : α) (rest : Fin n → α),
          Fin.cons x₀ rest = a ↔ x₀ = a 0 ∧ rest = Fin.tail a := by
        intro x₀ rest
        constructor
        · rintro rfl
          simp [Fin.tail_cons]
        · rintro ⟨rfl, rfl⟩
          exact Fin.cons_self_tail a
      have expand : independentCopies (n + 1) X a =
          X.sum fun x₀ wx =>
            (independentCopies n X).sum fun rest wr =>
              if x₀ = a 0 ∧ rest = Fin.tail a then wx * wr else 0 := by
        simp only [independentCopies, Finsupp.sum_apply, Finsupp.single_apply]
        refine Finsupp.sum_congr fun x₀ _ => Finsupp.sum_congr fun rest _ => ?_
        simp only [hcons]
      have houter :
          (X.sum fun x₀ wx =>
            (independentCopies n X).sum fun rest wr =>
              if x₀ = a 0 ∧ rest = Fin.tail a then wx * wr else 0) =
          (independentCopies n X).sum fun rest wr =>
            if rest = Fin.tail a then X (a 0) * wr else 0 := by
        rw [Finsupp.sum_eq_single (a 0)
          (fun x₀ _ hne => Finset.sum_eq_zero fun rest _ => by simp [hne])
          (fun _ => Finset.sum_eq_zero fun rest _ => by simp)]
        refine Finsupp.sum_congr fun rest _ => ?_
        simp
      have hinner :
          ((independentCopies n X).sum fun rest wr =>
            if rest = Fin.tail a then X (a 0) * wr else 0) =
          X (a 0) * independentCopies n X (Fin.tail a) := by
        rw [Finsupp.sum_eq_single (Fin.tail a)
          (fun rest _ hne => by simp [hne])
          (fun _ => by simp)]
        simp
      rw [expand, houter, hinner, ih (Fin.tail a), Fin.prod_univ_succ]
      rfl

/-- The marginal of `independentCopies q X` at any fixed coordinate `i` is `X`.

Maurer: "each Xᵢ has the same (marginal) probability distribution as X."

⚠ The marginal equals `X` **only when `X` is a genuine probability distribution**
(`X.isProbDist`, i.e. `weight X = 1`).  The framework's `Dist` (LM20 Def 1)
admits *sub-distributions* of arbitrary weight, and for those the coordinate-`i`
marginal of the independent product is `weight(X)^(q-1) • X`, NOT `X`.  Maurer's
Definition 4.9 speaks of "X-random variables", i.e. probability distributions, so
this is exactly his hypothesis — but it must be made explicit here, otherwise the
claim is false (see the sub-distribution counterexample in the contrarian-review
note: for `X = single true (1/2)`, `q = 2`, `i = 0`, the marginal at `true` is
`1/4 ≠ 1/2 = X true`). -/
theorem independentCopies_marginal {α : Type*} (q : ℕ) (X : Dist α)
    [Fintype α] [DecidableEq α] (hX : X.isProbDist) (i : Fin q) (a : α) :
    (independentCopies q X).sum (fun f w => Finsupp.single (f i) w) a = X a := by
  classical
  -- Marginalisation is the pushforward (`Dist.fTransform`) along the i-th
  -- projection; rewrite it as a fiber sum (`fTransform_apply_eq_sum`).
  have hpush :
      (Dist.fTransform (fun f : Fin q → α => f i) (independentCopies q X)) a =
        ∑ f ∈ (Finset.univ : Finset (Fin q → α)).filter (fun f => f i = a),
          independentCopies q X f := by
    convert Dist.fTransform_apply_eq_sum (fun f : Fin q → α => f i) (independentCopies q X) a using 2
    ext g; simp [Finset.mem_filter]
  -- Per-coordinate factor pattern: coordinate `i` is pinned to `a`, the others free.
  set F : Fin q → α → NNReal :=
    fun j x => if j = i then (if x = a then X x else 0) else X x with hF
  have hterm : ∀ f : Fin q → α,
      (if f i = a then independentCopies q X f else 0) = ∏ j : Fin q, F j (f j) := by
    intro f
    by_cases hfa : f i = a
    · rw [if_pos hfa, independentCopies_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp [hF, hfa]
      · simp [hF, hj]
    · rw [if_neg hfa]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hF, hfa])
  have hfactor : ∀ j : Fin q, (∑ x : α, F j x) = if j = i then X a else 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hF]
    · simp only [hF, if_neg hj]
      rw [← Dist.weight_eq_sum]; exact hX
  calc
    (independentCopies q X).sum (fun f w => Finsupp.single (f i) w) a
        = ∑ f ∈ (Finset.univ : Finset (Fin q → α)).filter (fun f => f i = a),
            independentCopies q X f := hpush
    _ = ∑ f : Fin q → α, (if f i = a then independentCopies q X f else 0) :=
          Finset.sum_filter _ _
    _ = ∑ f ∈ Fintype.piFinset (fun _ : Fin q => (Finset.univ : Finset α)),
            ∏ j : Fin q, F j (f j) := by
          rw [Fintype.piFinset_univ]
          exact Finset.sum_congr rfl fun f _ => hterm f
    _ = ∏ j : Fin q, ∑ x : α, F j x := Finset.sum_prod_piFinset _ _
    _ = ∏ j : Fin q, (if j = i then X a else 1) :=
          Finset.prod_congr rfl fun j _ => hfactor j
    _ = X a := by simp

/-! ### Independent copies for probabilistic discrete systems -/

/-- CR18 §4.7.1 (prose after Def 4.9): when `S` is a probabilistic system
(`PDS X Y`, i.e., a `Dist (DDS X Y)`), the `q` independent copies form
**S^q**, the parallel composition of `q` independent copies of `S`.

`S^q` is modelled as `Dist (Fin q → DDS X Y)`: a distribution over `q`-tuples
of independent deterministic systems, each drawn from `S`. This is exactly
`independentCopies q S` instantiated at `DDS X Y`. -/
noncomputable abbrev PDS.independentCopies {X Y : Type*} [DecidableEq (DDS X Y)]
    (q : ℕ) (S : PDS X Y) : Dist (Fin q → DDS X Y) :=
  Def49.independentCopies q S

/-- CR18 §4.7.1: S^q is the same as `independentCopies q S` (definitional). -/
@[simp]
theorem PDS.independentCopies_def {X Y : Type*} [DecidableEq (DDS X Y)]
    (q : ℕ) (S : PDS X Y) :
    PDS.independentCopies q S = Def49.independentCopies q S :=
  rfl

/-! ### Infinite countable independent copies ⟨X⟩ (propositional only)

Maurer notes in footnote 24 that the infinite case "leaves the realm of
discrete probability theory since X^∞ is not countable."  We therefore
do NOT define ⟨X⟩ as a concrete `Dist`.  Instead, we record the characteristic
property as a Prop-valued predicate on sequences of `Dist`s. -/

/-- CR18 Definition 4.9 (infinite case, propositional):
a sequence of `α`-valued random variables `(Xᵢ)_{i : ℕ}` for the infinite
collection `⟨X⟩` of copies of `X : Dist α`.

This predicate records ONLY the **identical-marginal** requirement: every `Xᵢ`
has the same (marginal) distribution as `X` (`family i = X`).  It does NOT (and
cannot, at this type) encode the *independence* of the copies: `family : ℕ → Dist α`
is a sequence of separate marginals with no joint object `Dist (ℕ → α)` over
which independence could be stated.  Maurer footnote 24 notes the infinite case
"leaves the realm of discrete probability theory since `α^∞` is not countable",
so no concrete joint `Dist` is available — only the marginal characterisation is
formalised here.  (The finite `q`-fold *independent* product is `independentCopies`,
where independence IS encoded via the product construction.) -/
def IsIndependentCopiesFamily {α : Type*} (X : Dist α)
    (family : ℕ → Dist α) : Prop :=
  (∀ i : ℕ, family i = X)

end Def49

end RandomSystems.CR18

/-!
## CR18 Definition 4.15 — Pre-Winning Behavior of a Game

CR18 §4.10.1 (source ~line 5326):

> **Definition 4.15.** The **pre-winning behavior** of a game G is the sequence
> `p^G_{Y_i, A_i=0 | X^i, Y^{i-1}, A^{i-1}=0}` for i ≥ 1
> of conditional probability distributions.

That is, the pre-winning behavior records, at each round i, the conditional
probability of *both* producing output `y` at round i *and* the game not being
won at that round (`A_i = false`), conditioned on:
* the full input history `X^i = x^i`,
* the previous output history `Y^{i-1} = y^{i-1}`, and
* the event that the game was not won at any earlier round (`A^{i-1} = 0`).

### Lean strategy

A `PDG X Y = Dist (DDG X Y)` (see earlier in this file) is a random variable
over deterministic games.

We formalize the pre-winning behavior in two steps:

1. **Pre-winning projection** (`PDG.preWinningPDS`): map a `PDG X Y` to a
   `PDS X Y` that encodes only the "not-yet-won" trajectories.  Concretely,
   given a DDG `g`, the *pre-winning DDS* at `g` is the `DDS X Y` whose output
   at each in-domain prefix `l` is `g.regularOutput l hl` *when the game has
   not been won yet*, and undefined (i.e. not in the domain) once the game is
   won.  Pushing forward the `PDG` distribution along this DDG → DDS map gives
   a `PDS X Y` that concentrates only on not-won trajectories.

2. **Pre-winning behavior** (`preWinningBehavior`): the `Behavior X Y` of the
   projected PDS (Definition 3.18 / `behavior` from `Behavior.lean`).

   `preWinningBehavior G = behavior (G.preWinningPDS)`

   At each step i, `(preWinningBehavior G).step i xs ys y` gives the conditional
   probability of outputting `y` at round i+1 and the game not being won,
   given inputs `xs` (length i+1) and previous outputs `ys` (length i), with
   the implicit conditioning that the game was not won previously (encoded by
   restricting to not-won trajectories in the projected PDS).

### Relationship to `Behavior X Y`

The pre-winning behavior is literally a `Behavior X Y`, using the exact same
`condSlice`-based definition as the ordinary system behavior (Definition 3.18).
The "pre-winning" aspect is captured by the projection: the `PDS X Y` assigned
to game `G` carries zero probability mass on trajectories where the game has
already been won.
-/

namespace RandomSystems.CR18

namespace Def415

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Step 1: The pre-winning DDS of a DDG -/

/-- CR18 Definition 4.15 (auxiliary): the **pre-winning DDS** of a DDG `g`.

This is the `DDS X Y` whose domain restricts to input histories at which the
game has **not** been won.  Specifically:

* The domain of `preWinningDDS g` consists of those input prefixes `l ∈ g.toSystem.dom`
  at which every intermediate output bit is `false` (the game has not been won
  in any of the rounds covered by `l`).
* The response function is the regular Y-component of `g.toSystem.respond`,
  i.e. `(g.toSystem.respond l hl).1`.

This encodes the "conditioning on `A^{i-1} = 0`" part of Definition 4.15:
trajectories that enter the "game won" state are excluded from the domain. -/
-- Helper: the pre-winning domain predicate for a DDG.
-- A list `l` is in the pre-winning domain of `g` if:
-- (1) `l ∈ g.toSystem.dom`, and
-- (2) for every prefix `l.take (k+1)` (k < l.length), the game is not won there.
private def preWinningDom {X Y : Type*} (g : DDG X Y) : Set (List X) :=
  { l | l ∈ g.toSystem.dom ∧
    ∀ (k : ℕ) (_hk : k < l.length),
      ∃ (hpfx : l.take (k + 1) ∈ g.toSystem.dom),
        (g.toSystem.respond (l.take (k + 1)) hpfx).2 = false }

-- Helper: membership in preWinningDom implies membership in g.toSystem.dom.
private theorem preWinningDom_dom {X Y : Type*} (g : DDG X Y) (l : List X)
    (hl : l ∈ preWinningDom g) : l ∈ g.toSystem.dom :=
  hl.1

def preWinningDDS (g : DDG X Y) : DDS X Y where
  dom := preWinningDom g
  nonempty_input := by
    -- [] ∉ preWinningDom g because [] ∉ g.toSystem.dom
    intro hmem
    simp only [preWinningDom, Set.mem_setOf_eq] at hmem
    exact g.toSystem.nonempty_input hmem.1
  prefix_closed := by
    intro l₁ l₂ hprefix hne hmem
    simp only [preWinningDom, Set.mem_setOf_eq] at hmem ⊢
    obtain ⟨hmd, hmall⟩ := hmem
    refine ⟨g.toSystem.prefix_closed hprefix hne hmd, ?_⟩
    intro k hk
    -- k < l₁.length ≤ l₂.length since l₁ <+: l₂
    have hlm : l₁.length ≤ l₂.length := List.IsPrefix.length_le hprefix
    have hkm : k < l₂.length := lt_of_lt_of_le hk hlm
    -- l₁.take (k+1) = l₂.take (k+1) since l₁ <+: l₂ and k+1 ≤ l₁.length
    have htake : l₁.take (k + 1) = l₂.take (k + 1) := by
      obtain ⟨t, rfl⟩ := hprefix
      rw [List.take_append_of_le_length (by omega)]
    obtain ⟨hpfx_m, hbit⟩ := hmall k hkm
    -- hpfx_m : l₂.take (k+1) ∈ dom,  htake : l₁.take = l₂.take.
    -- Rewrite the goal along `htake` so it is stated over `l₂.take (k+1)`,
    -- then the `l₂` witness `⟨hpfx_m, hbit⟩` closes it directly.
    rw [htake]
    exact ⟨hpfx_m, hbit⟩
  respond := fun l hl => by
    simp only [preWinningDom, Set.mem_setOf_eq] at hl
    exact (g.toSystem.respond l hl.1).1

/-! #### Public characterisation of the pre-winning DDS (domain and response)

`preWinningDom` is `private`; the following `rfl`-lemmas expose the domain
membership condition and the response value so that other files (notably the
Lemma 4.16 assembly in `Indist.lean`) can reason about `preWinningDDS`
without unfolding private names. -/

/-- Membership in the pre-winning domain: `l ∈ (preWinningDDS g).dom` iff `l`
is in `g`'s domain and the MBO bit is `false` at every nonempty prefix of `l`
(the game has not been won in any round covered by `l`). -/
theorem mem_preWinningDDS_dom_iff (g : DDG X Y) (l : List X) :
    l ∈ (preWinningDDS g).dom ↔
      l ∈ g.toSystem.dom ∧
        ∀ (k : ℕ), k < l.length →
          ∃ (hpfx : l.take (k + 1) ∈ g.toSystem.dom),
            (g.toSystem.respond (l.take (k + 1)) hpfx).2 = false :=
  Iff.rfl

/-- The pre-winning domain is contained in the original game's domain. -/
theorem preWinningDDS_dom_subset (g : DDG X Y) :
    (preWinningDDS g).dom ⊆ g.toSystem.dom := fun l hl =>
  ((mem_preWinningDDS_dom_iff g l).mp hl).1

/-- The response of the pre-winning DDS is the `Y`-component of the game's
response (at the same history; the membership proof transports by proof
irrelevance). -/
theorem preWinningDDS_respond (g : DDG X Y) (l : List X)
    (hl : l ∈ (preWinningDDS g).dom) :
    (preWinningDDS g).respond l hl =
      (g.toSystem.respond l (preWinningDDS_dom_subset g hl)).1 :=
  rfl

/-- If a history is in the pre-winning domain, the current MBO bit is `false`.

This is the terminal-prefix instance of the all-prefix condition in
Definition 4.15.  It is the deterministic algebraic fact behind the
`Aᵢ = 0` side of the cumulative pre-winning transcript formulas. -/
theorem preWinningDDS_bit_false (g : DDG X Y) (l : List X)
    (hl : l ∈ (preWinningDDS g).dom) :
    (g.toSystem.respond l (preWinningDDS_dom_subset g hl)).2 = false := by
  have hmem := (mem_preWinningDDS_dom_iff g l).mp hl
  cases l with
  | nil => exact False.elim (g.toSystem.nonempty_input hmem.1)
  | cons x xs =>
      let l := x :: xs
      let k := l.length - 1
      have hk : k < l.length := by
        dsimp [k, l]
        omega
      obtain ⟨hpfx, hbit⟩ := hmem.2 k hk
      have hklen : k + 1 = l.length := by
        dsimp [k, l]
      have htake : (x :: xs).take (k + 1) = x :: xs := by
        calc
          (x :: xs).take (k + 1) = (x :: xs).take l.length := by rw [hklen]
          _ = x :: xs := by simp [l]
      have hresp := g.toSystem.respond_congr htake hpfx (preWinningDDS_dom_subset g hl)
      exact congrArg Prod.snd hresp ▸ hbit

/-- Under a fixed proof that `l` is in the game's query domain, membership in
the pre-winning domain is equivalent to the current MBO bit being `false`.

The reverse direction is Maurer's monotonicity argument: if any earlier prefix
had bit `true`, the MBO property would force the terminal bit at `l` to be
`true`, contradicting the current `false` bit. -/
theorem mem_preWinningDDS_dom_iff_current_bit_false (g : DDG X Y) (l : List X)
    (hl : l ∈ g.toSystem.dom) :
    l ∈ (preWinningDDS g).dom ↔ (g.toSystem.respond l hl).2 = false := by
  constructor
  · intro hpw
    exact preWinningDDS_bit_false g l hpw
  · intro hcur
    rw [mem_preWinningDDS_dom_iff]
    refine ⟨hl, ?_⟩
    intro k hk
    have hpfx : l.take (k + 1) ∈ g.toSystem.dom := by
      refine g.toSystem.prefix_closed (List.take_prefix _ _) ?_ hl
      exact List.ne_nil_of_length_pos (by simp [hk])
    refine ⟨hpfx, ?_⟩
    by_contra hnot
    have hpfx_true : (g.toSystem.respond (l.take (k + 1)) hpfx).2 = true := by
      cases h : (g.toSystem.respond (l.take (k + 1)) hpfx).2 <;> simp [h] at hnot ⊢
    let j := l.length - 1
    have hj : j < l.length := by
      dsimp [j]
      have hln : l.length ≠ 0 := by
        intro h0
        have : l = [] := List.eq_nil_iff_length_eq_zero.mpr h0
        exact g.toSystem.nonempty_input (this ▸ hl)
      omega
    have hkj : k ≤ j := by
      dsimp [j]
      omega
    obtain ⟨hjdom, hjbit⟩ := g.mbo l hl k j hkj hj ⟨hpfx, hpfx_true⟩
    have hjlen : j + 1 = l.length := by
      dsimp [j]
      omega
    have htake : l.take (j + 1) = l := by
      rw [hjlen, List.take_length]
    have hresp := g.toSystem.respond_congr htake hjdom hl
    have hcurTrue : (g.toSystem.respond l hl).2 = true := by
      simpa [hresp] using hjbit
    rw [hcur] at hcurTrue
    simp at hcurTrue

/-! ### Step 2: The pre-winning PDS of a PDG -/

/-- CR18 Definition 4.15 (auxiliary): the **pre-winning PDS** of a PDG `G`.

`preWinningPDS G` is the `PDS X Y` obtained by pushing forward the distribution
`G : Dist (DDG X Y)` along the map `DDG.preWinningDDS : DDG X Y → DDS X Y`.

This PDS encodes all the probabilistic weight of `G` concentrated on the
not-won DDS trajectories.  Its behavior (Definition 3.18) is the pre-winning
behavior (Definition 4.15). -/
noncomputable def preWinningPDS (G : PDG X Y) : PDS X Y :=
  Dist.fTransform preWinningDDS G

/-! ### Step 3: The pre-winning behavior -/

/-- CR18 Definition 4.15: the **pre-winning behavior** of a probabilistic
game `G`.

The pre-winning behavior is the sequence
  `p^G_{Y_i, A_i=0 | X^i, Y^{i-1}, A^{i-1}=0}` for i ≥ 1
of conditional probability distributions (Definition 4.15, source line 5326).

In Lean, this is the `Behavior X Y` of the pre-winning PDS of `G`
(Definition 3.18 applied to `preWinningPDS G`).

At each round i, `(preWinningBehavior G).step i xs ys y` gives:
  `Pr[ G outputs y at round i+1  AND  game not won at round i+1
       | inputs = xs,  prev outputs = ys,  game not won at rounds 1..i ]`

computed via the `condSlice` formula from Definition 3.18. -/
noncomputable def preWinningBehavior
    [DecidableEq (List (Option Y))]
    (G : PDG X Y) : Behavior X Y :=
  behavior (preWinningPDS G)

/-! ### Basic properties -/

/-- CR18 Definition 4.15 (unfolding): the pre-winning behavior is computed via
`condSlice` of the pre-winning PDS.

This is the definitional unfolding lemma. -/
@[simp]
theorem preWinningBehavior_step
    [DecidableEq (List (Option Y))]
    (G : PDG X Y) (i : ℕ) (xs : List X) (ys : List Y) (y : Y) :
    (preWinningBehavior G).step i xs ys y =
      condSlice (preWinningPDS G) xs ys y := rfl

/-- CR18 Definition 4.15: two PDGs that are equal have the same pre-winning
behavior. -/
theorem preWinningBehavior_congr
    [DecidableEq (List (Option Y))]
    {G H : PDG X Y} (h : G = H) :
    preWinningBehavior G = preWinningBehavior H := by
  subst h; rfl

/-- CR18 Definition 4.15 (degenerate case): the pre-winning behavior of a
deterministic game `g` (as a point-mass PDG) equals the behavior of the
pre-winning DDS of `g` treated as a PDS.

For a degenerate PDG concentrated at a single DDG `g`, the pre-winning PDS
is the point-mass PDS concentrated at `preWinningDDS g`. -/
theorem preWinningPDS_pure
    (g : DDG X Y) :
    preWinningPDS (PDG.pure g) = PDS.pure (preWinningDDS g) := by
  classical
  simp only [preWinningPDS, PDG.pure, PDS.pure, Dist.fTransform]
  rw [Finsupp.sum_single_index (by simp)]

end Def415

end RandomSystems.CR18

/-!
## CR18 Definition 4.16 — Game Equivalence G ≡ H

CR18 §4.10.1 (source ~line 5343):

> **Definition 4.16.** Two (probabilistic) games G and H are **equivalent as
> games**, denoted `G ≡ H`, if their **pre-winning behavior** is identical.

From the surrounding prose (§4.10.1, line 5337–5389):

* The pre-winning behavior of G is the sequence
  `p^G_{Y_i, A_i=0 | X^i, Y^{i-1}, A^{i-1}=0}` for i ≥ 1 (Definition 4.15).
* Two games are equivalent iff this sequence agrees for every round i, every
  input history x^i, every output history y^{i-1}, and every output value y.
* An equivalent condition (noted in the source text, equation (4.36) onwards) is:
  `p^G_{Y^q, A^q=0 | X^q}(y^q, x^q) = p^H_{Y^q, A^q=0 | X^q}(y^q, x^q)`
  for all q ≥ 1, x^q, y^q.
* Lemma 4.15 in CR18 (the lemma just before Definition 4.16) states: if G ≡ H
  then G(W) = H(W) for any winner W (i.e. winning probability is the same).
  This is Lemma 4.15 in the source (not to be confused with Definition 4.15).

### Lean strategy

We use `Def415.preWinningBehavior` (from the `Def415` namespace above) directly:
`G ≡ H` is the Prop that `preWinningBehavior G = preWinningBehavior H`.

This is a faithful, definitionally-minimal formalization: the equivalence is
exactly equality of the `Behavior X Y` objects produced by the two games.
-/

namespace RandomSystems.CR18

namespace Def416

universe u v

variable {X : Type u} {Y : Type v}
  [DecidableEq (DDS X Y)] [DecidableEq (List (Option Y))]

/-! ### Game equivalence relation -/

/-- CR18 Definition 4.16: **game equivalence** `G ≡_g H`.

Two probabilistic `(X, Y)`-games `G` and `H` are **equivalent as games**,
written `G.GameEquiv H`, if and only if their **pre-winning behaviors** are
identical (Definition 4.15):

  `G ≡_g H  :↔  preWinningBehavior G = preWinningBehavior H`

Maurer (source line 5343–5346):
  "Two (probabilistic) games G and H are equivalent as games, denoted G ≡ H,
   if their pre-winning behavior is identical."

An equivalent characterisation (from equation (4.35)–(4.36) in §4.10.1) is that
  `p^G_{Y_i, A_i=0 | X^i, Y^{i-1}, A^{i-1}=0}(y, x^i, y^{i-1})`
equals the corresponding probability for H, for all i ≥ 1 and all x^i, y^{i-1}, y.
This is exactly the componentwise version of equality of `Behavior X Y`:
  `∀ i xs ys y, (preWinningBehavior G).step i xs ys y = (preWinningBehavior H).step i xs ys y`.
Both forms are equivalent; we use the `=`-form as the definition and provide
the componentwise characterisation as `gameEquiv_iff_stepwise`. -/
def GameEquiv (G H : PDG X Y) : Prop :=
  Def415.preWinningBehavior G = Def415.preWinningBehavior H

/-- Notation for game equivalence: `G ≡_g H`. -/
scoped notation:50 G " ≡_g " H => GameEquiv G H

/-! ### Equivalence relation properties -/

/-- Game equivalence is reflexive: every game is equivalent to itself. -/
@[refl]
theorem GameEquiv.refl (G : PDG X Y) : G ≡_g G :=
  rfl

/-- Game equivalence is symmetric. -/
theorem gameEquiv_symm {G H : PDG X Y} (h : G ≡_g H) : H ≡_g G :=
  Eq.symm h

/-- Game equivalence is transitive. -/
theorem gameEquiv_trans {G H K : PDG X Y} (h₁ : G ≡_g H) (h₂ : H ≡_g K) :
    G ≡_g K :=
  Eq.trans h₁ h₂

/-- Game equivalence is an equivalence relation on `PDG X Y`. -/
theorem gameEquiv_equivalence :
    Equivalence (fun G H : PDG X Y => G ≡_g H) where
  refl  := GameEquiv.refl
  symm  := fun {_ _} h => gameEquiv_symm h
  trans := fun {_ _ _} h₁ h₂ => gameEquiv_trans h₁ h₂

/-! ### Componentwise characterisation -/

/-- CR18 §4.10.1, equation (4.35)–(4.36): game equivalence is equivalent to
agreeing stepwise at every round and every input/output history.

  `G ≡_g H  ↔
    ∀ i xs ys y, (preWinningBehavior G).step i xs ys y =
                 (preWinningBehavior H).step i xs ys y`

This is the pointwise unfolding of the `Behavior X Y` equality; it is
"one can show that an equivalent condition for G ≡ H is" from CR18 line 5377. -/
theorem gameEquiv_iff_stepwise {G H : PDG X Y} :
    (G ≡_g H) ↔
    ∀ (i : ℕ) (xs : List X) (ys : List Y) (y : Y),
      (Def415.preWinningBehavior G).step i xs ys y =
      (Def415.preWinningBehavior H).step i xs ys y := by
  simp only [GameEquiv]
  constructor
  · intro h i xs ys y; rw [h]
  · intro h
    -- `Behavior` is a single-field structure, so equality reduces to equality of
    -- the `step` functions; build it by `funext` and fold via structure
    -- injectivity (the same pattern as `behaviorEq_iff_behaviorEquiv`).
    have hstep :
        (Def415.preWinningBehavior G).step = (Def415.preWinningBehavior H).step :=
      funext fun i => funext fun xs => funext fun ys => funext fun y => h i xs ys y
    exact Behavior.mk.injEq _ _ ▸ hstep

/-- Equality of all cumulative pre-winning transcript masses implies game
equivalence.

This is the cumulative-transcript form stated after CR18 Definition 4.16:
instead of proving equality of every conditional kernel directly, it suffices
to prove the joint identities
`p^G_{Y^i,A_i=0|X^i} = p^H_{Y^i,A_i=0|X^i}` for every visible transcript. -/
theorem gameEquiv_of_jointProb_preWinningPDS_eq {G H : PDG X Y}
    (h : ∀ xs ys,
      jointProb (Def415.preWinningPDS G) xs ys =
        jointProb (Def415.preWinningPDS H) xs ys) :
    GameEquiv G H :=
  behaviorEq_of_jointProb_eq h

/-! ### Consequence: equal winning probability (CR18 Lemma 4.15 in prose)

The source says immediately before Definition 4.16 (line 5337):
  "If G and H are equivalent as games, then the process of winning either of
   them is identical up to the point where it is won. Therefore we have: [Lemma 4.15]
   If G ≡ H then, for any winner W for (X, Y)-games, we have G(W) = H(W)."

We state this consequence here in abstract terms using `Def45.GameStructure.winProb`.
The proof is closed once the winning functional is explicitly required to factor
through pre-winning behavior; proving that factoring property for a concrete
winner is the substantive CR18 content. -/

/-- CR18 Lemma 4.15 (prose): if `G ≡_g H`, then for any winning-probability
functional that factors through the pre-winning behavior — i.e. there is
`f : Behavior X Y → NNReal` with `winFun = f ∘ preWinningBehavior`, which is
exactly the content of CR18 eqs 4.35–4.37 — game equivalence forces equal
winning probability `winFun G = winFun H`.

This is the genuine consequence (NOT a tautology over an arbitrary `winFun`):
the hypothesis `hWin` is the substantive CR18 obligation, and the proof USES the
factoring witness, so the statement fails for a functional that does not factor
through pre-winning behavior.  The fully-fledged version lives in the `Lem415`
namespace (`gameEquiv_winFun_eq`, `gameEquiv_winProb_eq_concrete`). -/
theorem gameEquiv_winProb_eq {G H : PDG X Y}
    {winFun : PDG X Y → NNReal}
    (hWin : ∃ f : Behavior X Y → NNReal,
      ∀ K : PDG X Y, winFun K = f (Def415.preWinningBehavior K))
    (heq : G ≡_g H) :
    winFun G = winFun H := by
  obtain ⟨f, hf⟩ := hWin
  rw [hf G, hf H, GameEquiv] at *
  exact congrArg f heq

end Def416

end RandomSystems.CR18

/-!
## CR18 Lemma 4.15 — Game-Equivalence implies Equal Winner Behavior

CR18 §4.10.1 (source ~line 5365):

> **Lemma 4.15.** If `G ≡ H` then, for any winner W for `(X, Y)`-games, we have
> `G(W) = H(W)`.

**Proof sketch (CR18, line 5370–5378):**
According to equation (4.37), the winning probability `G(W)` is computed as
`1 − Σ_{x^q, y^q} P^{WG}_{X^q, Y^q, A^q=0}(x^q, y^q)`.
Each summand, by equation (4.35), is identical for G and H since the probability
of any event defined on the transcript `(X^q, Y^q)` for which `A^q = 0` is the
same for G and H (this follows from equation (4.36), which is exactly the
game-equivalence condition G ≡ H).
In particular, `Pr^{WG}[A^q = 0] = Pr^{WH}[A^q = 0]` and thus
`Pr^{WG}[A^q = 1] = Pr^{WH}[A^q = 1]`, i.e., `G(W) = H(W)`.

### Lean strategy

We formalize Lemma 4.15 in two forms:

1. **Abstract form** (`gameEquiv_winProb_eq_abstract`): given any map
   `φ : PDG X Y → gs.ProbGame` that is compatible with game equivalence
   (i.e. `G ≡_g H → φ G = φ H`), game equivalence implies equal winning
   probability.  This is the direct abstract rendering of the CR18 proof and
   follows immediately from `φ G = φ H` → `winProb W (φ G) = winProb W (φ H)`.

2. **Concrete form** (`gameEquiv_winProb_eq`): instantiated to the natural
   game structure on `DDG X Y` where `gs.Game = DDG X Y`, `gs.Winner = Winner X Y`,
   and the winning predicate is the literal DDG-winning predicate.  The concrete
   φ sends a PDG to itself as a `Dist (DDG X Y)`.  Under this instantiation,
   `gs.winProb W G` is exactly Maurer's `G(W)` from Definition 4.5.

The concrete form below is proved under an explicit factoring hypothesis
`hWin`.  A caller that wants the literal CR18 `G(W)` instance must still supply
the Eq. 4.35--4.37 bridge showing that its concrete winning probability depends
only on `preWinningBehavior`.
-/

namespace RandomSystems.CR18

namespace Lem415

universe u v

variable {X : Type u} {Y : Type v}
  [DecidableEq (DDS X Y)] [DecidableEq (List (Option Y))]

open Def415 Def416 Def45

/-! ### The factoring bridge (substance of CR18 Lemma 4.15)

The whole content of Lemma 4.15 is that the winning probability `G(W)` is a
function of the *pre-winning behavior* of `G` alone (CR18 eqs 4.35–4.37): two
games with the same pre-winning behavior are won with the same probability by
every winner.  We make this bridge an explicit, named predicate so that
Lemma 4.15 is NOT stated as a tautology over an arbitrary unconstrained map.

A winning-probability functional `winFun : PDG X Y → NNReal` (think: `G ↦ G(W)`
for a fixed winner `W`) **factors through the pre-winning behavior** when its
value is determined by `preWinningBehavior` — i.e. there is `f : Behavior X Y →
NNReal` with `winFun = f ∘ preWinningBehavior`. -/
def FactorsThroughPreWinning (winFun : PDG X Y → NNReal) : Prop :=
  ∃ f : Behavior X Y → NNReal, ∀ G : PDG X Y, winFun G = f (preWinningBehavior G)

/-- **Factoring-bridge interface (CR18 eqs 4.35–4.37, the substance of
Lemma 4.15):**
for the concrete Definition-4.5 winning probability against any winner `W`, the
functional `G ↦ winProb W (φ G)` factors through the pre-winning behavior,
PROVIDED `φ` is the natural embedding of a `PDG X Y` into `gs.ProbGame` for a
game structure whose winning predicate only inspects the not-yet-won transcript.

This declaration does not prove the bridge; it records the exact hypothesis
needed by the downstream Lemma 4.15 assembly.  The body is intentionally a
passthrough of `hφ`, keeping the remaining concrete modeling obligation visible
instead of hiding it inside an opaque theorem name. -/
theorem winProb_factorsThroughPreWinning
    (gs : GameStructure)
    (W : gs.ProbWinner)
    (φ : PDG X Y → gs.ProbGame)
    -- `φ` is "pre-winning compatible": its image only depends on the not-won
    -- transcript distribution, the standing requirement on a game structure
    -- whose winning predicate fires exactly when some MBO bit is set.
    (hφ : FactorsThroughPreWinning (fun G => gs.winProb W (φ G))) :
    FactorsThroughPreWinning (fun G => gs.winProb W (φ G)) :=
  hφ

/-! ### Lemma 4.15 from the bridge -/

/-- CR18 Lemma 4.15 (the real statement): if the winning probability factors
through the pre-winning behavior (CR18 eqs 4.35–4.37), then **game equivalence
implies equal winning probability**: `G ≡_g H → winFun G = winFun H`.

Unlike a tautology `a = b → f a = f b`, this is the genuine lemma: the hypothesis
`hWin : FactorsThroughPreWinning winFun` is the substantive CR18 obligation, and
the conclusion is Maurer's `G(W) = H(W)`.  Crucially the proof USES the factoring
witness, so the statement is NOT vacuous: it fails for a `winFun` that does not
factor through pre-winning behavior. -/
theorem gameEquiv_winFun_eq
    {winFun : PDG X Y → NNReal}
    (hWin : FactorsThroughPreWinning winFun)
    {G H : PDG X Y}
    (heq : G ≡_g H) :
    winFun G = winFun H := by
  obtain ⟨f, hf⟩ := hWin
  rw [hf G, hf H]
  -- `heq : preWinningBehavior G = preWinningBehavior H`
  exact congrArg f heq

/-- CR18 Lemma 4.15 (concrete winning-probability form): for the Definition-4.5
winning probability of a probabilistic winner `W` against `φ G`, IF that
probability factors through the pre-winning behavior (the CR18 bridge), THEN
`G ≡_g H → winProb W (φ G) = winProb W (φ H)`.

**CR18 reference:** Lemma 4.15 (source line 5365–5378):
  "If G ≡ H then, for any winner W for (X, Y)-games, we have G(W) = H(W)."

The CR18 proof (line 5370–5378): `G(W) = 1 − Σ_{x^q, y^q} P^{WG}_{X^q Y^q, A^q=0}`,
and each term is identical for G and H by equation (4.36) — the game-equivalence
condition.  Hence `G(W) = H(W)`.

The substance lives in `hWin` (the factoring bridge, CR18 eqs 4.35–4.37, a TRUE
but currently-deferred obligation, see `winProb_factorsThroughPreWinning`); given
it, the conclusion follows because equivalence is *definitionally* equal
pre-winning behavior and the winning probability depends on nothing else. -/
theorem gameEquiv_winProb_eq_concrete
    (gs : GameStructure)
    (W : gs.ProbWinner)
    (φ : PDG X Y → gs.ProbGame)
    (hWin : FactorsThroughPreWinning (fun G => gs.winProb W (φ G)))
    {G H : PDG X Y}
    (heq : G ≡_g H) :
    gs.winProb W (φ G) = gs.winProb W (φ H) :=
  gameEquiv_winFun_eq hWin heq

/-- CR18 Lemma 4.15 (simplest closed statement): game equivalence implies that
any measure on the game that factors through the pre-winning behavior assigns
equal mass to equivalent games.

This is the direct consequence of `G ≡_g H → preWinningBehavior G = preWinningBehavior H`:
any quantity that depends on a `PDG` only through its `preWinningBehavior` is
equal for equivalent games.  Applied to `winProb`, this yields CR18 Lemma 4.15.

**CR18 reference:** "If G ≡ H then G(W) = H(W)." -/
theorem gameEquiv_implies_preWinningBehavior_eq
    {G H : PDG X Y}
    (heq : G ≡_g H) :
    preWinningBehavior G = preWinningBehavior H := heq

/-- CR18 Lemma 4.15 (consequence for any Behavior-dependent functional):
if `f : Behavior X Y → α` is any function, then game equivalence implies
`f (preWinningBehavior G) = f (preWinningBehavior H)`.

This is the general form of the CR18 argument: the winning probability
`G(W) = f_W (preWinningBehavior G)` for some functional `f_W` depending on `W`,
so `G ≡ H → G(W) = H(W)` follows by `congr_arg f_W heq`. -/
theorem gameEquiv_behavior_functional
    {α : Type*} (f : Behavior X Y → α)
    {G H : PDG X Y}
    (heq : G ≡_g H) :
    f (preWinningBehavior G) = f (preWinningBehavior H) :=
  congr_arg f heq

end Lem415

end RandomSystems.CR18

/-!
## CR18 Definition 4.17 — Maximal Winning Probability Γ(G)

CR18 §4.10.1 (source ~line 5373):

> **Definition 4.17.** We denote the maximal winning probability for game G as
>
>   `Γ(G) := sup_W G(W)`
>
> where the supremum is taken over all winners W.

### Lean strategy

`Γ(G)` is the supremum of the winning probability `G(W)` over all probabilistic
winners `W : gs.ProbWinner = Dist gs.Winner`.

We work at the level of `Def45.GameStructure` so that `Γ` is defined in terms
of the already-formalised `winProb` (Definition 4.5).

`NNReal` is a `ConditionallyCompleteLinearOrder` (not a full `CompleteLattice`),
so we use `sSup (Set.range ...)` to form the supremum over the image of the
winning-probability function.  This is definitionally equivalent to the
`iSup`-form but avoids the `CompleteLattice` requirement.
-/

namespace RandomSystems.CR18

namespace Def417

universe u v

variable {X : Type u} {Y : Type v}

open Def45 Def415 Def416

/-! ### Γ at the abstract GameStructure level -/

/-- CR18 Definition 4.17: the **maximal winning probability** `Γ(G)` for a
probabilistic game `G` in an abstract game structure `gs`.

Maurer:
  "We denote the maximal winning probability for game G as
   Γ(G) := sup_W G(W)."

The supremum is over all probabilistic winners `W`, i.e. `W : gs.ProbWinner`
with `W.isProbDist` (weight `= 1`).  This restriction is ESSENTIAL: in our
framework `Dist` (LM20 Def 1) is a *sub-distribution of arbitrary weight*, so
a raw `Dist gs.Winner` may have weight `> 1`.  Maurer's winners `W` are genuine
random variables (Def 4.5: "a winner W is a W-valued random variable"), hence
have weight `1`; without `isProbDist` the range of `winProb · G` is *unbounded*
(e.g. `winProb (single w 2) (single g 2) = 4`), so `sSup` would return its junk
value `0` and `winProb_le_maxWinProb` would be FALSE.

`NNReal` is a `ConditionallyCompleteLinearOrder`, so we use
`sSup (winProb · G '' {W | W.isProbDist})` — the supremum of the image of the
winning-probability function over probability-distribution winners. -/
noncomputable def maxWinProb (gs : GameStructure) [Fintype gs.Winner]
    (G : gs.ProbGame) : NNReal :=
  sSup ((fun W : gs.ProbWinner => gs.winProb W G) '' {W | W.isProbDist})

/-! ### Basic properties -/

/-- CR18 Definition 4.17: the winning probability of any fixed winner is a lower
bound on `Γ(G)`.

  `G(W) ≤ Γ(G)`

Proof: `gs.winProb W G` is in the image, and `sSup` is an upper bound of any
element when the set is `BddAbove` (which holds since over probability
distributions `winProb` values are ≤ 1, via `winProb_le_one`).

Note: `W` must be a genuine probability distribution (`hW : W.isProbDist`); a
sub-distribution of weight `> 1` is not a valid winner (Def 4.5) and would not
be bounded by `Γ(G)`.

The game-side hypothesis is stated `Fintype`-free as the Finsupp total mass
`G.sum (fun _ p => p) = 1` so that the lemma applies to concrete game types
(`gs.Game = DDG X Y`, an infinite type); for `Fintype gs.Game` this is
equivalent to `G.isProbDist` via `Dist.weight_eq_finsupp_sum`. -/
theorem winProb_le_maxWinProb (gs : GameStructure) [Fintype gs.Winner]
    (G : gs.ProbGame) (hG : G.sum (fun _ p => p) = 1)
    (W : gs.ProbWinner) (hW : W.isProbDist) :
    gs.winProb W G ≤ maxWinProb gs G := by
  apply le_csSup
  · -- BddAbove: winProb values are bounded above by 1 (over prob. distributions)
    refine ⟨1, ?_⟩
    rintro _ ⟨W', hW', rfl⟩
    exact gs.winProb_le_one W' G
      (by rw [← Dist.weight_eq_finsupp_sum]; exact hW') hG
  · exact ⟨W, hW, rfl⟩

/-- `Γ(G)` is the least upper bound: any upper bound `b` on winning probabilities
satisfies `Γ(G) ≤ b`.

  `(∀ W probabilistic, G(W) ≤ b) → Γ(G) ≤ b` -/
theorem maxWinProb_le_of_forall_le (gs : GameStructure) [Fintype gs.Winner]
    (G : gs.ProbGame) (b : NNReal)
    (hne : ((fun W : gs.ProbWinner => gs.winProb W G) '' {W | W.isProbDist}).Nonempty)
    (h : ∀ W : gs.ProbWinner, W.isProbDist → gs.winProb W G ≤ b) :
    maxWinProb gs G ≤ b := by
  apply csSup_le hne
  rintro _ ⟨W, hW, rfl⟩
  exact h W hW

/-- The maximal winning probability is non-negative.

  `0 ≤ Γ(G)` -/
theorem maxWinProb_nonneg (gs : GameStructure) [Fintype gs.Winner]
    (G : gs.ProbGame) :
    0 ≤ maxWinProb gs G :=
  zero_le _

/-- `Γ(G) ≤ 1`: the maximal winning probability is bounded by 1, assuming the
game `G` is a probability distribution and the set of probabilistic winners is
nonempty.  The per-winner bound `winProb W G ≤ 1` holds for every probabilistic
winner by `winProb_le_one` (Def 4.5). -/
theorem maxWinProb_le_one (gs : GameStructure) [Fintype gs.Winner]
    [Fintype gs.Game] (G : gs.ProbGame) (hG : G.isProbDist)
    (hne : ((fun W : gs.ProbWinner => gs.winProb W G) '' {W | W.isProbDist}).Nonempty) :
    maxWinProb gs G ≤ 1 :=
  maxWinProb_le_of_forall_le gs G 1 hne (fun W hW =>
    gs.winProb_le_one W G
      (by rw [← Dist.weight_eq_finsupp_sum]; exact hW)
      (by rw [← Dist.weight_eq_finsupp_sum]; exact hG))

/-! ### Monotonicity and game equivalence -/

/-- `Γ(G)` is monotone: if `G(W) ≤ H(W)` for all probabilistic `W`, then
`Γ(G) ≤ Γ(H)`.

Requires the image for `G` to be nonempty and `H` to be a probability
distribution (so that `winProb W H ≤ Γ(H)` holds via `winProb_le_maxWinProb`). -/
theorem maxWinProb_mono (gs : GameStructure) [Fintype gs.Winner] [Fintype gs.Game]
    (G H : gs.ProbGame) (hH : H.isProbDist)
    (hne : ((fun W : gs.ProbWinner => gs.winProb W G) '' {W | W.isProbDist}).Nonempty)
    (h : ∀ W : gs.ProbWinner, W.isProbDist → gs.winProb W G ≤ gs.winProb W H) :
    maxWinProb gs G ≤ maxWinProb gs H := by
  apply csSup_le hne
  rintro _ ⟨W, hW, rfl⟩
  -- winProb W G ≤ winProb W H ≤ Γ(H)
  exact le_trans (h W hW)
    (winProb_le_maxWinProb gs H
      (by rw [← Dist.weight_eq_finsupp_sum]; exact hH) W hW)

/-- CR18 Lemma 4.15 consequence: game-equivalent games have the same maximal
winning probability.

  `G ≡_g H → Γ(G) = Γ(H)` -/
theorem maxWinProb_congr_gameEquiv
    [DecidableEq (List (Option Y))]
    (gs : GameStructure) [Fintype gs.Winner] (G H : PDG X Y)
    (φ : PDG X Y → gs.ProbGame)
    (hφ : ∀ W : gs.ProbWinner, Lem415.FactorsThroughPreWinning
                (fun K => gs.winProb W (φ K)))
    (heq : G ≡_g H) :
    maxWinProb gs (φ G) = maxWinProb gs (φ H) := by
  classical
  -- For each fixed `W`, `winProb W (φ G) = winProb W (φ H)` by Lemma 4.15.
  have hW : ∀ W : gs.ProbWinner, gs.winProb W (φ G) = gs.winProb W (φ H) :=
    fun W => Lem415.gameEquiv_winFun_eq (hφ W) heq
  -- The range sets are equal, so the suprema agree.
  simp_rw [maxWinProb, hW]

end Def417

end RandomSystems.CR18
