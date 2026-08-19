/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Surface
import RandomSystems.Jost.Combinators

/-!
# Surface proof tactics: `machine_step`, `bisim_cases`, `couple using`

The bisimulation and coupling proofs of the authoring surface all run the
same drill; these tactics package it with the two measured traps baked in
(STATUS.md §7): `Option.map`/`Option.bind` are UNFOLDED rather than
rewritten by `Option.map_some`/`Option.some.injEq` (which fail across
defeq-but-not-syntactic state types), and constructor equations are closed
by `injection` + `subst`, never `injEq`-rewriting.

* the `machine_step` bundle — the package-step reduction set
  (`Converter.attach_step`, `Machine.runProg_ret/call`, the
  `Option.map`/`Option.bind` unfolds), carried by the macros below; author
  extras are passed as `with [defName, …]`.  (The taggable `@[machine_step]`
  attribute form needs its own module — see the bundle section — and is a
  one-line promotion at integration time.)
* `bisim_cases rel` (optionally `bisim_cases rel with [f, g]` for extra
  unfolds) — applies the bisimulation congruence
  (`Resource.ofRealization_congr_of_bisim` or `Machine.toDDS_eq_of_bisim`),
  splits per interface/input constructor, runs the bundle, and leaves only
  the genuinely creative residues open.
* `couple using j` — applies `Resource.sampleInit_eq_of_coupling` with the
  joint law `j`, discharges the two marginal goals for the common shapes
  (identity / bijection pushforwards of a uniform seed, with finite-carrier
  bijectivity decided), and pre-extracts the support membership in the
  fibres goal when `j` is literally a pushforward.

Limitations are documented on each tactic; residual goals are left open by
design — they are the proof's actual content.
-/

namespace RandomSystems.CC

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource

/-! ## The `machine_step` bundle

A `register_simp_attr machine_step` attribute cannot be *used* in the
module that declares it (Lean initializes extensions at import time), and
this module is single-file by construction-phase constraint; the bundle is
therefore carried by the two macros below — `Converter.attach_step`,
`Machine.runProg_ret/call`, and the `Option.map`/`Option.bind` unfolds —
with author extras supplied via `with [...]`.  Promoting the bundle to a
taggable attribute is a one-line move into its own module at integration
time. -/

/-! ## `bisim_cases` -/

/-- `bisim_cases rel` / `bisim_cases rel with [extra, defs]`.

Targets goals `Resource.ofRealization a = Resource.ofRealization b`
(including `ofState`-built resources, which unfold to it) and
`m₁.toDDS = m₂.toDDS`.  Applies the congruence with relation `rel`,
attempts the initialization condition (`rfl`/`trivial`), destructures the
query, case-splits on the interface and its input, and per case: splits
the answer/preservation conjunction, reduces the step applications with
the `machine_step` set plus the given extras, closes constructor move
equations by `subst`-or-`injection`, and tries `exact rel-hypothesis` /
`simp_all` on what remains.  Unclosed residues stay open, labelled by
their constructor case.

Limitations: a nontrivial initialization condition is left as the first
open goal; if the relation itself is a `∀`-shaped proposition the
intro-pattern heuristic cannot distinguish it from the step goal (state
the initialization manually first in that case). -/
syntax "bisim_cases " term : tactic
syntax "bisim_cases " term " with " "[" ident,* "]" : tactic

macro_rules
  | `(tactic| bisim_cases $rel:term) =>
      `(tactic| bisim_cases $rel with [])
  | `(tactic| bisim_cases $rel:term with [$extras:ident,*]) => do
      let lemmas ← extras.getElems.mapM fun name =>
        `(Lean.Parser.Tactic.simpLemma| $name:ident)
      `(tactic| (
        first
          | refine Resource.ofRealization_congr_of_bisim $rel ?_ ?_
          | refine Machine.toDDS_eq_of_bisim $rel ?_ ?_
        all_goals try (first | rfl | trivial)
        all_goals try (
          rintro s₁ s₂ bisim ⟨iface, inp⟩
          cases iface <;> cases inp <;>
            refine ⟨?_, fun next₁ next₂ move₁ move₂ => ?_⟩ <;>
              first
                | rfl
                | (simp only [Converter.attach_step, Machine.runProg_ret,
                      Machine.runProg_call, Option.map, Option.bind, $lemmas,*]
                    at move₁ move₂
                   first
                     | subst move₁
                     | (injection move₁ with h₁; subst h₁)
                     | skip
                   first
                     | subst move₂
                     | (injection move₂ with h₂; subst h₂)
                     | skip
                   first
                     | exact bisim
                     | simp_all [Converter.attach_step, Machine.runProg_ret,
                         Machine.runProg_call, Option.map, Option.bind,
                         $lemmas,*])
                | simp_all [Converter.attach_step, Machine.runProg_ret,
                    Machine.runProg_call, Option.map, Option.bind, $lemmas,*]
                | skip)))

/-! ## `couple using` -/

/-- `couple using j` — prove `sampleInit f₁ s₁ _ = sampleInit f₂ s₂ _` by
the coupling `j`.  The marginal goals are discharged automatically when
`j` is a pushforward of the (uniform) seed whose projection composite is
the identity or a bijection with decidable bijectivity (any finite
carrier); the fibres goal is pre-processed by introducing the pair and
extracting a representative from the pushforward support.  Whatever
remains open is the coupling's genuine content. -/
syntax "couple " "using " term : tactic

macro_rules
  | `(tactic| couple using $j:term) =>
      `(tactic| (
        refine Resource.sampleInit_eq_of_coupling _ _ $j ?_ ?_ ?_
        all_goals try (first
          | rfl
          | (rw [Dist.fTransform_comp]
             first
               | exact Dist.fTransform_id _
               | exact Dist.fTransform_bijection_uniform _ (by decide)))
        all_goals try (
          intro pair member
          try (obtain ⟨seedPoint, seedMem, seedShape⟩ :=
                Dist.mem_support_fTransform _ _ member
               subst seedShape)
          try simp)))

/-! ## Receipts

The showcase objects, reproduced locally, plus a two-conjunct
delivered-store pair mimicking the shape of a real construction leaf
(`Jost/Construction.lean`'s B-receive case). -/

namespace SurfaceTacticsTests

/-! ### Receipt (a): the counter, one line (was 9). -/

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

noncomputable def counterB : Resource ctr :=
  Resource.ofState ([] : List Unit) fun log query =>
    match query with
    | ⟨.user, .ping⟩ => some (() :: log, ())
    | ⟨.audit, .read⟩ => some (log, log.length)

theorem counterA_eq_counterB : counterA = counterB := by
  bisim_cases (fun n (log : List Unit) => n = log.length)

/-! ### Receipt (b): the coin coupling, two lines (was 10). -/

inductive CoinIface | holder
  deriving DecidableEq
inductive CoinIn | look

def coinIfaces : Interfaces where
  Iface := CoinIface
  In := fun _ => CoinIn
  Out := fun _ => Bool

def coinBox (b : Bool) : coinIfaces.Realization where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨.holder, .look⟩ => some ((), b)

noncomputable def fairCoin : Resource coinIfaces :=
  Resource.sampleInit coinBox (Dist.uniform Bool) Dist.uniform_isProbDist

noncomputable def fairCoinFlipped : Resource coinIfaces :=
  Resource.sampleInit (fun b => coinBox (!b))
    (Dist.uniform Bool) Dist.uniform_isProbDist

theorem fairCoin_eq_flipped : fairCoin = fairCoinFlipped := by
  couple using Dist.fTransform (fun b => (b, !b)) (Dist.uniform Bool)

/-! ### Receipt (c): a two-conjunct invariant with a delivered store —
the `Jost/Construction.lean` B-receive shape (answer read off one
conjunct, counter tracked by the other).  One line (the original case
pattern is ~8 lines per case across five cases). -/

inductive StoreIface | writer | reader
  deriving DecidableEq
inductive WriterIn | put (n : Nat)
inductive ReaderIn | get

def store : Interfaces where
  Iface := StoreIface
  In := fun | .writer => WriterIn | .reader => ReaderIn
  Out := fun | .writer => Unit | .reader => Option Nat

noncomputable def storeAsLog : Resource store :=
  Resource.ofState (([], none) : List Nat × Option Nat) fun s query =>
    match query with
    | ⟨.writer, .put n⟩ => some ((n :: s.1, some n), ())
    | ⟨.reader, .get⟩ => some (s, s.2)

noncomputable def storeAsCount : Resource store :=
  Resource.ofState ((0, none) : Nat × Option Nat) fun s query =>
    match query with
    | ⟨.writer, .put n⟩ => some ((s.1 + 1, some n), ())
    | ⟨.reader, .get⟩ => some (s, s.2)

theorem storeAsLog_eq_storeAsCount : storeAsLog = storeAsCount := by
  bisim_cases (fun (l : List Nat × Option Nat) (c : Nat × Option Nat) =>
    l.1.length = c.1 ∧ l.2 = c.2)

end SurfaceTacticsTests

end RandomSystems.CC
