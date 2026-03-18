/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import RandomSystems.DDS
import RandomSystems.DDE
import RandomSystems.Transcript

/-!
# Probabilistic Discrete Systems (PDS)

Lean 4 formalization of Definitions 8-9 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `PDS X Y q` — a probabilistic discrete system (distribution over DDS)
* `PDS.isProbPDS` — the distribution has weight 1
* `PDS.transcriptDist` — transcript distribution under a non-adaptive environment
* `PDS.adaptiveTranscriptDist` — transcript distribution under an adaptive environment

## Design Notes

A PDS is a `Dist (DDS X Y q)` — a finite-support distribution over
deterministic systems. The "common domain" axiom from the paper is
enforced by the type: every DDS in the distribution has the same type
`DDS X Y q`, so they all answer `q` queries over the same alphabets.

We require `[Fintype (DDS X Y q)]` to make sums computable. This
holds when `X` and `Y` are finite types (the paper's setting).
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-- A Probabilistic Discrete System: a distribution over deterministic systems.

Paper Definition 8: "A PDS S is a distribution over (X,Y)-DDS such that
all DDS in the support of S have the same domain."

The common-domain axiom is enforced by the type: every DDS in the
distribution has type `DDS X Y q`. -/
structure PDS (X : Type*) (Y : Type*) (q : ℕ) [Fintype (DDS X Y q)] where
  /-- The underlying distribution over DDS. -/
  dist : Dist (DDS X Y q)

namespace PDS

variable {X Y : Type*} {q : ℕ} [Fintype (DDS X Y q)]

/-- A PDS is a probability PDS if the underlying distribution has weight 1. -/
def isProbPDS (S : PDS X Y q) : Prop := S.dist.isProbDist

/-- The transcript distribution of a PDS under a fixed (non-adaptive) query sequence.

For a PDS S and input sequence `inputs`, the transcript distribution is:
  tr(S, inputs)(t) := ∑_{s : DDS | s.transcript inputs = t} S.dist(s)

Paper: this is `tr(S, e)` for the non-adaptive environment determined
by `inputs`. -/
def transcriptDist (S : PDS X Y q) (inputs : Fin q → X)
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)] :
    Dist (Transcript X Y q) :=
  Dist.fTransform (fun s => DDS.transcript s inputs) S.dist

/-- `transcriptDist` evaluated at a transcript, written as a sum over the corresponding fiber. -/
theorem transcriptDist_apply_eq_sum (S : PDS X Y q) (inputs : Fin q → X)
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (t : Transcript X Y q) :
    S.transcriptDist inputs t =
      ∑ s ∈ (Finset.univ : Finset (DDS X Y q)).filter (fun s => DDS.transcript s inputs = t),
        S.dist s := by
  simpa [transcriptDist] using
    (Dist.fTransform_apply_eq_sum (f := fun s : DDS X Y q => DDS.transcript s inputs) (X := S.dist)
      (b := t))

/-- The transcript distribution of a PDS under an adaptive environment. -/
def adaptiveTranscriptDist (S : PDS X Y q) (e : DDE X Y q)
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)] :
    Dist (Transcript X Y q) :=
  Dist.fTransform (fun s => interact s e) S.dist

/-- `adaptiveTranscriptDist` evaluated at a transcript, written as a sum over the corresponding
fiber. -/
theorem adaptiveTranscriptDist_apply_eq_sum (S : PDS X Y q) (e : DDE X Y q)
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (t : Transcript X Y q) :
    S.adaptiveTranscriptDist e t =
      ∑ s ∈ (Finset.univ : Finset (DDS X Y q)).filter (fun s => interact s e = t),
        S.dist s := by
  simpa [adaptiveTranscriptDist] using
    (Dist.fTransform_apply_eq_sum (f := fun s : DDS X Y q => interact s e) (X := S.dist) (b := t))

/-- For non-adaptive environments, `adaptiveTranscriptDist` coincides with `transcriptDist`. -/
theorem adaptiveTranscriptDist_nonadaptive (S : PDS X Y q) (inputs : Fin q → X)
    [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)] :
    S.adaptiveTranscriptDist (DDE.nonadaptive inputs) = S.transcriptDist inputs := by
  ext t
  simp [adaptiveTranscriptDist, transcriptDist, interact_nonadaptive]

/-- Two PDS are equal iff their underlying distributions are equal. -/
@[ext]
theorem ext {S T : PDS X Y q} (h : S.dist = T.dist) : S = T := by
  cases S; cases T; simp_all

/-- Construct a PDS from a single DDS (point distribution). -/
def ofDDS (s : DDS X Y q) : PDS X Y q where
  dist := Finsupp.single s 1

/-- The successor PDS: condition on the first query yielding `(x, y)`.

Paper: `S^{↑x↓y}` is the PDS over `DDS X Y q` obtained by conditioning
S on the first query input being `x` and output being `y`, then
taking the successor of each DDS. -/
def successor [DecidableEq X] [DecidableEq Y] [Fintype (DDS X Y (q + 1))]
    (S : PDS X Y (q + 1)) (x : X) (y : Y) : PDS X Y q where
  dist := S.dist.sum (fun s w =>
    if s.firstQuery (Nat.zero_lt_succ q) x = y
    then Finsupp.single (s.successor x) w
    else 0)

end PDS

end RandomSystems
