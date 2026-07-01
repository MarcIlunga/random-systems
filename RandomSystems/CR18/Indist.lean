/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.CR18.DDS
import RandomSystems.CR18.PDS
import RandomSystems.CR18.Behavior
import RandomSystems.CR18.Game

open RandomSystems (Dist)

-- The struct `DDS`/`DDG` carry no decidable membership or equality; this is a noncomputable proof
-- module, so make decidability classical and ambient (low priority) file-wide. This dissolves the
-- `Decidable (· ∈ dom)` / `DecidableEq (DDS X Y)` synthesis obligations that the (deprecated) struct
-- behavior and the `preWinning*`/`gameStructure` machinery would otherwise demand.
open scoped Classical

/-!
# CR18 Definition 4.18 — S⁻ (Strip MBO)

This module formalizes CR18 Definition 4.18 (Maurer's lecture notes,
"Cryptography: Random Systems", §4.10):

> **Definition 4.18.**  For an `(X, Y × {0, 1})`-system `S` with MBO we
> define `S⁻` as the `(X, Y)`-system resulting from `S` by **ignoring the
> MBO**, i.e.,
>
>   `p_{S⁻}_{Yᵢ | Xⁱ Yⁱ⁻¹} = p^S_{Yᵢ | Xⁱ Yⁱ⁻¹}`
>
> In other words, `S⁻` has the same transition kernels as `S` but the
> binary output component `aᵢ` (the MBO bit) is projected away; the
> resulting system has output alphabet `Y` (not `Y × Bool`).

## Design

* **Deterministic layer** (`DDG.strip`): given a `DDG X Y` (a `(X, Y × Bool)`-DDS
  with MBO), produce the `(X, Y)`-DDS that projects out the Bool component at
  every response.  This is the deterministic kernel of the strip operation.

* **Probabilistic layer** (`PDG.strip`): lift `DDG.strip` to the probabilistic
  level by pushing forward along the DDS projection.  A `PDG X Y` (= `Dist (DDG X Y)`)
  becomes a `PDS X Y` (= `Dist (DDS X Y)`) by mapping each `DDG X Y` to the
  stripped `DDS X Y`.

## Relation to existing code

* `DDG X Y` and `PDG X Y` are defined in `RandomSystems.CR18.Game`.
* `DDS X Y` and `PDS X Y` are defined in `RandomSystems.CR18.DDS` /
  `RandomSystems.CR18.PDS`.
* `Winner.projectGame` (in `Game.lean`) is essentially the same projection
  applied *inside* the winner's view of a DDG.  `DDG.strip` lifts this to the
  top-level system level and is defined independently to avoid namespace
  confusion.
-/

namespace RandomSystems.CR18

/-! ## Deterministic strip: DDG → DDS -/

/-- CR18 Definition 4.18 (deterministic layer): strip the MBO from a DDG.

Given a `(X, Y × Bool)`-DDG `g`, produce the `(X, Y)`-DDS `g⁻` by projecting
away the Bool component `aᵢ` at every response.

Maurer: "S⁻ is the (X, Y)-system resulting from S by ignoring the MBO, i.e.,
  `p^{S⁻}_{Yᵢ|XⁱYⁱ⁻¹} = p^S_{Yᵢ|XⁱYⁱ⁻¹}`."

The domain and prefix-closure structure are inherited unchanged from `g`; only
the response type changes from `Y × Bool` to `Y` via `Prod.fst`. -/
def DDG.strip {X Y : Type*} (g : DDG X Y) : DDS X Y where
  dom            := g.toSystem.dom
  nonempty_input := g.toSystem.nonempty_input
  prefix_closed  := g.toSystem.prefix_closed
  respond        := fun l hl => (g.toSystem.respond l hl).1

namespace DDG.strip

variable {X Y : Type*}

/-- The domain of the stripped system equals the domain of the original DDG. -/
@[simp]
theorem dom_eq (g : DDG X Y) : g.strip.dom = g.toSystem.dom := rfl

/-- The response of the stripped system at history `l` is the `Y`-component
of the DDG's full `(Y × Bool)` response. -/
@[simp]
theorem respond_eq (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) :
    g.strip.respond l hl = (g.toSystem.respond l hl).1 := rfl

/-- Stripping recovers the same `Y`-output as `DDG.regularOutput`. -/
theorem strip_eq_regularOutput (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) :
    g.strip.respond l hl = g.regularOutput l hl := rfl

/-- Stripping is consistent with `Winner.projectGame`: both project the DDG to
the `Y`-view that the winner sees. -/
theorem strip_eq_projectGame (g : DDG X Y) : g.strip = Winner.projectGame g := rfl

end DDG.strip

/-! ## Probabilistic strip: PDG → PDS -/

/-- CR18 Definition 4.18 (probabilistic layer): strip the MBO from a PDG.

A `PDG X Y` is a `Dist (DDG X Y)` — a random variable over DDGs.  `S⁻`
(read: "S minus") is the `PDS X Y` (= `Dist (DDS X Y)`) obtained by mapping
each DDG in the support of `S` to its stripped `DDS` via `DDG.strip`, then
pushing forward the distribution.

Formally, for every `(X, Y × Bool)`-game `g` in the support of `S`:
  `S⁻(s) = ∑_{g : DDG.strip g = s} S(g)`

which is precisely `Dist.fTransform DDG.strip S`. -/
noncomputable def PDG.strip {X Y : Type*} (S : PDG X Y) : PDS X Y :=
  Dist.fTransform DDG.strip S

namespace PDG.strip

variable {X Y : Type*}

/-- `PDG.strip` is `Dist.fTransform DDG.strip` by definition. -/
@[simp]
theorem eq_fTransform (S : PDG X Y) :
    S.strip = Dist.fTransform DDG.strip S := rfl

/-- Stripping the degenerate PDG concentrated at a single DDG `g` gives the
degenerate PDS concentrated at `g.strip`. -/
theorem strip_pure (g : DDG X Y) :
    (PDG.pure g).strip = PDS.pure g.strip := by
  simp only [PDG.strip, PDG.pure, PDS.pure, Dist.fTransform]
  rw [Finsupp.sum_single_index (by simp)]

/-- Stripping the degenerate PDG `PDG.ofDDG g` equals `PDS.pure g.strip`. -/
theorem strip_ofDDG (g : DDG X Y) :
    (PDG.ofDDG g).strip = PDS.pure g.strip :=
  strip_pure g

end PDG.strip

/-! ## S⁻ notation and abbreviation

We introduce the postfix `⁻` notation (via a dedicated def + notation) so
that the usual CR18 prose `S⁻` reads naturally in Lean.
-/

/-- CR18 Definition 4.18: `stripMBO S` is the `(X, Y)`-PDS `S⁻` obtained from
the `(X, Y × Bool)`-PDG `S` by ignoring the MBO.

This is the main exported definition for item 4.18. -/
noncomputable abbrev stripMBO {X Y : Type*} (S : PDG X Y) : PDS X Y :=
  S.strip

end RandomSystems.CR18

/-!
## CR18 Lemma 4.16, Stages K1/K2 — The Pre-Winning Transcript Distribution

CR18 §4.11 (printed proof of Lemma 4.16, source ~line 5509–5536) rests on the
**cancellation step**

  `Pr^{DS}(Z=1 ∧ Aq=0) = Pr^{DT}(Z=1 ∧ Aq=0)`,

i.e. the joint probability of (visible transcript event ∧ game not yet won) is
identical for two game-equivalent games.  The cancellation holds because this
joint probability **factorizes** through the pre-winning behavior
`p^G_{Y_i, A_i=0 | X^i, Y^{i-1}, A^{i-1}=0}` (Definition 4.15; cf. Maurer
eq 4.38 `p^S_{Y^i, A_i=0 | X^i} = p^S_{A_i=0 | X^i} · p^S_{Y^i | X^i, A_i=0}`)
and the behavior of the distinguishing environment — the exact Lemma 3.2
factorization shape with the pre-winning behavior in place of the full
behavior.  Since `Z = 1` is an event over the **visible** transcript only (the
distinguisher never sees the MBO), `Pr(Z=1 ∧ Aq=0)` is a sum of pre-winning
transcript probabilities, and termwise equality yields the cancellation.

This block supplies the three ingredients (stages K1/K2 of the Lemma 4.16
assembly; the `Z=1` summation and the elimination of the former `hBridge`
are completed in the K3/K4 section further below):

1. `preWinTranscriptDist G E xs ys` — the joint probability that the `E‖G`
   interaction produces the visible transcript `(xs, ys)` AND the MBO of `G`
   is still `0` after all `|xs|` rounds.

2. `preWinTranscriptDist_factorization` — the Lemma 3.2-shaped factorization
   of that probability into the chain-rule product of the environment behavior
   and the **pre-winning** behavior (Def 4.15).

3. `preWinTranscriptDist_congr_gameEquiv` — the invariance: game-equivalent
   probability games (Def 4.16) induce the SAME pre-winning transcript
   distribution against every environment.  This is the precise content of
   the cancellation step in Maurer's printed proof of Lemma 4.16.
-/

namespace RandomSystems.CR18

namespace Lem416

universe u v

variable {X : Type u} {Y : Type v}
  [DecidableEq (DDS X Y)]
  [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]

/-- **CR18 Lemma 4.16 (K1): the pre-winning transcript distribution.**

`preWinTranscriptDist G E xs ys` is the joint probability, in the random
experiment where the game `G : PDG X Y` and the environment `E : PDE X Y` are
drawn independently (CR18 §3.5) and interact, of the event

  `{ visible transcript = (xs, ys) }  ∧  { A_q = 0 }`     (q = `|xs|`)

— the interaction produces input history `xs` and **visible** output history
`ys` (the `Y`-components; the distinguisher of Lemma 4.16 interacts with the
stripped `S⁻` and never sees the MBO), and the monotone binary output of `G`
is still `0` after all `q` rounds.

It is defined equationally as the `transcriptJointProb` (Lemma 3.2 LHS) of the
**pre-winning PDS** of `G` (Definition 4.15):

* `(Def415.preWinningDDS g).outputSeq xs = ys.map some` holds iff every prefix
  `xs.take (k+1)` lies in `g`'s domain with all MBO bits `false` and the
  regular outputs are exactly `ys` — i.e. iff `g` answers `ys` on `xs` with
  the game not won through round `q`.  Pushing `G` forward along
  `Def415.preWinningDDS` (= `Def415.preWinningPDS G`) therefore makes
  `jointProb (Def415.preWinningPDS G) xs ys = Pr_{g~G}[outputs ys on xs ∧ Aq=0]`.
* Independence of `G` and `E` turns the interaction event into the rectangle
  product with `envJointProb E ys xs = Pr_{e~E}[e asks xs on ys]`, exactly as
  in the closed `transcriptJointProb` (see the Lem 3.2 block, Behavior.lean).

So `preWinTranscriptDist G E xs ys = Pr^{EG}[X^qY^q = (xs,ys) ∧ A_q = 0]`,
the quantity whose `S`/`T` equality is the cancellation step of Lemma 4.16. -/
noncomputable def preWinTranscriptDist
    (G : PDG X Y) (E : PDE X Y) (xs : List X) (ys : List Y) : NNReal :=
  transcriptJointProb (Def415.preWinningPDS G) E xs ys

/-- Unfolding lemma: the pre-winning transcript distribution is the rectangle
product of the pre-winning system event and the environment event. -/
theorem preWinTranscriptDist_eq
    (G : PDG X Y) (E : PDE X Y) (xs : List X) (ys : List Y) :
    preWinTranscriptDist G E xs ys =
      jointProb (Def415.preWinningPDS G) xs ys * envJointProb E ys xs := rfl

/-- **CR18 Lemma 4.16 (K1): the factorization lemma.**

The pre-winning transcript distribution factors as the interleaved chain-rule
product of the environment behavior `b(E)` and the **pre-winning behavior**
of `G` (Definition 4.15):

  `Pr^{EG}[X^qY^q = (xs,ys) ∧ A_q=0]
     = base · ∏_{i=1}^{q} pᴱ_{X_i|X^{i-1}Y^{i-1}} · p^G_{Y_i,A_i=0|X^i,Y^{i-1},A^{i-1}=0}`

This is exactly the Lemma 3.2 factorization with the pre-winning slice
`p_{Y_i, A_i=0 | …, A^{i-1}=0}` replacing the full behavior `p_{Y_i | …}`
(Maurer eq 4.38 splits the same joint), obtained by instantiating the proved
`lem_3_2` at the pre-winning PDS of `G` — `Def415.preWinningBehavior G` is by
definition `behavior (Def415.preWinningPDS G)`.

`base` is the chain-rule base factor of the `E‖G` experiment (the product of
the total masses; `= 1` on CR18's weight-1 domain — see the EQUATIONAL RECAST
notes on `transcriptDist`/`condSliceProd` in Behavior.lean). -/
theorem preWinTranscriptDist_factorization
    (G : PDG X Y) (E : PDE X Y) (xs : List X) (ys : List Y)
    (hlen : xs.length = ys.length) :
    preWinTranscriptDist G E xs ys =
      transcriptDist
        (jointProb (Def415.preWinningPDS G) [] [] * envJointProb E [] [])
        (Def415.preWinningBehavior G) (envBehavior E) xs ys :=
  lem_3_2 (Def415.preWinningPDS G) E xs ys hlen

/-- **CR18 Lemma 4.16 (K2): the invariance lemma — the cancellation step.**

If `G ≡_g H` (game equivalence, Definition 4.16 = identical pre-winning
behavior) and `G`, `H` are genuine probability distributions (Maurer's
weight-1 setting, stated `Fintype`-free as Finsupp mass `= 1`; on the LM20
sub-distribution model the statement is FALSE without it — rescaling `G` by
`c ≠ 1` preserves every behavior ratio, hence game equivalence, while scaling
the transcript probability by `c`), then `G` and `H` induce the **same**
pre-winning transcript distribution against **every** environment `E` and
**every** transcript `(xs, ys)`:

  `Pr^{EG}[X^qY^q = (xs,ys) ∧ A_q=0] = Pr^{EH}[X^qY^q = (xs,ys) ∧ A_q=0]`.

Summing over the visible transcripts with `Z = 1` (the distinguisher's output
is a function of the visible transcript only) yields Maurer's cancellation
`Pr^{DS}(Z=1 ∧ Aq=0) = Pr^{DT}(Z=1 ∧ Aq=0)` — the second step of the printed
proof of Lemma 4.16 (source ~line 5530).

No length hypothesis is needed: for `|xs| ≠ |ys|` both sides vanish (no
output sequence of length `|xs|` equals a `some`-image of length `|ys|`).

**Proof**: factorize both sides (`preWinTranscriptDist_factorization` =
`lem_3_2` at the pre-winning PDS), reduce both base factors to the mass of
`E`'s empty event via weight-1 (the pre-winning pushforward preserves total
mass), and rewrite the pre-winning behavior of `G` to that of `H` along the
game equivalence — the termwise-equal-products assembly of
`transcriptDist_congr_bS`/`gameEquiv_iff_stepwise`. -/
theorem preWinTranscriptDist_congr_gameEquiv
    {G H : PDG X Y} (heq : Def416.GameEquiv G H)
    (hG : G.sum (fun _ p => p) = 1) (hH : H.sum (fun _ p => p) = 1)
    (E : PDE X Y) (xs : List X) (ys : List Y) :
    preWinTranscriptDist G E xs ys = preWinTranscriptDist H E xs ys := by
  -- Game equivalence is, by Definition 4.16, equality of pre-winning behaviors.
  have hbeh : Def415.preWinningBehavior G = Def415.preWinningBehavior H := heq
  rcases eq_or_ne xs.length ys.length with hlen | hlen
  · -- Genuine transcript shape: factorize both sides and compare.
    -- (1) The pre-winning pushforward preserves the total mass, so weight-1
    --     games have base factor `jointProb (preWinningPDS K) [] [] = 1`.
    have hbase : ∀ (K : PDG X Y), K.sum (fun _ p => p) = 1 →
        jointProb (Def415.preWinningPDS K) [] [] = 1 := by
      intro K hK
      -- `jointProb S [] []` is the total mass of `S` (the empty event is sure):
      -- every DDS has `outputSeq [] = [] = [].map some`.
      have hempty : jointProb (Def415.preWinningPDS K) [] [] =
          (Def415.preWinningPDS K).sum (fun _ p => p) := by
        rw [jointProb_eq_sum_support]
        refine Finset.sum_congr rfl fun s _ => if_pos ?_
        simp [DDS.outputSeq]
      -- `fTransform` (the pre-winning pushforward) preserves the total mass.
      have hmass : (Def415.preWinningPDS K).sum (fun _ p => p) =
          K.sum (fun _ p => p) := by
        unfold Def415.preWinningPDS Dist.fTransform
        rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
        exact Finsupp.sum_congr fun g _ => Finsupp.sum_single_index rfl
      rw [hempty, hmass, hK]
    rw [preWinTranscriptDist_factorization G E xs ys hlen,
      preWinTranscriptDist_factorization H E xs ys hlen,
      hbase G hG, hbase H hH, hbeh]
  · -- Degenerate shape `|xs| ≠ |ys|`: both sides are 0, since an output
    -- sequence on `xs` always has length `|xs|` and can never equal
    -- `ys.map some` of length `|ys|`.
    have hzero : ∀ (S : PDS X Y), jointProb S xs ys = 0 := by
      intro S
      rw [jointProb_eq_sum_support]
      refine Finset.sum_eq_zero fun s _ => if_neg fun hc => hlen ?_
      simpa [DDS.outputSeq] using congrArg List.length hc
    rw [preWinTranscriptDist_eq, preWinTranscriptDist_eq, hzero, hzero,
      zero_mul]

end Lem416

end RandomSystems.CR18

/-!
## CR18 Lemma 4.16, Stages K3/K4 — The Concrete Lemma 4.16 (cancellation proven)

This section UN-HOLLOWS Lemma 4.16: the former abstract statements carried the
entire probabilistic content in a caller-supplied bridge hypothesis `hBridge`
(documented `⚠ HOLLOW` in the checklist).  Here the lemma is **de-abstracted to
the concrete PDG/PDS level** and the bridge is **proven internally** from the
K1/K2 ingredients (`preWinTranscriptDist` + factorization + game-equivalence
invariance), following Maurer's printed proof (CR18 §4.11, source ~5509–5536):

  `⟨S⁻|T⁻⟩(D) = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`
  `           = Pr^{DT}(Z=1∧Aq=0) + Pr^{DT}(Z=1∧Aq=1) − Pr^{DS}(Z=1∧Aq=0) − Pr^{DS}(Z=1∧Aq=1)`
  `           = Pr^{DT}(Z=1∧Aq=1) − Pr^{DS}(Z=1∧Aq=1)`   (cancellation, eqs 4.35–4.36)
  `           ≤ Pr^{DT}(Z=1∧Aq=1) ≤ Pr^{DT}(Aq=1) = T(D) = S(D) ≤ Γ(S).`

### Concrete model (the de-abstraction)

* **Query horizon `q`**: Maurer fixes "the maximal number of queries that D
  makes" and pads to exactly `q` dummy queries (source ~5280: "we therefore
  consider transcripts (X^q, Y^q) of q inputs and outputs").  The concrete
  distinguishers/winners are therefore parameterized by `q`, and transcripts
  are pairs `t : (Fin q → X) × (Fin q → Y)` (a `Fintype`, so `Σ_{x^q,y^q}` is
  a `Finset.sum` — this is also why the section assumes `[Fintype X]
  [Fintype Y]`, Maurer's finite-alphabet setting).

* **`Strategy X Y q`** — a total `q`-query winner: for each round `k < q`, a
  next query as a function of the `k` outputs seen so far.  This is exactly
  Maurer's deterministic winner (Def 3.23, a `(Y,X)`-environment) in its
  total, exactly-`q`-queries normal form; crucially it is a **`Fintype`**, so
  the existing `Def417.maxWinProb` (whose supremum ranges over
  `{W | W.isProbDist}`) applies verbatim.

* **`CompletesAt e s xs ys`** — the equational completed-transcript event:
  `s` outputs `ys` on `xs` AND `e` asks `xs` on `ys`.  Deterministic
  interaction is captured by `completesAt_unique` (at most one completed
  transcript per pair) — no operational driver loop is used.

* **`distinctionStructure X Y q`** — the concrete `Def47.DistinctionStructure`:
  objects are `DDS X Y`, deterministic distinguishers are pairs
  `(w, Z) : Strategy X Y q × (transcript → Bool)` (Maurer §4.10.2: the output
  bit `Z` is generated from the transcript by `p^D_{Z|X^qY^q}`; a
  deterministic distinguisher has a deterministic `Z`), and
  `κ (w, Z) s = 1` iff the interaction completes at an accepted transcript.

* **`gameStructure X Y q`** — the concrete `Def45.GameStructure`: games are
  `DDG X Y`, winners are `Strategy X Y q`, and the winning predicate is
  Maurer's **eq (4.37) complement form**
  `G(W) = 1 − Pr^{WG}(Aq = 0)`:  `win w g` holds iff there is **no** `q`-round
  transcript completed by the **pre-winning** DDS of `g` (Def 4.15) against
  `w`.  On Maurer's domain (total systems, weight-1 distributions) this is
  exactly `Aq = 1`; on the partial-DDS generalization a run that aborts
  before round `q` also counts as "won", which is the faithful reading of
  eq (4.37) (and what makes `Pr(Aq=1) = 1 − Pr(Aq=0)` an identity rather
  than an extra totality hypothesis).

### Hypotheses audit (anti-hollowness)

The theorems below take ONLY Maurer's hypotheses: `GameEquiv S T` (the
lemma's premise), weight-1 of `S`, `T`, `D` (games/winners/distinguishers are
genuine random variables, Def 4.5/4.7; stated `Fintype`-free as Finsupp mass
`= 1` where the carrier is infinite), and the setting parameters
(`q`, `[Fintype X] [Fintype Y]`, decidability/inhabitedness instances).
There is NO `hBridge`-style content-assuming hypothesis.
-/

namespace RandomSystems.CR18

namespace Lem416

universe u v

/-! ### Total `q`-query strategies and the transcript-completion event -/

/-- A **total `q`-query strategy**: for each round `k < q`, the next query
`x_{k+1} ∈ X` as a function of the outputs `y_1, …, y_k` seen so far.

This is Maurer's deterministic winner/distinguisher strategy in its
exactly-`q`-queries normal form (CR18 ~5280: shorter interactions are padded
with dummy queries, so w.l.o.g. every winner/distinguisher makes exactly `q`
queries).  For `[Fintype X] [Fintype Y]` this type is a `Fintype` — the key
to instantiating `Def417.maxWinProb` concretely. -/
abbrev Strategy (X : Type u) (Y : Type v) (q : ℕ) :=
  ∀ k : Fin q, (Fin k.val → Y) → X

/-- Embed a total `q`-query strategy as a `DDE X Y` (Def 3.16): on an output
history of length `k < q` it asks the strategy's round-`k` query (extracting
the `Y`-values from the `Option Y` entries; the interaction protocol only
ever presents all-`some` histories), and it stops after `q` rounds. -/
def Strategy.toDDE {X : Type u} {Y : Type v} [Inhabited Y] {q : ℕ}
    (w : Strategy X Y q) : DDE X Y := fun l =>
  if h : l.length < q then
    some (w ⟨l.length, h⟩ fun i => (l[(i : ℕ)]'i.isLt).getD default)
  else
    none

/-- The **completed-transcript event**: the interaction of environment `e`
with system `s` produces exactly the visible transcript `(xs, ys)` — the
system outputs `ys` on `xs` (every prefix of `xs` is answered, with values
`ys`) and the environment asks `xs` on `ys`.

This is the equational (event-intersection) description of deterministic
interaction; no operational driver is involved.  `completesAt_unique` below
shows the event holds for at most one transcript of each length. -/
def CompletesAt {X : Type u} {Y : Type v} (e : DDE X Y) (s : DDS X Y)
    (xs : List X) (ys : List Y) : Prop :=
  s.outputSeq xs = ys.map some ∧ DDE.inputSeq e ys = xs.map some

/-! ### The concrete distinction and game structures -/

open scoped Classical in
/-- The concrete `Def47.DistinctionStructure` of CR18 §4.10.2 at query
horizon `q`: objects are `(X,Y)`-DDSs; a deterministic distinguisher is a
pair `(w, Z)` of a total `q`-query strategy and a decision predicate `Z` on
the visible `q`-round transcript; `κ (w,Z) s = 1` iff the `w`↔`s`
interaction completes at a transcript accepted by `Z`.

(The decision `Z` is Maurer's output bit `p^D_{Z|X^qY^q}`, deterministic for
a deterministic distinguisher; probabilistic distinguishers are `Dist`s over
these pairs, exactly Def 4.7.) -/
noncomputable def distinctionStructure (X : Type u) (Y : Type v) [Inhabited Y]
    (q : ℕ) : Def47.DistinctionStructure where
  O := DDS X Y
  D := Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)
  κ := fun d s =>
    decide (∃ t : (Fin q → X) × (Fin q → Y),
      CompletesAt (Strategy.toDDE d.1) s (List.ofFn t.1) (List.ofFn t.2) ∧
        d.2 t = true)

open scoped Classical in
/-- The concrete `Def45.GameStructure` of CR18 §4.10.1 at query horizon `q`:
games are `(X,Y)`-DDGs, winners are total `q`-query strategies, and the
winning predicate is Maurer's eq (4.37) complement form
`G(W) = Pr^{WG}(Aq=1) = 1 − Pr^{WG}(Aq=0)`:

`win w g` holds iff there is NO `q`-round transcript completed by the
**pre-winning** DDS of `g` (Definition 4.15 — the restriction of `g` to
histories with all MBO bits `0`) against `w`; i.e. iff the event `Aq = 0`
fails.  On total games this is literally "some MBO bit fires within `q`
rounds"; on partial DDSs an aborted run also counts as `Aq ≠ 0` (the
faithful reading of eq 4.37 — see the section header). -/
noncomputable def gameStructure (X : Type u) (Y : Type v) [Inhabited Y]
    (q : ℕ) : Def45.GameStructure where
  Game := DDG X Y
  Winner := Strategy X Y q
  win := fun w g =>
    decide (¬ ∃ t : (Fin q → X) × (Fin q → Y),
      CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
        (List.ofFn t.1) (List.ofFn t.2))

open scoped Classical in
/-- Definitional unfolding of the concrete `κ`. -/
theorem distinctionStructure_κ {X : Type u} {Y : Type v} [Inhabited Y]
    {q : ℕ} (d : Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool))
    (s : DDS X Y) :
    (distinctionStructure X Y q).κ d s =
      decide (∃ t : (Fin q → X) × (Fin q → Y),
        CompletesAt (Strategy.toDDE d.1) s (List.ofFn t.1) (List.ofFn t.2) ∧
          d.2 t = true) := rfl

open scoped Classical in
/-- Definitional unfolding of the concrete winning predicate. -/
theorem gameStructure_win {X : Type u} {Y : Type v} [Inhabited Y]
    {q : ℕ} (w : Strategy X Y q) (g : DDG X Y) :
    (gameStructure X Y q).win w g =
      decide (¬ ∃ t : (Fin q → X) × (Fin q → Y),
        CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
          (List.ofFn t.1) (List.ofFn t.2)) := rfl

instance {X : Type u} {Y : Type v} [Inhabited Y]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (q : ℕ) :
    Fintype ((distinctionStructure X Y q).D) :=
  inferInstanceAs
    (Fintype (Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)))

instance {X : Type u} {Y : Type v} [Inhabited Y]
    [Fintype X] [Fintype Y] [DecidableEq Y] (q : ℕ) :
    Fintype ((gameStructure X Y q).Winner) :=
  inferInstanceAs (Fintype (Strategy X Y q))

instance {X : Type u} {Y : Type v} [Inhabited Y]
    [Fintype Y] [DecidableEq X] [DecidableEq Y] (q : ℕ) :
    DecidableEq ((gameStructure X Y q).Winner) :=
  inferInstanceAs (DecidableEq (Strategy X Y q))

-- NOTE: deliberately NO local `[DecidableEq (DDS X Y)]` variable here — `PDG.strip`
-- bakes the global classical instance into its definition, so all `DDS`-level
-- decidability in this section must resolve to that same global instance.
variable {X : Type u} {Y : Type v}
  [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-! ### Uniqueness of the completed transcript -/

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y] in
/-- A completed transcript has matching input/output lengths. -/
theorem CompletesAt.length_eq {e : DDE X Y} {s : DDS X Y}
    {xs : List X} {ys : List Y} (h : CompletesAt e s xs ys) :
    xs.length = ys.length := by
  simpa [DDS.outputSeq] using congrArg List.length h.1

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y] in
/-- **Determinism of interaction (equational form)**: a deterministic
environment and a deterministic system complete at most ONE transcript of
each length.  Round-by-round, the next query is determined by the outputs so
far (`DDE.inputSeq`) and the next output is determined by the queries so far
(`DDS.outputSeq`); the two interleaved recurrences pin the transcript down.

This replaces any operational "run the interaction" driver: it is the only
inductive ingredient of the Lemma 4.16 assembly. -/
theorem completesAt_unique {e : DDE X Y} {s : DDS X Y}
    {xs xs' : List X} {ys ys' : List Y}
    (h : CompletesAt e s xs ys) (h' : CompletesAt e s xs' ys')
    (hlen : xs.length = xs'.length) :
    xs = xs' ∧ ys = ys' := by
  have hxy : xs.length = ys.length := h.length_eq
  have hxy' : xs'.length = ys'.length := h'.length_eq
  -- Entry form of the environment component of `CompletesAt`.
  have hIN : ∀ (m : List X) (zs : List Y),
      DDE.inputSeq e zs = m.map some →
      ∀ (hl : m.length = zs.length) (k : ℕ) (hk : k < zs.length),
        e ((zs.take k).map some) = some (m[k]'(by omega)) := by
    intro m zs hmz hl k hk
    have h1 := List.getElem_of_eq hmz (i := k)
      (by simpa [DDE.inputSeq] using hk)
    simpa [DDE.inputSeq] using h1
  -- Entry form of the system component of `CompletesAt`.
  have hOUT : ∀ (m : List X) (zs : List Y),
      s.outputSeq m = zs.map some →
      ∀ (hl : m.length = zs.length) (k : ℕ) (hk : k < m.length),
        (if hd : m.take (k + 1) ∈ s.dom
          then some (s.respond (m.take (k + 1)) hd) else none) =
          some (zs[k]'(by omega)) := by
    intro m zs hmz hl k hk
    have h1 := List.getElem_of_eq hmz (i := k)
      (by simpa [DDS.outputSeq] using hk)
    simpa [DDS.outputSeq] using h1
  -- Interleaved induction: the transcripts agree on every prefix.
  have key : ∀ k : ℕ, xs.take k = xs'.take k ∧ ys.take k = ys'.take k := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      rcases Nat.lt_or_ge k xs.length with hlt | hge
      · -- genuine round `k+1`
        have hxk : xs[k]'hlt = xs'[k]'(hlen ▸ hlt) := by
          have e1 := hIN xs ys h.2 hxy k (by omega)
          have e2 := hIN xs' ys' h'.2 hxy' k (by omega)
          rw [ih.2] at e1
          exact Option.some.inj (e1.symm.trans e2)
        have htx : xs.take (k + 1) = xs'.take (k + 1) := by
          rw [List.take_add_one, List.take_add_one, ih.1,
            List.getElem?_eq_getElem hlt,
            List.getElem?_eq_getElem (hlen ▸ hlt), hxk]
        have hyk : ys[k]'(by omega) = ys'[k]'(by omega) := by
          have o1 := hOUT xs ys h.1 hxy k hlt
          have o2 := hOUT xs' ys' h'.1 hxy' k (hlen ▸ hlt)
          rw [htx] at o1
          exact Option.some.inj (o1.symm.trans o2)
        have hty : ys.take (k + 1) = ys'.take (k + 1) := by
          rw [List.take_add_one, List.take_add_one, ih.2,
            List.getElem?_eq_getElem (show k < ys.length by omega),
            List.getElem?_eq_getElem (show k < ys'.length by omega), hyk]
        exact ⟨htx, hty⟩
      · -- saturated: both transcripts are already exhausted
        have hxx : xs = xs' := by
          have t1 : xs.take k = xs := List.take_of_length_le hge
          have t2 : xs'.take k = xs' := List.take_of_length_le (by omega)
          rw [← t1, ← t2]; exact ih.1
        have hyy : ys = ys' := by
          have t1 : ys.take k = ys := List.take_of_length_le (by omega)
          have t2 : ys'.take k = ys' := List.take_of_length_le (by omega)
          rw [← t1, ← t2]; exact ih.2
        exact ⟨by rw [hxx], by rw [hyy]⟩
  refine ⟨?_, ?_⟩
  · have hx := (key xs.length).1
    rwa [List.take_length, List.take_of_length_le (le_of_eq hlen.symm)] at hx
  · have hy := (key ys.length).2
    rwa [List.take_length, List.take_of_length_le (by omega)] at hy

/-! ### Pre-winning completion implies visible completion -/

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y] in
/-- If the **pre-winning** DDS of `g` (Def 4.15) outputs `ys` on `xs`, then so
does the **stripped** system `g⁻` (Def 4.18): the pre-winning domain is a
restriction of `g`'s domain and both respond with the visible `Y`-component. -/
theorem strip_outputSeq_of_preWinning {g : DDG X Y}
    {xs : List X} {ys : List Y}
    (h : (Def415.preWinningDDS g).outputSeq xs = ys.map some) :
    (DDG.strip g).outputSeq xs = ys.map some := by
  have hlen : xs.length = ys.length := by
    simpa [DDS.outputSeq] using congrArg List.length h
  apply List.ext_getElem (by simpa [DDS.outputSeq] using hlen)
  intro k hk1 hk2
  have hk : k < xs.length := by simpa [DDS.outputSeq] using hk1
  have hsrc := List.getElem_of_eq h (i := k)
    (by simpa [DDS.outputSeq] using hk)
  simp only [DDS.outputSeq, List.getElem_map, List.getElem_finRange,
    Fin.val_cast] at hsrc ⊢
  -- The condition's index `↑(finRange xs.length)[k]` sits in the `dite`'s `Decidable` position, which
  -- `simp`/`rw` cannot reduce there; `split` case-splits the `dite` on the actual condition instead.
  split at hsrc
  · rename_i hmem
    split
    · rw [← hsrc]; rfl
    · rename_i hnotmem
      exact absurd (Def415.preWinningDDS_dom_subset g hmem) hnotmem
  · simp at hsrc

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y] in
/-- A transcript completed by the pre-winning DDS is completed by the
stripped system (same environment component). -/
theorem completesAt_strip_of_preWinning {e : DDE X Y} {g : DDG X Y}
    {xs : List X} {ys : List Y}
    (h : CompletesAt e (Def415.preWinningDDS g) xs ys) :
    CompletesAt e (DDG.strip g) xs ys :=
  ⟨strip_outputSeq_of_preWinning h.1, h.2⟩

/-! ### Finsupp/Finset toolbox -/

/-- Pointwise evaluation of a pushforward (`Dist.fTransform`) as a fiber sum. -/
theorem fTransform_apply_finsupp {α : Type*} {β : Type*} [DecidableEq β]
    (f : α → β) (G : Dist α) (b : β) :
    Dist.fTransform f G b = G.sum fun a w => if f a = b then w else 0 := by
  simp only [Dist.fTransform]
  rw [Finsupp.sum_apply]
  exact Finsupp.sum_congr fun a _ => Finsupp.single_apply

omit [DecidableEq (List (Option X))] [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- `jointProb` of a pushforward PDS as a sum over the source distribution. -/
theorem jointProb_fTransform {α : Type*} (f : α → DDS X Y) (G : Dist α)
    (xs : List X) (ys : List Y) :
    jointProb (Dist.fTransform f G) xs ys =
      G.sum fun g w => if (f g).outputSeq xs = ys.map some then w else 0 := by
  simp only [jointProb, jointOutputDist]
  rw [Dist.fTransform_comp, fTransform_apply_finsupp]
  rfl

/-- Marginal-style sum transport along a pushforward (Finsupp form). -/
theorem fTransform_sum_mul_finsupp {α : Type*} {β : Type*} [DecidableEq β]
    (D : Dist α) (f : α → β) (F : β → NNReal) :
    (Dist.fTransform f D).sum (fun b w => w * F b) =
      D.sum fun a w => w * F (f a) := by
  simp only [Dist.fTransform]
  rw [Finsupp.sum_sum_index (fun b => by simp)
    (fun b m₁ m₂ => add_mul m₁ m₂ (F b))]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [Finsupp.sum_single_index (by simp)]

/-- A `Fintype` sum of a `{0,1}`-indicator with at most one witness is the
indicator of existence. -/
theorem sum_indicator_unique {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] (huniq : ∀ a b, P a → P b → a = b) :
    (∑ a : α, if P a then (1 : NNReal) else 0) =
      if ∃ a, P a then 1 else 0 := by
  by_cases hex : ∃ a, P a
  · obtain ⟨a₀, ha₀⟩ := hex
    rw [if_pos ⟨a₀, ha₀⟩, Finset.sum_eq_single a₀]
    · rw [if_pos ha₀]
    · intro b _ hb
      exact if_neg fun hP => hb (huniq b a₀ hP ha₀)
    · intro hmem
      exact absurd (Finset.mem_univ a₀) hmem
  · rw [if_neg hex]
    exact Finset.sum_eq_zero fun a _ => if_neg fun hP => hex ⟨a, hP⟩

/-! ### The won/not-won split of the visible-transcript probability -/

/-- The joint probability that `G` answers the full visible transcript
`(xs, ys)` AND the game is won along the way (`Aq = 1` on a completed
transcript): the mass of game realizations whose **stripped** system outputs
`ys` on `xs` while the **pre-winning** DDS does not (some MBO bit fired). -/
noncomputable def winJointProb (G : PDG X Y) (xs : List X) (ys : List Y) :
    NNReal :=
  G.sum fun g w =>
    if ((DDG.strip g).outputSeq xs = ys.map some ∧
        ¬ ((Def415.preWinningDDS g).outputSeq xs = ys.map some)) then w else 0

omit [DecidableEq (List (Option X))] [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- **Maurer's first step (the event partition)** at the system-side level:
the visible-transcript probability of the stripped game splits as
(pre-winning part) + (won part), per transcript.

  `Pr_G[outputs (xs,ys)] = Pr_G[outputs (xs,ys) ∧ Aq=0] + Pr_G[outputs (xs,ys) ∧ Aq=1]` -/
theorem jointProb_strip_partition (G : PDG X Y) (xs : List X) (ys : List Y) :
    jointProb (PDG.strip G) xs ys =
      jointProb (Def415.preWinningPDS G) xs ys + winJointProb G xs ys := by
  simp only [PDG.strip.eq_fTransform, Def415.preWinningPDS, winJointProb]
  rw [jointProb_fTransform, jointProb_fTransform, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun g _ => ?_
  by_cases hp : (Def415.preWinningDDS g).outputSeq xs = ys.map some
  · have hs := strip_outputSeq_of_preWinning hp
    simp [hp, hs]
  · by_cases hs : (DDG.strip g).outputSeq xs = ys.map some <;> simp [hp, hs]

/-! ### The system-side cancellation (from K2) -/

/-- The oblivious environment that asks the fixed queries `xs` regardless of
the outputs it sees (used to extract the system-side factor from K2). -/
def constAsker (xs : List X) : DDE X Y := fun l =>
  some (xs.getD l.length default)

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited Y] [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- `constAsker xs` asks exactly `xs` on any output history of matching
length. -/
theorem inputSeq_constAsker (xs : List X) (ys : List Y)
    (hlen : xs.length = ys.length) :
    DDE.inputSeq (constAsker (Y := Y) xs) ys = xs.map some := by
  apply List.ext_getElem (by simp [DDE.inputSeq, hlen])
  intro k hk1 hk2
  have hk : k < ys.length := by simpa [DDE.inputSeq] using hk1
  have hkx : k < xs.length := by omega
  simp [DDE.inputSeq, constAsker, List.getElem?_eq_getElem hkx]

omit [DecidableEq (List (Option Y))] [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- The environment factor of a point-mass PDE is the ask indicator. -/
theorem envJointProb_single (e : DDE X Y) (ys : List Y) (xs : List X) :
    envJointProb (Finsupp.single e 1 : PDE X Y) ys xs =
      if DDE.inputSeq e ys = xs.map some then 1 else 0 := by
  simp only [envJointProb, envJointInputDist]
  rw [fTransform_apply_finsupp, Finsupp.sum_single_index (by simp)]

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- **The K2 cancellation, system-side form**: game-equivalent weight-1 games
give the same pre-winning joint probability at every visible transcript.
Extracted from `preWinTranscriptDist_congr_gameEquiv` by playing the
oblivious point-mass environment `constAsker xs`. -/
theorem jointProb_preWinningPDS_congr_gameEquiv {S T : PDG X Y}
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (xs : List X) (ys : List Y) :
    jointProb (Def415.preWinningPDS S) xs ys =
      jointProb (Def415.preWinningPDS T) xs ys := by
  rcases eq_or_ne xs.length ys.length with hlen | hlen
  · have hkey := preWinTranscriptDist_congr_gameEquiv heq hS hT
      (Finsupp.single (constAsker (Y := Y) xs) 1) xs ys
    rw [preWinTranscriptDist_eq, preWinTranscriptDist_eq,
      envJointProb_single, inputSeq_constAsker xs ys hlen, if_pos rfl,
      mul_one, mul_one] at hkey
    exact hkey
  · have hzero : ∀ S' : PDS X Y, jointProb S' xs ys = 0 := by
      intro S'
      rw [jointProb_eq_sum_support]
      refine Finset.sum_eq_zero fun s _ => if_neg fun hc => hlen ?_
      simpa [DDS.outputSeq] using congrArg List.length hc
    rw [hzero, hzero]

/-! ### The transcript-level event probabilities (Maurer's chain, quantified)

`Pr^{DG}(Z=1 ∧ Aq=0)` and `Pr^{DG}(Z=1 ∧ Aq=1)` for a deterministic
distinguisher `(w, Z)` against the game `G`, as `Fintype` sums over the
`q`-round transcript space. -/

/-- **K3 deliverable (the cancellation quantity)**:
`Pr^{DG}(Z=1 ∧ Aq=0) = Σ_{t : Z(t)=1} preWinTranscriptDist G E t` — the
acceptance∧not-won probability is the sum, over accepted visible transcripts,
of the K1 pre-winning transcript distribution. -/
noncomputable def acceptNotWonProb (q : ℕ) (G : PDG X Y) (E : PDE X Y)
    (Z : (Fin q → X) × (Fin q → Y) → Bool) : NNReal :=
  ∑ t : (Fin q → X) × (Fin q → Y),
    if Z t = true then
      preWinTranscriptDist G E (List.ofFn t.1) (List.ofFn t.2)
    else 0

omit [DecidableEq X] [DecidableEq Y] in
/-- **K3 step 1 — THE CANCELLATION (Maurer's second step, eqs 4.35–4.36)**:
under game equivalence, `Pr^{DS}(Z=1 ∧ Aq=0) = Pr^{DT}(Z=1 ∧ Aq=0)` for every
environment and every transcript predicate `Z` — termwise from the K2
invariance `preWinTranscriptDist_congr_gameEquiv`. -/
theorem acceptNotWonProb_congr_gameEquiv {S T : PDG X Y}
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (q : ℕ) (E : PDE X Y) (Z : (Fin q → X) × (Fin q → Y) → Bool) :
    acceptNotWonProb q S E Z = acceptNotWonProb q T E Z :=
  Finset.sum_congr rfl fun t _ => by
    rw [preWinTranscriptDist_congr_gameEquiv heq hS hT]

/-- `Pr^{DG}(Z=1 ∧ Aq=1)` for the deterministic environment `e`: the
acceptance∧won probability — the sum over accepted transcripts of
(won joint probability) × (ask indicator). -/
noncomputable def acceptWonProb (q : ℕ) (G : PDG X Y) (e : DDE X Y)
    (Z : (Fin q → X) × (Fin q → Y) → Bool) : NNReal :=
  ∑ t : (Fin q → X) × (Fin q → Y),
    if Z t = true then
      winJointProb G (List.ofFn t.1) (List.ofFn t.2) *
        (if DDE.inputSeq e (List.ofFn t.2) = (List.ofFn t.1).map some
          then 1 else 0)
    else 0

omit [DecidableEq X] [DecidableEq Y] in
/-- **Maurer's first step (the event partition), acceptance level**: for a
deterministic distinguisher `d = (w, Z)`, the acceptance probability against
the stripped game `G⁻` splits as

  `Pr^{dG⁻}(Z=1) = Pr^{dG}(Z=1 ∧ Aq=0) + Pr^{dG}(Z=1 ∧ Aq=1)`.

The proof expands the acceptance event into the (unique) completed transcript
(`sum_indicator_unique` + `completesAt_unique`), factorizes each transcript
term into (system event) × (ask event), and splits the system event by
`jointProb_strip_partition`. -/
theorem acceptProb_det_strip (q : ℕ) (G : PDG X Y)
    (d : Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) :
    ((PDG.strip G).sum fun s sw =>
        sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) =
      acceptNotWonProb q G (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
        acceptWonProb q G (Strategy.toDDE d.1) d.2 := by
  classical
  -- Step 1: the acceptance indicator as a transcript sum.
  have hκ : ∀ s : DDS X Y,
      (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0) =
        ∑ t : (Fin q → X) × (Fin q → Y),
          if (CompletesAt (Strategy.toDDE d.1) s
              (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
            then (1 : NNReal) else 0 := by
    intro s
    have huniq : ∀ t t' : (Fin q → X) × (Fin q → Y),
        (CompletesAt (Strategy.toDDE d.1) s
          (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) →
        (CompletesAt (Strategy.toDDE d.1) s
          (List.ofFn t'.1) (List.ofFn t'.2) ∧ d.2 t' = true) →
        t = t' := by
      rintro t t' ⟨ht, -⟩ ⟨ht', -⟩
      obtain ⟨hx, hy⟩ := completesAt_unique ht ht' (by simp)
      exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hy)
    rw [sum_indicator_unique _ huniq, distinctionStructure_κ]
    simp only [decide_eq_true_eq]
  -- Step 2: swap the system sum with the transcript sum.
  calc ((PDG.strip G).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
      = ∑ t : (Fin q → X) × (Fin q → Y), (PDG.strip G).sum fun s sw =>
          sw * (if (CompletesAt (Strategy.toDDE d.1) s
              (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
            then (1 : NNReal) else 0) := by
        rw [show ((PDG.strip G).sum fun s sw =>
            sw * (if (distinctionStructure X Y q).κ d s then (1:NNReal) else 0)) =
            (PDG.strip G).sum fun s sw =>
              ∑ t : (Fin q → X) × (Fin q → Y),
                sw * (if (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
                  then (1:NNReal) else 0) from
          Finsupp.sum_congr fun s _ => by rw [hκ s, Finset.mul_sum]]
        simp only [Finsupp.sum]
        exact Finset.sum_comm
    -- Step 3: factor each transcript term into accept × system × ask.
    _ = ∑ t : (Fin q → X) × (Fin q → Y),
          (if d.2 t = true then (1 : NNReal) else 0) *
            jointProb (PDG.strip G) (List.ofFn t.1) (List.ofFn t.2) *
            (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hacc : d.2 t = true
        · by_cases hask : DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
              (List.ofFn t.1).map some
          · rw [if_pos hacc, if_pos hask, one_mul, mul_one,
              jointProb_eq_sum_support]
            simp only [Finsupp.sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases hout : s.outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some
            · rw [if_pos hout,
                if_pos (show (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) from
                  ⟨⟨hout, hask⟩, hacc⟩), mul_one]
            · rw [if_neg hout,
                if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
                  hout hc.1.1), mul_zero]
          · rw [if_neg hask, mul_zero]
            exact Finset.sum_eq_zero fun s _ => by
              dsimp only
              rw [if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                  (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
                hask hc.1.2), mul_zero]
        · rw [if_neg hacc, zero_mul, zero_mul]
          exact Finset.sum_eq_zero fun s _ => by
            dsimp only
            rw [if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
              hacc hc.2), mul_zero]
    -- Step 4: split the system event into pre-winning + won parts.
    _ = ∑ t : (Fin q → X) × (Fin q → Y),
          ((if d.2 t = true then
              preWinTranscriptDist G (Finsupp.single (Strategy.toDDE d.1) 1)
                (List.ofFn t.1) (List.ofFn t.2) else 0) +
            (if d.2 t = true then
              winJointProb G (List.ofFn t.1) (List.ofFn t.2) *
                (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0) else 0)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hacc : d.2 t = true
        · simp only [hacc, if_true]
          rw [jointProb_strip_partition, preWinTranscriptDist_eq,
            envJointProb_single]
          ring
        · simp [hacc]
    _ = _ := by
        rw [Finset.sum_add_distrib]
        rfl

omit [Inhabited X] [DecidableEq X] [DecidableEq Y] in
/-- **Maurer's third and fourth steps**:
`Pr^{DT}(Z=1 ∧ Aq=1) ≤ Pr^{DT}(Aq=1) = T(d.1)` — the acceptance∧won
probability is bounded by the (eq 4.37) winning probability of the
distinguisher's strategy playing `T` as a winner.

`(Z=1 ∧ Aq=1) ⊆ (Aq=1)`: a completed won transcript for `(toDDE w, g)` rules
out (by uniqueness of the completed transcript) any completed transcript of
the pre-winning DDS, i.e. forces the eq-4.37 winning event. -/
theorem acceptWonProb_le_winProb_det (q : ℕ) (G : PDG X Y)
    (w : Strategy X Y q) (Z : (Fin q → X) × (Fin q → Y) → Bool) :
    acceptWonProb q G (Strategy.toDDE w) Z ≤
      G.sum fun g gp =>
        gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0) := by
  classical
  -- Drop the acceptance indicator.
  have h1 : acceptWonProb q G (Strategy.toDDE w) Z ≤
      ∑ t : (Fin q → X) × (Fin q → Y),
        winJointProb G (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0) := by
    refine Finset.sum_le_sum fun t _ => ?_
    split
    · exact le_rfl
    · exact zero_le _
  refine le_trans h1 ?_
  -- Swap to a per-game sum.
  have h2 : (∑ t : (Fin q → X) × (Fin q → Y),
      winJointProb G (List.ofFn t.1) (List.ofFn t.2) *
        (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
            (List.ofFn t.1).map some then 1 else 0)) =
      G.sum fun g gp => ∑ t : (Fin q → X) × (Fin q → Y),
        gp * ((if ((DDG.strip g).outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some ∧
              ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some)) then (1 : NNReal) else 0) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0)) := by
    rw [show (∑ t : (Fin q → X) × (Fin q → Y),
        winJointProb G (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0)) =
        ∑ t : (Fin q → X) × (Fin q → Y), G.sum fun g gp =>
          gp * ((if ((DDG.strip g).outputSeq (List.ofFn t.1) =
                  (List.ofFn t.2).map some ∧
                ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
                  (List.ofFn t.2).map some)) then (1 : NNReal) else 0) *
            (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) from
      Finset.sum_congr rfl fun t _ => by
        simp only [winJointProb]
        rw [Finsupp.sum_mul]
        refine Finsupp.sum_congr fun g _ => ?_
        by_cases hc : ((DDG.strip g).outputSeq (List.ofFn t.1) =
            (List.ofFn t.2).map some ∧
          ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
            (List.ofFn t.2).map some))
        · rw [if_pos hc, if_pos hc, one_mul]
        · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]]
    simp only [Finsupp.sum]
    exact Finset.sum_comm
  rw [h2]
  -- Per-game: the completed-won transcript count is at most the eq-4.37
  -- winning indicator.
  refine Finsupp.sum_le_sum fun g _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  by_cases hex : ∃ t : (Fin q → X) × (Fin q → Y),
      CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
        (List.ofFn t.1) (List.ofFn t.2)
  · -- The pre-winning DDS completes: the game is NOT won (eq 4.37), and no
    -- completed transcript can be a won one (uniqueness).
    have hwin : ¬ ((gameStructure X Y q).win w g = true) := by
      rw [gameStructure_win]
      simp only [decide_eq_true_eq]
      exact fun hc => hc hex
    rw [if_neg hwin]
    refine le_of_eq (Finset.sum_eq_zero fun t _ => ?_)
    obtain ⟨t', ht'⟩ := hex
    by_cases hc : ((DDG.strip g).outputSeq (List.ofFn t.1) =
        (List.ofFn t.2).map some ∧
      ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
        (List.ofFn t.2).map some))
    · by_cases hask : DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
          (List.ofFn t.1).map some
      · exfalso
        have hcs : CompletesAt (Strategy.toDDE w) (DDG.strip g)
            (List.ofFn t.1) (List.ofFn t.2) := ⟨hc.1, hask⟩
        have hcs' : CompletesAt (Strategy.toDDE w) (DDG.strip g)
            (List.ofFn t'.1) (List.ofFn t'.2) :=
          completesAt_strip_of_preWinning ht'
        obtain ⟨hx, hy⟩ := completesAt_unique hcs hcs' (by simp)
        exact hc.2 (by rw [hx, hy]; exact ht'.1)
      · rw [if_neg hask, mul_zero]
    · rw [if_neg hc, zero_mul]
  · -- No pre-winning completion: the game IS won (eq 4.37); the completed
    -- transcript (if any) is unique, so the sum is at most 1.
    have hwin : (gameStructure X Y q).win w g = true := by
      rw [gameStructure_win]
      simp only [decide_eq_true_eq]
      exact hex
    rw [if_pos hwin]
    calc (∑ t : (Fin q → X) × (Fin q → Y),
            (if ((DDG.strip g).outputSeq (List.ofFn t.1) =
                  (List.ofFn t.2).map some ∧
                ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
                  (List.ofFn t.2).map some)) then (1 : NNReal) else 0) *
              (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0))
        ≤ ∑ t : (Fin q → X) × (Fin q → Y),
            (if CompletesAt (Strategy.toDDE w) (DDG.strip g)
                (List.ofFn t.1) (List.ofFn t.2) then (1 : NNReal) else 0) := by
          refine Finset.sum_le_sum fun t _ => ?_
          by_cases h1 : ((DDG.strip g).outputSeq (List.ofFn t.1) =
              (List.ofFn t.2).map some ∧
            ¬ ((Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
              (List.ofFn t.2).map some))
          · by_cases h2 : DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some
            · rw [if_pos h1, if_pos h2, one_mul]
              split
              · exact le_rfl
              · next hno => exact absurd ⟨h1.1, h2⟩ hno
            · rw [if_neg h2, mul_zero]
              exact zero_le _
          · rw [if_neg h1, zero_mul]
            exact zero_le _
      _ ≤ 1 := by
          rw [sum_indicator_unique]
          · split <;> simp
          · intro t t' ht ht'
            obtain ⟨hx, hy⟩ := completesAt_unique ht ht' (by simp)
            exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hy)

omit [DecidableEq X] [DecidableEq Y] in
/-- **CR18 Lemma 4.15, concrete form (Maurer's fifth step `T(D) = S(D)`)**:
game-equivalent weight-1 games are won with the same probability by every
probabilistic winner — for the concrete eq-4.37 winning predicate.

Proof: per deterministic winner `w`, eq (4.37) gives
`Σ_g G(g)·[win w g] + Σ_t Pr_G[pre-winning transcript t against w] = |G| = 1`
(the transcript sum collapses to the `Aq=0` indicator by uniqueness), and the
transcript sum is invariant under game equivalence (the K2 cancellation). -/
theorem winProb_congr_gameEquiv (q : ℕ) {S T : PDG X Y}
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (W : Dist (Strategy X Y q)) :
    (gameStructure X Y q).winProb W S = (gameStructure X Y q).winProb W T := by
  classical
  rw [Def45.GameStructure.winProb, Def45.GameStructure.winProb]
  refine Finsupp.sum_congr fun w _ => ?_
  -- The complementary `Aq=0` probability, as a transcript sum.
  have hpre : ∀ (G : PDG X Y),
      (G.sum fun g gp => gp *
        (if (∃ t : (Fin q → X) × (Fin q → Y),
            CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
              (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0)) =
      ∑ t : (Fin q → X) × (Fin q → Y),
        jointProb (Def415.preWinningPDS G) (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0) := by
    intro G
    have hstep : ∀ (g : DDG X Y) (gp : NNReal),
        gp * (if (∃ t : (Fin q → X) × (Fin q → Y),
            CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
              (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0) =
        ∑ t : (Fin q → X) × (Fin q → Y),
          gp * ((if (Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
              (List.ofFn t.2).map some then (1 : NNReal) else 0) *
            (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) := by
      intro g gp
      rw [← sum_indicator_unique
        (fun t : (Fin q → X) × (Fin q → Y) =>
          CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
            (List.ofFn t.1) (List.ofFn t.2))
        (fun t t' ht ht' => by
          obtain ⟨hx, hy⟩ := completesAt_unique ht ht' (by simp)
          exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hy)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : (Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
          (List.ofFn t.2).map some
      · by_cases h2 : DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
            (List.ofFn t.1).map some
        · rw [if_pos h1, if_pos h2]
          split
          · rw [one_mul]
          · next hno => exact absurd ⟨h1, h2⟩ hno
        · rw [if_neg h2]
          split
          · next hyes => exact absurd hyes.2 h2
          · simp
      · rw [if_neg h1]
        split
        · next hyes => exact absurd hyes.1 h1
        · simp
    calc (G.sum fun g gp => gp * (if (∃ t : (Fin q → X) × (Fin q → Y),
            CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
              (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0))
        = G.sum fun g gp => ∑ t : (Fin q → X) × (Fin q → Y),
            gp * ((if (Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some then (1 : NNReal) else 0) *
              (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0)) :=
          Finsupp.sum_congr fun g _ => hstep g (G g)
      _ = ∑ t : (Fin q → X) × (Fin q → Y), G.sum fun g gp =>
            gp * ((if (Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some then (1 : NNReal) else 0) *
              (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0)) := by
          simp only [Finsupp.sum]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [Def415.preWinningPDS]
          rw [jointProb_fTransform, Finsupp.sum_mul]
          refine Finsupp.sum_congr fun g _ => ?_
          by_cases h1 : (Def415.preWinningDDS g).outputSeq (List.ofFn t.1) =
              (List.ofFn t.2).map some
          · rw [if_pos h1, if_pos h1, one_mul]
          · rw [if_neg h1, if_neg h1, zero_mul, mul_zero]
  -- eq (4.37): winning + not-winning masses add to the total mass.
  have hsplit : ∀ (G : PDG X Y), G.sum (fun _ p => p) = 1 →
      (G.sum fun g gp => W w * gp *
          (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) +
        W w * (∑ t : (Fin q → X) × (Fin q → Y),
          jointProb (Def415.preWinningPDS G) (List.ofFn t.1) (List.ofFn t.2) *
            (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) = W w := by
    intro G hG
    rw [← hpre G, Finsupp.mul_sum, ← Finsupp.sum_add]
    have hone : ∀ g : DDG X Y,
        (if (gameStructure X Y q).win w g then (1 : NNReal) else 0) +
          (if (∃ t : (Fin q → X) × (Fin q → Y),
              CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
                (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0) = 1 := by
      intro g
      rw [gameStructure_win]
      simp only [decide_eq_true_eq]
      by_cases hex : ∃ t : (Fin q → X) × (Fin q → Y),
          CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
            (List.ofFn t.1) (List.ofFn t.2)
      · rw [if_neg (not_not_intro hex), if_pos hex, zero_add]
      · rw [if_pos hex, if_neg hex, add_zero]
    calc (G.sum fun g gp => W w * gp *
            (if (gameStructure X Y q).win w g then (1 : NNReal) else 0) +
          W w * (gp * (if (∃ t : (Fin q → X) × (Fin q → Y),
              CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
                (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0)))
        = G.sum fun g gp => W w * gp := by
          refine Finsupp.sum_congr fun g _ => ?_
          rw [show ∀ a b c d : NNReal, a * b * c + a * (b * d) = a * b * (c + d)
            from fun a b c d => by ring, hone g, mul_one]
      _ = W w * G.sum fun _ p => p := by
          rw [Finsupp.mul_sum]
      _ = W w := by rw [hG, mul_one]
  -- Conclude: the winning masses agree (additive cancellation against the
  -- gameEquiv-invariant `Aq=0` transcript sum).
  have hSsplit := hsplit S hS
  have hTsplit := hsplit T hT
  have hinv : (∑ t : (Fin q → X) × (Fin q → Y),
      jointProb (Def415.preWinningPDS S) (List.ofFn t.1) (List.ofFn t.2) *
        (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
            (List.ofFn t.1).map some then 1 else 0)) =
      ∑ t : (Fin q → X) × (Fin q → Y),
        jointProb (Def415.preWinningPDS T) (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0) :=
    Finset.sum_congr rfl fun t _ => by
      rw [jointProb_preWinningPDS_congr_gameEquiv heq hS hT]
  rw [hinv] at hSsplit
  exact add_right_cancel (hSsplit.trans hTsplit.symm)

/-! ### The concrete Lemma 4.16 (hBridge ELIMINATED) -/

/-- **CR18 Lemma 4.16, concrete per-distinguisher core (Maurer's full chain
through `S(D)`)**: if `S ≡_g T` then for every probabilistic `q`-query
distinguisher `D`,

  `⟨S⁻ | T⁻⟩(D) ≤ S(D)`

where the right-hand side is the Definition-4.5 winning probability of `D`'s
querying strategy (the marginal `Dist.fTransform Prod.fst D`) playing `S` as
a winner of the concrete `gameStructure`.

NO bridge hypothesis: the cancellation
`Pr^{DS}(Z=1∧Aq=0) = Pr^{DT}(Z=1∧Aq=0)` is PROVEN internally
(`acceptNotWonProb_congr_gameEquiv`, from K1/K2), as are the partition,
the `≤ Pr^{DT}(Aq=1)` step and the Lemma 4.15 transfer `T(D) = S(D)`. -/
theorem advantage_le_winProb (q : ℕ) (S T : PDG X Y)
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher) :
    (distinctionStructure X Y q).performance (PDG.strip S, PDG.strip T) D ≤
      ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S : Real) := by
  classical
  -- (0) Performance as a difference of NNReal acceptance probabilities.
  have hcast : ∀ G' : PDS X Y,
      (D.sum fun d dw => G'.sum fun s sw =>
          (dw : Real) * (sw : Real) *
            if (distinctionStructure X Y q).κ d s then 1 else 0) =
      ((D.sum fun d dw => dw * (G'.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    intro G'
    simp only [Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (distinctionStructure X Y q).κ d s
    · simp [h]
    · simp [h]
  have hperf : (distinctionStructure X Y q).performance
      (PDG.strip S, PDG.strip T) D =
      ((D.sum fun d dw => dw * ((PDG.strip T).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) -
      ((D.sum fun d dw => dw * ((PDG.strip S).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    rw [Def47.DistinctionStructure.performance, ← hcast, ← hcast]
    rfl
  -- (1) Acceptance partition (Maurer step 1) under each deterministic d,
  --     mixed over D.
  have hsplitmix : ∀ G : PDG X Y,
      (D.sum fun d dw => dw * ((PDG.strip G).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))) =
      (D.sum fun d dw => dw *
          acceptNotWonProb q G (Finsupp.single (Strategy.toDDE d.1) 1) d.2) +
        (D.sum fun d dw => dw * acceptWonProb q G (Strategy.toDDE d.1) d.2) := by
    intro G
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [acceptProb_det_strip q G d, mul_add]
  -- (2) THE CANCELLATION (Maurer step 2, proven internally from K1/K2).
  have hcancel : (D.sum fun d dw => dw *
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2) =
      (D.sum fun d dw => dw *
        acceptNotWonProb q T (Finsupp.single (Strategy.toDDE d.1) 1) d.2) :=
    Finsupp.sum_congr fun d _ => by
      rw [acceptNotWonProb_congr_gameEquiv heq hS hT]
  -- (3) Bound the won part by the winning probability (Maurer steps 3–4).
  have hwon : (D.sum fun d dw => dw * acceptWonProb q T (Strategy.toDDE d.1) d.2)
      ≤ (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) T := by
    have hshape : (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) T =
        (Dist.fTransform Prod.fst D).sum fun w wp =>
          wp * (T.sum fun g gp =>
            gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) := by
      rw [Def45.GameStructure.winProb]
      refine Finsupp.sum_congr fun w _ => ?_
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun g _ => by ring
    rw [hshape, fTransform_sum_mul_finsupp]
    exact Finsupp.sum_le_sum fun d _ =>
      mul_le_mul_right (acceptWonProb_le_winProb_det q T d.1 d.2) _
  -- (4) Lemma 4.15 transfer (Maurer step 5): T(D) = S(D).
  have htransfer : (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) T =
      (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S :=
    (winProb_congr_gameEquiv q heq hS hT _).symm
  -- Assemble Maurer's chain.
  rw [hperf, hsplitmix T, hsplitmix S, hcancel]
  set P := (D.sum fun d dw => dw *
    acceptNotWonProb q T (Finsupp.single (Strategy.toDDE d.1) 1) d.2)
  set WT := (D.sum fun d dw => dw * acceptWonProb q T (Strategy.toDDE d.1) d.2)
  set WS := (D.sum fun d dw => dw * acceptWonProb q S (Strategy.toDDE d.1) d.2)
  calc ((P + WT : NNReal) : Real) - ((P + WS : NNReal) : Real)
      = (WT : Real) - (WS : Real) := by push_cast; ring
    _ ≤ (WT : Real) := sub_le_self _ (by positivity)
    _ ≤ ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) T : Real) := by
        exact_mod_cast hwon
    _ = ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S : Real) := by
        exact_mod_cast htransfer

/-- **CR18 Lemma 4.16 (concrete form, hBridge eliminated)**: if `S ≡_g T`,
then for every probabilistic `q`-query distinguisher `D` (a probability
distribution over deterministic strategy/decision pairs),

  `⟨S⁻ | T⁻⟩(D) ≤ Γ(S)`

— the distinguishing advantage of `D` for the stripped pair is bounded by the
maximal winning probability `Def417.maxWinProb` of the concrete game
structure.  Hypotheses are exactly Maurer's: game equivalence and the
weight-1 (probability-distribution) conditions on `S`, `T`, `D`.

**CR18 reference:** Lemma 4.16 (source ~5508–5563), assembled from the
printed chain; the former `hBridge` hypothesis is GONE — its content is
`acceptNotWonProb_congr_gameEquiv` + `acceptProb_det_strip` +
`acceptWonProb_le_winProb_det` + `winProb_congr_gameEquiv`. -/
theorem advantage_le_maxWinProb (q : ℕ) (S T : PDG X Y)
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (distinctionStructure X Y q).performance (PDG.strip S, PDG.strip T) D ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) := by
  refine le_trans (advantage_le_winProb q S T heq hS hT D) ?_
  have hW : (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).isProbDist := by
    show (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).weight = 1
    rw [Dist.weight_fTransform]
    exact hD
  exact_mod_cast Def417.winProb_le_maxWinProb (gameStructure X Y q) S hS _ hW

/-- **CR18 Lemma 4.16 (PDG/strip concrete form)** — same statement as
`advantage_le_maxWinProb`, kept under the historical `_pdg` name (the
checklist row references both names).  `hBridge`-free. -/
theorem advantage_le_maxWinProb_pdg (q : ℕ) (S T : PDG X Y)
    (heq : Def416.GameEquiv S T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (distinctionStructure X Y q).performance (PDG.strip S, PDG.strip T) D ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) :=
  advantage_le_maxWinProb q S T heq hS hT D hD

end Lem416

end RandomSystems.CR18

/-!
## Interaction toolbox — entry views, the interaction path, eq-4.37 masses

Shared deterministic/equational infrastructure for the Def 4.20 blinding
argument (CR18 §4.11.2) and the one-sided fundamental lemma (Thm 4.17′):

* **entry views** of the two `CompletesAt` components (`outputSeq_entry_*`,
  `inputSeq_entry`) and their converse builders — the round-by-round reading
  of the equational transcript events;
* **the interaction path** `pathList w t`: the query list that a total
  `q`-query strategy `w` traces against a system `t`.  This is the only piece
  of data the blinding argument needs: the path depends on `(w, t)` ONLY, so
  the winner that a distinguisher induces against the independent enhancement
  `T̂ = T̃bŜ` (Def 4.21 / eq 4.40) commits to its queries without ever seeing
  `Ŝ` — it is a BLIND winner of `bŜ`;
* **eq-4.37 mass identities** for an arbitrary `PDS` (acceptance expansion,
  completion mass, win/pre-win complement), generalizing the corresponding
  in-proof steps of the Lemma 4.16 assembly.

This block reopens `Lem416` with a fresh (minimal) variable scope.
-/

namespace RandomSystems.CR18

namespace Lem416

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Entry-level views of `outputSeq` / `inputSeq` equalities -/

/-- Lengths agree across `s.outputSeq xs = ys.map some`. -/
theorem length_eq_of_outputSeq {s : DDS X Y} {xs : List X} {ys : List Y}
    (h : s.outputSeq xs = ys.map some) : xs.length = ys.length := by
  simpa [DDS.outputSeq] using congrArg List.length h

/-- Entry view of `s.outputSeq xs = ys.map some`, domain part: every nonempty
prefix of `xs` is answered by `s`. -/
theorem outputSeq_entry_dom {s : DDS X Y} {xs : List X} {ys : List Y}
    (h : s.outputSeq xs = ys.map some) {k : ℕ} (hk : k < xs.length) :
    xs.take (k + 1) ∈ s.dom := by
  have hsrc := List.getElem_of_eq h (i := k) (by simpa [DDS.outputSeq] using hk)
  simp only [DDS.outputSeq, List.getElem_map, List.getElem_finRange,
    Fin.val_cast] at hsrc
  by_cases hd : xs.take (k + 1) ∈ s.dom
  · exact hd
  · rw [dif_neg hd] at hsrc
    exact absurd hsrc (by simp)

/-- Entry view of `s.outputSeq xs = ys.map some`, value part: the round-`k+1`
response is the `k`-th entry of `ys`. -/
theorem outputSeq_entry_respond {s : DDS X Y} {xs : List X} {ys : List Y}
    (h : s.outputSeq xs = ys.map some) {k : ℕ} (hk : k < xs.length)
    (hd : xs.take (k + 1) ∈ s.dom) :
    s.respond (xs.take (k + 1)) hd = ys[k]'(length_eq_of_outputSeq h ▸ hk) := by
  have hsrc := List.getElem_of_eq h (i := k) (by simpa [DDS.outputSeq] using hk)
  simp only [DDS.outputSeq, List.getElem_map, List.getElem_finRange,
    Fin.val_cast] at hsrc
  rw [dif_pos hd] at hsrc
  exact Option.some.inj hsrc

/-- Converse builder for `s.outputSeq xs = ys.map some` from the entry data. -/
theorem outputSeq_eq_map_some {s : DDS X Y} {xs : List X} {ys : List Y}
    (hlen : xs.length = ys.length)
    (hdom : ∀ k, k < xs.length → xs.take (k + 1) ∈ s.dom)
    (hval : ∀ (k : ℕ) (hk : k < xs.length),
      s.respond (xs.take (k + 1)) (hdom k hk) = ys[k]'(hlen ▸ hk)) :
    s.outputSeq xs = ys.map some := by
  apply List.ext_getElem (by simpa [DDS.outputSeq] using hlen)
  intro k hk1 hk2
  have hk : k < xs.length := by simpa [DDS.outputSeq] using hk1
  simp only [DDS.outputSeq, List.getElem_map, List.getElem_finRange,
    Fin.val_cast]
  rw [dif_pos (hdom k hk), hval k hk]

/-- Lengths agree across `DDE.inputSeq e ys = xs.map some`. -/
theorem length_eq_of_inputSeq {e : DDE X Y} {xs : List X} {ys : List Y}
    (h : DDE.inputSeq e ys = xs.map some) : ys.length = xs.length := by
  simpa [DDE.inputSeq] using congrArg List.length h

/-- Entry view of `DDE.inputSeq e ys = xs.map some`: at every round the
environment asks the corresponding entry of `xs`. -/
theorem inputSeq_entry {e : DDE X Y} {xs : List X} {ys : List Y}
    (h : DDE.inputSeq e ys = xs.map some) {k : ℕ} (hk : k < ys.length) :
    e ((ys.take k).map some) = some (xs[k]'(length_eq_of_inputSeq h ▸ hk)) := by
  have hsrc := List.getElem_of_eq h (i := k) (by simpa [DDE.inputSeq] using hk)
  simpa [DDE.inputSeq] using hsrc

/-- Converse builder for `DDE.inputSeq e ys = xs.map some` from entry data. -/
theorem inputSeq_eq_map_some {e : DDE X Y} {xs : List X} {ys : List Y}
    (hlen : ys.length = xs.length)
    (hval : ∀ (k : ℕ) (hk : k < ys.length),
      e ((ys.take k).map some) = some (xs[k]'(hlen ▸ hk))) :
    DDE.inputSeq e ys = xs.map some := by
  apply List.ext_getElem (by simpa [DDE.inputSeq] using hlen)
  intro k hk1 hk2
  have hk : k < ys.length := by simpa [DDE.inputSeq] using hk1
  simp only [DDE.inputSeq, List.getElem_map, List.getElem_finRange,
    Fin.val_cast]
  exact hval k hk

/-! ### Evaluating `Strategy.toDDE` -/

/-- `Strategy.toDDE` unfolded (definitional). -/
theorem toDDE_apply [Inhabited Y] {q : ℕ} (w : Strategy X Y q)
    (l : List (Option Y)) :
    Strategy.toDDE w l = if h : l.length < q then
      some (w ⟨l.length, h⟩ fun i => (l[(i : ℕ)]'i.isLt).getD default)
    else none := rfl

/-- `Strategy.toDDE` on a history of known length `k < q`. -/
theorem toDDE_apply_len [Inhabited Y] {q : ℕ} (w : Strategy X Y q)
    {l : List (Option Y)} {k : ℕ} (hl : l.length = k) (hk : k < q) :
    Strategy.toDDE w l = some (w ⟨k, hk⟩ fun i : Fin k =>
      (l[(i : ℕ)]'(by omega)).getD default) := by
  subst hl
  exact dif_pos hk

/-! ### The interaction path `pathList` -/

section Path

variable [Inhabited Y]

open scoped Classical in
/-- The default-padded response of `t` to round `i+1` along the query list
`l`: the genuine response when the prefix is answered, `default` otherwise
(the padding value is immaterial — see `pathList`). -/
noncomputable def respPad (t : DDS X Y) (l : List X) (i : ℕ) : Y :=
  if h : l.take (i + 1) ∈ t.dom then t.respond (l.take (i + 1)) h else default

/-- **The interaction path** (CR18 §4.11.2, the winner `DT̃` of eq 4.40): the
query list that the total `q`-query strategy `w` traces against the system
`t` over the first `k` rounds.  Round `j+1` asks `w`'s round-`j` query on
`t`'s (default-padded) answers to the previous rounds.

If `t` aborts (a prefix leaves `t.dom`), the remaining entries are computed
from padded answers; this is immaterial because the aborting prefix already
left every relevant domain (prefix-closure), so any extension wins the
blinded game — see `win_enhanceDDG_eq_win_blind`. -/
noncomputable def pathList {q : ℕ} (w : Strategy X Y q) (t : DDS X Y) :
    ℕ → List X
  | 0 => []
  | k + 1 =>
    pathList w t k ++
      (if h : k < q then
        [w ⟨k, h⟩ fun i => respPad t (pathList w t k) i.val]
      else [])

/-- Unfolding lemma for `pathList` at a successor round. -/
theorem pathList_succ {q : ℕ} (w : Strategy X Y q) (t : DDS X Y) (k : ℕ) :
    pathList w t (k + 1) =
      pathList w t k ++
        (if h : k < q then
          [w ⟨k, h⟩ fun i => respPad t (pathList w t k) i.val]
        else []) := by
  rw [pathList]

/-- The path after `k` rounds has length `min k q` (the strategy stops asking
after `q` rounds). -/
theorem pathList_length {q : ℕ} (w : Strategy X Y q) (t : DDS X Y) (k : ℕ) :
    (pathList w t k).length = min k q := by
  induction k with
  | zero => simp [pathList]
  | succ k ih =>
    rw [pathList_succ]
    by_cases h : k < q <;> simp [h, ih] <;> omega

/-- Truncating the path replays the shorter interaction: the interaction is
history-deterministic. -/
theorem pathList_take {q : ℕ} (w : Strategy X Y q) (t : DDS X Y)
    {j k : ℕ} (hjk : j ≤ k) :
    (pathList w t k).take j = pathList w t j := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.mp hjk
    simp [pathList]
  | succ k ih =>
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · exact List.take_of_length_le (by rw [pathList_length]; omega)
    · have hj : j ≤ k := by omega
      rw [pathList_succ]
      by_cases hq : k < q
      · rw [List.take_append_of_le_length (by rw [pathList_length]; omega)]
        exact ih hj
      · rw [dif_neg hq, List.append_nil]
        exact ih hj

/-- Entry view of the `q`-round path: round `k+1` asks `w`'s round-`k` query
on the padded answers along the round-`k` path. -/
theorem pathList_getElem {q : ℕ} (w : Strategy X Y q) (t : DDS X Y)
    {k : ℕ} (hk : k < q) (hk' : k < (pathList w t q).length) :
    (pathList w t q)[k] =
      w ⟨k, hk⟩ (fun i => respPad t (pathList w t k) i.val) := by
  have hlenk : (pathList w t k).length = k := by
    rw [pathList_length]; omega
  have h4 : (pathList w t q)[k]? =
      some (w ⟨k, hk⟩ fun i => respPad t (pathList w t k) i.val) := by
    rw [← List.getElem?_take_of_succ (l := pathList w t q) (i := k),
      pathList_take w t (by omega : k + 1 ≤ q), pathList_succ, dif_pos hk,
      List.getElem?_append_right (by omega), hlenk]
    simp
  rw [List.getElem?_eq_getElem hk'] at h4
  exact Option.some.inj h4

/-- **The genuine-interaction lemma**: if `t` answers every round of the
`q`-round interaction path with values `ys`, then `w` asks exactly the path
on `ys` — `(pathList w t q, ys)` is the completed transcript of `w ↔ t`. -/
theorem inputSeq_toDDE_pathList {q : ℕ} (w : Strategy X Y q) (t : DDS X Y)
    {ys : List Y} (hout : t.outputSeq (pathList w t q) = ys.map some) :
    DDE.inputSeq (Strategy.toDDE w) ys = (pathList w t q).map some := by
  have hlenp : (pathList w t q).length = q := by rw [pathList_length]; omega
  have hlen : ys.length = (pathList w t q).length :=
    (length_eq_of_outputSeq hout).symm
  apply inputSeq_eq_map_some hlen
  intro k hk
  have hkq : k < q := by omega
  rw [toDDE_apply_len w (l := (ys.take k).map some)
    (by simp only [List.length_map, List.length_take]; omega) hkq]
  rw [pathList_getElem w t hkq (by omega)]
  congr 2
  funext i
  have hiq : (i : ℕ) < q := by omega
  have hilen : (i : ℕ) < (pathList w t q).length := by omega
  -- LHS: the `i`-th answer recorded in `ys`.
  have hlhs : (((ys.take k).map some)[(i : ℕ)]'(by
      simp only [List.length_map, List.length_take]; omega)).getD default =
      ys[(i : ℕ)]'(by omega) := by
    simp [List.getElem_take]
  -- RHS: the padded response along the round-`k` path.
  have hPk : (pathList w t k).take ((i : ℕ) + 1) =
      (pathList w t q).take ((i : ℕ) + 1) := by
    rw [← pathList_take w t hkq.le, List.take_take]
    congr 1
    omega
  have hdt : (pathList w t q).take ((i : ℕ) + 1) ∈ t.dom :=
    outputSeq_entry_dom hout hilen
  have hrhs : respPad t (pathList w t k) (i : ℕ) = ys[(i : ℕ)]'(by omega) := by
    rw [respPad, hPk, dif_pos hdt]
    exact outputSeq_entry_respond hout hilen hdt
  rw [hlhs, hrhs]

/-- **Uniqueness of the completed transcript against a refinement**: a
completed `q`-round transcript of `w` against any refinement `s` of `t`
(sub-domain, same responses — e.g. the pre-winning DDS of an enhancement of
`t`) traces exactly the interaction path of `w` against `t`. -/
theorem completesAt_eq_pathList {q : ℕ} {w : Strategy X Y q} {t s : DDS X Y}
    (hsub : ∀ (l : List X) (hl : l ∈ s.dom),
      ∃ hlt : l ∈ t.dom, s.respond l hl = t.respond l hlt)
    {xs : List X} {ys : List Y}
    (h : CompletesAt (Strategy.toDDE w) s xs ys) (hlen : xs.length = q) :
    xs = pathList w t q := by
  have hxy : xs.length = ys.length := h.length_eq
  have key : ∀ j, j ≤ q → xs.take j = pathList w t j := by
    intro j
    induction j with
    | zero => intro _; simp [pathList]
    | succ j ih =>
      intro hj1
      have hjq : j < q := by omega
      have ihj := ih (by omega)
      have hxj : j < xs.length := by omega
      rw [pathList_succ, dif_pos hjq, List.take_add_one,
        List.getElem?_eq_getElem hxj, ihj]
      congr 1
      have hask := inputSeq_entry h.2 (k := j) (by omega)
      rw [toDDE_apply_len w (l := (ys.take j).map some)
        (by simp only [List.length_map, List.length_take]; omega) hjq] at hask
      have hxj_eq := Option.some.inj hask
      simp only [Option.toList_some]
      congr 1
      rw [← hxj_eq]
      congr 1
      funext i
      have hix : (i : ℕ) < xs.length := by omega
      have hds : xs.take ((i : ℕ) + 1) ∈ s.dom :=
        outputSeq_entry_dom h.1 hix
      obtain ⟨hdt, hresp⟩ := hsub _ hds
      have hPj : (pathList w t j).take ((i : ℕ) + 1) =
          xs.take ((i : ℕ) + 1) := by
        rw [← ihj, List.take_take]
        congr 1
        omega
      have hlhs : (((ys.take j).map some)[(i : ℕ)]'(by
          simp only [List.length_map, List.length_take]; omega)).getD default =
          ys[(i : ℕ)]'(by omega) := by
        simp [List.getElem_take]
      have hrhs : respPad t (pathList w t j) (i : ℕ) =
          ys[(i : ℕ)]'(by omega) := by
        rw [respPad, hPj, dif_pos hdt, ← hresp]
        exact outputSeq_entry_respond h.1 hix hds
      rw [hlhs, hrhs]
  have hq := key q le_rfl
  rwa [List.take_of_length_le (le_of_eq hlen)] at hq

/-! ### Path congruence under refinement, and the completion criterion

The blind-winner argument (CR18 §4.11.2, Def 4.20) reduces winning-event
equivalences to two facts about the interaction path: (i) the path against a
REFINEMENT `s` of `t` (sub-domain, same responses — e.g. a pre-winning DDS)
agrees with the path against `t` as long as it stays in `s`'s domain, and
(ii) a `q`-query strategy completes a `q`-round transcript against `s` iff
every round of its interaction path lies in `s.dom`.  Both are pure
`pathList` inductions — no operational driver. -/

omit [Inhabited Y] in
/-- `List.ofFn` of the entries of a length-`q` list is the list itself. -/
theorem ofFn_getElem_of_length {α : Type*} {l : List α} {q : ℕ}
    (h : l.length = q) :
    List.ofFn (fun k : Fin q => l[(k : ℕ)]'(by have := k.isLt; omega)) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp

/-- Path congruence against a refinement (`s` ⊑ `t`: smaller domain, same
responses), given that the `s`-side path stays inside `s.dom`. -/
theorem pathList_congr_refine_left {q : ℕ} {w : Strategy X Y q} {s t : DDS X Y}
    (hsub : ∀ (l : List X) (hl : l ∈ s.dom),
      ∃ hlt : l ∈ t.dom, s.respond l hl = t.respond l hlt)
    (hdom : ∀ j, j < q → pathList w s (j + 1) ∈ s.dom) :
    ∀ k, k ≤ q → pathList w s k = pathList w t k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk1
    have hkq : k < q := by omega
    have ihk := ih (by omega)
    have hquery : (w ⟨k, hkq⟩ fun i => respPad s (pathList w s k) i.val) =
        (w ⟨k, hkq⟩ fun i => respPad t (pathList w t k) i.val) := by
      congr 1
      funext i
      have hi1 : (i : ℕ) + 1 ≤ k := i.isLt
      have htake_s : (pathList w s k).take ((i : ℕ) + 1) =
          pathList w s ((i : ℕ) + 1) := pathList_take w s hi1
      have hmem_s : pathList w s ((i : ℕ) + 1) ∈ s.dom :=
        hdom (i : ℕ) (by omega)
      obtain ⟨hmem_t, hresp⟩ := hsub _ hmem_s
      have hmem_s' : (pathList w s k).take ((i : ℕ) + 1) ∈ s.dom :=
        htake_s ▸ hmem_s
      have htake_t : (pathList w t k).take ((i : ℕ) + 1) =
          pathList w s ((i : ℕ) + 1) := by
        rw [← ihk]; exact htake_s
      have hmem_t' : (pathList w t k).take ((i : ℕ) + 1) ∈ t.dom :=
        htake_t ▸ hmem_t
      rw [respPad, respPad, dif_pos hmem_s', dif_pos hmem_t']
      calc s.respond ((pathList w s k).take ((i : ℕ) + 1)) hmem_s'
          = s.respond (pathList w s ((i : ℕ) + 1)) hmem_s :=
            s.respond_congr htake_s _ _
        _ = t.respond (pathList w s ((i : ℕ) + 1)) hmem_t := hresp
        _ = t.respond ((pathList w t k).take ((i : ℕ) + 1)) hmem_t' :=
            t.respond_congr htake_t.symm _ _
    rw [pathList_succ, pathList_succ, dif_pos hkq, dif_pos hkq, hquery, ihk]

/-- Path congruence against a refinement, given that the `t`-side path stays
inside `s.dom` (the converse-membership variant of
`pathList_congr_refine_left`). -/
theorem pathList_congr_refine_right {q : ℕ} {w : Strategy X Y q} {s t : DDS X Y}
    (hsub : ∀ (l : List X) (hl : l ∈ s.dom),
      ∃ hlt : l ∈ t.dom, s.respond l hl = t.respond l hlt)
    (hdom : ∀ j, j < q → pathList w t (j + 1) ∈ s.dom) :
    ∀ k, k ≤ q → pathList w s k = pathList w t k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk1
    have hkq : k < q := by omega
    have ihk := ih (by omega)
    have hquery : (w ⟨k, hkq⟩ fun i => respPad s (pathList w s k) i.val) =
        (w ⟨k, hkq⟩ fun i => respPad t (pathList w t k) i.val) := by
      congr 1
      funext i
      have hi1 : (i : ℕ) + 1 ≤ k := i.isLt
      have htake_t : (pathList w t k).take ((i : ℕ) + 1) =
          pathList w t ((i : ℕ) + 1) := pathList_take w t hi1
      have hmem_s : pathList w t ((i : ℕ) + 1) ∈ s.dom :=
        hdom (i : ℕ) (by omega)
      obtain ⟨hmem_t, hresp⟩ := hsub _ hmem_s
      have htake_s : (pathList w s k).take ((i : ℕ) + 1) =
          pathList w t ((i : ℕ) + 1) := by
        rw [ihk]; exact htake_t
      have hmem_s' : (pathList w s k).take ((i : ℕ) + 1) ∈ s.dom :=
        htake_s ▸ hmem_s
      have hmem_t' : (pathList w t k).take ((i : ℕ) + 1) ∈ t.dom :=
        htake_t ▸ hmem_t
      rw [respPad, respPad, dif_pos hmem_s', dif_pos hmem_t']
      calc s.respond ((pathList w s k).take ((i : ℕ) + 1)) hmem_s'
          = s.respond (pathList w t ((i : ℕ) + 1)) hmem_s :=
            s.respond_congr htake_s _ _
        _ = t.respond (pathList w t ((i : ℕ) + 1)) hmem_t := hresp
        _ = t.respond ((pathList w t k).take ((i : ℕ) + 1)) hmem_t' :=
            t.respond_congr htake_t.symm _ _
    rw [pathList_succ, pathList_succ, dif_pos hkq, dif_pos hkq, hquery, ihk]

/-- **The completion criterion**: a total `q`-query strategy completes a
`q`-round transcript against `s` iff every round of its interaction path
against `s` is answered by `s`.  (⇒ is uniqueness of the completed
transcript; ⇐ replays the path.) -/
theorem completesAt_exists_iff_path_dom {q : ℕ} (w : Strategy X Y q)
    (s : DDS X Y) :
    (∃ tr : (Fin q → X) × (Fin q → Y),
        CompletesAt (Strategy.toDDE w) s (List.ofFn tr.1) (List.ofFn tr.2)) ↔
      ∀ k, k < q → pathList w s (k + 1) ∈ s.dom := by
  constructor
  · rintro ⟨tr, htr⟩ k hk
    have hxs : List.ofFn tr.1 = pathList w s q :=
      completesAt_eq_pathList (fun l hl => ⟨hl, rfl⟩) htr (by simp)
    have hmem := outputSeq_entry_dom htr.1 (k := k)
      (by simp only [List.length_ofFn]; omega)
    rw [hxs, pathList_take w s (by omega)] at hmem
    exact hmem
  · intro hdom
    have hlen : (pathList w s q).length = q := by
      rw [pathList_length]; omega
    have hdom' : ∀ k, k < (pathList w s q).length →
        (pathList w s q).take (k + 1) ∈ s.dom := by
      intro k hk
      rw [pathList_take w s (by omega)]
      exact hdom k (by omega)
    refine ⟨⟨fun k : Fin q =>
        (pathList w s q)[(k : ℕ)]'(by have := k.isLt; omega),
      fun k : Fin q =>
        s.respond (pathList w s ((k : ℕ) + 1)) (hdom (k : ℕ) k.isLt)⟩, ?_⟩
    have hofn : List.ofFn (fun k : Fin q =>
        (pathList w s q)[(k : ℕ)]'(by have := k.isLt; omega)) =
        pathList w s q := ofFn_getElem_of_length hlen
    have houtput : s.outputSeq (pathList w s q) =
        (List.ofFn (fun k : Fin q =>
          s.respond (pathList w s ((k : ℕ) + 1)) (hdom (k : ℕ) k.isLt))).map
            some := by
      apply outputSeq_eq_map_some (by simp [hlen]) hdom'
      intro k hk
      simp only [List.getElem_ofFn]
      exact s.respond_congr (pathList_take w s (by omega)) _ _
    refine ⟨?_, ?_⟩
    · show s.outputSeq (List.ofFn _) = _
      rw [hofn]
      exact houtput
    · show DDE.inputSeq (Strategy.toDDE w) _ = (List.ofFn _).map some
      rw [hofn]
      exact inputSeq_toDDE_pathList w s houtput

/-! ### Oblivious and unblinded strategies -/

/-- The **oblivious strategy** committed to the fixed query list `xs`: the
blind winner of CR18 §4.11.2 ("the inputs `x₁, …, x_q` can be interpreted as
being chosen in advance, before seeing any outputs"). -/
def constStrategy [Inhabited X] (q : ℕ) (xs : List X) : Strategy X Y q :=
  fun k _ => xs.getD k default

/-- The interaction path of the oblivious strategy is its committed list,
independently of the answering system. -/
theorem pathList_constStrategy [Inhabited X] {q : ℕ} {xs : List X}
    (hlen : xs.length = q) (s : DDS X Y) :
    ∀ k, k ≤ q → pathList (constStrategy q xs) s k = xs.take k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk1
    have hkq : k < q := by omega
    have hk2 : k < xs.length := by omega
    rw [pathList_succ, dif_pos hkq, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hk2]
    simp [constStrategy, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk2]

/-- Reading a blind (`PUnit`-reply) strategy as an adaptive `(X,Y)`-strategy
that ignores the replies.  Maurer (Def 4.20 discussion): a non-adaptive
winning strategy is in particular an adaptive one. -/
def unblind {q : ℕ} (w : Strategy X PUnit q) : Strategy X Y q :=
  fun k _ => w k (fun _ => PUnit.unit)

/-- `unblind w` traces the same interaction path as `w` against any pair of
systems — the replies carry no usable information in either case. -/
theorem pathList_unblind {q : ℕ} (w : Strategy X PUnit q)
    (s' : DDS X PUnit) (t : DDS X Y) (k : ℕ) :
    pathList (unblind w) t k = pathList w s' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pathList_succ, pathList_succ, ih]
    by_cases hkq : k < q
    · rw [dif_pos hkq, dif_pos hkq]
      congr 2
    · rw [dif_neg hkq, dif_neg hkq]

end Path

/-! ### Finsupp transport along `Dist.fTransform` and `Dist.prod`

UPSTREAM-CANDIDATE (RandomSystems/Dist.lean): Fintype-free mass/sum transport
for the pushforward and the independent product. -/

/-- Pushforward transport for an arbitrary additive summand
(generalizes `fTransform_sum_mul_finsupp`). -/
theorem fTransform_sum_finsupp {α : Type*} {β : Type*} [DecidableEq β]
    (f : α → β) (D : Dist α) (F : β → NNReal → NNReal)
    (h0 : ∀ b, F b 0 = 0) (hadd : ∀ b m n, F b (m + n) = F b m + F b n) :
    (Dist.fTransform f D).sum F = D.sum fun a w => F (f a) w := by
  simp only [Dist.fTransform]
  rw [Finsupp.sum_sum_index h0 hadd]
  exact Finsupp.sum_congr fun a _ => Finsupp.sum_single_index (h0 _)

/-- The pushforward preserves the total Finsupp mass (Fintype-free `weight`
preservation). -/
theorem fTransform_mass {α : Type*} {β : Type*} [DecidableEq β]
    (f : α → β) (D : Dist α) :
    (Dist.fTransform f D).sum (fun _ p => p) = D.sum (fun _ p => p) :=
  fTransform_sum_finsupp f D (fun _ p => p) (fun _ => rfl) (fun _ _ _ => rfl)

/-- Sum transport across the independent product `Dist.prod`. -/
theorem prod_sum_finsupp {α : Type*} {β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Dist α) (B : Dist β) (F : α × β → NNReal → NNReal)
    (h0 : ∀ p, F p 0 = 0) (hadd : ∀ p m n, F p (m + n) = F p m + F p n) :
    (Dist.prod A B).sum F =
      A.sum fun a wa => B.sum fun b wb => F (a, b) (wa * wb) := by
  simp only [Dist.prod]
  rw [Finsupp.sum_sum_index h0 hadd]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [Finsupp.sum_sum_index h0 hadd]
  exact Finsupp.sum_congr fun b _ => Finsupp.sum_single_index (h0 _)

/-- The total mass of the independent product is the product of the masses
(Fintype-free `Dist.weight_prod`). -/
theorem prod_mass {α : Type*} {β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Dist α) (B : Dist β) :
    (Dist.prod A B).sum (fun _ p => p) =
      (A.sum fun _ p => p) * (B.sum fun _ p => p) := by
  rw [prod_sum_finsupp A B (fun _ p => p) (fun _ => rfl) (fun _ _ _ => rfl)]
  calc A.sum (fun _ wa => B.sum fun _ wb => wa * wb)
      = A.sum fun _ wa => wa * (B.sum fun _ p => p) :=
        Finsupp.sum_congr fun a _ => by rw [Finsupp.mul_sum]
    _ = (A.sum fun _ p => p) * (B.sum fun _ p => p) := by
        rw [Finsupp.sum_mul]

/-- Support projection for the independent product. -/
theorem mem_support_of_prod {α : Type*} {β : Type*} [DecidableEq α]
    [DecidableEq β] {A : Dist α} {B : Dist β} {a : α} {b : β}
    (h : (a, b) ∈ (Dist.prod A B).support) :
    a ∈ A.support ∧ b ∈ B.support := by
  rw [Finsupp.mem_support_iff, Dist.prod_apply] at h
  exact ⟨Finsupp.mem_support_iff.mpr fun h0 => h (by rw [h0, zero_mul]),
    Finsupp.mem_support_iff.mpr fun h0 => h (by rw [h0, mul_zero])⟩

/-- The first marginal of the independent product with a weight-1 second
factor is the first factor. -/
theorem fst_fTransform_prod {α : Type*} {β : Type*} [DecidableEq α]
    [DecidableEq β] (A : Dist α) (B : Dist β)
    (hB : B.sum (fun _ p => p) = 1) :
    Dist.fTransform Prod.fst (Dist.prod A B) = A := by
  refine Finsupp.ext fun a => ?_
  rw [fTransform_apply_finsupp]
  rw [prod_sum_finsupp A B (fun p w => if p.1 = a then w else 0)
    (fun p => by simp)
    (fun p m n => by by_cases h : p.1 = a <;> simp [h])]
  have hinner : ∀ x (wa : NNReal),
      (B.sum fun b wb => if ((x, b) : α × β).1 = a then wa * wb else 0) =
        if x = a then wa else 0 := by
    intro x wa
    show (B.sum fun _ wb => if x = a then wa * wb else 0) =
      if x = a then wa else 0
    by_cases hx : x = a
    · rw [if_pos hx]
      calc (B.sum fun _ wb => if x = a then wa * wb else 0)
          = B.sum fun _ wb => wa * wb :=
            Finsupp.sum_congr fun b _ => if_pos hx
        _ = wa * B.sum fun _ p => p := by rw [Finsupp.mul_sum]
        _ = wa := by rw [hB, mul_one]
    · rw [if_neg hx]
      simp only [Finsupp.sum]
      exact Finset.sum_eq_zero fun b _ => if_neg hx
  rw [Finsupp.sum_congr (g2 := fun x wa => if x = a then wa else 0)
    fun x _ => hinner x (A x)]
  rw [Finsupp.sum_ite_eq' A a (fun _ w => w)]
  split
  · rfl
  · next h => exact (Finsupp.notMem_support_iff.mp h).symm

/-! ### eq-4.37 mass identities for an arbitrary `PDS` -/

section Eq437

variable [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [Fintype X] [Fintype Y]

omit [Inhabited X] in
/-- Acceptance expansion for an arbitrary `PDS` (steps 1–3 of
`acceptProb_det_strip`, without the strip partition): the κ-acceptance
probability of a deterministic distinguisher `d = (w, Z)` against `G'` is the
transcript sum `Σ_t [Z t] · Pr_{G'}[transcript t] · [w asks t]`. -/
theorem acceptProb_det_pds (q : ℕ) (G' : PDS X Y)
    (d : Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) :
    (G'.sum fun s sw =>
        sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) =
      ∑ t : (Fin q → X) × (Fin q → Y),
        (if d.2 t = true then (1 : NNReal) else 0) *
          jointProb G' (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0) := by
  classical
  -- Step 1: the acceptance indicator as a transcript sum.
  have hκ : ∀ s : DDS X Y,
      (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0) =
        ∑ t : (Fin q → X) × (Fin q → Y),
          if (CompletesAt (Strategy.toDDE d.1) s
              (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
            then (1 : NNReal) else 0 := by
    intro s
    have huniq : ∀ t t' : (Fin q → X) × (Fin q → Y),
        (CompletesAt (Strategy.toDDE d.1) s
          (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) →
        (CompletesAt (Strategy.toDDE d.1) s
          (List.ofFn t'.1) (List.ofFn t'.2) ∧ d.2 t' = true) →
        t = t' := by
      rintro t t' ⟨ht, -⟩ ⟨ht', -⟩
      obtain ⟨hx, hy⟩ := completesAt_unique ht ht' (by simp)
      exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hy)
    rw [sum_indicator_unique _ huniq, distinctionStructure_κ]
    simp only [decide_eq_true_eq]
  -- Step 2: swap the system sum with the transcript sum.
  calc (G'.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
      = ∑ t : (Fin q → X) × (Fin q → Y), G'.sum fun s sw =>
          sw * (if (CompletesAt (Strategy.toDDE d.1) s
              (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
            then (1 : NNReal) else 0) := by
        rw [show (G'.sum fun s sw =>
            sw * (if (distinctionStructure X Y q).κ d s then (1:NNReal) else 0)) =
            G'.sum fun s sw =>
              ∑ t : (Fin q → X) × (Fin q → Y),
                sw * (if (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true)
                  then (1:NNReal) else 0) from
          Finsupp.sum_congr fun s _ => by rw [hκ s, Finset.mul_sum]]
        simp only [Finsupp.sum]
        exact Finset.sum_comm
    -- Step 3: factor each transcript term into accept × system × ask.
    _ = _ := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hacc : d.2 t = true
        · by_cases hask : DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
              (List.ofFn t.1).map some
          · rw [if_pos hacc, if_pos hask, one_mul, mul_one,
              jointProb_eq_sum_support]
            simp only [Finsupp.sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases hout : s.outputSeq (List.ofFn t.1) =
                (List.ofFn t.2).map some
            · rw [if_pos hout,
                if_pos (show (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) from
                  ⟨⟨hout, hask⟩, hacc⟩), mul_one]
            · rw [if_neg hout,
                if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                    (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
                  hout hc.1.1), mul_zero]
          · rw [if_neg hask, mul_zero]
            simp only [Finsupp.sum]
            exact Finset.sum_eq_zero fun s _ => by
              rw [if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                  (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
                hask hc.1.2), mul_zero]
        · rw [if_neg hacc, zero_mul, zero_mul]
          simp only [Finsupp.sum]
          exact Finset.sum_eq_zero fun s _ => by
            rw [if_neg (fun hc : (CompletesAt (Strategy.toDDE d.1) s
                (List.ofFn t.1) (List.ofFn t.2) ∧ d.2 t = true) =>
              hacc hc.2), mul_zero]

open scoped Classical in
omit [Inhabited X] in
/-- The `q`-round completion mass of `w ↔ G'`: the transcript sum
`Σ_t Pr_{G'}[t] · [w asks t]` is the mass of realizations with a completed
`q`-round transcript. -/
theorem sum_jointProb_ask_eq (q : ℕ) (G' : PDS X Y) (w : Strategy X Y q) :
    (∑ t : (Fin q → X) × (Fin q → Y),
      jointProb G' (List.ofFn t.1) (List.ofFn t.2) *
        (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
            (List.ofFn t.1).map some then 1 else 0)) =
      G'.sum fun s sw =>
        sw * (if (∃ t : (Fin q → X) × (Fin q → Y),
            CompletesAt (Strategy.toDDE w) s
              (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0) := by
  classical
  calc (∑ t : (Fin q → X) × (Fin q → Y),
        jointProb G' (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0))
      = ∑ t : (Fin q → X) × (Fin q → Y), G'.sum fun s sw =>
          sw * ((if s.outputSeq (List.ofFn t.1) = (List.ofFn t.2).map some
              then (1 : NNReal) else 0) *
            (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [jointProb_eq_sum_support]
        simp only [Finsupp.sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hout : s.outputSeq (List.ofFn t.1) = (List.ofFn t.2).map some
        · rw [if_pos hout, if_pos hout, one_mul]
        · rw [if_neg hout, if_neg hout, zero_mul, mul_zero]
    _ = G'.sum fun s sw => ∑ t : (Fin q → X) × (Fin q → Y),
          sw * ((if s.outputSeq (List.ofFn t.1) = (List.ofFn t.2).map some
              then (1 : NNReal) else 0) *
            (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) := by
        simp only [Finsupp.sum]
        exact Finset.sum_comm
    _ = _ := by
        refine Finsupp.sum_congr fun s _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [← sum_indicator_unique
          (fun t : (Fin q → X) × (Fin q → Y) =>
            CompletesAt (Strategy.toDDE w) s
              (List.ofFn t.1) (List.ofFn t.2))
          (fun t t' ht ht' => by
            obtain ⟨hx, hy⟩ := completesAt_unique ht ht' (by simp)
            exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hy))]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases h1 : s.outputSeq (List.ofFn t.1) = (List.ofFn t.2).map some
        · by_cases h2 : DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some
          · rw [if_pos h1, if_pos h2, if_pos
              (show CompletesAt (Strategy.toDDE w) s (List.ofFn t.1)
                (List.ofFn t.2) from ⟨h1, h2⟩), one_mul]
          · rw [if_pos h1, if_neg h2,
              if_neg (fun hc : CompletesAt (Strategy.toDDE w) s (List.ofFn t.1)
                (List.ofFn t.2) => h2 hc.2), mul_zero]
        · rw [if_neg h1, zero_mul,
            if_neg (fun hc : CompletesAt (Strategy.toDDE w) s (List.ofFn t.1)
              (List.ofFn t.2) => h1 hc.1)]

omit [Inhabited X] in
/-- The completion mass is at most the total mass (`Pr[completes] ≤ Pr[⊤]`). -/
theorem sum_jointProb_ask_le_mass (q : ℕ) (G' : PDS X Y) (w : Strategy X Y q) :
    (∑ t : (Fin q → X) × (Fin q → Y),
      jointProb G' (List.ofFn t.1) (List.ofFn t.2) *
        (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
            (List.ofFn t.1).map some then 1 else 0)) ≤
      G'.sum fun _ p => p := by
  rw [sum_jointProb_ask_eq]
  refine Finsupp.sum_le_sum fun s _ => ?_
  split
  · exact le_of_eq (mul_one _)
  · simp

omit [Inhabited X] in
/-- **CR18 eq (4.37), additive complement form**: for every strategy `w` and
game `G`, the winning mass plus the pre-winning completion mass is the total
mass — `Pr^{wG}(Aq=1) + Pr^{wG}(Aq=0) = Pr[⊤]` with `Aq=0` read as "the
pre-winning system completes all `q` rounds" (the faithful partial-DDS
reading; see the `gameStructure` docstring). -/
theorem winMass_add_preWinCompletion (q : ℕ) (G : PDG X Y)
    (w : Strategy X Y q) :
    (G.sum fun g gp =>
        gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) +
      (∑ t : (Fin q → X) × (Fin q → Y),
        jointProb (Def415.preWinningPDS G) (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE w) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0)) =
      G.sum fun _ p => p := by
  classical
  rw [sum_jointProb_ask_eq q (Def415.preWinningPDS G) w]
  have htrans : ((Def415.preWinningPDS G).sum fun s sw =>
      sw * (if (∃ t : (Fin q → X) × (Fin q → Y),
          CompletesAt (Strategy.toDDE w) s
            (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0)) =
      G.sum fun g gp =>
        gp * (if (∃ t : (Fin q → X) × (Fin q → Y),
            CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
              (List.ofFn t.1) (List.ofFn t.2)) then (1 : NNReal) else 0) := by
    rw [Def415.preWinningPDS]
    exact fTransform_sum_finsupp Def415.preWinningDDS G _
      (fun _ => zero_mul _) (fun _ m n => add_mul m n _)
  rw [htrans, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [gameStructure_win]
  simp only [decide_eq_true_eq]
  by_cases hex : ∃ t : (Fin q → X) × (Fin q → Y),
      CompletesAt (Strategy.toDDE w) (Def415.preWinningDDS g)
        (List.ofFn t.1) (List.ofFn t.2)
  · rw [if_neg (not_not_intro hex), if_pos hex, mul_zero, mul_one, zero_add]
  · rw [if_pos hex, if_neg hex, mul_one, mul_zero, add_zero]

end Eq437

end Lem416

end RandomSystems.CR18

/-!
## CR18 Definition 4.19 — Conditional Equivalence `Ŝ |≡ T`

CR18 §4.11.1 (source line 5519–5575):

> **Definition 4.19.**  For an `(X, Y) × {0, 1}`-system `S` with MBO (denoted `Aᵢ`)
> and an `(X, Y)`-system `T` we say that `S` is **conditionally equivalent** to `T`,
> denoted
>
>   `Ŝ |≡ T`,
>
> if, for `i ≥ 1`,
>
>   `p^S_{Yⁱ | Xⁱ, Aᵢ=0} = p^T_{Yⁱ | Xⁱ}`.
>
> In other words, conditioned on the MBO not having been triggered (all `Aⱼ = 0`
> for `j ≤ i`), the `Y`-output distribution of `S` equals the output distribution
> of `T`.

### Design

Definition 4.19 is, at its core, a statement about the **conditional probability
distributions** of the probabilistic systems `S` and `T` (CR18 footnote 29: two
conditional distributions are equal "if they are equal for all arguments for
which they are both defined"; the equivalent joint form is eq. (4.38)).  We
formalize it at **two levels**:

1. **Deterministic** (`DDG.CondEquiv`): a *helper* relating a single concrete
   game `g : DDG X Y` to a single concrete system `t : DDS X Y`.  For every input
   history `l` (nonempty, in the domains of both), if the MBO bit at `l` is
   `false`, the `Y`-component of `g`'s response equals `t`'s response.  This is
   only a pointwise calculation aid for deterministic subgoals.  It is not the
   official probabilistic Definition 4.19, which is cumulative and
   distributional.

2. **Probabilistic** (`PDG.CondEquiv`): the genuine, *distributional* Definition
   4.19.  The rendered lecture note uses cumulative transcripts `Yⁱ`, not a
   single output `Yᵢ`: for every nonempty input history `xs` and visible output
   transcript `ys`, the `Yⁱ`-distribution of `S` conditioned on `Aᵢ = 0` equals
   the `Yⁱ`-distribution of `T`.  We state the division-free Eq. (4.38) as
   `massYAfalse S xs ys · massDom T xs = massY T xs ys · massAfalse S xs`.

   ⚠ HISTORY: the originally committed `PDG.CondEquiv` read
   `∀ g ∈ supp(S), ∀ t ∈ supp(T), g |≡_det t`, i.e. *every* realization of `S`
   agrees pointwise with *every* realization of `T`.  That is strictly **stronger
   than Maurer's distributional condition** and is FALSE on Maurer's own
   Example 4.14 (`R̂ₘ,ₙ |≡ Bₙ`): a uniform random function and a beacon have equal
   *output distributions* given distinct inputs, but no fixed function in the
   URF's support equals every beacon realization pointwise.  The contrarian review
   replaced it with the distributional form above (IMPL_BUG fix — the lecture note
   was correct; the prior Lean was not).

### Relation to `ConditionBased.lean`

`RandomSystems.PDS.condEquiv` (in `ConditionBased.lean`) is the same
distributional idea at the fixed-arity LM20 transcript layer: it compares
transcript *distributions* on the "good" transcripts of a `TranscriptCondition`.
The CR18 Def 4.19 here is the variable-length (`List X` history, `Dist (DDG X Y)`)
analogue, instantiated with the MBO event `Aᵢ = 0` as the condition.

The DDG-level `DDG.CondEquiv` is a pointwise deterministic helper.  The official
probabilistic `PDG.CondEquiv` is cumulative, matching Def. 4.19 and the
equivalent game-equivalence condition stated just after Def. 4.16.
-/

namespace RandomSystems.CR18

namespace Def419

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Deterministic conditional equivalence -/

/-- CR18 Definition 4.19 (deterministic layer): a DDG `g` is **conditionally
equivalent** to a DDS `t`, written `g |≡_det t`, if for every nonempty input
history `l` that lies in both domains, the MBO-not-triggered condition
(`(g.toSystem.respond l hg).2 = false`) implies that the Y-output agrees with `t`:

  `(g.toSystem.respond l hg).1 = t.respond l ht`

This is the pointwise deterministic reading of a single query.  It is useful for
concrete DDS/DDG calculations, but the official probabilistic Def. 4.19 below is
cumulative over `Yⁱ`, as in the lecture note.

**Note on domain matching**: CR18 does not require `S` and `T` to have the same
domain.  We quantify over all `l` lying in **both** domains.  In typical use,
`T`'s domain is all of `(X*)⁺`, so the quantifier reduces to `l ∈ g.toSystem.dom`. -/
def DDG.CondEquiv (g : DDG X Y) (t : DDS X Y) : Prop :=
  ∀ (l : List X) (hg : l ∈ g.toSystem.dom) (ht : l ∈ t.dom),
    (g.toSystem.respond l hg).2 = false →
    (g.toSystem.respond l hg).1 = t.respond l ht

/-- Notation for deterministic conditional equivalence. -/
scoped notation:50 g " |≡_det " t => DDG.CondEquiv g t

/-! ### Properties of deterministic conditional equivalence -/

/-- If a DDG's MBO is always triggered (every response has bit = true), then
it is vacuously conditionally equivalent to any DDS.

This formalizes the edge case: if the condition `Aᵢ = false` is never satisfied,
the implication `Aᵢ = false → Yᵢ = Tᵢ` holds vacuously. -/
theorem condEquiv_of_mbo_always_true (g : DDG X Y) (t : DDS X Y)
    (h : ∀ (l : List X) (hl : l ∈ g.toSystem.dom),
           (g.toSystem.respond l hl).2 = true) :
    g |≡_det t := by
  intro l hg ht hA
  -- hA : (g.toSystem.respond l hg).2 = false
  -- h l hg : (g.toSystem.respond l hg).2 = true
  simp [h l hg] at hA

-- Deterministic conditional equivalence is not symmetric in general:
-- `g |≡_det t` relates a DDG to a plain DDS, which have different output types.

/-! ### Probabilistic conditional equivalence

CR18 Definition 4.19 is a statement about the **conditional probability
distributions** of the probabilistic systems `S` and `T` (cf. CR18 footnote 29,
which makes explicit that two conditional distributions are equal "if they are
equal for all arguments for which they are both defined"; the joint form is
eq. (4.38)).  It is **NOT** a pointwise "every realization of `S` equals every
realization of `T`" condition.

The following mass functions sum, over the finitely-supported sub-distributions
`S : Dist (DDG X Y)` / `T : Dist (DDS X Y)`, the weight of the realizations that
contribute to each conditional probability.  Domain membership of the history
`xs` is decided classically (it is a `Set` predicate). -/

open scoped Classical in
/-- `p^S_{Yⁱ,Aᵢ=0 | Xⁱ=xs}(ys)` (unnormalized): the cumulative probability that
the game `S` produces the visible transcript `ys` on input transcript `xs` and
has not won by round `i`.  This is exactly the joint probability of the
pre-winning PDS from Def. 4.15. -/
noncomputable def PDG.massYAfalse [DecidableEq (List (Option Y))]
    (S : PDG X Y) (xs : List X) (ys : List Y) : NNReal :=
  jointProb (Def415.preWinningPDS S) xs ys

open scoped Classical in
/-- `p^S_{Aᵢ=0 | Xⁱ=l}` (unnormalized): the total weight of DDGs `g` in `S` for
which `l` is in `g`'s domain and the MBO bit at `l` is `false`. -/
noncomputable def PDG.massAfalse (S : PDG X Y) (l : List X) : NNReal :=
  S.sum fun g w =>
    if h : l ∈ g.toSystem.dom then
      (if (g.toSystem.respond l h).2 = false then w else 0)
    else 0

open scoped Classical in
/-- `p^T_{Yⁱ | Xⁱ=xs}(ys)` (unnormalized): the cumulative probability that the
plain system `T` produces the visible transcript `ys` on input transcript `xs`. -/
noncomputable def PDS.massY [DecidableEq (List (Option Y))]
    (T : PDS X Y) (xs : List X) (ys : List Y) : NNReal :=
  jointProb T xs ys

open scoped Classical in
/-- The total weight of DDSs `t` in `T` for which `l` is in `t`'s domain — the
normalizer for `T`'s conditional output distribution at history `l`. -/
noncomputable def PDS.massDom (T : PDS X Y) (l : List X) : NNReal :=
  T.sum fun t w => if l ∈ t.dom then w else 0

/-- The paper treats systems as defined on the histories under discussion.  In
the Lean partial-system model, the corresponding support condition is that every
realization in `T`'s support accepts every nonempty input history. -/
def PDS.TotalOnNonempty (T : PDS X Y) : Prop :=
  ∀ t ∈ T.support, ∀ xs : List X, xs ≠ [] → xs ∈ t.dom

/-- Random functions are total on every nonempty input history in the partial
`DDS` model: each support realization is a `DDS.functionEvaluator`. -/
theorem PDS.totalOnNonempty_of_isRandomFunction {T : PDS X Y}
    (hRF : RandomFunction.IsRandomFunction T) :
    PDS.TotalOnNonempty T := by
  intro t ht xs hxs
  rcases hRF t (Finsupp.mem_support_iff.mp ht) with ⟨f, rfl⟩
  exact hxs

/-- The canonical PDS built from a distribution on total functions satisfies
the support-totality side condition needed for CR18 Definition 4.19. -/
theorem PDS.totalOnNonempty_ofFunDist [Fintype (X → Y)] [DecidableEq (DDS X Y)]
    (Df : Dist (X → Y)) :
    PDS.TotalOnNonempty (RandomFunction.ofFunDist Df) :=
  PDS.totalOnNonempty_of_isRandomFunction
    (RandomFunction.ofFunDist_isRandomFunction Df)

/-- CR18 Definition 4.19 (probabilistic layer): a PDG `S` is **conditionally
equivalent** to a PDS `T`, written `S |≡ T`, iff for every nonempty input
history `xs` and visible output transcript `ys` of the same length, the
cumulative `Yⁱ`-output distribution of `S` **conditioned on the MBO event
`Aᵢ = 0`** equals the cumulative output distribution of `T`:

  `p^S_{Yⁱ | Xⁱ=xs, Aᵢ=0}(ys) = p^T_{Yⁱ | Xⁱ=xs}(ys)`.

To avoid division — and to honour CR18 footnote 29 ("equal for all arguments for
which they are both defined") — we state the equality in **cross-multiplied**
form, guarded by the two defined-ness conditions (`p^S_{Aᵢ=0 | Xⁱ} ≠ 0` and
`p^T mass at `xs` ≠ 0`):

  `massYAfalse S xs ys · massDom T xs = massY T xs ys · massAfalse S xs`,

which is equivalent to
`massYAfalse S xs ys / massAfalse S xs = massY T xs ys / massDom T xs`
wherever both denominators are nonzero.  This is exactly the equality of the two
conditional distributions, and the cross-multiplied form is CR18 equation (4.38)
read at the unnormalized-mass level.

CONTRARIAN-REVIEW FIX (IMPL_BUG — the lecture note is correct, the prior Lean was
not): the originally committed `PDG.CondEquiv` read
`∀ g ∈ supp(S), ∀ t ∈ supp(T), g |≡_det t` (every realization of `S` agrees
pointwise with every realization of `T`).  That is strictly **stronger** than
Maurer's distributional condition and is FALSE on Maurer's own Example 4.14
(`R̂ₘ,ₙ |≡ Bₙ`): a uniform random function and a beacon have matching *output
distributions* given distinct inputs, but no fixed function in the URF's support
equals every beacon realization pointwise.  The definition is now stated
distributionally and cumulatively, faithful to Def 4.19 + footnote 29 + eq.
(4.38). -/
noncomputable def PDG.CondEquiv [DecidableEq (List (Option Y))]
    (S : PDG X Y) (T : PDS X Y) : Prop :=
  ∀ (xs : List X) (_ : xs ≠ []) (ys : List Y), ys.length = xs.length →
    PDG.massAfalse S xs ≠ 0 → PDS.massDom T xs ≠ 0 →
    PDG.massYAfalse S xs ys * PDS.massDom T xs =
      PDS.massY T xs ys * PDG.massAfalse S xs

/-- Notation for probabilistic conditional equivalence: `S |≡ T`. -/
scoped notation:50 S " |≡ " T => PDG.CondEquiv S T

/-! ### Mass of the point-mass (`pure`) distributions -/

/-- The `Aᵢ=0` mass of a point-mass PDG is `1` exactly when `l` is in the game's
domain and the MBO bit is `false` there, and `0` otherwise. -/
theorem massAfalse_pure (g : DDG X Y) (l : List X) :
    PDG.massAfalse (PDG.pure g) l =
      if h : l ∈ g.toSystem.dom then
        (if (g.toSystem.respond l h).2 = false then 1 else 0)
      else 0 := by
  classical
  rw [PDG.massAfalse, PDG.pure, Finsupp.sum_single_index]
  simp

/-- The domain mass of a point-mass PDS. -/
theorem massDom_pure (t : DDS X Y) (l : List X) :
    PDS.massDom (PDS.pure t) l = if l ∈ t.dom then 1 else 0 := by
  classical
  rw [PDS.massDom, PDS.pure, Finsupp.sum_single_index]
  simp

/-- A weight-1 PDS whose support is total on nonempty histories has conditional
normalizer `1` on every nonempty history.  This packages the partial-system
bookkeeping that is implicit in CR18's conditional distributions. -/
theorem massDom_eq_one_of_totalOnNonempty (T : PDS X Y)
    (hT : T.sum (fun _ p => p) = 1)
    (hTotal : PDS.TotalOnNonempty T) :
    ∀ xs : List X, xs ≠ [] → PDS.massDom T xs = 1 := by
  intro xs hxs
  rw [PDS.massDom]
  rw [← hT]
  exact Finsupp.sum_congr fun t ht => by
    rw [if_pos (hTotal t ht xs hxs)]

/-! ### Relation to CR18 equation (4.38) -/

/-- CR18 equation (4.38), deterministic helper: when the MBO bit is false, the
regular output of `g` agrees with the system output of `t`.

This is a pointwise deterministic reformulation of `DDG.CondEquiv`; the
probabilistic Eq. (4.38) above is cumulative over `Yⁱ`. -/
theorem condEquiv_iff_factorization (g : DDG X Y) (t : DDS X Y) :
    (g |≡_det t) ↔
    ∀ (l : List X) (hg : l ∈ g.toSystem.dom) (ht : l ∈ t.dom),
      (g.toSystem.respond l hg).2 = false →
      (g.toSystem.respond l hg).1 = t.respond l ht := by
  -- `DDG.CondEquiv` is definitionally equal to this
  rfl

end Def419

end RandomSystems.CR18

/-!
## CR18 Theorem 4.17 — Fundamental Theorem

CR18 §4.11.1 (source ~line 5600–5670):

> **Theorem 4.17.** If for an `(X, Y)`-system `S` one can define an MBO such
> that `Ŝ |≡ T`, then
>
>   `⟨S|T⟩ ≤ bŜ ◦ ρT`
>
> In particular,
>
>   `Δ(S, T) ≤ Γ(bŜ)`.

The CR18 proof chain is:

1. Construct a game `T̂` by enhancing `T` with a copy of `Ŝ`'s MBO.
2. Since `Ŝ |≡ T`, the MBO-conditional output distributions agree:
   `pŜ_{Y,A=0|X} = pT̂_{Y,A=0|X}` (eq. 4.39), i.e. `Ŝ ≡_g T̂` (game equivalence).
3. By Lemma 4.16 (advantage ≤ winning probability):
   `⟨Ŝ⁻|T̂⁻⟩(D) ≤ Ŝ(D) ≤ Γ(Ŝ)` for every distinguisher `D`.
4. Since `Ŝ⁻ = S` and `T̂⁻ = T`, this is `⟨S|T⟩(D) ≤ Γ(Ŝ)`.
5. Taking the supremum over `D`: `Δ(S, T) ≤ Γ(Ŝ)`.
### Lean representation (K4 — un-hollowed)

The former statements carried the entire Lemma 4.16 content in a caller-supplied
bridge hypothesis `hBridge` (documented `⚠ HOLLOW` in the checklist).  They are
now stated at the CONCRETE `Lem416.distinctionStructure` /
`Lem416.gameStructure` level and consume the PROVEN concrete Lemma 4.16
(`Lem416.advantage_le_maxWinProb`): **`hBridge` is GONE**, and with it the
abstract `ds`/`gs`/`phi_D`/`phi_G`/`iota` packaging that existed only to
carry it.

Remaining caller obligations (CR18 proof steps 1–2, eq. 4.39 — SEPARATE
content, not Lemma 4.16): construct the enhanced game `That` (Def 4.21) with
`PDG.strip That = T` and derive `Shat ≡_g That` from `Shat |≡ T`.  These stay
as the explicit hypotheses `That`/`hGameEquiv`/`hStrip` (the
conditional-equivalence ⇒ game-equivalence bridge is a separate checklist
obligation); `hCondEquiv` is retained as Maurer's official premise.

`Δ(S,T)` is rendered as the supremum of the signed performance over
**probability-distribution** distinguishers (`sSup` over the image of
`{D | D.isProbDist}`, mirroring `Def417.maxWinProb`).  The previous `⨆` over
ALL `Dist`-distinguishers was concretely meaningless: sub-distributions of
weight ≠ 1 are not Maurer distinguishers (Def 4.7) and their performance is
unbounded.

SCOPE NOTE / WEAKER-BOUND (CR18 Theorem 4.17, unchanged from the previous
revision): Maurer's published conclusion is `Δ(S,T) ≤ Γ(b·Ŝ)`, with the
BLINDING converter `b` (Def 4.20) forcing a non-adaptive winner.  We prove the
strictly WEAKER but fully SOUND corollary `Δ(S,T) ≤ Γ(Ŝ)`: Maurer's own proof
chain passes through `Ŝ(D) ≤ Γ(Ŝ)` (Lemma 4.16) before tightening to
`Γ(b·Ŝ)` via eq 4.40, and `Γ(b·Ŝ) ≤ Γ(Ŝ)` (blinding only restricts the
winner), so our bound is implied by Maurer's.  The `Γ(b·Ŝ)` sharpening awaits
the instantiation of `b` (Def 4.20) at this concrete game structure.

Relation to `RandomSystems.FundamentalTheorem` (`delta_eq_advantage`): the LM20
result `Δ(S, T) = Adv(S, T)` operates on the fixed-arity `DDS X Y q` model with
a different `Δ` (inf over equivalent PDS representatives).  CR18 Thm 4.17 instead
gives an *upper bound* `Δ(S, T) ≤ Γ(Ŝ)` in the variable-length PDG/PDS model
with a game `Ŝ` having MBO `|≡ T`.  The two results are conceptually complementary
but live in separate frameworks.
-/

namespace RandomSystems.CR18

namespace Thm417

universe u v

variable {X : Type u} {Y : Type v}
  [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

open Def45 Def47 Def416 Def417 Def419 Lem416

/-! ### Per-distinguisher form of Theorem 4.17

The CR18 proof establishes the inequality distinguisher-by-distinguisher.
For a fixed `D`, the chain is:
  `⟨Ŝ⁻ | T̂⁻⟩(D) ≤ Ŝ(D) ≤ Γ(Ŝ)`  —  now FULLY PROVEN by the concrete
Lemma 4.16; only the eq-4.39 construction (`That`, `hGameEquiv`, `hStrip`)
remains a hypothesis.
-/

/-- **CR18 Theorem 4.17 (per-distinguisher form, hBridge eliminated)**:

If `Shat |≡ T` (conditional equivalence, Def 4.19) and `That` is the enhanced
game of Def 4.21 (`T` with a copy of `Shat`'s MBO: `That⁻ = T` and
`Shat ≡_g That`, CR18 eq. 4.39), then for every probabilistic `q`-query
distinguisher `D`,

  `⟨Shat⁻ | T⟩(D) ≤ Γ(Shat)`.

The Lemma 4.16 content (pre-winning-event cancellation, partition, `Aq=1`
bound, Lemma 4.15 transfer) is no longer assumed: it is supplied by the proven
`Lem416.advantage_le_maxWinProb`.

**CR18 reference:** Theorem 4.17 (source ~line 5600), steps 3–5 of the proof. -/
theorem advantage_le_maxWinProb (q : ℕ)
    (Shat : PDG X Y) (T : PDS X Y)
    (_hCondEquiv : Shat |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Shat ≡_g That)
    (hStrip : PDG.strip That = T)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hThat : That.sum (fun _ p => p) = 1)
    (D : (Lem416.distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D ≤
      (Def417.maxWinProb (Lem416.gameStructure X Y q) Shat : Real) := by
  rw [← hStrip]
  exact Lem416.advantage_le_maxWinProb q Shat That hGameEquiv hShat hThat D hD

/-! ### Delta form of Theorem 4.17 -/

/-- **CR18 Theorem 4.17 (delta form, hBridge eliminated)**: the optimal
distinguishing advantage of the stripped pair is bounded by the maximal
winning probability,

  `Δ(Shat⁻, T) = sup_D ⟨Shat⁻ | T⟩(D) ≤ Γ(Shat)`,

the supremum ranging over probability-distribution distinguishers (Def 4.7).
Derived from the per-distinguisher form via `csSup_le`; the supremum set is
nonempty (the always-reject distinguisher).

NOTE — bound is `Γ(Shat)`, NOT Maurer's tighter `Γ(b·Shat)`: see the section
header (the blinding sharpening is deferred until `b` is instantiated at this
game structure).

**CR18 reference:** Theorem 4.17: "In particular, Δ(S,T) ≤ Γ(bŜ)." -/
theorem delta_le_gamma (q : ℕ)
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Shat ≡_g That)
    (hStrip : PDG.strip That = T)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hThat : That.sum (fun _ p => p) = 1) :
    sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
        (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (Lem416.gameStructure X Y q) Shat : Real) := by
  apply csSup_le
  · -- Nonempty: the always-reject distinguisher (point mass, weight 1).
    refine ⟨_, ⟨Finsupp.single
      ((fun _ _ => default, fun _ => false) :
        Lem416.Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) 1,
      ?_, rfl⟩⟩
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  · rintro x ⟨D, hD, rfl⟩
    exact advantage_le_maxWinProb q Shat T hCondEquiv That hGameEquiv hStrip
      hShat hThat D hD

/-! ### The headline statement -/

/-- **CR18 Theorem 4.17 (the fundamental theorem, hBridge eliminated)**:
conditional equivalence `Shat |≡ T` (with the eq-4.39 enhanced game `That`)
implies `Δ(Shat⁻, T) ≤ Γ(Shat)`.

Alias of `delta_le_gamma` under the headline name; the Lemma 4.16 content is
PROVEN (no bridge hypothesis), only the Def-4.21/eq-4.39 construction
(`That`/`hGameEquiv`/`hStrip`) remains a caller obligation. -/
theorem fundamental (q : ℕ)
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Shat ≡_g That)
    (hStrip : PDG.strip That = T)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hThat : That.sum (fun _ p => p) = 1) :
    sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
        (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (Lem416.gameStructure X Y q) Shat : Real) :=
  delta_le_gamma q Shat T hCondEquiv That hGameEquiv hStrip hShat hThat

end Thm417

end RandomSystems.CR18

/-!
## CR18 Definition 4.20 — `bS` Game System (Blinding Converter)

CR18 §4.11.2 (source line 5616–5623):

> **Definition 4.20.**  For a game `S` we define `bS` as the game system `S`
> for which the outputs `Yᵢ` are **blocked**, i.e., `b` is the simple converter
> that is transparent for the queries `Xᵢ` but blocks the replies `Yᵢ`.

To win game `bS` means to win game `S` **blindly**, without seeing the outputs.
Equivalently, this means to win the game **non-adaptively** since the inputs
`x₁, …, xq` can be interpreted as being chosen in advance, before seeing any
outputs.  The best probability in winning a game `S` non-adaptively (i.e., `Γ(bS)`)
is generally lower than the best probability in winning it adaptively (i.e., `Γ(S)`).

### Design

`b` is the **blinding converter**: transparent to queries, but it replaces every
reply `yᵢ : Y` with a fixed canonical value `PUnit.unit : PUnit` (the blocked
reply `⊥`).  This gives a game with the same internal structure (same domain, same
MBO) but with `Y`-output type replaced by `PUnit`.

* **Deterministic layer** (`DDG.blind`): given a `DDG X Y`, produce the
  `DDG X PUnit` that replaces every `(y, a) : Y × Bool` response with
  `(PUnit.unit, a) : PUnit × Bool` — the `Y` information is destroyed, only the
  MBO bit survives (so that winning / MBO structure is preserved).

* **Probabilistic layer** (`PDG.blind`): lift `DDG.blind` to the probabilistic
  level by pushing forward along the DDG projection.

The winner of `bS` is a `Winner X PUnit` — it still queries with `X` inputs, but
the replies it receives carry no `Y` information (`PUnit.unit` every time), so it
must commit to all queries before seeing any output.  This is exactly the
non-adaptive / blind winning condition from CR18.

### Relation to Theorem 4.17

Theorem 4.17 states `Δ(S, T) ≤ Γ(bŜ)`.  The formalization in `Thm417` currently
proves the weaker `Γ(Ŝ)` bound (see the SCOPE NOTE in `delta_le_gamma`).  Once
`PDG.blind` is available (this definition), the tighter bound can be recovered:
`Γ(bŜ) ≤ Γ(Ŝ)` because blinding restricts the winner's adaptivity (fewer
strategies available ⟹ max winning probability cannot increase).

### CR18 reference: Definition 4.20, source line 5616.
-/

namespace RandomSystems.CR18

namespace Def420

universe u v

variable {X : Type u} {Y : Type v}

/-! ### The blinding converter applied at the deterministic level -/

/-- CR18 Definition 4.20 (deterministic layer): **blind** a DDG by replacing
every `Y`-output with `PUnit.unit`.

Given a `(X, Y)`-game `g : DDG X Y`, `blindDDG g` is the `(X, PUnit)`-game that
has the same domain, the same MBO structure, and the same MBO bit at every history,
but returns `PUnit.unit` instead of the actual `Y` output at each round.

Maurer: "b is the simple converter that is transparent for the queries Xᵢ but
blocks the replies Yᵢ."

The MBO bit `aᵢ` is **not** blocked — it remains the same boolean as in `g` —
because the winning condition (the MBO becoming `true`) must be preserved in `bS`
for the game to be non-trivially winnable.  Only the regular `Y` output is
replaced with the uninformative value `PUnit.unit`. -/
def blindDDG (g : DDG X Y) : DDG X PUnit where
  toSystem := {
    dom            := g.toSystem.dom
    nonempty_input := g.toSystem.nonempty_input
    prefix_closed  := g.toSystem.prefix_closed
    respond        := fun l hl => (PUnit.unit, (g.toSystem.respond l hl).2)
  }
  mbo := by
    -- The MBO property transfers: the second component of (blindDDG g).toSystem.respond
    -- is definitionally equal to (g.toSystem.respond l hl).2, which is monotone by g.mbo.
    intro l hl i j hij hj ⟨hi_dom, ha⟩
    exact g.mbo l hl i j hij hj ⟨hi_dom, ha⟩

/-! ### Basic lemmas about blindDDG -/

/-- The domain of the blinded game equals the domain of the original game. -/
@[simp]
theorem blindDDG_dom_eq (g : DDG X Y) :
    (blindDDG g).toSystem.dom = g.toSystem.dom := rfl

/-- The MBO bit of the blinded game equals the MBO bit of the original game. -/
@[simp]
theorem blindDDG_mboOutput_eq (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) :
    ((blindDDG g).toSystem.respond l hl).2 = (g.toSystem.respond l hl).2 := rfl

/-- The regular output of the blinded game is always `PUnit.unit` — all
`Y`-information is destroyed by the blinding converter. -/
@[simp]
theorem blindDDG_regularOutput (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) :
    ((blindDDG g).toSystem.respond l hl).1 = PUnit.unit := rfl

/-- Blinding preserves the MBO (winning) structure: `blindDDG g` is won at
history `l` if and only if the original game `g` is won at history `l`. -/
theorem blindDDG_isWon_iff (g : DDG X Y) (l : List X) (hl : l ∈ g.toSystem.dom) :
    DDG.IsWon (blindDDG g) l (blindDDG_dom_eq g ▸ hl) ↔ DDG.IsWon g l hl := by
  simp [DDG.IsWon, DDG.binaryOutput]

/-! ### The blinded probabilistic game -/

/-- CR18 Definition 4.20 (probabilistic layer): **blind** a PDG.

A `PDG X Y` (= `Dist (DDG X Y)`) is a random variable over deterministic games.
`blindPDG S` (written `bS` in CR18) is the `PDG X PUnit` obtained by applying
`blindDDG` to each realisation `g` of `S` and pushing forward the distribution.

Maurer: "For a game S we define bS as the game system S for which the outputs Yᵢ
are blocked."

A winner for `bS` receives only `PUnit.unit` at every round, making its strategy
entirely non-adaptive: since all replies are identical, the winner must decide all
queries `x₁, …, xq` before the interaction (or equivalently, all query choices are
independent of the history). -/
noncomputable def blindPDG {X Y : Type*} [DecidableEq (DDG X PUnit)]
    (S : PDG X Y) : PDG X PUnit :=
  Dist.fTransform blindDDG S

/-! ### Basic lemmas about blindPDG -/

/-- `blindPDG` is `Dist.fTransform blindDDG` by definition. -/
@[simp]
theorem blindPDG_eq_fTransform {X Y : Type*} [DecidableEq (DDG X PUnit)]
    (S : PDG X Y) :
    blindPDG S = Dist.fTransform blindDDG S := rfl

/-- Blinding the degenerate PDG concentrated at `g` gives the degenerate PDG
concentrated at `blindDDG g`. -/
theorem blindPDG_pure {X Y : Type*} [DecidableEq (DDG X PUnit)]
    (g : DDG X Y) :
    blindPDG (PDG.pure g) = PDG.pure (blindDDG g) := by
  classical
  simp only [blindPDG, PDG.pure, Dist.fTransform]
  rw [Finsupp.sum_single_index (by simp)]

/-! ### The `blindGame` abbreviation and `Γ(bS)` -/

/-- CR18 Definition 4.20: `blindGame S` is the `(X, PUnit)`-PDG `bS` obtained
from `S : PDG X Y` by applying the blinding converter `b`.

This is the main exported definition.  In CR18 notation, this is `bS`.

The blinding converter `b` is transparent for queries (the winner still sends
`X`-inputs) but blocks all `Y`-replies (the winner receives `PUnit.unit` every
round, conveying zero information about the system's actual response). -/
noncomputable abbrev blindGame {X Y : Type*} [DecidableEq (DDG X PUnit)]
    (S : PDG X Y) : PDG X PUnit :=
  blindPDG S

/-! ### `Γ(bS) ≤ Γ(S)` at the concrete game structure (hBridge ELIMINATED)

The former statement of `blindGame_maxWinProb_le` was abstract (arbitrary
`gs_orig`/`gs_blind`/`φ` packaging) and carried its entire content in a
caller-supplied bridge hypothesis `hBridge : W_b(bS) ≤ Γ(S)` (documented
`⚠ HOLLOW` in the checklist).  It is now stated at the CONCRETE
`Lem416.gameStructure` level and PROVEN: a blind winner
`w : Strategy X PUnit q` of `bS` is in particular the adaptive winner
`Lem416.unblind w : Strategy X Y q` of `S` — the interaction path is the same
(`pathList_unblind`), the pre-winning domain is preserved by blinding
(`preWinningDDS_blindDDG_dom`), so the eq-4.37 winning events coincide
(`win_blindDDG_iff` via the completion criterion
`completesAt_exists_iff_path_dom`). -/

section Concrete

variable {q : ℕ}
variable [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

open Lem416

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y] in
/-- The pre-winning DDS of the blinded game equals that of the original game
up to output blinding: in particular the **domains** coincide (blinding
preserves both the interaction domain and the MBO bits). -/
theorem preWinningDDS_blindDDG_dom (g : DDG X Y) :
    (Def415.preWinningDDS (blindDDG g)).dom = (Def415.preWinningDDS g).dom :=
  rfl

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- **The blind-winner reduction (deterministic core)**: a blind strategy `w`
wins the blinded game `b·g` iff its unblinded reading wins `g` itself — the
interaction paths agree round by round and the pre-winning domains coincide,
so the eq-4.37 winning events are the same event. -/
theorem win_blindDDG_iff (q : ℕ) (w : Strategy X PUnit q) (g : DDG X Y) :
    (gameStructure X PUnit q).win w (blindDDG g) =
      (gameStructure X Y q).win (unblind w) g := by
  rw [gameStructure_win, gameStructure_win, decide_eq_decide]
  rw [completesAt_exists_iff_path_dom, completesAt_exists_iff_path_dom]
  simp only [pathList_unblind w (Def415.preWinningDDS (blindDDG g))
    (Def415.preWinningDDS g), preWinningDDS_blindDDG_dom]

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Fintype X] in
/-- **The blind-winner reduction (probabilistic)**: the winning probability of
a blind probabilistic winner `W` against `bS` equals the winning probability
of its unblinded pushforward against `S`. -/
theorem winProb_blindPDG (q : ℕ) [DecidableEq (DDG X PUnit)] (S : PDG X Y)
    (W : Dist (Strategy X PUnit q)) :
    (gameStructure X PUnit q).winProb W (blindPDG S) =
      (gameStructure X Y q).winProb
        (Dist.fTransform (unblind (Y := Y)) W) S := by
  rw [Def45.GameStructure.winProb, Def45.GameStructure.winProb]
  refine Eq.trans ?_ (fTransform_sum_finsupp (unblind (Y := Y)) W
    (fun w p => S.sum fun g gp =>
      p * gp * if (gameStructure X Y q).win w g then (1 : NNReal) else 0)
    (fun w => by
      simp only [Finsupp.sum]
      exact Finset.sum_eq_zero fun g _ => by rw [zero_mul, zero_mul])
    (fun w m n => by
      rw [← Finsupp.sum_add]
      exact Finsupp.sum_congr fun g _ => by ring)).symm
  refine Finsupp.sum_congr fun wb _ => ?_
  exact (fTransform_sum_finsupp blindDDG S
      (fun g' p => W wb * p *
        if (gameStructure X PUnit q).win wb g' then (1 : NNReal) else 0)
      (fun g' => by simp)
      (fun g' m n => by ring)).trans
    (Finsupp.sum_congr fun g _ => congrArg (fun z => W wb * S g * z)
      (if_congr (by rw [win_blindDDG_iff]) rfl rfl))

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))] in
/-- **CR18 Definition 4.20 key property (hBridge ELIMINATED)**: the maximal
winning probability for the blinded game `bS` is at most the maximal winning
probability for the original game `S`,

  `Γ(bS) ≤ Γ(S)`.

This formalizes Maurer's statement (source line 5620–5621):
  "The best probability in winning a game S non-adaptively (i.e., Γ(bS)) is
   generally lower than the best probability in winning it adaptively
   (i.e., Γ(S))."

Since a winner of `bS` receives no `Y` information, it cannot adapt its
queries to the system's responses; its unblinded reading is a (generally
non-optimal) adaptive winner of `S` with the SAME winning probability
(`winProb_blindPDG`), so the sup over blind winners is dominated.  The former
`hBridge` hypothesis is GONE — its content is `win_blindDDG_iff` +
`winProb_blindPDG`. -/
theorem blindGame_maxWinProb_le (q : ℕ) [DecidableEq (DDG X PUnit)]
    (S : PDG X Y) (hS : S.sum (fun _ p => p) = 1) :
    Def417.maxWinProb (gameStructure X PUnit q) (blindGame S) ≤
      Def417.maxWinProb (gameStructure X Y q) S := by
  apply Def417.maxWinProb_le_of_forall_le
  · -- Nonempty: the trivial blind winner (point mass, weight 1).
    refine ⟨_, ⟨Finsupp.single
      ((fun _ _ => default) : Strategy X PUnit q) 1, ?_, rfl⟩⟩
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  · intro W hW
    rw [winProb_blindPDG q S W]
    refine Def417.winProb_le_maxWinProb _ _ hS _ ?_
    show (Dist.fTransform (unblind (Y := Y)) W :
      Dist (Strategy X Y q)).weight = 1
    rw [Dist.weight_fTransform]
    exact hW

end Concrete

end Def420

end RandomSystems.CR18

/-!
## CR18 Definition 4.21 — T̃ (T with MBO): the query-copying converter and T̂

CR18 §4.11.1 (source line 5636–5643):

> **Definition 4.21.**  For a system T, let T̃ denote the converter which is
> identical to T at the left interface but, in addition, **copies all queries
> from the left interface to the (system connected to the) right interface**.
> It ignores replies received at the right interface.

The converter T̃ is used in the proof of Theorem 4.17 to enhance the plain
system T with an MBO borrowed from the game Ŝ:

  **T̂ := T̃ ∘ Ŝ**

Concretely (per the proof of Theorem 4.17, source lines 5680–5688 in
`CR18_LN.pdf`):

  `p^{T̂}_{Yⁱ, Aᵢ | Xⁱ} = p^T_{Yⁱ | Xⁱ} · p^{Ŝ}_{Aᵢ | Xⁱ}`

i.e. T̂'s Y-output is T's output, and T̂'s MBO bit is Ŝ's MBO bit, **independently**.

### Key properties

* `T̂⁻ = T` — stripping T̂'s MBO recovers T (used in Theorem 4.17 step 1).
* The MBO of T̂ is exactly Ŝ's MBO: `T̂.binaryOutput l = g.binaryOutput l`.
* Under conditional equivalence `Ŝ |≡ T`, we have `Ŝ ≡_g T̂` (game equivalence,
  CR18 eq. 4.39) — this is the key consequence used in Theorem 4.17.

### Design

We formalize T̂ at two levels:

* **Deterministic layer** (`DDS.enhanceDDG`): given a `DDS X Y` (the system T)
  and a `DDG X Y` (the game Ŝ) that share the same domain, produce the `DDG X Y`
  whose Y-output is T's output and whose MBO bit is Ŝ's bit.  This is T̂ at the
  deterministic level.

* **Probabilistic layer** (`PDS.enhancePDG`): lift `DDS.enhanceDDG` to the
  probabilistic level using the joint distribution of `(t, g)` pairs.  Given a
  `PDS X Y` (the system T) and a `PDG X Y` (the game Ŝ), a coupling
  `κ : Dist (DDS X Y × DDG X Y)` pairs up their realizations, and `enhancePDG`
  maps each pair to the corresponding deterministic T̂.

The probabilistic layer is stated with an explicit coupling `κ` rather than the
product measure, to allow the general (possibly correlated) case that Maurer's
prose describes.
-/

namespace RandomSystems.CR18

namespace Def421

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Deterministic layer: DDS + DDG → DDG (T̂) -/

/-- CR18 Definition 4.21 (deterministic layer): **enhance** a system `t : DDS X Y`
with the MBO of a game `g : DDG X Y` (sharing the same domain) to produce the
game T̂.

The resulting `DDG X Y` has:
- domain = `t.dom` (= `g.toSystem.dom`, given `hdom : t.dom = g.toSystem.dom`)
- Y-output at history `l` = `t.respond l`  (T's own response)
- MBO bit at history `l` = `(g.toSystem.respond l).2` (Ŝ's MBO bit, copied by T̃)

This is the "T̂" constructed in the proof of Theorem 4.17 (CR18 source line 5606):
  `p^{T̂}_{Yⁱ Aᵢ | Xⁱ} = p^T_{Yⁱ | Xⁱ} · p^{Ŝ}_{Aᵢ | Xⁱ}`

The MBO invariant is inherited directly from `g.mbo`. -/
def enhanceDDG (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) : DDG X Y where
  toSystem := {
    dom           := t.dom
    nonempty_input := t.nonempty_input
    prefix_closed  := t.prefix_closed
    respond        := fun l hl =>
      -- Y-output from t; MBO bit from g (queries copied by T̃)
      (t.respond l hl, (g.toSystem.respond l (hdom ▸ hl)).2)
  }
  mbo := by
    -- The MBO invariant: inherited from g (the bit component is exactly g's bit)
    intro l hl i j hij hj ⟨hi_dom, ha⟩
    simp only at ha
    -- hi_dom is a proof that l.take (i+1) ∈ t.dom
    -- ha says the bit at l.take (i+1) is true, which (by construction) is g's bit
    -- We need: ∃ hj_dom, g.toSystem.respond (l.take (j+1)) hj_dom |>.2 = true
    have hi_g : l.take (i + 1) ∈ g.toSystem.dom := hdom ▸ hi_dom
    have ha_g : (g.toSystem.respond (l.take (i + 1)) hi_g).2 = true := ha
    have hg_mbo := g.mbo l (hdom ▸ hl) i j hij hj ⟨hi_g, ha_g⟩
    obtain ⟨hj_g, hj_bit⟩ := hg_mbo
    exact ⟨hdom.symm ▸ hj_g, hj_bit⟩

/-! ### Basic lemmas about enhanceDDG -/

/-- The domain of T̂ equals the domain of the original system T. -/
@[simp]
theorem enhanceDDG_dom_eq (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) :
    (enhanceDDG t g hdom).toSystem.dom = t.dom := rfl

/-- The Y-output of T̂ at history `l` equals T's response. -/
@[simp]
theorem enhanceDDG_regularOutput (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom)
    (l : List X) (hl : l ∈ (enhanceDDG t g hdom).toSystem.dom) :
    (enhanceDDG t g hdom).regularOutput l hl = t.respond l hl := rfl

/-- The MBO bit of T̂ at history `l` equals Ŝ's MBO bit at `l`. -/
@[simp]
theorem enhanceDDG_binaryOutput (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom)
    (l : List X) (hl : l ∈ (enhanceDDG t g hdom).toSystem.dom) :
    (enhanceDDG t g hdom).binaryOutput l hl =
      (g.toSystem.respond l (hdom ▸ hl)).2 := rfl

/-- Stripping T̂'s MBO recovers T.

CR18 identity: `T̂⁻ = T`.  The strip operation projects out the Bool component,
leaving exactly T's respond function on T's domain.

This is used in the proof of Theorem 4.17 (step "Ŝ⁻ = S and T̂⁻ = T"). -/
theorem enhanceDDG_strip_eq (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) :
    DDG.strip (enhanceDDG t g hdom) = t := by
  simp [DDG.strip, enhanceDDG]

/-! ### Probabilistic layer: PDS + PDG → PDG (T̂ as a game)

At the probabilistic level, T is a `PDS X Y` and Ŝ is a `PDG X Y`.  Maurer's
construction pairs each realization `t : DDS X Y` of T with a realization
`g : DDG X Y` of Ŝ and applies `enhanceDDG` to produce a `DDG X Y` (a
realization of T̂).  The joint distribution over `(t, g)` pairs is a **coupling**
`κ : Dist (DDS X Y × DDG X Y)`.

We require `κ` to be a coupling of `T` and `Ŝ` (i.e., its marginals are `T`
and `Ŝ` respectively) and that every pair `(t, g)` in the support of `κ` has
equal domains (so `enhanceDDG t g (hdom t g)` is well-typed).

In the proof of Theorem 4.17, Maurer uses the **product** coupling (T and Ŝ are
independent), but the construction is valid for any coupling.
-/

/-- Trivial placeholder game built directly from a system `t : DDS X Y`:
its Y-output is `t`'s output and its MBO bit is always `false`.

This is a *valid* `DDG X Y` for **any** `t` (no domain-matching hypothesis is
needed), because an all-`false` binary output is vacuously monotone (the MBO
invariant's antecedent `(respond ..).2 = true` is never satisfied).

It is used only as the out-of-support fallback in `enhancePDG`: out-of-support
pairs carry weight `0` and never influence the resulting distribution, so the
choice of fallback is immaterial to the distribution.  Crucially, building this
fallback needs **no** `t.dom = g.toSystem.dom` proof, so `enhancePDG` is total
and `sorry`-free. -/
def trivialDDG (t : DDS X Y) : DDG X Y where
  toSystem := {
    dom            := t.dom
    nonempty_input := t.nonempty_input
    prefix_closed  := t.prefix_closed
    respond        := fun l hl => (t.respond l hl, false)
  }
  mbo := by
    -- All-`false` MBO bit: the antecedent `(respond ..).2 = true` is `false = true`.
    intro l hl i j hij hj ⟨hi_dom, ha⟩
    simp only at ha
    exact absurd ha (by simp)

/-- CR18 Definition 4.21 (probabilistic layer): **enhance** a PDS `T` with the
MBO of a PDG `Ŝ` to produce the game T̂.

Given a coupling `κ : Dist (DDS X Y × DDG X Y)` of `T` and `Ŝ` such that every
`(t, g)` in `κ`'s support has equal domains, `enhancePDG κ hdomComp` is the
`PDG X Y` obtained by mapping each `(t, g)` pair to `enhanceDDG t g (hdomComp t g ·)`.

For pairs **outside** `κ`'s support (which carry weight `0` and so never affect
the resulting distribution) the domain-matching hypothesis is unavailable, so we
map to the `sorry`-free fallback `trivialDDG t` (which needs no such hypothesis).

Key properties:
- `(enhancePDG κ hdomComp)⁻ = T`  (strip recovers T; CR18: `T̂⁻ = T`)
- The MBO bits of T̂ match Ŝ's MBO bits at every history. -/
noncomputable def enhancePDGRealization
    (κ : Dist (DDS X Y × DDG X Y))
    (hdomComp : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ κ.support → t.dom = g.toSystem.dom) :
    DDS X Y × DDG X Y → DDG X Y :=
  fun ⟨t, g⟩ =>
    by
      classical
      exact
        if h : ∃ _ : (t, g) ∈ κ.support, True then
          -- In-support pair: enhance T with Ŝ's MBO (domains match by `hdomComp`).
          enhanceDDG t g (hdomComp t g h.choose)
        else
          -- Out-of-support pair (weight 0, never sampled): use a domain-proof-free
          -- placeholder.  This keeps `enhancePDG` total WITHOUT asserting the false
          -- claim `t.dom = g.toSystem.dom` for arbitrary out-of-support `(t, g)`.
          trivialDDG t

/-- CR18 Definition 4.21 (probabilistic layer): push the coupling through the
realization-level enhancement map. -/
noncomputable def enhancePDG
    (κ : Dist (DDS X Y × DDG X Y))
    [DecidableEq (DDG X Y)]
    (hdomComp : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ κ.support → t.dom = g.toSystem.dom) :
    PDG X Y :=
  Dist.fTransform (enhancePDGRealization κ hdomComp) κ

/-! ### Key behavioral property: T̂⁻ = T at the probabilistic level

The stripping lemma at the probabilistic level states that the PDG T̂ enhanced
from T has the same distribution over `DDS X Y` as T itself, i.e. `(T̂)⁻ = T`.
This is CR18's `T̂⁻ = T` identity (used in Theorem 4.17 step 1).
-/

/-- CR18 Definition 4.21: key property — stripping T̂'s MBO recovers T.

For the deterministic layer: `(enhanceDDG t g hdom).strip = t`.
This is `enhanceDDG_strip_eq` above.

At the probabilistic level, the statement is:
  `PDG.strip (enhancePDG κ hdomComp) = T`
where `T = Dist.fTransform Prod.fst κ` (the first marginal of `κ`).

This deterministic identity is fully proved by the defining equation
`enhanceDDG_strip_eq`; the corresponding probabilistic strip identity for a
coupling is handled later by `strip_enhancePDG`. -/
theorem enhanceDDG_strip_eq' (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) :
    DDG.strip (enhanceDDG t g hdom) = t :=
  enhanceDDG_strip_eq t g hdom

/-- CR18 Definition 4.21: T̂'s MBO at history `l` is exactly Ŝ's MBO at `l`.

This is the key property used to establish `Ŝ ≡_g T̂` (game equivalence) from
conditional equivalence `Ŝ |≡ T` (CR18 eq. 4.39):
  `p^{T̂}_{Aᵢ | Xⁱ Yⁱ} = p^{Ŝ}_{Aᵢ | Xⁱ}`.

At the deterministic level: `(enhanceDDG t g hdom).binaryOutput l hl = (g.toSystem.respond l (hdom ▸ hl)).2`.
This is `enhanceDDG_binaryOutput` above. -/
theorem enhanceDDG_mbo_eq_game (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom)
    (l : List X) (hl : l ∈ (enhanceDDG t g hdom).toSystem.dom) :
    (enhanceDDG t g hdom).binaryOutput l hl =
      g.binaryOutput l (hdom ▸ hl) := by
  simp [DDG.binaryOutput, enhanceDDG]

/-- CR18 Definition 4.21: T̂'s regular output at history `l` equals T's output.

This confirms that T̂ is "T at the left interface": the Y-component is unchanged
from T, only the MBO (Bool component) is borrowed from Ŝ. -/
theorem enhanceDDG_output_eq_system (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom)
    (l : List X) (hl : l ∈ (enhanceDDG t g hdom).toSystem.dom) :
    (enhanceDDG t g hdom).toSystem.respond l hl =
      (t.respond l hl, (g.toSystem.respond l (hdom ▸ hl)).2) := rfl

/-- CR18 Definition 4.21: the MBO of T̂ is the same as the MBO of Ŝ.

The `DDG.IsWon` predicate for T̂ coincides with the `DDG.IsWon` predicate for Ŝ,
since T̂'s MBO bit is exactly Ŝ's bit at every history. -/
theorem enhanceDDG_isWon_iff (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom)
    (l : List X) (hl : l ∈ (enhanceDDG t g hdom).toSystem.dom) :
    DDG.IsWon (enhanceDDG t g hdom) l hl ↔
      DDG.IsWon g l (hdom ▸ hl) := by
  simp [DDG.IsWon, DDG.binaryOutput, enhanceDDG]

end Def421

end RandomSystems.CR18

/-!
## CR18 Theorem 4.17 — the `Γ(b·Ŝ)` sharpening (Maurer's full strength)

Maurer's Theorem 4.17 concludes `∆(S, T) ≤ Γ(bŜ)` — the **blind**
(non-adaptive) maximal winning probability — not merely `Γ(Ŝ)`.  The printed
chain (CR18 §4.11.1–4.11.2, source ~5600–5700) is

  `⟨S|T⟩(D) = ⟨Ŝ⁻|T̂⁻⟩(D) ≤ Ŝ(D) = T̂(D) = (T̃bŜ)(D) = bŜ(DT̃) ≤ Γ(bŜ)`,

where the fourth step is eq (4.40), `T̂ = T̃bŜ`: the enhanced game generates
the outputs `Yᵢ` and the MBOs `Aᵢ` **independently** (by `T` and `Ŝ`
respectively), and the fifth step absorbs the converter `T̃` into the winner —
the composite winner `DT̃` answers `D`'s queries from `T` and forwards them to
`bŜ`, **never seeing `Ŝ`'s outputs**: it is a BLIND winner of `bŜ`.

### Lean rendering

* The independent enhancement `T̂` is `Def421.enhancePDG` at the **product
  coupling** `Dist.prod T Ŝ` (eq 4.40 is the independence of the coupling).
* `T̂⁻ = T` is now PROVEN (`Def421.strip_enhancePDG` + `fst_fTransform_prod`),
  so the former `hStrip` hypothesis of `Thm417.delta_le_gamma` disappears.
* The blind winner `DT̃` is, per realization `(w, t)` of (strategy, `T`), the
  oblivious strategy `constStrategy (pathList w t q)` committed to the
  interaction path of `w` against `t` — the path depends on `(w, t)` ONLY
  (`Lem416.pathList`).  The deterministic core
  `win_enhanceDDG_eq_win_blind` shows the eq-4.37 winning events coincide,
  and `winProb_enhanceProd_le_blind_maxWinProb` mixes it over `W, T, Ŝ`.
* CR18 eq. (4.39), `Ŝ ≡_g T̂`, is now derived internally from
  `Ŝ |≡ T`; Lean asks for `PDS.TotalOnNonempty T`, the support-level
  totality condition that derives the normalizer `PDS.massDom T xs = 1` for
  nonempty histories in the partial-system model. `hdomC` is the coupling
  well-formedness of the Def-4.21 construction (every paired `(t, g)` shares
  its query domain).

The weaker `Γ(Ŝ)` bound remains available as a trivial corollary via
`Γ(bŜ) ≤ Γ(Ŝ)` (`Def420.blindGame_maxWinProb_le`); see
`delta_le_gamma_of_blind` below and the original abstract-`That` versions in
the `Thm417` section above.
-/

namespace RandomSystems.CR18

namespace Def421

universe u v

variable {X : Type u} {Y : Type v}

/-! ### Strip and mass bookkeeping for the probabilistic enhancement -/

/-- Stripping the out-of-support placeholder game recovers the underlying
system: the constant-`false` MBO bit is projected away. -/
theorem strip_trivialDDG (t : DDS X Y) : DDG.strip (trivialDDG t) = t := by
  simp [DDG.strip, trivialDDG]

/-- **CR18 Theorem 4.17, proof step 1 (`T̂⁻ = T`) at the probabilistic
level**: stripping the enhanced game recovers the first marginal of the
coupling.  Both branches of the `enhancePDG` realization map strip to the
system component — in-support pairs via `enhanceDDG_strip_eq`, the
out-of-support placeholder via `strip_trivialDDG` — so the composite is the
first projection. -/
theorem strip_enhancePDG [DecidableEq (DDG X Y)]
    (κ : Dist (DDS X Y × DDG X Y))
    (hdomComp : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ κ.support → t.dom = g.toSystem.dom) :
    PDG.strip (enhancePDG κ hdomComp) = Dist.fTransform Prod.fst κ := by
  show Dist.fTransform DDG.strip
      (Dist.fTransform (enhancePDGRealization κ hdomComp) κ) = _
  rw [Dist.fTransform_comp]
  congr 1
  funext p
  show DDG.strip (enhancePDGRealization κ hdomComp p) = p.1
  simp only [enhancePDGRealization]
  split
  · exact enhanceDDG_strip_eq p.1 p.2 _
  · exact strip_trivialDDG p.1

/-- The enhancement preserves the total Finsupp mass of the coupling: a
weight-1 coupling yields a weight-1 enhanced game (the Def-4.5 hypothesis of
Lemma 4.16). -/
theorem enhancePDG_mass [DecidableEq (DDG X Y)]
    (κ : Dist (DDS X Y × DDG X Y))
    (hdomComp : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ κ.support → t.dom = g.toSystem.dom) :
    (enhancePDG κ hdomComp).sum (fun _ p => p) = κ.sum (fun _ p => p) :=
  Lem416.fTransform_mass _ κ

/-! ### The pre-winning DDS of the enhancement -/

/-- The pre-winning domain of the enhanced game `T̂ = enhanceDDG t g` equals
the pre-winning domain of the game `g` itself: the enhancement keeps `g`'s
MBO bits and (by the Def-4.21 hypothesis) `g`'s query domain, changing only
the regular `Y`-outputs — which the pre-winning DOMAIN does not consult. -/
theorem preWinningDDS_enhanceDDG_dom (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) :
    (Def415.preWinningDDS (enhanceDDG t g hdom)).dom =
      (Def415.preWinningDDS g).dom := by
  ext l
  rw [Def415.mem_preWinningDDS_dom_iff, Def415.mem_preWinningDDS_dom_iff]
  constructor
  · rintro ⟨hl, hbits⟩
    refine ⟨hdom ▸ hl, fun k hk => ?_⟩
    obtain ⟨hpfx, hbit⟩ := hbits k hk
    exact ⟨hdom ▸ hpfx, hbit⟩
  · rintro ⟨hl, hbits⟩
    refine ⟨hdom.symm ▸ hl, fun k hk => ?_⟩
    obtain ⟨hpfx, hbit⟩ := hbits k hk
    exact ⟨hdom.symm ▸ hpfx, hbit⟩

/-- The pre-winning DDS of the enhancement is a **refinement of the system
`t`**: a sub-domain on which it responds exactly as `t` (the enhancement's
regular output is `t`'s output, and pre-winning restriction only shrinks the
domain).  This is the `hsub` hypothesis shape consumed by the
`pathList_congr_refine_*` lemmas. -/
theorem preWinningDDS_enhanceDDG_refines (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) :
    ∀ (l : List X)
      (hl : l ∈ (Def415.preWinningDDS (enhanceDDG t g hdom)).dom),
      ∃ hlt : l ∈ t.dom,
        (Def415.preWinningDDS (enhanceDDG t g hdom)).respond l hl =
          t.respond l hlt := fun _ hl =>
  ⟨Def415.preWinningDDS_dom_subset _ hl, rfl⟩

/-- **Deterministic core of CR18 eq. (4.39)**: if the concrete game `g` is
conditionally equivalent to the concrete system `t`, then replacing `g`'s
visible output by `t`'s output while keeping `g`'s MBO does not change the
pre-winning DDS.

The proof is the lecture-note calculation in deterministic form:
the pre-winning domains agree because `enhanceDDG` copies `g`'s MBO bits, and
on that domain the terminal MBO bit is `false`, so `g |≡_det t` rewrites the
visible output to `t`'s output. -/
theorem preWinningDDS_eq_enhanceDDG_of_condEquiv (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) (hcond : Def419.DDG.CondEquiv g t) :
    Def415.preWinningDDS g = Def415.preWinningDDS (enhanceDDG t g hdom) := by
  apply DDS.ext
  · exact (preWinningDDS_enhanceDDG_dom t g hdom).symm
  · intro l hs ht
    obtain ⟨hlt, hrespT⟩ := preWinningDDS_enhanceDDG_refines t g hdom l ht
    rw [DDS.output, Def415.preWinningDDS_respond]
    exact (hcond l (Def415.preWinningDDS_dom_subset g hs) hlt
      (Def415.preWinningDDS_bit_false g l hs)).trans hrespT.symm

/-- Event split for the deterministic enhanced game.

For a nonempty input history, the enhanced pre-winning DDS produces visible
transcript `ys` exactly when the system component `t` produces `ys` and the
game component `g` is still pre-winning on that input history.  This is the
pointwise event identity behind the product factorization in CR18 eq. (4.39). -/
theorem outputSeq_preWinningDDS_enhanceDDG_iff (t : DDS X Y) (g : DDG X Y)
    (hdom : t.dom = g.toSystem.dom) {xs : List X} {ys : List Y} (hxs : xs ≠ []) :
    (Def415.preWinningDDS (enhanceDDG t g hdom)).outputSeq xs = ys.map some ↔
      t.outputSeq xs = ys.map some ∧ xs ∈ (Def415.preWinningDDS g).dom := by
  constructor
  · intro hout
    have hlen := Lem416.length_eq_of_outputSeq hout
    have hpos : 0 < xs.length := by
      cases xs with
      | nil => exact False.elim (hxs rfl)
      | cons _ _ => simp
    have hlast : xs.length - 1 < xs.length := by omega
    have hxs_dom_enh : xs ∈ (Def415.preWinningDDS (enhanceDDG t g hdom)).dom := by
      have hentry := Lem416.outputSeq_entry_dom hout hlast
      have htake : xs.take (xs.length - 1 + 1) = xs := by
        have : xs.length - 1 + 1 = xs.length := by omega
        rw [this, List.take_length]
      rwa [htake] at hentry
    have hxs_dom_g : xs ∈ (Def415.preWinningDDS g).dom := by
      rwa [preWinningDDS_enhanceDDG_dom t g hdom] at hxs_dom_enh
    have htout : t.outputSeq xs = ys.map some := by
      refine Lem416.outputSeq_eq_map_some hlen ?_ ?_
      · intro k hk
        have hpfx_enh := Lem416.outputSeq_entry_dom hout hk
        exact (preWinningDDS_enhanceDDG_refines t g hdom
          (xs.take (k + 1)) hpfx_enh).choose
      · intro k hk
        have hpfx_enh := Lem416.outputSeq_entry_dom hout hk
        obtain ⟨hlt, hresp⟩ := preWinningDDS_enhanceDDG_refines t g hdom
          (xs.take (k + 1)) hpfx_enh
        have hv := Lem416.outputSeq_entry_respond hout hk hpfx_enh
        exact hresp.symm.trans hv
    exact ⟨htout, hxs_dom_g⟩
  · rintro ⟨htout, hxs_dom_g⟩
    have hlen := Lem416.length_eq_of_outputSeq htout
    refine Lem416.outputSeq_eq_map_some hlen ?_ ?_
    · intro k hk
      have hpfx_g : xs.take (k + 1) ∈ (Def415.preWinningDDS g).dom := by
        refine (Def415.preWinningDDS g).prefix_closed (List.take_prefix _ _) ?_ hxs_dom_g
        exact List.ne_nil_of_length_pos (by simp [hk])
      rwa [preWinningDDS_enhanceDDG_dom t g hdom]
    · intro k hk
      have hpfx_enh :
          xs.take (k + 1) ∈ (Def415.preWinningDDS (enhanceDDG t g hdom)).dom := by
        have hpfx_g : xs.take (k + 1) ∈ (Def415.preWinningDDS g).dom := by
          refine (Def415.preWinningDDS g).prefix_closed
            (List.take_prefix _ _) ?_ hxs_dom_g
          exact List.ne_nil_of_length_pos (by simp [hk])
        rwa [preWinningDDS_enhanceDDG_dom t g hdom]
      obtain ⟨hlt, hresp⟩ := preWinningDDS_enhanceDDG_refines t g hdom
        (xs.take (k + 1)) hpfx_enh
      have htv := Lem416.outputSeq_entry_respond htout hk hlt
      exact hresp.trans htv

/-- The pre-winning visible-transcript event is contained in the `Aᵢ = 0`
event.  For nonempty histories, any realization counted by
`p^S_{Y^i,A_i=0|X^i}` must have the full input history in the pre-winning
domain, hence in the original domain with terminal MBO bit `false`. -/
theorem massYAfalse_le_massAfalse [DecidableEq (List (Option Y))]
    (S : PDG X Y) (xs : List X) (ys : List Y) (hxs : xs ≠ []) :
    Def419.PDG.massYAfalse S xs ys ≤ Def419.PDG.massAfalse S xs := by
  classical
  rw [Def419.PDG.massYAfalse, Def419.PDG.massAfalse, Def415.preWinningPDS,
    Lem416.jointProb_fTransform]
  refine Finsupp.sum_le_sum fun g _ => ?_
  by_cases hout : (Def415.preWinningDDS g).outputSeq xs = ys.map some
  · have hpos : 0 < xs.length := by
      cases xs with
      | nil => exact False.elim (hxs rfl)
      | cons _ _ => simp
    have hlast : xs.length - 1 < xs.length := by omega
    have hxs_dom_pre : xs ∈ (Def415.preWinningDDS g).dom := by
      have hentry := Lem416.outputSeq_entry_dom hout hlast
      have htake : xs.take (xs.length - 1 + 1) = xs := by
        have : xs.length - 1 + 1 = xs.length := by omega
        rw [this, List.take_length]
      rwa [htake] at hentry
    have hxs_dom : xs ∈ g.toSystem.dom :=
      Def415.preWinningDDS_dom_subset g hxs_dom_pre
    have hbit : (g.toSystem.respond xs hxs_dom).2 = false :=
      Def415.preWinningDDS_bit_false g xs hxs_dom_pre
    simp [hout, hxs_dom, hbit]
  · simp [hout]

/-- **CR18 eq. (4.39), independent-enhancement factorization, nonempty form.**

For nonempty input histories, the pre-winning transcript mass of the independently
enhanced game `T̂ = T̃ ∘ S` factors into the visible-output mass of `T` and the
not-yet-won mass of `S`:

`p^{T̂}_{Y^i,A_i=0|X^i}(ys,xs) = p^T_{Y^i|X^i}(ys,xs) · p^S_{A_i=0|X^i}(xs)`.

The proof is pure `Dist` algebra: expand the two pushforwards, use
  `outputSeq_preWinningDDS_enhanceDDG_iff` to split the event, then factor the
  independent product sum. -/
theorem jointProb_preWinningPDS_enhancePDG_prod
    [DecidableEq (DDG X Y)] [DecidableEq (List (Option Y))]
    (T : PDS X Y) (S : PDG X Y)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T S).support → t.dom = g.toSystem.dom)
    (xs : List X) (ys : List Y) (hxs : xs ≠ []) :
    jointProb (Def415.preWinningPDS (enhancePDG (Dist.prod T S) hdomC)) xs ys =
      Def419.PDS.massY T xs ys * Def419.PDG.massAfalse S xs := by
  classical
  rw [Def415.preWinningPDS, enhancePDG]
  simp only [jointProb, jointOutputDist]
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Lem416.fTransform_apply_finsupp]
  simp only [Function.comp_apply]
  refine (Lem416.prod_sum_finsupp (A := T) (B := S)
    (F := fun p w =>
      if (Def415.preWinningDDS
          (enhancePDGRealization (Dist.prod T S) hdomC p)).outputSeq xs =
          ys.map some then w else 0)
    (by intro p; simp)
    (by
      intro p m n
      by_cases h : (Def415.preWinningDDS
          (enhancePDGRealization (Dist.prod T S) hdomC p)).outputSeq xs =
          ys.map some <;>
        simp [h])).trans ?_
  rw [Def419.PDS.massY, Def419.PDG.massAfalse]
  simp only [jointProb, jointOutputDist]
  rw [Lem416.fTransform_apply_finsupp]
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun t htSupp => ?_
  by_cases htout : t.outputSeq xs = ys.map some
  · rw [if_pos htout]
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun g hgSupp => ?_
    have hpSupport : (t, g) ∈ (Dist.prod T S).support := by
      rw [Finsupp.mem_support_iff, Dist.prod_apply]
      intro hzero
      exact mul_ne_zero (Finsupp.mem_support_iff.mp htSupp)
        (Finsupp.mem_support_iff.mp hgSupp) hzero
    have hbranch :
        enhancePDGRealization (Dist.prod T S) hdomC (t, g) =
          enhanceDDG t g (hdomC t g hpSupport) := by
      simp only [enhancePDGRealization]
      split
      · congr 1
      · exfalso
        exact ‹¬∃ _ : ((t, g) : DDS X Y × DDG X Y) ∈ (Dist.prod T S).support, True›
          ⟨hpSupport, trivial⟩
    rw [hbranch]
    have hevent :
        ((Def415.preWinningDDS (enhanceDDG t g (hdomC t g hpSupport))).outputSeq xs =
          ys.map some) ↔ xs ∈ (Def415.preWinningDDS g).dom := by
      rw [outputSeq_preWinningDDS_enhanceDDG_iff t g (hdomC t g hpSupport) hxs]
      simp [htout]
    by_cases hgd : xs ∈ g.toSystem.dom
    · have hiff := Def415.mem_preWinningDDS_dom_iff_current_bit_false g xs hgd
      by_cases hbit : (g.toSystem.respond xs hgd).2 = false
      · have hpw : xs ∈ (Def415.preWinningDDS g).dom := hiff.mpr hbit
        rw [if_pos (hevent.mpr hpw), dif_pos hgd, if_pos hbit]
      · have hnpw : xs ∉ (Def415.preWinningDDS g).dom := fun hpw => hbit (hiff.mp hpw)
        rw [if_neg (fun h => hnpw (hevent.mp h)), dif_pos hgd, if_neg hbit]
        simp
    · have hnpw : xs ∉ (Def415.preWinningDDS g).dom :=
        fun hpw => hgd (Def415.preWinningDDS_dom_subset g hpw)
      rw [if_neg (fun h => hnpw (hevent.mp h)), dif_neg hgd]
      simp
  · rw [if_neg htout]
    simp
    refine Finset.sum_eq_zero fun g _hgSupp => ?_
    by_cases hp : (t, g) ∈ (Dist.prod T S).support
    · have hbranch :
          enhancePDGRealization (Dist.prod T S) hdomC (t, g) =
            enhanceDDG t g (hdomC t g hp) := by
        simp only [enhancePDGRealization]
        split
        · congr 1
        · exfalso
          exact ‹¬∃ _ : ((t, g) : DDS X Y × DDG X Y) ∈
              (Dist.prod T S).support, True› ⟨hp, trivial⟩
      dsimp only
      rw [hbranch]
      have hevent := outputSeq_preWinningDDS_enhanceDDG_iff t g (hdomC t g hp)
        (xs := xs) (ys := ys) hxs
      simp
      intro hout
      exact False.elim (htout (hevent.mp hout).1)
    · have hzero : T t * S g = 0 := by
        rw [← Dist.prod_apply T S t g]
        exact Finsupp.notMem_support_iff.mp hp
      simp [hzero]

/-- Nonempty, same-length form of CR18 eq. (4.39).

Once the independent enhancement has been factored as
`p^T_{Y^i|X^i} · p^S_{A_i=0|X^i}`, Def. 4.19 rewrites that product back to
`p^S_{Y^i,A_i=0|X^i}` on histories where `T`'s conditioning normalizer is 1.
This is the lecture-note calculation at (4.39), with the total-domain
normalizer made explicit for Lean's partial/sub-distribution model. -/
theorem jointProb_preWinningPDS_eq_enhancePDG_prod_of_condEquiv
    [DecidableEq (DDG X Y)] [DecidableEq (List (Option Y))]
    (S : PDG X Y) (T : PDS X Y)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T S).support → t.dom = g.toSystem.dom)
    (hcond : Def419.PDG.CondEquiv S T)
    (hTdom : ∀ xs : List X, xs ≠ [] → Def419.PDS.massDom T xs = 1)
    (xs : List X) (ys : List Y) (hxs : xs ≠ []) (hlen : ys.length = xs.length) :
    jointProb (Def415.preWinningPDS S) xs ys =
      jointProb (Def415.preWinningPDS (enhancePDG (Dist.prod T S) hdomC)) xs ys := by
  rw [jointProb_preWinningPDS_enhancePDG_prod T S hdomC xs ys hxs]
  change Def419.PDG.massYAfalse S xs ys =
    Def419.PDS.massY T xs ys * Def419.PDG.massAfalse S xs
  by_cases hA : Def419.PDG.massAfalse S xs = 0
  · have hle := massYAfalse_le_massAfalse S xs ys hxs
    have hle0 : Def419.PDG.massYAfalse S xs ys ≤ 0 := by
      simpa [hA] using hle
    have hz : Def419.PDG.massYAfalse S xs ys = 0 :=
      le_antisymm hle0 (zero_le _)
    simp [hz, hA]
  · have hD : Def419.PDS.massDom T xs ≠ 0 := by
      rw [hTdom xs hxs]
      exact one_ne_zero
    have h := hcond xs hxs ys hlen hA hD
    rwa [hTdom xs hxs, mul_one] at h

/-- CR18 eq. (4.39), with Lean's totality assumptions made explicit.

For a weight-1, total-on-history `T`, conditional equivalence `S |≡ T` implies
game equivalence between `S` and the independently enhanced game
`T̂ = enhancePDG (Dist.prod T S) hdomC`.  This is Maurer's
`Ŝ ≡g T̂` step: nonempty transcripts use
`jointProb_preWinningPDS_eq_enhancePDG_prod_of_condEquiv`, mismatched lengths
are zero on both sides, and the empty transcript is total-mass bookkeeping.
-/
theorem gameEquiv_enhancePDG_prod_of_condEquiv
    [DecidableEq (DDG X Y)] [DecidableEq (List (Option Y))]
    (S : PDG X Y) (T : PDS X Y)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T S).support → t.dom = g.toSystem.dom)
    (hcond : Def419.PDG.CondEquiv S T)
    (hTmass : T.sum (fun _ p => p) = 1)
    (hTtotal : Def419.PDS.TotalOnNonempty T) :
    Def416.GameEquiv S (enhancePDG (Dist.prod T S) hdomC) := by
  have hTdom := Def419.massDom_eq_one_of_totalOnNonempty T hTmass hTtotal
  apply Def416.gameEquiv_of_jointProb_preWinningPDS_eq
  intro xs ys
  by_cases hlen : ys.length = xs.length
  · cases xs with
    | nil =>
        have hys : ys = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using hlen)
        subst ys
        rw [RandomSystems.CR18.jointProb_nil_nil_eq_mass,
          RandomSystems.CR18.jointProb_nil_nil_eq_mass]
        simp [Def415.preWinningPDS, Lem416.fTransform_mass,
          enhancePDG_mass, Lem416.prod_mass, hTmass]
    | cons x xs' =>
        exact jointProb_preWinningPDS_eq_enhancePDG_prod_of_condEquiv
          S T hdomC hcond hTdom (x :: xs') ys (by simp) hlen
  · have hzero : ∀ G : PDG X Y,
        jointProb (Def415.preWinningPDS G) xs ys = 0 := by
      intro G
      rw [jointProb_eq_sum_support]
      refine Finset.sum_eq_zero fun s _ => if_neg fun hc => hlen ?_
      simpa [DDS.outputSeq] using (congrArg List.length hc).symm
    rw [hzero S, hzero (enhancePDG (Dist.prod T S) hdomC)]

end Def421

namespace Thm417

universe u v

section Blind

variable {X : Type u} {Y : Type v}
  [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

open Def45 Def47 Def416 Def417 Def419 Def420 Def421 Lem416

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
/-- **The induced winner is blind (deterministic core of CR18 eq 4.40)**: a
strategy `w` wins the enhanced game `T̂ = enhanceDDG t g` iff the oblivious
strategy committed to the interaction path of `w` against `t` wins the
blinded game `b·g`.

The winning events are literally the same event: the pre-winning DDS of the
enhancement refines `t` (same `Y`-responses, smaller domain), so its
interaction path is the path against `t` for as long as it stays in the
pre-winning domain (`pathList_congr_refine_*`); and the pre-winning DOMAINS
of `T̂` and of `b·g` are both `g`'s pre-winning domain
(`preWinningDDS_enhanceDDG_dom`, `preWinningDDS_blindDDG_dom`).  The
committed path never consults `g` — the induced winner is non-adaptive in the
game's outputs, exactly Maurer's "the inputs `x₁, …, x_q` can be interpreted
as being chosen in advance". -/
theorem win_enhanceDDG_eq_win_blind (q : ℕ) (w : Strategy X Y q)
    (t : DDS X Y) (g : DDG X Y) (hdom : t.dom = g.toSystem.dom) :
    (gameStructure X Y q).win w (enhanceDDG t g hdom) =
      (gameStructure X PUnit q).win
        (constStrategy q (pathList w t q)) (blindDDG g) := by
  rw [gameStructure_win, gameStructure_win, decide_eq_decide,
    completesAt_exists_iff_path_dom, completesAt_exists_iff_path_dom,
    not_iff_not]
  have hlenP : (pathList w t q).length = q := by
    rw [pathList_length]; omega
  have hPB : ∀ k, k ≤ q →
      pathList (constStrategy q (pathList w t q))
        (Def415.preWinningDDS (blindDDG g)) k = (pathList w t q).take k :=
    pathList_constStrategy hlenP _
  have hdomEq : (Def415.preWinningDDS (enhanceDDG t g hdom)).dom =
      (Def415.preWinningDDS (blindDDG g)).dom := by
    rw [preWinningDDS_enhanceDDG_dom, preWinningDDS_blindDDG_dom]
  constructor
  · intro h k hk
    have hcong := pathList_congr_refine_left
      (preWinningDDS_enhanceDDG_refines t g hdom) h
    rw [hPB (k + 1) (by omega),
      pathList_take w t (show k + 1 ≤ q by omega),
      ← hcong (k + 1) (by omega), ← hdomEq]
    exact h k hk
  · intro h k hk
    have hPdom : ∀ j, j < q →
        pathList w t (j + 1) ∈
          (Def415.preWinningDDS (enhanceDDG t g hdom)).dom := by
      intro j hj
      rw [hdomEq, ← pathList_take w t (show j + 1 ≤ q by omega),
        ← hPB (j + 1) (by omega)]
      exact h j hj
    have hcong := pathList_congr_refine_right
      (preWinningDDS_enhanceDDG_refines t g hdom) hPdom
    rw [hcong (k + 1) (by omega)]
    exact hPdom k hk

omit [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [DecidableEq X] [DecidableEq Y] [Fintype Y] in
/-- **The induced winner is blind (probabilistic, CR18 eq 4.40 +
"`DT̃` is a game winner")**: the winning probability of any probabilistic
winner `W` against the independently enhanced game `T̂` (the `enhancePDG` of
the PRODUCT coupling `T ⊗ Ŝ`) is at most the maximal **blind** winning
probability `Γ(bŜ)` — per realization `(w, t)` the induced winner of `bŜ` is
the oblivious strategy committed to `pathList w t q`, with the same winning
probability against `Ŝ`'s blinding. -/
theorem winProb_enhanceProd_le_blind_maxWinProb (q : ℕ)
    [DecidableEq (DDG X Y)] [DecidableEq (DDG X PUnit.{v + 1})]
    (Shat : PDG X Y) (T : PDS X Y)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T Shat).support → t.dom = g.toSystem.dom)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1)
    (W : Dist (Strategy X Y q)) (hW : W.sum (fun _ p => p) = 1) :
    (gameStructure X Y q).winProb W (enhancePDG (Dist.prod T Shat) hdomC) ≤
      Def417.maxWinProb (gameStructure X PUnit.{v + 1} q) (blindGame Shat) := by
  classical
  -- The blinded game is weight-1.
  have hbS : (blindPDG Shat).sum (fun _ p => p) = 1 := by
    rw [blindPDG_eq_fTransform, fTransform_mass]; exact hShat
  -- Per-(w, t): the induced oblivious strategy is a blind winner of `bŜ`.
  have hblind : ∀ (w : Strategy X Y q) (t : DDS X Y),
      (Shat.sum fun g gp =>
        gp * (if (gameStructure X PUnit q).win
            (constStrategy q (pathList w t q)) (blindDDG g)
          then (1 : NNReal) else 0)) ≤
        Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) := by
    intro w t
    have hkey : (gameStructure X PUnit q).winProb
        (Finsupp.single (constStrategy q (pathList w t q)) (1 : NNReal))
        (blindPDG Shat) =
        Shat.sum fun g gp =>
          gp * (if (gameStructure X PUnit q).win
              (constStrategy q (pathList w t q)) (blindDDG g)
            then (1 : NNReal) else 0) := by
      rw [Def45.GameStructure.winProb,
        Finsupp.sum_single_index (by
          simp only [Finsupp.sum]
          exact Finset.sum_eq_zero fun g _ => by rw [zero_mul, zero_mul])]
      refine Eq.trans (fTransform_sum_finsupp blindDDG Shat
        (fun g' gp => 1 * gp *
          (if (gameStructure X PUnit q).win
              (constStrategy q (pathList w t q)) g'
            then (1 : NNReal) else 0))
        (fun g' => by simp)
        (fun g' m n => by dsimp only; ring)) ?_
      exact Finsupp.sum_congr fun g _ => by dsimp only; rw [one_mul]
    rw [← hkey]
    refine Def417.winProb_le_maxWinProb _ _ hbS _ ?_
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  -- Reduce the enhanced-game winning probability to the (w, t, g) triple sum.
  have hG : ∀ (w : Strategy X Y q) (wp : NNReal),
      ((enhancePDG (Dist.prod T Shat) hdomC).sum fun g gp =>
          wp * gp *
            (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) =
        T.sum fun t tp => Shat.sum fun g gp =>
          wp * (tp * gp) *
            (if (gameStructure X PUnit q).win
                (constStrategy q (pathList w t q)) (blindDDG g)
              then (1 : NNReal) else 0) := by
    intro w wp
    refine Eq.trans (fTransform_sum_finsupp _ (Dist.prod T Shat)
      (fun g gp => wp * gp *
        (if (gameStructure X Y q).win w g then (1 : NNReal) else 0))
      (fun g => by simp)
      (fun g m n => by dsimp only; ring)) ?_
    refine Eq.trans (prod_sum_finsupp T Shat _
      (fun p => by simp)
      (fun p m n => by dsimp only; ring)) ?_
    refine Finsupp.sum_congr fun t ht => Finsupp.sum_congr fun g hg => ?_
    have hmem : (t, g) ∈ (Dist.prod T Shat).support := by
      rw [Finsupp.mem_support_iff, Dist.prod_apply]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp ht)
        (Finsupp.mem_support_iff.mp hg)
    have hbranch :
        enhancePDGRealization (Dist.prod T Shat) hdomC (t, g) =
          enhanceDDG t g (hdomC t g hmem) := by
      simp only [enhancePDGRealization]
      split
      · congr 1
      · exfalso
        exact ‹¬∃ _ : ((t, g) : DDS X Y × DDG X Y) ∈
            (Dist.prod T Shat).support, True› ⟨hmem, trivial⟩
    rw [hbranch]
    dsimp only
    rw [win_enhanceDDG_eq_win_blind q w t g (hdomC t g hmem)]
  -- Per-strategy block: bound by `Γ(bŜ)` and collapse the `T` mass.
  have hper : ∀ w : Strategy X Y q,
      ((enhancePDG (Dist.prod T Shat) hdomC).sum fun g gp =>
          W w * gp *
            (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) ≤
        W w * Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) := by
    intro w
    rw [hG w (W w)]
    calc (T.sum fun t tp => Shat.sum fun g gp =>
            W w * (tp * gp) *
              (if (gameStructure X PUnit q).win
                  (constStrategy q (pathList w t q)) (blindDDG g)
                then (1 : NNReal) else 0))
        = T.sum fun t tp => (W w * tp) *
            (Shat.sum fun g gp =>
              gp * (if (gameStructure X PUnit q).win
                  (constStrategy q (pathList w t q)) (blindDDG g)
                then (1 : NNReal) else 0)) := by
          refine Finsupp.sum_congr fun t _ => ?_
          rw [Finsupp.mul_sum]
          exact Finsupp.sum_congr fun g _ => by ring
      _ ≤ T.sum fun t tp => (W w * tp) *
            Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) :=
          Finsupp.sum_le_sum fun t _ => mul_le_mul_right (hblind w t) _
      _ = (W w * Def417.maxWinProb (gameStructure X PUnit q)
            (blindGame Shat)) * T.sum (fun _ p => p) := by
          rw [Finsupp.mul_sum]
          exact Finsupp.sum_congr fun t _ => by ring
      _ = W w * Def417.maxWinProb (gameStructure X PUnit q)
            (blindGame Shat) := by
          rw [hT, mul_one]
  -- Assemble: mix over the (weight-1) winner distribution.
  rw [Def45.GameStructure.winProb]
  calc (W.sum fun w wp =>
        (enhancePDG (Dist.prod T Shat) hdomC).sum fun g gp =>
          wp * gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0))
      ≤ W.sum fun w wp =>
          wp * Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) :=
        Finsupp.sum_le_sum fun w _ => hper w
    _ = (W.sum fun _ p => p) *
          Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) := by
        rw [← Finsupp.sum_mul]
    _ = Def417.maxWinProb (gameStructure X PUnit q) (blindGame Shat) := by
        rw [hW, one_mul]

/-! ### Theorem 4.17 at Maurer's full strength: `Δ(S, T) ≤ Γ(bŜ)` -/

/-- **CR18 Theorem 4.17 (per-distinguisher form, Maurer's full `Γ(bŜ)`
strength)**: with `T̂` the INDEPENDENT enhancement of `T` by `Ŝ`'s MBO
(Def 4.21 at the product coupling — CR18 eq 4.40 `T̂ = T̃bŜ`), conditional
equivalence gives `Ŝ ≡_g T̂` (CR18 eq 4.39) and hence, for every probabilistic
`q`-query distinguisher `D`,

  `⟨Ŝ⁻ | T⟩(D) ≤ Γ(bŜ)`

— the BLIND (non-adaptive) maximal winning probability.  Maurer's chain:
`⟨Ŝ⁻|T̂⁻⟩(D) ≤ Ŝ(D)` (Lemma 4.16) `= T̂(D)` (eq 4.39 + Lemma 4.15)
`= bŜ(DT̃) ≤ Γ(bŜ)` (eq 4.40 — the induced winner is blind,
`winProb_enhanceProd_le_blind_maxWinProb`).  The former `hStrip` hypothesis
is PROVEN (`strip_enhancePDG` + `fst_fTransform_prod`): stripping the
independent enhancement recovers `T`.

**CR18 reference:** Theorem 4.17 (source ~5600–5700), full proof chain. -/
theorem advantage_le_blind_maxWinProb (q : ℕ)
    [DecidableEq (DDG X Y)] [DecidableEq (DDG X PUnit.{v + 1})]
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T Shat).support → t.dom = g.toSystem.dom)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1)
    (hTtotal : Def419.PDS.TotalOnNonempty T)
    (D : (Lem416.distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D ≤
      (Def417.maxWinProb (gameStructure X PUnit.{v + 1} q)
        (blindGame Shat) : Real) := by
  set That := Def421.enhancePDG (Dist.prod T Shat) hdomC with hThatDef
  have hGameEquiv : Shat ≡_g That := by
    rw [hThatDef]
    exact Def421.gameEquiv_enhancePDG_prod_of_condEquiv
      Shat T hdomC hCondEquiv hT hTtotal
  -- The enhanced game is weight-1 (mass of the product coupling).
  have hThatMass : That.sum (fun _ p => p) = 1 := by
    rw [hThatDef, Def421.enhancePDG_mass, prod_mass, hT, hShat, mul_one]
  -- `T̂⁻ = T`: stripping recovers the first marginal (proven, not assumed).
  have hStrip : PDG.strip That = T := by
    rw [hThatDef, Def421.strip_enhancePDG, fst_fTransform_prod T Shat hShat]
  -- The distinguisher's querying strategy is a weight-1 winner.
  have hfstD : (Dist.fTransform Prod.fst D :
      Dist (Strategy X Y q)).sum (fun _ p => p) = 1 := by
    rw [fTransform_mass, ← Dist.weight_eq_finsupp_sum]
    exact hD
  calc (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D
      = (Lem416.distinctionStructure X Y q).performance
          (PDG.strip Shat, PDG.strip That) D := by rw [hStrip]
    _ ≤ ((gameStructure X Y q).winProb
          (Dist.fTransform Prod.fst D) Shat : Real) :=
        Lem416.advantage_le_winProb q Shat That hGameEquiv hShat hThatMass D
    _ = ((gameStructure X Y q).winProb
          (Dist.fTransform Prod.fst D) That : Real) := by
        norm_cast
        exact winProb_congr_gameEquiv q hGameEquiv hShat hThatMass _
    _ ≤ (Def417.maxWinProb (gameStructure X PUnit q)
          (blindGame Shat) : Real) := by
        exact_mod_cast winProb_enhanceProd_le_blind_maxWinProb q Shat T
          hdomC hShat hT (Dist.fTransform Prod.fst D) hfstD

/-- **CR18 Theorem 4.17 (delta form, Maurer's full `Γ(bŜ)` strength)**:

  `Δ(Ŝ⁻, T) = sup_D ⟨Ŝ⁻ | T⟩(D) ≤ Γ(bŜ)`,

the supremum over probability-distribution distinguishers, with the blind
(non-adaptive) maximal winning probability on the right.

**CR18 reference:** Theorem 4.17: "In particular, ∆(S, T) ≤ Γ(bŜ)."  The
additional `hTtotal` hypothesis is the Lean-side support-totality condition
that makes CR18's conditional distributions defined in the partial-system
model. -/
theorem delta_le_blind_gamma (q : ℕ)
    [DecidableEq (DDG X Y)] [DecidableEq (DDG X PUnit.{v + 1})]
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T Shat).support → t.dom = g.toSystem.dom)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1)
    (hTtotal : Def419.PDS.TotalOnNonempty T) :
    sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
        (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (gameStructure X PUnit.{v + 1} q)
        (blindGame Shat) : Real) := by
  apply csSup_le
  · -- Nonempty: the always-reject distinguisher (point mass, weight 1).
    refine ⟨_, ⟨Finsupp.single
      ((fun _ _ => default, fun _ => false) :
        Lem416.Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) 1,
      ?_, rfl⟩⟩
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  · rintro x ⟨D, hD, rfl⟩
    exact advantage_le_blind_maxWinProb q Shat T hCondEquiv hdomC
      hShat hT hTtotal D hD

/-- The weaker `Γ(Ŝ)` bound, recovered as a TRIVIAL corollary of the
`Γ(bŜ)` sharpening via `Γ(bŜ) ≤ Γ(Ŝ)` (`Def420.blindGame_maxWinProb_le`):
blinding only restricts the winner.  (The abstract-`That` version with the
same conclusion is `Thm417.delta_le_gamma` above.) -/
theorem delta_le_gamma_of_blind (q : ℕ)
    [DecidableEq (DDG X Y)] [DecidableEq (DDG X PUnit)]
    (Shat : PDG X Y) (T : PDS X Y)
    (hCondEquiv : Shat |≡ T)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T Shat).support → t.dom = g.toSystem.dom)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1)
    (hTtotal : Def419.PDS.TotalOnNonempty T) :
    sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
        (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (gameStructure X Y q) Shat : Real) :=
  le_trans
    (delta_le_blind_gamma q Shat T hCondEquiv hdomC hShat hT hTtotal)
    (by exact_mod_cast Def420.blindGame_maxWinProb_le q Shat hShat)

end Blind

end Thm417

end RandomSystems.CR18

/-!
## CR18 Definition 4.19′ / Theorem 4.17′ — one-sided conditional DOMINATION

The fundamental theorem needs only HALF of conditional equivalence.  Define
(Def 4.19′) the **conditional domination** `Ŝ |⊑ T`:

  `p^{Ŝ}_{Y^i, A_i=0 | X^i} ≤ p^{T}_{Y^i | X^i}`   pointwise, for all `i`

— the pre-winning (cumulative, eq-4.38 LHS) transcript masses of `Ŝ` are
dominated by `T`'s transcript masses.  In the `Dist` model this is the pure
sub-distribution comparison

  `jointProb (preWinningPDS Ŝ) xs ys ≤ jointProb T xs ys`

(the "preWinBehavior ≤ behavior" inequality; on Maurer's weight-1 total
systems the `X^i`-conditioning normalizers are `1`, so this IS the
conditional statement).  Conditional EQUIVALENCE gives it via the eq-4.38
factorization `p^{Ŝ}_{Y^i,A_i=0|X^i} = p^{Ŝ}_{A_i=0|X^i} · p^{T}_{Y^i|X^i}
≤ p^{T}_{Y^i|X^i}` — in the formalization the cumulative factorization
travels through the eq-4.39 enhanced game.  The abstract helper
`condDominates_of_gameEquiv` still accepts explicit `That`/`hGameEquiv`/`hStrip`
data for arbitrary enhanced games, while `condDominates_of_condEquiv_enhance`
uses Maurer's independent Def.-4.21 construction and derives that game
equivalence from `S |≡ T` plus support-totality of `T`.

**Theorem 4.17′ (one-sided fundamental lemma)**: `Ŝ |⊑ T` already implies

  `Δ(Ŝ⁻, T) ≤ Γ(Ŝ)`  —  BOTH signed directions.

*Proof (direction `T` minus `Ŝ⁻`)*: the keystone cancellation chain with the
equality step weakened to `≤`.  Per deterministic `(w, Z)`, additively in
`NNReal` (no truncated subtraction):

  `Pr^{DT}(Z=1) + Pr^{wŜ}(Aq=0)`
  `  ≤ Pr^{DŜ}(Z=1 ∧ Aq=0) + Pr^{wT}(completes)`     (termwise; the
       transcripts with `Z=1` swap sides AT EQUALITY, those with `Z=0` use
       domination — the decision indicator is dropped exactly because
       domination makes every summand comparison hold)
  `  ≤ Pr^{DŜ}(Z=1 ∧ Aq=0) + 1`
  `  = Pr^{DŜ}(Z=1 ∧ Aq=0) + Pr^{wŜ}(Aq=1) + Pr^{wŜ}(Aq=0)`   (eq 4.37)

and cancelling `Pr^{wŜ}(Aq=0)` gives
`Pr^{DT}(Z=1) ≤ Pr^{DŜ}(Z=1 ∧ Aq=0) + Ŝ(w)`; subtracting the partition
`Pr^{DŜ⁻}(Z=1) = Pr^{DŜ}(Z=1∧Aq=0) + Pr^{DŜ}(Z=1∧Aq=1)` yields
`⟨Ŝ⁻|T⟩(D) ≤ Ŝ(w) ≤ Γ(Ŝ)`.

*Proof (direction `Ŝ⁻` minus `T` — Maurer's symmetric direction, available
here directly by the anti-symmetry of the signed performance rather than via
complement-closure of the decision predicate)*: even simpler —
`Pr^{DŜ}(Z=1∧Aq=0) ≤ Pr^{DT}(Z=1)` termwise by domination, and
`Pr^{DŜ}(Z=1∧Aq=1) ≤ Ŝ(w)` is the keystone's `acceptWonProb_le_winProb_det`.

⚠ SHARPNESS (documented, NOT a deviation — Maurer never claims it): under
domination ALONE the bound canNOT be tightened to the blind `Γ(bŜ)`.
Counterexample: the adaptive guessing game — `Ŝ` draws `z` uniform, outputs
`y₁ = z`, MBO fires at round 2 iff `x₂ = z`, `y₂ = 0`; `T` outputs `y₁ = z`
and `y₂ = 1` iff `x₂ = z`.  Domination holds (the pre-winning transcripts of
`Ŝ` have `x₂ ≠ z, y₂ = 0`, mass `1/|Z|` each, equal to `T`'s mass there),
`Δ(Ŝ⁻, T) = 1` (query `x₂ = y₁` and read `y₂`), `Γ(Ŝ) = 1`, but
`Γ(bŜ) = 1/|Z|`.  The blind sharpening genuinely needs the eq-4.39
EQUALITY (the `Γ(bŜ)` theorems of the section above).

The equality-route Theorem 4.17 (`Γ(Ŝ)` bound) is rederived below as a
one-line corollary of 4.17′ + `condDominates_of_gameEquiv`
(`delta_le_gamma_of_condEquiv`) — with EXACTLY the hypothesis list of
`Thm417.delta_le_gamma`.
-/

namespace RandomSystems.CR18

namespace Def419'

universe u v

variable {X : Type u} {Y : Type v}

/-- **CR18 Definition 4.19′ (conditional domination)**: a PDG `S` is
**conditionally dominated** by a PDS `T`, written `S |⊑ T`, iff at every
visible transcript the pre-winning mass of `S` is at most `T`'s mass:

  `p^{S}_{Y^i, A_i=0 | X^i}(ys | xs) ≤ p^{T}_{Y^i | X^i}(ys | xs)`,

stated at the unnormalized `Dist` level (`jointProb` of the Definition-4.15
pre-winning PDS vs `jointProb` of `T`) — the preWinBehavior ≤ behavior
inequality, a pure sub-distribution comparison with no division and no
defined-ness guards.  On Maurer's domain (weight-1 distributions over total
systems) the `X^i`-conditioning normalizers are `1` and this is literally
the conditional-distribution inequality. -/
def PDG.CondDominates [DecidableEq (List (Option Y))]
    (S : PDG X Y) (T : PDS X Y) : Prop :=
  ∀ (xs : List X) (ys : List Y),
    jointProb (Def415.preWinningPDS S) xs ys ≤ jointProb T xs ys

/-- Notation for conditional domination: `S |⊑ T`. -/
scoped notation:50 S " |⊑ " T => PDG.CondDominates S T

section OfEquiv

variable [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]

/-- **Conditional equivalence ⇒ conditional domination (the eq-4.38
factorization, one line)**: if `S ≡_g That` (the eq-4.39 game equivalence
with the enhanced game, CR18's carrier of the cumulative factorization
`p^{Ŝ}_{Y^i,A_i=0|X^i} = p^{Ŝ}_{A_i=0|X^i} · p^{T}_{Y^i|X^i}`) and
`That⁻ = T`, then `S |⊑ T`: the pre-winning mass of `S` equals that of
`That` (K2 invariance) and is at most the FULL mass of `That⁻ = T` (the
strip partition — dropping the non-negative `A_q=1` part is the
`p^{Ŝ}_{A_i=0|X^i} ≤ 1` step of eq 4.38). -/
theorem condDominates_of_gameEquiv {S That : PDG X Y} {T : PDS X Y}
    (hGameEquiv : Def416.GameEquiv S That) (hStrip : PDG.strip That = T)
    (hS : S.sum (fun _ p => p) = 1) (hThat : That.sum (fun _ p => p) = 1) :
    S |⊑ T := by
  intro xs ys
  rw [Lem416.jointProb_preWinningPDS_congr_gameEquiv hGameEquiv hS hThat xs ys,
    ← hStrip, Lem416.jointProb_strip_partition That xs ys]
  exact le_self_add

open Def419 in
/-- **CR18 (b): `condEquiv → condDominates`**, abstract enhanced-game form.

This wrapper keeps explicit `That`/`hGameEquiv`/`hStrip` data for callers that
already have an enhanced game.  The source-shaped independent-enhancement form
below is `condDominates_of_condEquiv_enhance`, which constructs `That` by
Def. 4.21 and proves eq. (4.39) internally. -/
theorem condDominates_of_condEquiv (S : PDG X Y) (T : PDS X Y)
    (_hCondEquiv : S |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Def416.GameEquiv S That)
    (hStrip : PDG.strip That = T)
    (hS : S.sum (fun _ p => p) = 1) (hThat : That.sum (fun _ p => p) = 1) :
    S |⊑ T :=
  condDominates_of_gameEquiv hGameEquiv hStrip hS hThat

open Def419 in
/-- Conditional equivalence gives conditional domination through Maurer's
independent enhanced game, with the Lean-side support-totality condition for
the reference system `T` explicit. -/
theorem condDominates_of_condEquiv_enhance
    [DecidableEq (DDG X Y)]
    (S : PDG X Y) (T : PDS X Y)
    (hCondEquiv : S |≡ T)
    (hdomC : ∀ (t : DDS X Y) (g : DDG X Y),
        (t, g) ∈ (Dist.prod T S).support → t.dom = g.toSystem.dom)
    (hS : S.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1)
    (hTtotal : Def419.PDS.TotalOnNonempty T) :
    S |⊑ T := by
  refine condDominates_of_gameEquiv
    (That := Def421.enhancePDG (Dist.prod T S) hdomC)
    ?_ ?_ hS ?_
  · exact Def421.gameEquiv_enhancePDG_prod_of_condEquiv
      S T hdomC hCondEquiv hT hTtotal
  · rw [Def421.strip_enhancePDG, Lem416.fst_fTransform_prod T S hS]
  · rw [Def421.enhancePDG_mass, Lem416.prod_mass, hT, hS, mul_one]

end OfEquiv

end Def419'

namespace Thm417'

universe u v

variable {X : Type u} {Y : Type v}
  [DecidableEq (List (Option Y))] [DecidableEq (List (Option X))]
  [Inhabited X] [Inhabited Y]
  [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

open Def45 Def47 Def416 Def417 Def419' Lem416

/-- **CR18 Theorem 4.17′ (per-distinguisher, direction `T − Ŝ⁻`)**: under
conditional domination `S |⊑ T`, for every probabilistic `q`-query
distinguisher `D`,

  `Pr^{DT}(Z=1) − Pr^{DŜ⁻}(Z=1) ≤ S(D) ≤ Γ(S)`.

This is the keystone cancellation chain with the equality step weakened to
`≤` (see the section header): no game equivalence, no enhanced game, no
strip hypothesis — domination alone. -/
theorem advantage_le_winProb (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher) :
    (distinctionStructure X Y q).performance (PDG.strip S, T) D ≤
      ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S : Real) := by
  classical
  -- (0) Performance as a difference of NNReal acceptance probabilities.
  have hcast : ∀ G' : PDS X Y,
      (D.sum fun d dw => G'.sum fun s sw =>
          (dw : Real) * (sw : Real) *
            if (distinctionStructure X Y q).κ d s then 1 else 0) =
      ((D.sum fun d dw => dw * (G'.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    intro G'
    simp only [Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (distinctionStructure X Y q).κ d s
    · simp [h]
    · simp [h]
  have hperf : (distinctionStructure X Y q).performance (PDG.strip S, T) D =
      ((D.sum fun d dw => dw * (T.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) -
      ((D.sum fun d dw => dw * ((PDG.strip S).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    rw [Def47.DistinctionStructure.performance, ← hcast, ← hcast]
    rfl
  -- (1) Per-deterministic-distinguisher key inequality (pure NNReal,
  --     additive — no truncated subtraction):
  --       accept_T(d) ≤ acceptNotWon_S(d) + winMass_S(d.1).
  have hkey : ∀ d : Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool),
      (T.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) ≤
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
          (S.sum fun g gp =>
            gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0)) := by
    intro d
    -- eq 4.37: winMass + (pre-winning completion mass) = mass S = 1.
    have h437 := winMass_add_preWinCompletion q S d.1
    rw [hS] at h437
    -- acceptNotWonProb as an explicit transcript sum.
    have hNW : acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 =
        ∑ t : (Fin q → X) × (Fin q → Y),
          if d.2 t = true then
            jointProb (Def415.preWinningPDS S) (List.ofFn t.1) (List.ofFn t.2) *
              (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0)
          else 0 := by
      simp only [acceptNotWonProb]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [preWinTranscriptDist_eq, envJointProb_single]
    -- (A) additive comparison: accept_T + preWinCompletion ≤ NW + completion_T.
    have hA : (T.sum fun s sw =>
        sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) +
        (∑ t : (Fin q → X) × (Fin q → Y),
          jointProb (Def415.preWinningPDS S) (List.ofFn t.1) (List.ofFn t.2) *
            (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                (List.ofFn t.1).map some then 1 else 0)) ≤
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
          (∑ t : (Fin q → X) × (Fin q → Y),
            jointProb T (List.ofFn t.1) (List.ofFn t.2) *
              (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                  (List.ofFn t.1).map some then 1 else 0)) := by
      rw [acceptProb_det_pds q T d, hNW, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      by_cases hz : d.2 t = true
      · -- accepted transcript: the two sides swap at equality.
        rw [if_pos hz, if_pos hz, one_mul]
        exact le_of_eq (add_comm _ _)
      · -- rejected transcript: domination.
        rw [if_neg hz, if_neg hz, zero_mul, zero_mul, zero_add, zero_add]
        exact mul_le_mul' (hdomi _ _) le_rfl
    -- (B) the T-completion mass is at most the (weight-1) total mass.
    have hB : (∑ t : (Fin q → X) × (Fin q → Y),
        jointProb T (List.ofFn t.1) (List.ofFn t.2) *
          (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
              (List.ofFn t.1).map some then 1 else 0)) ≤ 1 := by
      have h := sum_jointProb_ask_le_mass q T d.1
      rwa [hT] at h
    -- chain and cancel the pre-winning completion mass (NNReal is
    -- additively cancellative).
    exact le_of_add_le_add_right <|
      calc (T.sum fun s sw =>
              sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) +
            (∑ t : (Fin q → X) × (Fin q → Y),
              jointProb (Def415.preWinningPDS S) (List.ofFn t.1) (List.ofFn t.2) *
                (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                    (List.ofFn t.1).map some then 1 else 0))
          ≤ acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
              (∑ t : (Fin q → X) × (Fin q → Y),
                jointProb T (List.ofFn t.1) (List.ofFn t.2) *
                  (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                      (List.ofFn t.1).map some then 1 else 0)) := hA
        _ ≤ acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
              1 := add_le_add_right hB _
        _ = (acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
              (S.sum fun g gp =>
                gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0))) +
            (∑ t : (Fin q → X) × (Fin q → Y),
              jointProb (Def415.preWinningPDS S) (List.ofFn t.1) (List.ofFn t.2) *
                (if DDE.inputSeq (Strategy.toDDE d.1) (List.ofFn t.2) =
                    (List.ofFn t.1).map some then 1 else 0)) := by
            rw [add_assoc, h437]
  -- (2) Identify the winning-probability shape as a D-indexed mix.
  have hwinShape : (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S =
      D.sum fun d dw => dw * (S.sum fun g gp =>
        gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0)) := by
    have hshape : (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S =
        (Dist.fTransform Prod.fst D).sum fun w wp =>
          wp * (S.sum fun g gp =>
            gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) := by
      rw [Def45.GameStructure.winProb]
      refine Finsupp.sum_congr fun w _ => ?_
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun g _ => by ring
    rw [hshape]
    exact fTransform_sum_mul_finsupp D Prod.fst
      (fun w => S.sum fun g gp =>
        gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0))
  -- (3) Mix the per-d inequality over D.
  have hmix : (D.sum fun d dw => dw * (T.sum fun s sw =>
      sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))) ≤
      (D.sum fun d dw => dw *
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2) +
      (D.sum fun d dw => dw * (S.sum fun g gp =>
        gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0))) :=
    calc (D.sum fun d dw => dw * (T.sum fun s sw =>
            sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)))
        ≤ D.sum fun d dw =>
            dw * acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 +
            dw * (S.sum fun g gp =>
              gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0)) := by
          refine Finsupp.sum_le_sum fun d _ => ?_
          rw [← mul_add]
          exact mul_le_mul_right (hkey d) _
      _ = _ := Finsupp.sum_add
  -- (4) The strip-S acceptance partitions as not-won + won (≥ not-won).
  have hsplit : (D.sum fun d dw => dw * ((PDG.strip S).sum fun s sw =>
      sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))) =
      (D.sum fun d dw => dw *
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2) +
      (D.sum fun d dw => dw * acceptWonProb q S (Strategy.toDDE d.1) d.2) := by
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [acceptProb_det_strip q S d, mul_add]
  -- (5) Assemble at the Real level.
  rw [hperf, hsplit, hwinShape]
  push_cast
  have h1 : ((D.sum fun d dw => dw * (T.sum fun s sw =>
      sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
      : NNReal) : Real) ≤
      ((D.sum fun d dw => dw *
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2
        : NNReal) : Real) +
      ((D.sum fun d dw => dw * (S.sum fun g gp =>
        gp * (if (gameStructure X Y q).win d.1 g then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    exact_mod_cast hmix
  have h2 : (0 : Real) ≤ ((D.sum fun d dw =>
      dw * acceptWonProb q S (Strategy.toDDE d.1) d.2 : NNReal) : Real) := by
    positivity
  linarith

/-- **CR18 Theorem 4.17′ (per-distinguisher, symmetric direction
`Ŝ⁻ − T`)**: under conditional domination, the reverse signed performance is
ALSO bounded by `S(D)` — Maurer's symmetric direction, obtained directly
from the anti-symmetry of the signed performance (equivalently, via the
complement-closure `Z ↦ ¬Z` of the decision class): the acceptance∧not-won
mass is dominated termwise, and the acceptance∧won mass is the keystone's
`acceptWonProb_le_winProb_det`. -/
theorem advantage_rev_le_winProb (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (_hS : S.sum (fun _ p => p) = 1) (_hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher) :
    (distinctionStructure X Y q).performance (T, PDG.strip S) D ≤
      ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S : Real) := by
  classical
  have hcast : ∀ G' : PDS X Y,
      (D.sum fun d dw => G'.sum fun s sw =>
          (dw : Real) * (sw : Real) *
            if (distinctionStructure X Y q).κ d s then 1 else 0) =
      ((D.sum fun d dw => dw * (G'.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    intro G'
    simp only [Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (distinctionStructure X Y q).κ d s
    · simp [h]
    · simp [h]
  have hperf : (distinctionStructure X Y q).performance (T, PDG.strip S) D =
      ((D.sum fun d dw => dw * ((PDG.strip S).sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) -
      ((D.sum fun d dw => dw * (T.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
        : NNReal) : Real) := by
    rw [Def47.DistinctionStructure.performance, ← hcast, ← hcast]
    rfl
  -- Per-d: the not-won part is dominated by the T-acceptance, termwise.
  have hkeyrev : ∀ d : Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool),
      acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2 ≤
        (T.sum fun s sw =>
          sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0)) := by
    intro d
    rw [acceptProb_det_pds q T d]
    simp only [acceptNotWonProb]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [preWinTranscriptDist_eq, envJointProb_single]
    by_cases hz : d.2 t = true
    · rw [if_pos hz, if_pos hz, one_mul]
      exact mul_le_mul' (hdomi _ _) le_rfl
    · rw [if_neg hz, if_neg hz, zero_mul, zero_mul]
  -- The strip-S acceptance partitions as not-won + won.
  have hsplit : (D.sum fun d dw => dw * ((PDG.strip S).sum fun s sw =>
      sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))) =
      (D.sum fun d dw => dw *
        acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2) +
      (D.sum fun d dw => dw * acceptWonProb q S (Strategy.toDDE d.1) d.2) := by
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [acceptProb_det_strip q S d, mul_add]
  -- The won part is bounded by the winning probability (keystone step).
  have hwon : (D.sum fun d dw =>
      dw * acceptWonProb q S (Strategy.toDDE d.1) d.2) ≤
      (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S := by
    have hshape : (gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S =
        (Dist.fTransform Prod.fst D).sum fun w wp =>
          wp * (S.sum fun g gp =>
            gp * (if (gameStructure X Y q).win w g then (1 : NNReal) else 0)) := by
      rw [Def45.GameStructure.winProb]
      refine Finsupp.sum_congr fun w _ => ?_
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun g _ => by ring
    rw [hshape, fTransform_sum_mul_finsupp]
    exact Finsupp.sum_le_sum fun d _ =>
      mul_le_mul_right (acceptWonProb_le_winProb_det q S d.1 d.2) _
  -- The not-won mix is dominated by the T-acceptance mix.
  have hmixrev : (D.sum fun d dw => dw *
      acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2) ≤
      (D.sum fun d dw => dw * (T.sum fun s sw =>
        sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))) :=
    Finsupp.sum_le_sum fun d _ => mul_le_mul_right (hkeyrev d) _
  -- Assemble at the Real level.
  rw [hperf, hsplit]
  push_cast
  have h1 : ((D.sum fun d dw => dw *
      acceptNotWonProb q S (Finsupp.single (Strategy.toDDE d.1) 1) d.2
      : NNReal) : Real) ≤
      ((D.sum fun d dw => dw * (T.sum fun s sw =>
        sw * (if (distinctionStructure X Y q).κ d s then (1 : NNReal) else 0))
      : NNReal) : Real) := by exact_mod_cast hmixrev
  have h2 : ((D.sum fun d dw =>
      dw * acceptWonProb q S (Strategy.toDDE d.1) d.2 : NNReal) : Real) ≤
      ((gameStructure X Y q).winProb (Dist.fTransform Prod.fst D) S : Real) := by
    exact_mod_cast hwon
  linarith

/-- **CR18 Theorem 4.17′ (per-distinguisher, `Γ` form)**: conditional
domination bounds the distinguishing advantage by the maximal winning
probability, `⟨Ŝ⁻ | T⟩(D) ≤ Γ(Ŝ)`. -/
theorem advantage_le_maxWinProb (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (distinctionStructure X Y q).performance (PDG.strip S, T) D ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) := by
  refine le_trans (advantage_le_winProb q S T hdomi hS hT D) ?_
  have hW : (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).isProbDist := by
    show (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).weight = 1
    rw [Dist.weight_fTransform]
    exact hD
  exact_mod_cast Def417.winProb_le_maxWinProb (gameStructure X Y q) S hS _ hW

/-- **CR18 Theorem 4.17′ (per-distinguisher, `Γ` form, symmetric
direction)**: `⟨T | Ŝ⁻⟩(D) ≤ Γ(Ŝ)`. -/
theorem advantage_rev_le_maxWinProb (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
    (D : (distinctionStructure X Y q).ProbDistinguisher)
    (hD : D.isProbDist) :
    (distinctionStructure X Y q).performance (T, PDG.strip S) D ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) := by
  refine le_trans (advantage_rev_le_winProb q S T hdomi hS hT D) ?_
  have hW : (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).isProbDist := by
    show (Dist.fTransform Prod.fst D : Dist (Strategy X Y q)).weight = 1
    rw [Dist.weight_fTransform]
    exact hD
  exact_mod_cast Def417.winProb_le_maxWinProb (gameStructure X Y q) S hS _ hW

/-- **CR18 Theorem 4.17′ (delta form)**: conditional domination implies

  `Δ(Ŝ⁻, T) = sup_D ⟨Ŝ⁻ | T⟩(D) ≤ Γ(Ŝ)`,

the supremum over probability-distribution distinguishers — with NO enhanced
game, NO game-equivalence and NO strip hypothesis.  Downstream consumers
(hctr2 PO-3f) instantiate `hdomi` directly. -/
theorem delta_le_gamma (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1) :
    sSup ((fun D : (distinctionStructure X Y q).ProbDistinguisher =>
        (distinctionStructure X Y q).performance (PDG.strip S, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) := by
  apply csSup_le
  · refine ⟨_, ⟨Finsupp.single
      ((fun _ _ => default, fun _ => false) :
        Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) 1,
      ?_, rfl⟩⟩
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  · rintro x ⟨D, hD, rfl⟩
    exact advantage_le_maxWinProb q S T hdomi hS hT D hD

/-- **CR18 Theorem 4.17′ (delta form, symmetric direction)**:
`Δ(T, Ŝ⁻) ≤ Γ(Ŝ)`.  Together with `delta_le_gamma` this bounds the
two-sided (absolute) distinguishing advantage. -/
theorem delta_rev_le_gamma (q : ℕ) (S : PDG X Y) (T : PDS X Y)
    (hdomi : S |⊑ T)
    (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1) :
    sSup ((fun D : (distinctionStructure X Y q).ProbDistinguisher =>
        (distinctionStructure X Y q).performance (T, PDG.strip S) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (gameStructure X Y q) S : Real) := by
  apply csSup_le
  · refine ⟨_, ⟨Finsupp.single
      ((fun _ _ => default, fun _ => false) :
        Strategy X Y q × (((Fin q → X) × (Fin q → Y)) → Bool)) 1,
      ?_, rfl⟩⟩
    show Dist.weight (Finsupp.single _ (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  · rintro x ⟨D, hD, rfl⟩
    exact advantage_rev_le_maxWinProb q S T hdomi hS hT D hD

open Def419 in
/-- **The equality-route Theorem 4.17 as a corollary of 4.17′ + (b)**: with
EXACTLY the hypothesis list of `Thm417.delta_le_gamma` (Maurer's premise
`Shat |≡ T` plus the eq-4.39 data `That`/`hGameEquiv`/`hStrip` and the
weight-1 conditions), the `Γ(Ŝ)` bound follows from conditional domination
(`condDominates_of_gameEquiv`) and the one-sided fundamental lemma — the
cancellation EQUALITY is needed only for the `Γ(bŜ)` sharpening
(`Thm417.delta_le_blind_gamma`). -/
theorem delta_le_gamma_of_condEquiv (q : ℕ)
    (Shat : PDG X Y) (T : PDS X Y)
    (_hCondEquiv : Shat |≡ T)
    (That : PDG X Y)
    (hGameEquiv : Shat ≡_g That)
    (hStrip : PDG.strip That = T)
    (hShat : Shat.sum (fun _ p => p) = 1)
    (hThat : That.sum (fun _ p => p) = 1)
    (hT : T.sum (fun _ p => p) = 1) :
    sSup ((fun D : (distinctionStructure X Y q).ProbDistinguisher =>
        (distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
      {D | D.isProbDist}) ≤
      (Def417.maxWinProb (gameStructure X Y q) Shat : Real) :=
  delta_le_gamma q Shat T
    (Def419'.condDominates_of_gameEquiv hGameEquiv hStrip hShat hThat)
    hShat hT

end Thm417'

end RandomSystems.CR18

/-!
## CR18 Definition 4.22 — `pcoll(t, q)` Collision Probability

CR18 §4.11 (source line 5710):

> **Definition 4.22.**  The probability that a set of `q` independent and
> uniformly chosen values from an alphabet of size `t` contains a value
> twice (a collision) is denoted as `pcoll(t, q)`.

The complementary event — no collision — has probability
```
  Pr[no collision] = t · (t − 1) · · · (t − q + 1) / t^q
                   = t.descFactorial(q) / t^q
```
(by a standard counting argument: the first draw is free, the second must
avoid 1 previously-seen value, etc.).  Therefore

```
  pcoll(t, q) = 1 − t.descFactorial(q) / t^q
```
with the convention `pcoll(t, q) = 1` whenever `q > t` (by the pigeonhole
principle, a collision is certain) or `t = 0`.

CR18 Lemma 4.18 asserts `pcoll(t, q) ≤ q² / (2 · t)`.

### Lean design

* We work in `ℝ≥0` (`NNReal`) to match the `Dist`/`NNReal` conventions used
  throughout this file.
* The no-collision probability `pnocoll(t, q)` is defined as the `NNReal`
  value `t.descFactorial(q) / t^q`, where `Nat.descFactorial` is the
  Mathlib falling-factorial `t.descFactorial q = t * (t-1) * ⋯ * (t-q+1)`.
* `pcoll(t, q) = 1 - pnocoll(t, q)`, using `NNReal` truncated subtraction,
  which equals 0 when `pnocoll ≥ 1` (but `pnocoll ≤ 1` always holds for
  `q ≤ t`), and equals 1 exactly when `q > t` (pigeonhole via
  `Nat.descFactorial_eq_zero_iff`).
-/

namespace RandomSystems.CR18

namespace Def422

/-! ### No-collision probability -/

/-- CR18 Definition 4.22 (complement): the probability of **no collision**
among `q` independent uniform draws from an alphabet of size `t`.

```
  pnocoll t q = t.descFactorial q / t ^ q
```

`Nat.descFactorial t q = t * (t − 1) * ⋯ * (t − q + 1)` (falling factorial).
When `q = 0`, `pnocoll t 0 = 1` (empty product / no collision vacuously).
When `q > t`, `t.descFactorial q = 0`, so `pnocoll t q = 0`. -/
noncomputable def pnocoll (t q : ℕ) : NNReal :=
  (t.descFactorial q : NNReal) / (t : NNReal) ^ q

/-- `pnocoll t 0 = 1`: zero draws, no collision is certain. -/
@[simp]
theorem pnocoll_zero (t : ℕ) : pnocoll t 0 = 1 := by
  simp [pnocoll]

/-- `pnocoll 0 0 = 1`. -/
@[simp]
theorem pnocoll_zero_zero : pnocoll 0 0 = 1 := pnocoll_zero 0

/-- `pnocoll t q = 0` when `q > t` (pigeonhole: `descFactorial = 0`). -/
theorem pnocoll_eq_zero_of_lt {t q : ℕ} (h : t < q) : pnocoll t q = 0 := by
  simp only [pnocoll]
  have : t.descFactorial q = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
  simp [this]

/-- `pnocoll t q ≤ 1` for all `t`, `q`. -/
theorem pnocoll_le_one (t q : ℕ) : pnocoll t q ≤ 1 := by
  simp only [pnocoll]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have : Nat.descFactorial 0 q = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.zero_lt_of_lt (Nat.lt_of_succ_le hq))
      simp [this]
  · rw [div_le_one (by positivity)]
    norm_cast
    exact Nat.descFactorial_le_pow t q

/-! ### Collision probability -/

/-- CR18 Definition 4.22: the **collision probability** for `q` independent
uniform draws from an alphabet of size `t`.

```
  pcoll t q = 1 − pnocoll t q
```

Uses `NNReal` truncated subtraction (= 0 when `pnocoll ≥ 1`, but
`pnocoll ≤ 1` always holds so this never truncates to 0 spuriously).

Special cases:
* `pcoll t 0 = 0` — zero draws, no collision possible.
* `pcoll t 1 = 0` — one draw, no collision possible.
* `pcoll t q = 1` when `q > t` — pigeonhole forces a collision.
* `pcoll 0 0 = 0` — empty alphabet, zero draws.
* `pcoll 0 q = 1` for `q ≥ 1` — empty alphabet, any draw is impossible but
  we adopt the convention that the probability of collision is 1 (= 1 − 0). -/
noncomputable def pcoll (t q : ℕ) : NNReal :=
  1 - pnocoll t q

/-- `pcoll t 0 = 0`: zero draws, collision probability is zero. -/
@[simp]
theorem pcoll_zero (t : ℕ) : pcoll t 0 = 0 := by
  simp [pcoll]

/-- `pcoll t q = 1` when `q > t` (collision is certain by pigeonhole). -/
theorem pcoll_eq_one_of_lt {t q : ℕ} (h : t < q) : pcoll t q = 1 := by
  simp [pcoll, pnocoll_eq_zero_of_lt h]

/-- `pcoll t q` and `pnocoll t q` sum to 1. -/
theorem pcoll_add_pnocoll (t q : ℕ) : pcoll t q + pnocoll t q = 1 := by
  simp only [pcoll]
  exact tsub_add_cancel_of_le (pnocoll_le_one t q)

/-- `pcoll t q ≤ 1` for all `t`, `q`. -/
theorem pcoll_le_one (t q : ℕ) : pcoll t q ≤ 1 :=
  tsub_le_self

/-- Unfolding lemma: `pcoll t q = 1 - t.descFactorial q / t ^ q`. -/
theorem pcoll_eq (t q : ℕ) :
    pcoll t q = 1 - (t.descFactorial q : NNReal) / (t : NNReal) ^ q :=
  rfl

end Def422

/-- CR18 Definition 4.22: `pcoll t q` is the probability of a collision
among `q` independent uniform samples from an alphabet of size `t`.

Exported from the `Def422` namespace for convenience. -/
noncomputable abbrev pcoll (t q : ℕ) : NNReal := Def422.pcoll t q

/-- CR18 Definition 4.22: `pnocoll t q` is the probability of no collision. -/
noncomputable abbrev pnocoll (t q : ℕ) : NNReal := Def422.pnocoll t q

end RandomSystems.CR18

/-!
## CR18 Lemma 4.18 — pcoll upper bound

CR18 §4.11 (source line 5711):

> **Lemma 4.18.** `pcoll(t, q) ≤ ½ q² / t`.

**Proof sketch (CR18, "left as an exercise"):**
The standard birthday-bound argument:
```
  pnocoll(t, q) = ∏_{i=0}^{q-1} (1 − i/t)  ≥  1 − ∑_{i=0}^{q-1} i/t
               = 1 − q(q−1)/(2t)
```
via Bernoulli / union-bound (1 − xᵢ ≥ 1 − ∑ xᵢ for 0 ≤ xᵢ ≤ 1).
Hence `pcoll(t, q) = 1 − pnocoll(t, q) ≤ q(q−1)/(2t) ≤ q²/(2t)`.

The hypothesis `0 < t` is necessary: when `t = 0` the RHS `q²/(2·0)` is `0`
in `NNReal` division, while `pcoll 0 q = 1` for `q ≥ 1`.

### Lean strategy

The proof is in `ℝ≥0` (`NNReal`).  We first show the bound in `ℝ`
and then lift it to `NNReal`.  The key ingredients are:
* `Nat.descFactorial_le_pow`: `t.descFactorial q ≤ t ^ q`.
* A lower bound `t ^ q − q * (q − 1) / 2 * t ^ (q − 1) ≤ t.descFactorial q`
  (standard, but hard to state cleanly in `ℕ` due to truncated subtraction).

The proof is complete (`sorry`-free): the `ℝ`-level inclusion–exclusion lower
bound `∏_{i<q}(1 - i/t) ≥ 1 - ∑_{i<q} i/t` is ported from
`RandomSystems.Applications.XoP.ANOVA`, the sum is bounded by `q²/(2t)`, and the
pigeonhole regime `q > t` is handled separately.
-/

namespace RandomSystems.CR18

namespace Lem418

/-- Finite product lower bound (first-order inclusion–exclusion): if each
`f i ∈ [0,1]` then `∏ (1 - f i) ≥ 1 - ∑ f i`.  Ported from
`RandomSystems.Applications.XoP.ANOVA.prod_one_sub_ge_one_sub_sum`. -/
private theorem prod_one_sub_ge_one_sub_sum {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1 - f i) := by
  rw [Finset.prod_one_sub_ordered]
  refine sub_le_sub_left ?_ 1
  refine Finset.sum_le_sum ?_
  intro i hi
  have hprefix_le_one : ∏ j ∈ s with j < i, (1 - f j) ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact sub_nonneg.mpr (h1 j hj.1)
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact sub_le_self 1 (h0 j hj.1)
  exact mul_le_of_le_one_right (h0 i hi) hprefix_le_one

/-- The falling-factorial ratio `(t)_q / t^q` dominates the first-order
inclusion–exclusion lower bound, in `ℝ`.  Ported from
`RandomSystems.Applications.XoP.ANOVA.descFactorial_div_pow_ge_one_sub_sum`. -/
private theorem descFactorial_div_pow_ge_one_sub_sum (t q : ℕ)
    (ht : 0 < t) (hq : q ≤ t) :
    1 - (∑ i ∈ Finset.range q, (i : ℝ) / (t : ℝ)) ≤
      ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
  have hprod : 1 - (∑ i ∈ Finset.range q, (i : ℝ) / (t : ℝ)) ≤
      ∏ i ∈ Finset.range q, (1 - (i : ℝ) / (t : ℝ)) := by
    refine prod_one_sub_ge_one_sub_sum (Finset.range q)
      (fun i : ℕ => (i : ℝ) / (t : ℝ)) ?_ ?_
    · intro i hi
      positivity
    · intro i hi
      rw [Finset.mem_range] at hi
      have hit : i ≤ t := le_trans hi.le hq
      have hreal : 0 < (t : ℝ) := by exact_mod_cast ht
      exact (div_le_one hreal).mpr (by exact_mod_cast hit)
  have hprod_eq : (∏ i ∈ Finset.range q, (1 - (i : ℝ) / (t : ℝ))) =
      ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
    calc
      (∏ i ∈ Finset.range q, (1 - (i : ℝ) / (t : ℝ)))
          = ∏ i ∈ Finset.range q, (((t - i : ℕ) : ℝ) / (t : ℝ)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [Finset.mem_range] at hi
            have hit : i ≤ t := le_trans hi.le hq
            have hcast : ((t - i : ℕ) : ℝ) = (t : ℝ) - (i : ℝ) :=
              Nat.cast_sub hit
            rw [hcast]
            field_simp [show (t : ℝ) ≠ 0 by exact_mod_cast ne_of_gt ht]
      _ = (∏ i ∈ Finset.range q, ((t - i : ℕ) : ℝ)) /
          ∏ _i ∈ Finset.range q, (t : ℝ) := by
            rw [Finset.prod_div_distrib]
      _ = ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
            rw [← Finset.prod_natCast, ← Nat.descFactorial_eq_prod_range,
              Finset.prod_const, Finset.card_range]
  exact hprod.trans_eq hprod_eq

/-- Auxiliary: the birthday bound in `NNReal`.

The key step bridging `pnocoll` to the RHS bound in `NNReal`:
  `1 - t.descFactorial q / t ^ q ≤ q ^ 2 / (2 * t)`.

This is the hard analytic content; it follows from the product inequality
  `∏_{i<q} (1 - i/t) ≥ 1 - ∑_{i<q} i/t = 1 - q*(q-1)/(2*t) ≥ 1 - q^2/(2*t)`. -/
private lemma pnocoll_ge_aux (t q : ℕ) (ht : 0 < t) :
    1 - (q : NNReal) ^ 2 / (2 * (t : NNReal)) ≤ Def422.pnocoll t q := by
  -- Reduce `1 - X ≤ Y` to `1 ≤ Y + X` (NNReal truncated subtraction).
  rw [Def422.pnocoll, tsub_le_iff_right]
  -- Move to `ℝ`: everything in sight is nonnegative.
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul]
  push_cast
  -- Now the goal is in `ℝ`:  1 ≤ (t)_q / t^q + q^2 / (2 t).
  have hreal : 0 < (t : ℝ) := by exact_mod_cast ht
  rcases le_or_gt q t with hqt | hqt
  · -- Main regime `q ≤ t`: use the inclusion–exclusion lower bound.
    have hlower := descFactorial_div_pow_ge_one_sub_sum t q ht hqt
    -- The first-order sum `∑_{i<q} i/t = (∑ i)/t` is at most `q^2/(2t)`.
    have hsum_le : (∑ i ∈ Finset.range q, (i : ℝ) / (t : ℝ)) ≤
        (q : ℝ) ^ 2 / (2 * (t : ℝ)) := by
      have hsum_eq : (∑ i ∈ Finset.range q, (i : ℝ) / (t : ℝ)) =
          ((∑ i ∈ Finset.range q, i : ℕ) : ℝ) / (t : ℝ) := by
        rw [← Finset.sum_div, Nat.cast_sum]
      rw [hsum_eq]
      have htwo : (∑ i ∈ Finset.range q, i) * 2 = q * (q - 1) :=
        Finset.sum_range_id_mul_two q
      have hnum : ((∑ i ∈ Finset.range q, i : ℕ) : ℝ) * 2 ≤ (q : ℝ) ^ 2 := by
        have : (((∑ i ∈ Finset.range q, i) * 2 : ℕ) : ℝ) =
            ((q * (q - 1) : ℕ) : ℝ) := by rw [htwo]
        have hq1 : (q * (q - 1) : ℕ) ≤ q * q := by
          rcases Nat.eq_zero_or_pos q with rfl | hqpos
          · simp
          · exact Nat.mul_le_mul_left q (Nat.sub_le q 1)
        calc ((∑ i ∈ Finset.range q, i : ℕ) : ℝ) * 2
            = (((∑ i ∈ Finset.range q, i) * 2 : ℕ) : ℝ) := by push_cast; ring
          _ = ((q * (q - 1) : ℕ) : ℝ) := by rw [htwo]
          _ ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hq1
          _ = (q : ℝ) ^ 2 := by push_cast; ring
      rw [div_le_div_iff₀ hreal (by positivity)]
      nlinarith [hnum, hreal]
    linarith [hlower, hsum_le]
  · -- Pigeonhole regime `q > t`:  q^2/(2t) ≥ 1, and `(t)_q/t^q ≥ 0`.
    have hge : (1 : ℝ) ≤ (q : ℝ) ^ 2 / (2 * (t : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hq1 : t + 1 ≤ q := hqt
      have hqR : (t : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq1
      nlinarith [hqR, hreal]
    have hnonneg : (0 : ℝ) ≤ ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
      positivity
    linarith [hge, hnonneg]

end Lem418

/-- CR18 Lemma 4.18: `pcoll(t, q) ≤ ½ q² / t`.

The birthday bound: the probability of a collision among `q` independent uniform
draws from an alphabet of size `t` is at most `q² / (2 * t)`.

**CR18 source:** Lemma 4.18 (line 5711): "pcoll(t, q) ≤ ½ q² / t."
**Proof:** left as an exercise in CR18.  Standard argument: by the product inequality
`pnocoll(t, q) = ∏_{i<q}(1 − i/t) ≥ 1 − ∑_{i<q} i/t = 1 − q(q−1)/(2t) ≥ 1 − q²/(2t)`,
so `pcoll(t, q) = 1 − pnocoll(t, q) ≤ q²/(2t)`.

The precondition `0 < t` is essential: the RHS equals `0` in `NNReal` when `t = 0`
(NNReal division by zero), while `pcoll 0 q = 1` for `q ≥ 1`.

**Lean type:** both sides live in `NNReal` = `ℝ≥0`. -/
theorem pcoll_le_sq_div_two (t q : ℕ) (ht : 0 < t) :
    pcoll t q ≤ (q : NNReal) ^ 2 / (2 * (t : NNReal)) := by
  -- pcoll t q = 1 - pnocoll t q  (NNReal truncated subtraction).
  -- Rewrite the goal as:  1 - pnocoll t q ≤ q²/(2t).
  -- By `tsub_le_iff_right`: this is  1 ≤ q²/(2t) + pnocoll t q.
  -- By `tsub_le_iff_left` on `pnocoll_ge_aux`:
  --   1 - q²/(2t) ≤ pnocoll t q  ↔  1 ≤ q²/(2t) + pnocoll t q.
  rw [pcoll, Def422.pcoll]
  exact tsub_le_iff_right.mpr (tsub_le_iff_left.mp (Lem418.pnocoll_ge_aux t q ht))

end RandomSystems.CR18

/-!
## CR18 Lemma 4.19 — URP–URF Switching Lemma

CR18 §4.11.3 (source line 5720):

> **Lemma 4.19.** `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ`.

where:
* `Rₙ,ₙ` is the Uniform Random Function (URF) with input and output alphabet
  `{0,1}ⁿ = Fin (2^n)`.
* `Pₙ` is the Uniform Random Permutation (URP) on `{0,1}ⁿ = Fin (2^n)`.
* `[q]S` denotes the system `S` limited to `q` queries.

The lemma is also written as `⟨[q]Rₙ,ₙ | [q]Pₙ⟩ ≤ ½ q² 2⁻ⁿ` (CR18 §4.11.3).

**Proof sketch (CR18):**
1. As shown in Example 4.15, we can define an MBO for `Rₙ,ₙ` — namely the game
   `R̂ₙ,ₙ` — where the MBO is `1` iff for some distinct inputs the outputs are
   equal (a collision).  One has `R̂ₙ,ₙ |≡ Pₙ` (conditional equivalence).
2. By Theorem 4.17: `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ Γ(b[q]R̂ₙ,ₙ)`.
3. The optimal non-adaptive strategy chooses q distinct inputs.  For any such
   choice the probability of causing a collision is `pcoll(2ⁿ, q)` (Definition
   4.22), and by Lemma 4.18: `pcoll(2ⁿ, q) ≤ ½ q² 2⁻ⁿ`.
4. Hence `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ pcoll(2ⁿ, q) ≤ ½ q² 2⁻ⁿ`.

### Lean strategy

* We state the **numerical bound** on `pcoll` directly (the combinatorial core).
* The connection to the `Applications.PRPPRFSwitching` birthday bound is noted via
  a `birthdayBound_le_pcoll_bound` lemma: `q(q-1)/(2·2ⁿ) ≤ q²/(2·2ⁿ)`.
* The full advantage statement `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½q²2⁻ⁿ` for the ACTUAL
  `Ex35.R n n` / `Ex35.P n` systems is `Lem419.urp_urf_switching` in
  `RandomSystems/CR18/SwitchingPort.lean` (it needs `AdvWith`, which lives
  downstream of this file): the ported transcript-factorization switching
  proof, with no bridge hypothesis.
-/

namespace RandomSystems.CR18

namespace Lem419

open scoped NNReal

/-! ### The URP–URF switching bound on `pcoll` -/

/-- CR18 Lemma 4.19 (numerical core): the collision probability `pcoll(2ⁿ, q)`
is at most `½ q² 2⁻ⁿ`.

This is the key numerical inequality behind the URP–URF switching lemma.
By CR18 Lemma 4.18 (`pcoll_le_sq_div_two`), `pcoll(2ⁿ, q) ≤ q² / (2 · 2ⁿ)`.

The RHS `q² / (2 · 2ⁿ) = ½ q² 2⁻ⁿ` matches the CR18 bound exactly.

**CR18 source:** Lemma 4.19 (line 5720): "pcoll(2ⁿ, q) ≤ ½ q² 2⁻ⁿ", which
is the bound that Γ(b[q]R̂ₙ,ₙ) inherits from Lemma 4.18 applied at t = 2ⁿ. -/
theorem pcoll_bound (n q : ℕ) :
    pcoll (2 ^ n) q ≤ (q : NNReal) ^ 2 / (2 * (2 : NNReal) ^ n) := by
  rcases n with _ | n
  · -- n = 0: alphabet size = 2^0 = 1
    simp only [pow_zero]
    convert pcoll_le_sq_div_two 1 q (by norm_num) using 2
    norm_cast
  · -- n + 1: 2^(n+1) > 0
    convert pcoll_le_sq_div_two (2 ^ (n + 1)) q (by positivity) using 2
    push_cast; ring

/-! ### Relation to `Applications.PRPPRFSwitching.birthdayBound` -/

/-- The `Applications.PRPPRFSwitching.birthdayBound q N` equals
`(q * (q - 1) : ℕ) / (2 * N : ℕ)` (as an `NNReal`).

CR18 Lemma 4.19 uses `q² / (2 · 2ⁿ)` as the bound, which is slightly looser
than `q(q-1) / (2 · 2ⁿ)` (the exact birthday bound).  The two coincide for
the purpose of upper-bounding `pcoll`:
  `pcoll(2ⁿ, q) ≤ q(q-1)/(2 · 2ⁿ) ≤ q²/(2 · 2ⁿ)`.

The Applications file's `urf_collision_bound_general` proves
`maxConditionFailure URF (allOutputsDistinct X q) ≤ birthdayBound q |X|`,
which (at `X = Fin (2^n)`) is exactly the computational certificate for
`Γ(b[q]R̂ₙ,ₙ) ≤ q(q-1)/(2·2ⁿ)` (step 3 of the CR18 proof).

See `RandomSystems.Applications.urf_collision_bound_general` and
`RandomSystems.Applications.prf_prp_switching_q1`. -/
theorem birthdayBound_le_pcoll_bound (q n : ℕ) :
    (q * (q - 1) : NNReal) / (2 * (2 : NNReal) ^ n) ≤
    (q : NNReal) ^ 2 / (2 * (2 : NNReal) ^ n) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  -- In NNReal: q * (q - 1) ≤ q^2
  -- NNReal subtraction is truncated: q - 1 ≤ q, so q * (q - 1) ≤ q * q = q^2
  calc (q : NNReal) * ((q : NNReal) - 1)
      ≤ (q : NNReal) * (q : NNReal) := by
        apply mul_le_mul_of_nonneg_left tsub_le_self (by positivity)
    _ = (q : NNReal) ^ 2 := by ring

/-! ### The URP–URF switching lemma — the REAL statement lives downstream

The full CR18 Lemma 4.19 — `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ` for the ACTUAL
Example 3.5 systems `Ex35.R n n` / `Ex35.P n` — is `Lem419.urp_urf_switching`
in `RandomSystems/CR18/SwitchingPort.lean` (downstream of this file because
it is stated through the shared advantage `AdvWith` of `AdvMetric.lean`).
It is proven by the ported transcript-factorization switching proof
(`SwitchingPort.advWith_urf_urp_le_birthday`, ported from hctr2-verification
`GAP2_switching`) instantiated at `A := Fin (2 ^ n)` — with NO abstract δ and
NO bridge hypothesis.  A former version at this spot assumed
`hBridge : δ ≤ pcoll(2ⁿ, q)` for an abstract `δ : NNReal`; it was DELETED
2026-06-11 when the port landed.
-/

end Lem419

end RandomSystems.CR18
