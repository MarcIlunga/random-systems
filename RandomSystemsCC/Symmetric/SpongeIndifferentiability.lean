/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedConstruct

/-!
# Indifferentiability of a hash construction, at the random-systems carrier

`AbstractCrypto.Relaxations` owns the notion — MauRen11 Definition 23 /
MauRen16 §4.2 Lemma 5,

  `Indifferentiable H ε R S :⟺ ∃ π, ∃ σ ∈ H, edist (π • R) (σ • S) ≤ ε`

— and `Applications.Sponge.sponge_indifferentiable` wraps `.construct`
around it.  That wrapper's own docstring records what it does *not* do:
"the concrete `RPerm`/`RO`, the sponge protocol/simulator converters, and the
`N²/|F|^c` bound are the instantiation layer's obligation."

This file is that instantiation layer: the two-interface setting the notion
needs, both resources built as honest random systems, **and both converters
pinned** — the sponge at `.honest`, a simulator at `.adversary`.

## Two simulators, and which endpoint uses which

The file carries both, because they trade the same two things against each other
and it is worth having the trade in one place.

* **Table-based** (`bdpvAns`, `Memory`) — rootedness decided from the
  simulator's own query/answer table.  At most one oracle query per permutation
  query (`length_bdpvOracleNeeds_le`).  Cost: the table can fail to recognize a
  genuinely rooted query, so the argument needs a **second** bad event on top of
  the capacity collision.

  **Wrong, now checked against the source**
  (`papers/BDPV08_SpongeIndifferentiability.pdf`, Algorithm 2).  It was written
  from memory, and the memory was wrong in the one place that carries the proof.
  See the section docstring for the corrected algorithm; the headline errors:

  - **The capacity is sampled from `C \ (R ∪ O)`, not uniformly.**  BDPV's
    simulator *avoids* capacity collisions by construction — it draws `t_c` from
    the supernodes that are neither rooted (`R`) nor already have an outgoing
    edge (`O`).  There is no capacity-collision bad event in their proof at all;
    what replaces it is **saturation** (`R ∪ O = C`), which cannot occur before
    `2^c` queries.  Ours draws `T u` unconstrained, which is a different
    simulator with a different (and unproved) analysis.
  - **Rootedness lives on supernodes, i.e. on capacities**: `R ⊆ C`, and a node
    `s` is rooted iff `s_c ∈ R` (§3.2, p. 9).  Ours carries full states in
    `rooted`.
  - **`capacityBad` is not on BDPV's critical path.**  Their advantage is a
    *variational distance* between uniform answers and fresh-capacity answers
    (Lemma 4), not an MBO/conditional-equivalence argument.
* **Ours** (`simAns`, `simChain`, `simLci`) — rootedness read off the seed.  The
  lazy/eager gap disappears, so the capacity collision is the *whole* MBO, and
  the two worlds then coincide outright (`realDDS_simAns_eq_idealDDS`, proved).
  Cost: **not efficient** — it consults the oracle at every message in `M`.  The
  basic notion (MauRen11 Definition 23) imposes no efficiency requirement on `σ`,
  so the statement is true of that notion, but it does not transport to any
  setting where the simulator's cost matters.

The endpoints below currently witness `σ` with **ours**, because that is the one
whose coupling is proved.

Both share BDPV's *shape* — absorb-chain, rooted-path detection, capacity
collision, capacity birthday bound — and both fall short of BDPV's actual
theorem in two further ways:

* **Forward-only primitive access.**  `Code.perm` offers `X → X`; there is no
  `P⁻¹` port.  BDPV's distinguisher gets both directions, and the inverse
  queries are a substantial part of their table-consistency argument.
* **`v = r`**: the digest is the full rate part, the boundary case of the regime
  the sponge converter already commits to.

## Why two interfaces

Indifferentiability is not a one-port statement.  The distinguisher must be
able to query *both* the construction and the underlying primitive, or the
notion collapses.  So the setting has

* `.honest` — where the hash is offered (the construction's outside), and
* `.adversary` — where the primitive is offered directly.

`permResource` answers permutation queries at **both** interfaces: the sponge
protocol attaches at `.honest` and drives it, while the distinguisher reaches
the very same permutation at `.adversary`.  `oracleCoinsResource` answers hash
queries at `.honest` and, at `.adversary`, hash queries *together with* the
simulator's coins.

Attaching the protocol at `.honest` and the simulator at `.adversary` sends
both worlds to the same boundary — hash at `.honest`, permutation at
`.adversary` — which is exactly the indifferentiability picture.

## Why the two interfaces need no new technique

They do not survive as *structure* below this file.  `TypedConstruct`'s
`edist_coe_prob` sends a typed distance to
`DependentPDS.contextualEDist`, and `edist_coe_prob_le_advantage` sends it on
to `Δ(DependentPDS.flatten …, DependentPDS.flatten …)` — a maximal
distinguishing advantage between two *ordinary* `PFunPDS` over the flat
alphabet `Query U σ`.  There the interfaces are mere tags in the query
alphabet, `⟨.honest, m⟩` versus `⟨.adversary, x⟩`, and a distinguisher for the
flat system interleaves both freely, which is precisely the
indifferentiability adversary.  So the leaf is one CR18 advantage between two
PDS, the same shape as `RandomSystems.CR18.cbc_mac_randomness_expander`; the
two interfaces only make the alphabet bigger.

## Why the simulator needs no probabilistic converter carrier

Any sponge simulator is randomized — it must answer with fresh capacity bits,
which the random oracle's `D`-valued answers cannot supply — and `Primitive` is
the *deterministic* converter layer (CR18 Definition 3.8).  The resolution is
the standing
discipline of this development — randomness lives in resources, converters are
deterministic: the simulator's coins are moved into the **ideal resource**, as
a second port `.hashCoins` at the adversary interface offering the random
oracle *and* a uniform `X → X`.  Given those coins the simulator is a
deterministic function of its history, so it is an ordinary
`Primitive.ofHistory`, exactly like the sponge.  A local randomness resource
reachable only at the dishonest interface is what "probabilistic simulator"
*means* in a deterministic-converter framework; nothing is assumed by it.

The coins are handed over in **one** query (`output .hashCoins = D ⊕ (X → X)`,
answered `.inr T`) rather than one query per point.  That is not cosmetic: it
makes the simulator's round count the constant `|M| + 1`, and
`isDDC_ofStep` demands an *exact* count — a query is issued **iff**
`ys.length < cnt` — which a constant satisfies outright.

## The simulator reads rootedness off the seed, not off its table

BDPV's simulator decides whether a permutation query `x` is *rooted* — reachable
from the initial state by absorbing a message — from its own query/answer
table.  Holding the coins it can instead read that off the seed directly
(`simChain`, `simLci`, `simAns`).  Two consequences:

* `simChain` is a plain structural recursion on the block index, with no
  fixpoint: prefix-freeness of `pad` means a proper prefix of `pad m` is never
  some `pad m'`, so the random-oracle branch fires only at the last block;
* the lazy/eager gap disappears, and with it one of BDPV's two bad events.  The
  adversary can no longer reach a chain input that the simulator fails to
  recognize, so **the capacity collision is the whole MBO** (`capacityBad`).

## Scope

Basic notion only, as scoped: no context restrictions (Jost Chapter 4's
RO-CRI is deliberately *not* used), no events, no interval-wise relaxation.
-/

noncomputable section

namespace RandomSystemsCC.Symmetric.SpongeIndifferentiability

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto ENNReal

universe u

/-- The two interfaces of an indifferentiability statement. -/
inductive Interface
  | honest
  | adversary
  deriving DecidableEq, Fintype

/-- The three codes: direct access to the permutation, access to the hash /
random oracle, and the adversary-side port offering the hash *together with*
the simulator's coins. -/
inductive Code
  | perm
  | hash
  | hashCoins
  deriving DecidableEq

/-- The signature universe: a permutation port over the state space `X`, a
hash port from messages `M` to digests `D`, and the ideal resource's
adversary-side port — a hash query or a one-shot draw of the simulator's coins
`X → X`. -/
abbrev signatures (X M D : Type u) : SignatureUniverse.{0, u, u} where
  Code := Code
  input
    | .perm => X
    | .hash => M
    | .hashCoins => M ⊕ PUnit
  output
    | .perm => X
    | .hash => D
    | .hashCoins => D ⊕ (X → X)

instance (X M D : Type u) : DecidableEq (signatures X M D).Code := by
  change DecidableEq Code
  infer_instance

section

variable {X M D : Type u}

/-- The assumed boundary: the public permutation, reachable at both
interfaces. -/
def permBoundary (X M D : Type u) : Boundary (signatures X M D) Interface
  | .honest => .perm
  | .adversary => .perm

/-- The ideal boundary: the random oracle at `.honest`, and at `.adversary` the
oracle together with the simulator's coins. -/
def oracleCoinsBoundary (X M D : Type u) : Boundary (signatures X M D) Interface
  | .honest => .hash
  | .adversary => .hashCoins

/-- The boundary both worlds present after the protocol is attached at
`.honest` and the simulator at `.adversary`: a hash outside, a permutation to
the adversary. -/
def indifferentiabilityBoundary (X M D : Type u) :
    Boundary (signatures X M D) Interface
  | .honest => .hash
  | .adversary => .perm

/-- Attaching the sponge at `.honest` moves the assumed boundary onto the
indifferentiability boundary. -/
theorem replaceBoundary_permBoundary_honest :
    replaceBoundary (permBoundary X M D) .honest .hash =
      indifferentiabilityBoundary X M D := by
  funext interface
  cases interface <;> rfl

/-- Attaching the simulator at `.adversary` moves the ideal boundary onto the
same one. -/
theorem replaceBoundary_oracleCoinsBoundary_adversary :
    replaceBoundary (oracleCoinsBoundary X M D) .adversary .perm =
      indifferentiabilityBoundary X M D := by
  funext interface
  cases interface <;> rfl

/-! ## The assumed resource -/

/-- The public permutation at a fixed bijection: both interfaces evaluate the
same `σ`. -/
def permDDS (sigma : Equiv.Perm X) :
    DependentDDS (signatures X M D) (permBoundary X M D) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.honest, x⟩ => sigma x
    | ⟨.adversary, x⟩ => sigma x

/-- The uniform random permutation law. -/
def permLaw [Fintype X] [DecidableEq X] :
    DependentPDS.Prob (signatures X M D) (permBoundary X M D) :=
  ⟨Dist.fTransform (permDDS (M := M) (D := D))
      (Dist.uniform (Equiv.Perm X)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- **The ideal permutation resource** — CR18's `𝖯`, presented at the two
indifferentiability interfaces. -/
def permResource [Fintype X] [DecidableEq X] :
    Phi Interface (signatures X M D) :=
  ⟨permBoundary X M D, DependentRandomSystem.ofProb (permLaw (M := M) (D := D))⟩

/-! ## The sponge converter

The absorbing sponge, as a CR18 Definition 3.8 converter at `.honest`: on a
hash query, walk the padded blocks, issuing one permutation query per block
with the running state absorbed into it, and answer with the squeeze of the
final state.

This is the SHA3 regime the output length makes available — for `v ≤ r` the
squeezing stage is just "read the leading `v` bits of the absorbing stage's
final state", so no squeeze rounds are needed and the round count is exactly
the block count.  That is what makes `cnt` exact, which is precisely what
`isDDC_ofStep` demands: a query is issued **iff** `ys.length < cnt m`. -/

/-- The absorbing sponge's protocol step: a permutation query per padded
block, then the squeezed digest. -/
def spongeStep (zero dflt : X) (absorb : X → X → X) (squeeze : X → D)
    (pad : M → List X) : M → List X → X ⊕ D :=
  fun m ys =>
    if ys.length < (pad m).length then
      Sum.inl (absorb (ys.getLastD zero) ((pad m).getD ys.length dflt))
    else Sum.inr (squeeze (ys.getLastD zero))

/-- The sponge issues a permutation query exactly while blocks remain — the
exact-count condition `isDDC_ofStep` requires. -/
theorem spongeStep_query_iff (zero dflt : X) (absorb : X → X → X)
    (squeeze : X → D) (pad : M → List X) (m : M) (ys : List X) :
    (∃ x, spongeStep zero dflt absorb squeeze pad m ys = Sum.inl x) ↔
      ys.length < (pad m).length := by
  by_cases h : ys.length < (pad m).length <;> simp [spongeStep, h]

/-- **The sponge converter**, attached at the honest interface: it consumes
the permutation port and offers the hash port. -/
def spongePrimitive (zero dflt : X) (absorb : X → X → X) (squeeze : X → D)
    (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) :
    Primitive Interface (signatures X M D) .honest :=
  Primitive.ofHistory .perm .hash
    (PFunConverter.ProtocolFn.ofStep
      (spongeStep zero dflt absorb squeeze pad) (fun m => (pad m).length))
    (PFunConverter.ProtocolFn.isDDC_ofStep _ _
      (spongeStep_query_iff zero dflt absorb squeeze pad)
      ⟨blockBound, padded⟩)

/-- The sponge protocol: the converter at `.honest`, identity elsewhere. -/
def spongeProtocol (zero dflt : X) (absorb : X → X → X) (squeeze : X → D)
    (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) :
    Protocol Interface (signatures X M D) :=
  Pi.mulSingle .honest
    (Gamma.ofPrimitive (spongePrimitive zero dflt absorb squeeze pad blockBound padded))

/-! ## The sponge's chaining, and the real world as a seeded evaluator

The chaining the converter drives, written directly as a function of the
primitive.  `spongeChain f m j` is the state after `j` absorbed blocks; the
sponge's answer is the squeeze of the state after all of them, and the
converter's own answer history reads back exactly these values. -/

/-- The state after absorbing `j` blocks of `pad m` through `f`. -/
def spongeChain (zero dflt : X) (absorb : X → X → X) (pad : M → List X)
    (f : X → X) (m : M) : ℕ → X
  | 0 => zero
  | j + 1 =>
      f (absorb (spongeChain zero dflt absorb pad f m j) ((pad m).getD j dflt))

/-- The primitive's input at block `j` of `pad m` — the point at which the
chaining evaluates `f`. -/
def spongeInput (zero dflt : X) (absorb : X → X → X) (pad : M → List X)
    (f : X → X) (m : M) (j : ℕ) : X :=
  absorb (spongeChain zero dflt absorb pad f m j) ((pad m).getD j dflt)

/-- The real world as a seeded history evaluator at the indifferentiability
boundary: the sponge outside, the primitive to the adversary. -/
def realDDS (zero dflt : X) (absorb : X → X → X) (squeeze : X → D)
    (pad : M → List X) (f : X → X) :
    DependentDDS (signatures X M D) (indifferentiabilityBoundary X M D) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.honest, m⟩ =>
        squeeze (spongeChain zero dflt absorb pad f m (pad m).length)
    | ⟨.adversary, x⟩ => f x

/-- The real world's law: the seeded evaluator over a uniform permutation. -/
def realLaw [Fintype X] [DecidableEq X] (zero dflt : X) (absorb : X → X → X)
    (squeeze : X → D) (pad : M → List X) :
    DependentPDS.Prob (signatures X M D) (indifferentiabilityBoundary X M D) :=
  ⟨Dist.fTransform
      (fun sigma : Equiv.Perm X => realDDS zero dflt absorb squeeze pad sigma)
      (Dist.uniform (Equiv.Perm X)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-! ## The ideal resource: the random oracle together with the simulator's coins -/

/-- The ideal resource at a fixed oracle and coin function: the oracle at
`.honest`, and at `.adversary` the same oracle plus a one-shot draw of the
coins. -/
def oracleCoinsDDS (seed : (M → D) × (X → X)) :
    DependentDDS (signatures X M D) (oracleCoinsBoundary X M D) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.honest, m⟩ => seed.1 m
    | ⟨.adversary, .inl m⟩ => Sum.inl (seed.1 m)
    | ⟨.adversary, .inr _⟩ => Sum.inr seed.2

/-- The uniform law of oracle and coins, drawn independently. -/
def oracleCoinsLaw [Fintype X] [DecidableEq X] [Fintype (M → D)]
    [Nonempty (M → D)] :
    DependentPDS.Prob (signatures X M D) (oracleCoinsBoundary X M D) :=
  letI : Nonempty (X → X) := ⟨id⟩
  ⟨Dist.fTransform (oracleCoinsDDS (X := X) (M := M) (D := D))
      (Dist.uniform ((M → D) × (X → X))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- **The ideal resource** — CR18's `𝖱` together with the simulator's local
randomness, the latter reachable only at `.adversary`. -/
def oracleCoinsResource [Fintype X] [DecidableEq X] [Fintype (M → D)]
    [Nonempty (M → D)] :
    Phi Interface (signatures X M D) :=
  ⟨oracleCoinsBoundary X M D,
    DependentRandomSystem.ofProb (oracleCoinsLaw (X := X) (M := M) (D := D))⟩

/-- The admitted simulator class: converter tuples supported at the
adversarial interface.  This is the same shape the channel constructions use
for Eve, and it is what `Indifferentiable`'s `σ ∈ H` ranges over. -/
def indifferentiabilitySimulators :
    Submonoid (Protocol Interface (signatures X M D)) :=
  supportedOn ({.adversary} : Set Interface) (fun _ => ⊤)

/-! ## A table-based simulator — **not** BDPV's, and superseded

Kept only because its parts (`Memory`, the table lookup, `unpad`) survive the
correction.  Its sampling rule does not.  Nothing downstream depends on it.

### What BDPV actually do (Algorithm 2, `papers/BDPV08_SpongeIndifferentiability.pdf`)

The graph has **nodes** `A × C` and **supernodes** `C` (§3.2): a supernode edge
`(s_c, t_c)` exists iff some node edge `((s_a, s_c), (t_a, t_c))` does.  `R ⊆ C`
is the rooted supernodes — `0^c` plus everything reachable from it — and a node
is rooted iff its capacity is.  `O ⊆ C` is the supernodes with an outgoing edge.
On a query at a node `s` with no outgoing edge:

* if `s` is rooted and `R ∪ O ≠ C`, take the path to `s`, append the block (a
  difference of `A`-parts — Lemma 1: "since `A` is a group, each `r`-bit block of
  the path is uniquely determined by the transitions on the `A`-part"), write the
  result as `p' 0^{r j}`, and if `p'` unpads to `x` set `t_a := z_j` for
  `z = RO(x)`; otherwise `t_a` uniform;
* **`t_c` uniform from `C \ (R ∪ O)`** — and this is the whole trick.  It makes
  every new rooted capacity fresh *by construction*, so the rooted supernodes
  form a **tree** (Lemma 1: at most one path per node) and the simulator is
  **exactly** sponge-consistent (Lemma 2).  No bad event, no conditioning;
* if `s` is not rooted, `t` uniform over all nodes.

Consequences for how this file should be organised, none of which the current
architecture reflects:

* **There is no capacity-collision MBO in BDPV's proof.**  Collisions are
  *prevented*, not tolerated-and-counted.  What can fail is **saturation**,
  `R ∪ O = C`, and `R ∪ O` grows by at most one per query, so it cannot happen
  before `2^c` queries — a hypothesis `N < 2^c`, not an event to bound.
* **The two interfaces collapse to one, by Lemma 3.**  The sponge is public, so a
  distinguisher can answer its own `H` queries from `F¹` queries at no greater
  cost; every `Q⁰` sequence is replaced by a `Q¹` sequence that is at least as
  informative.  So the leaf is a **one-port** advantage.  In this development
  that reduction is a converter/DPI step, not a two-port conditional
  equivalence.
* **The leaf is a switching lemma, not a birthday count.**  Lemma 4 bounds the
  advantage by the variational distance between uniform node answers and answers
  whose capacities are drawn without replacement:
  `f_T(N) = 1 - ∏_{i=1}^{N} (1 - i/2^c) ≈ N(N+1)/2^{c+1}`.  That is
  sampling-with- versus without-replacement on the capacity — the same shape as
  `RandomSystems.CR18.urf_urp_switching`, which this development already proves.
* **The permutation case (Algorithm 3)** additionally requires `t` to have no
  incoming edge (injectivity), and its `F⁻¹` interface draws `t_c` from `C \ R`
  among nodes with no outgoing edge, so an inverse query can never create a
  rooted node.  Theorem 2's bound is
  `f_P(N) = 1 - ∏_{i=0}^{N-1} (1 - (i+1)/2^c)/(1 - i/(2^r 2^c))`.
* **`N` is BDPV's *cost*** — total `F`/`F⁻¹` calls, direct or via the sponge
  (§3.5) — not a query count.

Modelling note for the rewrite: `t_c` uniform on `C \ (R ∪ O)` is not a draw from
a fixed set, so a coin resource of type `X → X` cannot supply it.  The natural
resource is a uniform `Equiv.Perm C` (or a sequence of them), used to take the
first capacity in that order avoiding `R ∪ O` — which keeps the "randomness lives
in resources, converters are deterministic" discipline intact.

### The superseded construction

Rootedness is decided from the simulator's
own **query/answer table**, not from the seed.  On a fresh permutation query `u`
it looks *backward* for the node it extends — the rooted node whose capacity
matches `u`'s — reads off the block by `unabsorb`, and asks `unpad` whether the
resulting block word is a complete padded message.  If it is, the answer's outer
part comes from the random oracle; otherwise the coins answer alone.

Three parameters that our eager simulator did not need, and each earns its keep:

* `cap` — the predecessor lookup is by capacity.  (Ours needed `cap` only in the
  MBO; here it is in the simulator itself.)
* `unabsorb` — recovers the absorbed block, `absorb s (unabsorb s x) = x`
  whenever `cap s = cap x`.  Concretely `(o, c) (o', c') ↦ (o' - o, 0)`.  Note
  that `absorb` itself never appears in this simulator: it walks the chain
  *backward* and only ever needs the inverse.  The law relating them is the
  coupling's business, not the simulator's.
* `unpad`, with `unpad (pad m) = some m` — deciding "this block word is a
  complete padded message" *without searching `M`* is exactly what makes this
  simulator efficient, and it is the assumption the eager version bought its way
  out of.

`Memory` is the state BDPV keep across queries.  `ofHistoryStep` hands a
converter all prior outer queries but only the current round's answers, so the
converter cannot keep that state — it replays the fold each round from `us` and
the seed.  `T` is free (one query, and the resource returns the same function
every round); `g` is not, which is what puts `us.length + 1` oracle slots in the
round count.  Quadratic overall, so still efficient in the sense
indifferentiability composition needs — but not BDPV's `O(1)` per query, and the
gap is an artifact of the converter interface rather than of the mathematics. -/

/-- **BDPV's simulator memory.**  The query/answer `table` it must stay
consistent with, and the `rooted` nodes it has *proved* reachable from `zero`,
each tagged with the block word that reaches it.

The gap between "reachable" and "proved reachable" is the whole reason this
simulator needs a second bad event: the adversary can query a genuinely rooted
point whose path is not yet in the table. -/
structure Memory (X : Type u) where
  /-- Query/answer pairs already fixed, in reverse order of asking. -/
  table : List (X × X)
  /-- Nodes proved reachable from the root, with the block word reaching each. -/
  rooted : List (X × List X)

/-- The initial memory: nothing answered, only the root known reachable. -/
def Memory.init (zero : X) : Memory X :=
  ⟨[], [(zero, [])]⟩

/-- **One BDPV step.**  Answer `u`, and record what answering it teaches.
Table consistency comes first — a repeated query gets its stored answer, which
is the invariant our eager simulator got for free. -/
def Memory.answer {C : Type u} [DecidableEq X] [DecidableEq C] (cap : X → C)
    (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (g : M → D) (T : X → X) (memory : Memory X)
    (u : X) : X × Memory X :=
  match memory.table.lookup u with
  | some y => (y, memory)
  | none =>
      match memory.rooted.find? fun node => decide (cap node.1 = cap u) with
      | none => (T u, ⟨(u, T u) :: memory.table, memory.rooted⟩)
      | some node =>
          let word := node.2 ++ [unabsorb node.1 u]
          let answer :=
            match unpad word with
            | some m => mk (g m) (T u)
            | none => T u
          (answer, ⟨(u, answer) :: memory.table, (answer, word) :: memory.rooted⟩)

/-- The memory BDPV's simulator holds after a history of permutation queries —
here rebuilt by replay, since the converter interface hides prior answers. -/
def bdpvMemory {C : Type u} [DecidableEq X] [DecidableEq C] (cap : X → C)
    (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (zero : X) (g : M → D) (T : X → X)
    (us : List X) : Memory X :=
  us.foldl
    (fun memory u =>
      (Memory.answer cap unabsorb mk unpad g T memory u).2)
    (Memory.init zero)

/-- **BDPV's answer** to `u`, after the history `us`. -/
def bdpvAns {C : Type u} [DecidableEq X] [DecidableEq C] (cap : X → C)
    (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (zero : X) (g : M → D) (T : X → X)
    (us : List X) (u : X) : X :=
  (Memory.answer cap unabsorb mk unpad g T
    (bdpvMemory cap unabsorb mk unpad zero g T us) u).1

/-- The message this step consults the random oracle at, if any: `u` is fresh,
extends a proved-reachable node, and the resulting block word unpads. -/
def Memory.oracleNeed {C : Type u} [DecidableEq X] [DecidableEq C]
    (cap : X → C) (unabsorb : X → X → X) (unpad : List X → Option M)
    (memory : Memory X) (u : X) : Option M :=
  match memory.table.lookup u with
  | some _ => none
  | none =>
      match memory.rooted.find? fun node => decide (cap node.1 = cap u) with
      | none => none
      | some node => unpad (node.2 ++ [unabsorb node.1 u])

/-- The oracle values a replay from `memory` consumes over the queries `us`, in
the order it meets them. -/
def bdpvOracleNeedsFrom {C : Type u} [DecidableEq X] [DecidableEq C]
    (cap : X → C) (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (g : M → D) (T : X → X) (memory : Memory X) :
    List X → List M
  | [] => []
  | u :: rest =>
      (memory.oracleNeed cap unabsorb unpad u).toList ++
        bdpvOracleNeedsFrom cap unabsorb mk unpad g T
          (Memory.answer cap unabsorb mk unpad g T memory u).2 rest

/-- The oracle values the full replay of `us` consumes.  Its length is what the
simulator's round count has to cover, and it is bounded by `us.length` — one
oracle query per permutation query, which is BDPV's own accounting. -/
def bdpvOracleNeeds {C : Type u} [DecidableEq X] [DecidableEq C] (cap : X → C)
    (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (zero : X) (g : M → D) (T : X → X)
    (us : List X) : List M :=
  bdpvOracleNeedsFrom cap unabsorb mk unpad g T (Memory.init zero) us

/-- **One oracle query per permutation query** — BDPV's accounting, and the
bound the round count is built on. -/
theorem length_bdpvOracleNeedsFrom_le {C : Type u} [DecidableEq X]
    [DecidableEq C] (cap : X → C) (unabsorb : X → X → X)
    (mk : D → X → X) (unpad : List X → Option M) (g : M → D) (T : X → X) :
    ∀ (memory : Memory X) (us : List X),
      (bdpvOracleNeedsFrom cap unabsorb mk unpad g T memory us).length ≤
        us.length := by
  intro memory us
  induction us generalizing memory with
  | nil => simp [bdpvOracleNeedsFrom]
  | cons u rest ih =>
      rw [bdpvOracleNeedsFrom, List.length_append, List.length_cons]
      have hone :
          (Memory.oracleNeed cap unabsorb unpad memory u).toList.length ≤ 1 := by
        cases Memory.oracleNeed cap unabsorb unpad memory u <;> simp
      have := ih (Memory.answer cap unabsorb mk unpad g T memory u).2
      omega

theorem length_bdpvOracleNeeds_le {C : Type u} [DecidableEq X] [DecidableEq C]
    (cap : X → C) (unabsorb : X → X → X) (mk : D → X → X)
    (unpad : List X → Option M) (zero : X) (g : M → D) (T : X → X)
    (us : List X) :
    (bdpvOracleNeeds cap unabsorb mk unpad zero g T us).length ≤
      us.length :=
  length_bdpvOracleNeedsFrom_le cap unabsorb mk unpad g T _ us

/-! ## Our simulator (kept: its coupling is proved)

Holding its coins `T`, this one does not need a query table: rootedness
is a function of the seed.  `simChain g T m j` is the state after `j` blocks of
`pad m` in the *ideal* world — the coins answer every intermediate block, and
the last block is answered by the random oracle, so that the sponge's outside
value comes out as `g m`.  `mk d y` re-glues a digest onto a coin value's
capacity; the two laws it must satisfy (`squeeze (mk d y) = d` and
`mk (squeeze y) y = y`) say exactly that `(squeeze, capacity)` splits the
state, and they are hypotheses of the leaf below rather than of these
definitions. -/

/-- The ideal-world state after absorbing `j` blocks of `pad m`. -/
def simChain (dflt : X) (zero : X) (absorb : X → X → X) (mk : D → X → X)
    (pad : M → List X) (g : M → D) (T : X → X) (m : M) : ℕ → X
  | 0 => zero
  | j + 1 =>
      let point :=
        absorb (simChain dflt zero absorb mk pad g T m j) ((pad m).getD j dflt)
      if j + 1 = (pad m).length then mk (g m) (T point) else T point

/-- The **last chain input** of `m` — the point at which the ideal world
consults the random oracle for `m`. -/
def simLci (dflt : X) (zero : X) (absorb : X → X → X) (mk : D → X → X)
    (pad : M → List X) (g : M → D) (T : X → X) (m : M) : X :=
  absorb
    (simChain dflt zero absorb mk pad g T m ((pad m).length - 1))
    ((pad m).getD ((pad m).length - 1) dflt)

/-- **The simulator's answer function.**  A query landing on some message's
last chain input is answered from the random oracle, with the capacity taken
from the coins; every other query is answered by the coins alone.  `ms` is the
fixed message enumeration that makes the choice among colliding messages
deterministic — a collision is exactly what `capacityBad` records. -/
def simAns [DecidableEq X] (ms : List M) (dflt : X) (zero : X)
    (absorb : X → X → X) (mk : D → X → X) (pad : M → List X) (g : M → D)
    (T : X → X) (x : X) : X :=
  match ms.find? fun m =>
      decide (pad m ≠ [] ∧ simLci dflt zero absorb mk pad g T m = x) with
  | some m => mk (g m) (T x)
  | none => T x

/-- The ideal world as a seeded history evaluator at the indifferentiability
boundary: the random oracle outside, the simulator to the adversary. -/
def idealDDS [DecidableEq X] (ms : List M) (dflt : X) (zero : X)
    (absorb : X → X → X) (mk : D → X → X) (pad : M → List X)
    (seed : (M → D) × (X → X)) :
    DependentDDS (signatures X M D) (indifferentiabilityBoundary X M D) :=
  DependentDDS.historyEvaluator fun history nonempty =>
    match history.getLast nonempty with
    | ⟨.honest, m⟩ => seed.1 m
    | ⟨.adversary, x⟩ =>
        simAns (X := X) (D := D) ms dflt zero absorb mk pad seed.1 seed.2 x

/-- The ideal world's law: the seeded evaluator over independent uniform
oracle and coins. -/
def idealLaw [Fintype X] [DecidableEq X] [Fintype (M → D)] [Nonempty (M → D)]
    (ms : List M) (dflt : X) (zero : X) (absorb : X → X → X) (mk : D → X → X)
    (pad : M → List X) :
    DependentPDS.Prob (signatures X M D) (indifferentiabilityBoundary X M D) :=
  letI : Nonempty (X → X) := ⟨id⟩
  ⟨Dist.fTransform (idealDDS ms dflt zero absorb mk pad)
      (Dist.uniform ((M → D) × (X → X))),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-! ### The simulator as a deterministic converter

The coins arrive in one query, then the oracle is read at every message, and
the answer is `simAns`.  The round count is therefore the constant
`ms.length + 1`, and the exact-count obligation of `isDDC_ofStep` — a query is
issued *iff* `ys.length < cnt` — holds by arithmetic alone. -/

/-- The oracle table the simulator reconstructs from its round's answers: the
`i`-th message's digest arrives at answer slot `i + 1`, the coins having taken
slot `0`. -/
def simulatorOracle [DecidableEq M] (ms : List M) (squeeze : X → D)
    (dflt : X) (ys : List (D ⊕ (X → X))) : M → D :=
  fun m =>
    match ys[ms.idxOf m + 1]? with
    | some (Sum.inl d) => d
    | _ => squeeze dflt

/-- The coin function the simulator reconstructs from answer slot `0`. -/
def simulatorCoins (ys : List (D ⊕ (X → X))) : X → X :=
  match ys[0]? with
  | some (Sum.inr T) => T
  | _ => id

/-- **The simulator's protocol step.**  Slot `0` draws the coins, slots
`1 … |ms|` read the oracle at every message, and the round then answers with
`simAns`.  The answer to the query issued at slot `k` arrives at `ys[k]`, which
is what `simulatorCoins` (slot `0`) and `simulatorOracle` (slot
`ms.idxOf m + 1`) read back.

The branch on `ys.length` is *not* interchangeable with `ms[ys.length - 1]?`:
`Nat` subtraction truncates, so the latter would issue `ms[0]?` at slot `0` and
again at slot `1` — never drawing the coins, and leaving `simulatorCoins` to
fall through to `id`. -/
def simulatorStep [DecidableEq X] [DecidableEq M] (ms : List M) (dflt : X)
    (zero : X) (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) : X → List (D ⊕ (X → X)) → (M ⊕ PUnit) ⊕ X :=
  fun x ys =>
    if ys.length < ms.length + 1 then
      match ys.length with
      | 0 => Sum.inl (Sum.inr PUnit.unit)
      | slot + 1 =>
          match ms[slot]? with
          | some m => Sum.inl (Sum.inl m)
          | none => Sum.inl (Sum.inr PUnit.unit)
    else
      Sum.inr
        (simAns ms dflt zero absorb mk pad
          (simulatorOracle ms squeeze dflt ys) (simulatorCoins ys) x)

/-- The simulator issues a query exactly while its fixed schedule is
unfinished — the exact-count condition `isDDC_ofStep` requires.  A constant
count makes it arithmetic. -/
theorem simulatorStep_query_iff [DecidableEq X] [DecidableEq M] (ms : List M)
    (dflt zero : X) (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) (x : X) (ys : List (D ⊕ (X → X))) :
    (∃ q, simulatorStep ms dflt zero absorb mk squeeze pad x ys = Sum.inl q) ↔
      ys.length < ms.length + 1 := by
  unfold simulatorStep
  by_cases h : ys.length < ms.length + 1
  · rw [if_pos h]
    refine ⟨fun _ => h, fun _ => ?_⟩
    match ys.length with
    | 0 => simp
    | slot + 1 => cases hslot : ms[slot]? <;> simp [hslot]
  · rw [if_neg h]
    simp [h]

/-- **The simulator**, attached at the adversarial interface: it consumes the
oracle-and-coins port and offers the permutation port. -/
def simulatorPrimitive [DecidableEq X] [DecidableEq M] (ms : List M)
    (dflt zero : X) (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) :
    Primitive Interface (signatures X M D) .adversary :=
  Primitive.ofHistory .hashCoins .perm
    (PFunConverter.ProtocolFn.ofStep
      (simulatorStep ms dflt zero absorb mk squeeze pad)
      (fun _ => ms.length + 1))
    (PFunConverter.ProtocolFn.isDDC_ofStep _ _
      (simulatorStep_query_iff ms dflt zero absorb mk squeeze pad)
      ⟨ms.length + 1, fun _ => le_refl _⟩)

/-- The simulator protocol: the converter at `.adversary`, identity
elsewhere. -/
def simulatorProtocol [DecidableEq X] [DecidableEq M] (ms : List M)
    (dflt zero : X) (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) :
    Protocol Interface (signatures X M D) :=
  Pi.mulSingle .adversary
    (Gamma.ofPrimitive
      (simulatorPrimitive ms dflt zero absorb mk squeeze pad))

/-- The simulator is admitted: it is supported at `.adversary`. -/
theorem simulatorProtocol_mem_simulators [DecidableEq X] [DecidableEq M]
    (ms : List M) (dflt zero : X) (absorb : X → X → X) (mk : D → X → X)
    (squeeze : X → D) (pad : M → List X) :
    simulatorProtocol ms dflt zero absorb mk squeeze pad ∈
      indifferentiabilitySimulators (X := X) (M := M) (D := D) := by
  refine AbstractCrypto.mem_supportedOn.mpr ⟨fun _ _ => Submonoid.mem_top _, ?_⟩
  intro interface outside
  unfold simulatorProtocol
  rw [Pi.mulSingle_eq_of_ne]
  exact outside

/-! ## The MBO: a capacity collision, over both ports

BDPV's bad event, with the "unrecognized rooted query" case removed by our
eager simulator — and that removal is exactly what costs us their efficiency.
What remains is Maurer's shape exactly: a non-trivial
collision at the input to the primitive, where non-trivial is measured in the
**capacity** and where the call sites range over *both* ports — the chaining's
inputs for every honest query, and the adversary's own points.  The extra
disjunct `cap (f u) = cap zero` is the capacity of the root, which must stay
fresh for the same reason. -/

/-- Every point at which the primitive is evaluated by a flat history: the
chaining's inputs for each honest query, and each adversarial point. -/
def evalPoints (zero dflt : X) (absorb : X → X → X) (pad : M → List X)
    (f : X → X) :
    List (Query (signatures X M D) (indifferentiabilityBoundary X M D)) →
      List X :=
  fun history =>
    history.flatMap fun query =>
      match query with
      | ⟨.honest, m⟩ =>
          (List.range (pad m).length).map
            (spongeInput zero dflt absorb pad f m)
      | ⟨.adversary, x⟩ => [x]

/-- **The MBO.**  A non-trivial capacity collision among the primitive's call
sites, or a call site whose answer hits the root capacity. -/
def capacityBad {C : Type u} (cap : X → C) (zero dflt : X)
    (absorb : X → X → X) (pad : M → List X) (f : X → X)
    (history :
      List (Query (signatures X M D) (indifferentiabilityBoundary X M D))) :
    Prop :=
  (∃ u ∈ evalPoints zero dflt absorb pad f history,
      ∃ v ∈ evalPoints zero dflt absorb pad f history,
        u ≠ v ∧ cap (f u) = cap (f v)) ∨
    ∃ u ∈ evalPoints zero dflt absorb pad f history, cap (f u) = cap zero

/-- The call sites of a prefix are call sites of the whole history. -/
theorem evalPoints_subset_of_prefix (zero dflt : X) (absorb : X → X → X)
    (pad : M → List X) (f : X → X)
    {left right :
      List (Query (signatures X M D) (indifferentiabilityBoundary X M D))}
    (hprefix : left <+: right) :
    evalPoints zero dflt absorb pad f left ⊆
      evalPoints zero dflt absorb pad f right := by
  obtain ⟨tail, rfl⟩ := hprefix
  intro point member
  unfold evalPoints at member ⊢
  rw [List.flatMap_append]
  exact List.mem_append_left _ member

/-- **The MBO is prefix-monotone** — CR18 Definition 3.22's requirement, and
what `Theorem417`'s reduction consumes. -/
theorem capacityBad_monotone {C : Type u} (cap : X → C) (zero dflt : X)
    (absorb : X → X → X) (pad : M → List X) (f : X → X)
    {left right :
      List (Query (signatures X M D) (indifferentiabilityBoundary X M D))}
    (hprefix : left <+: right)
    (bad : capacityBad cap zero dflt absorb pad f left) :
    capacityBad cap zero dflt absorb pad f right := by
  have hsub := evalPoints_subset_of_prefix zero dflt absorb pad f hprefix
  rcases bad with ⟨u, hu, v, hv, hne, hcap⟩ | ⟨u, hu, hcap⟩
  · exact Or.inl ⟨u, hsub hu, v, hsub hv, hne, hcap⟩
  · exact Or.inr ⟨u, hsub hu, hcap⟩

/-! ## The coupling: under the good event the two worlds *coincide*

The mathematical heart, and the reason the eager simulator is the right one.
Feed the real world the simulator's own answer function `simAns g T`.  Then the
real chaining is the ideal chaining step for step, so the real world's honest
port answers `g m` — the random oracle — and its adversary port answers
`simAns g T` by construction.  The two worlds are *equal*, not merely
indistinguishable.

Everything the argument needs from "no capacity collision" is isolated into two
hypotheses:

* `lciInj` — distinct messages have distinct last chain inputs, so the
  simulator's choice among them is forced;
* `interiorFresh` — no message's last chain input is hit by an *interior*
  chain input, so the oracle branch never fires early.

Both are consequences of `capacityBad` being false, and separating them is what
keeps the coupling free of the counting argument. -/

section Coupling

variable [DecidableEq X]

/-- `find?` on a predicate with a unique witness present in the list. -/
private theorem find?_eq_some_of_unique {α : Type u} (p : α → Bool) (l : List α)
    (a : α) (mem : a ∈ l) (holds : p a = true)
    (unique : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => exact absurd mem List.not_mem_nil
  | cons head tail ih =>
      by_cases hhead : p head = true
      · have hEq : head = a := unique head List.mem_cons_self hhead
        subst hEq
        simp [hhead]
      · rcases List.mem_cons.mp mem with rfl | tailMem
        · exact absurd holds hhead
        · rw [List.find?_cons_of_neg hhead]
          exact ih tailMem fun b bMem => unique b (List.mem_cons_of_mem _ bMem)

/-- **The coupling.**  Driven by the simulator's own answer function, the real
chaining *is* the ideal chaining, block for block. -/
theorem spongeChain_simAns_eq_simChain (ms : List M) (dflt zero : X)
    (absorb : X → X → X) (mk : D → X → X) (pad : M → List X) (g : M → D)
    (T : X → X) (enumerates : ∀ m, m ∈ ms)
    (lciInj : ∀ m m', pad m ≠ [] → pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m =
        simLci dflt zero absorb mk pad g T m' → m = m')
    (interiorFresh : ∀ m j, j + 1 < (pad m).length → ∀ m', pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m' ≠
        absorb (simChain dflt zero absorb mk pad g T m j)
          ((pad m).getD j dflt))
    (m : M) :
    ∀ j, j ≤ (pad m).length →
      spongeChain zero dflt absorb pad
          (simAns ms dflt zero absorb mk pad g T) m j =
        simChain dflt zero absorb mk pad g T m j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hjle : j ≤ (pad m).length := Nat.le_of_succ_le hj
      -- both worlds absorb block `j` into the *same* state, by induction
      have hstate := ih hjle
      show simAns ms dflt zero absorb mk pad g T
          (absorb
            (spongeChain zero dflt absorb pad
              (simAns ms dflt zero absorb mk pad g T) m j)
            ((pad m).getD j dflt)) = _
      rw [hstate]
      set point :=
        absorb (simChain dflt zero absorb mk pad g T m j) ((pad m).getD j dflt)
        with hpoint
      show simAns ms dflt zero absorb mk pad g T point = _
      unfold simAns
      rcases Nat.lt_or_ge (j + 1) (pad m).length with hlt | hge
      · -- interior block: the oracle branch must not fire
        have hnone :
            ms.find? (fun m' =>
                decide (pad m' ≠ [] ∧
                  simLci dflt zero absorb mk pad g T m' = point)) = none := by
          refine List.find?_eq_none.mpr fun m' _ hm' => ?_
          rw [decide_eq_true_eq] at hm'
          exact interiorFresh m j hlt m' hm'.1 hm'.2
        rw [hnone]
        show T point = _
        rw [simChain]
        exact (if_neg (by omega)).symm
      · -- last block: the point *is* this message's last chain input
        have hlen : j + 1 = (pad m).length := Nat.le_antisymm hj hge
        have hne : pad m ≠ [] := by
          intro hnil
          rw [hnil] at hlen
          exact Nat.succ_ne_zero j hlen
        have hlci : simLci dflt zero absorb mk pad g T m = point := by
          unfold simLci
          rw [hpoint, show (pad m).length - 1 = j by omega]
        have hsome :
            ms.find? (fun m' =>
                decide (pad m' ≠ [] ∧
                  simLci dflt zero absorb mk pad g T m' = point)) = some m := by
          refine find?_eq_some_of_unique _ _ _ (enumerates m)
            (by rw [decide_eq_true_eq]; exact ⟨hne, hlci⟩) fun m' _ hm' => ?_
          rw [decide_eq_true_eq] at hm'
          exact lciInj m' m hm'.1 hne (hm'.2.trans hlci.symm)
        rw [hsome]
        show mk (g m) (T point) = _
        rw [simChain]
        exact (if_pos hlen).symm

/-- **The real world's honest port answers the random oracle.**  The sponge's
digest of `m`, computed against the simulator's answer function, is `g m`. -/
theorem squeeze_spongeChain_simAns (ms : List M) (dflt zero : X)
    (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) (g : M → D) (T : X → X) (enumerates : ∀ m, m ∈ ms)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d) (padNe : ∀ m, pad m ≠ [])
    (lciInj : ∀ m m', pad m ≠ [] → pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m =
        simLci dflt zero absorb mk pad g T m' → m = m')
    (interiorFresh : ∀ m j, j + 1 < (pad m).length → ∀ m', pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m' ≠
        absorb (simChain dflt zero absorb mk pad g T m j)
          ((pad m).getD j dflt))
    (m : M) :
    squeeze
        (spongeChain zero dflt absorb pad
          (simAns ms dflt zero absorb mk pad g T) m (pad m).length) =
      g m := by
  rw [spongeChain_simAns_eq_simChain ms dflt zero absorb mk pad g T enumerates
    lciInj interiorFresh m (pad m).length (le_refl _)]
  obtain ⟨j, hj⟩ : ∃ j, (pad m).length = j + 1 :=
    ⟨(pad m).length - 1, by
      have := List.length_pos_of_ne_nil (padNe m); omega⟩
  rw [hj, simChain, if_pos hj.symm]
  exact split_squeeze _ _

/-- **The two worlds coincide under the coupling.**  Driven by `simAns g T`,
the real system *is* the ideal system: honest queries answer `g`, adversarial
queries answer the simulator.  This is the conditional-equivalence content at
the realization level — an equality of deterministic systems, with the good
event isolated in `lciInj`/`interiorFresh`. -/
theorem realDDS_simAns_eq_idealDDS (ms : List M) (dflt zero : X)
    (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) (g : M → D) (T : X → X) (enumerates : ∀ m, m ∈ ms)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d) (padNe : ∀ m, pad m ≠ [])
    (lciInj : ∀ m m', pad m ≠ [] → pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m =
        simLci dflt zero absorb mk pad g T m' → m = m')
    (interiorFresh : ∀ m j, j + 1 < (pad m).length → ∀ m', pad m' ≠ [] →
      simLci dflt zero absorb mk pad g T m' ≠
        absorb (simChain dflt zero absorb mk pad g T m j)
          ((pad m).getD j dflt)) :
    realDDS zero dflt absorb squeeze pad
        (simAns ms dflt zero absorb mk pad g T) =
      idealDDS (X := X) (D := D) ms dflt zero absorb mk pad (g, T) := by
  refine congrArg DependentDDS.historyEvaluator (funext fun history => ?_)
  funext nonempty
  rcases hlast : history.getLast nonempty with ⟨interface, value⟩
  cases interface with
  | honest =>
      show squeeze _ = _
      exact squeeze_spongeChain_simAns ms dflt zero absorb mk squeeze pad g T
        enumerates split_squeeze padNe lciInj interiorFresh value
  | adversary => rfl

end Coupling

/-! ## The statement, and the construction derived from it

Three named obligations remain, and the datum is now *derived* from them
rather than admitted:

* `spongeProtocol_smul_permResource` — the real side's normalization: what the
  sponge converter does to the permutation law;
* `simulatorProtocol_smul_oracleCoinsResource` — the ideal side's
  normalization, the same fact for the simulator;
* `maxAdvantage_realLaw_idealLaw_le` — the paper's leaf, one CR18 advantage
  between two flat PDS. -/

section Leaves

variable [Fintype X] [DecidableEq X] [DecidableEq M] [Fintype (M → D)]
variable [Nonempty (M → D)]

/-- **Real-side normalization.**  Attaching the sponge at `.honest` to the
uniform permutation is the seeded chaining evaluator.  Definitionally this is
`primitive_smul_coe_prob` followed by a `Primitive.ofHistory`/`ofStep`
realization equation at the `.honest` fibre, in the shape
`RandomSystems.CR18.apply_cbc_to_uniform_random_function_eq_real_system`
carries on the flat carrier. -/
theorem spongeProtocol_smul_permResource (zero dflt : X) (absorb : X → X → X)
    (squeeze : X → D) (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) :
    spongeProtocol zero dflt absorb squeeze pad blockBound padded •
        permResource (M := M) (D := D) =
      ((realLaw zero dflt absorb squeeze pad :
          DependentPDS.Prob (signatures X M D)
            (indifferentiabilityBoundary X M D)) :
        Phi Interface (signatures X M D)) := by
  sorry

/-- **Ideal-side normalization.**  Attaching the simulator at `.adversary` to
the oracle-and-coins resource is the seeded `simAns` evaluator.  Same shape as
the real side; the schedule the realization equation has to replay is the
constant one of `simulatorStep`. -/
theorem simulatorProtocol_smul_oracleCoinsResource (ms : List M)
    (dflt zero : X) (absorb : X → X → X) (mk : D → X → X) (squeeze : X → D)
    (pad : M → List X) :
    simulatorProtocol ms dflt zero absorb mk squeeze pad •
        oracleCoinsResource (X := X) (M := M) (D := D) =
      ((idealLaw ms dflt zero absorb mk pad :
          DependentPDS.Prob (signatures X M D)
            (indifferentiabilityBoundary X M D)) :
        Phi Interface (signatures X M D)) := by
  sorry

/-- **The paper's leaf**, and the only mathematical one: a CR18 maximal
distinguishing advantage between the two flattened global laws.  The
interfaces are tags in the flat alphabet here, so this is one ordinary
`PFunPDS` distance and the technique is `CBCMAC`'s.

Intended route, in order:

* switch the primitive from `𝖯 X` to `𝖱 X` (`urf_urp_switching` under the
  converter DPI, at `σ = q·blockBound + q'` primitive calls) — the exact
  fiber counting below is a counting argument over `X → X`, not over
  `Equiv.Perm X`;
* conditional equivalence of the real game against `idealLaw`, through
  `condEquiv_of_transcript_mass_reductions`.  Its three mass reductions are
  the packaged `massAfalse_fTransform_historyEvaluator` /
  `massY_fTransform_lastQuery` / `massYAfalse_fTransform_lastQuery`, as in
  `cbc_condEquiv`; the leaf is `hprod`, and under the split laws
  `squeeze (mk d y) = d`, `mk (squeeze y) y = y` it is a bijection rather
  than a count: `simAns g T` is exactly `|D|^|M|`-to-one onto the good
  primitives — off the `simLci` points the coins are pinned to `f`, and at
  `simLci m` the oracle value and the coin capacity are pinned while the
  coin's outer part stays free;
* CR18 Theorem 4.17 and the birthday count on `capacityBad`, giving the
  capacity bound (BDPV's shape, not their proof). -/
theorem maxAdvantage_realLaw_idealLaw_le (ms : List M) (zero dflt : X)
    (absorb : X → X → X) (squeeze : X → D) (mk : D → X → X)
    (pad : M → List X) (ε : ℝ)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d)
    (split_glue : ∀ y, mk (squeeze y) y = y) :
    Δ(DependentPDS.flatten (realLaw zero dflt absorb squeeze pad).val,
      DependentPDS.flatten (idealLaw ms dflt zero absorb mk pad).val) ≤ ε := by
  sorry

end Leaves

/-! ## The endpoints -/

section Endpoints

variable [Fintype X] [DecidableEq X] [DecidableEq M] [Fintype (M → D)]
variable [Nonempty (M → D)]

/-- **The indifferentiability datum, with both converters pinned.**  The sponge
converter — not merely *some* converter — makes the public permutation look
like a random oracle to a distinguisher that also holds direct permutation
access, up to `ε`, and the witness for `σ` is `simulatorProtocol` — *not* BDPV's
simulator, and in particular not an efficient one; the notion does not ask for
one, but a reader expecting the sponge literature's theorem should see the file
docstring first.

No longer admitted: it is the three obligations of the previous section,
composed through `edist_coe_prob_le_advantage`. -/
theorem sponge_indifferentiability_datum (ms : List M) (zero dflt : X)
    (absorb : X → X → X) (squeeze : X → D) (mk : D → X → X)
    (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) (ε : ℝ)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d)
    (split_glue : ∀ y, mk (squeeze y) y = y) :
    ∃ σ ∈ indifferentiabilitySimulators (X := X) (M := M) (D := D),
      edist
        (spongeProtocol zero dflt absorb squeeze pad blockBound padded •
          permResource (M := M) (D := D))
        (σ • oracleCoinsResource (X := X) (M := M) (D := D)) ≤
        ENNReal.ofReal ε := by
  refine ⟨simulatorProtocol ms dflt zero absorb mk squeeze pad,
    simulatorProtocol_mem_simulators ms dflt zero absorb mk squeeze pad, ?_⟩
  rw [spongeProtocol_smul_permResource zero dflt absorb squeeze pad blockBound
      padded,
    simulatorProtocol_smul_oracleCoinsResource ms dflt zero absorb mk squeeze
      pad]
  refine le_trans (edist_coe_prob_le_advantage _ _) (ENNReal.ofReal_le_ofReal ?_)
  exact maxAdvantage_realLaw_idealLaw_le ms zero dflt absorb squeeze mk pad ε
    split_squeeze split_glue

/-- The sponge is indifferentiable, with `π` witnessed by the sponge converter
and `σ` by the simulator. -/
theorem sponge_indifferentiable (ms : List M) (zero dflt : X)
    (absorb : X → X → X) (squeeze : X → D) (mk : D → X → X)
    (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) (ε : ℝ)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d)
    (split_glue : ∀ y, mk (squeeze y) y = y) :
    Indifferentiable (indifferentiabilitySimulators (X := X) (M := M) (D := D))
      (ENNReal.ofReal ε) (permResource (M := M) (D := D))
      (oracleCoinsResource (X := X) (M := M) (D := D)) :=
  ⟨spongeProtocol zero dflt absorb squeeze pad blockBound padded,
    sponge_indifferentiability_datum ms zero dflt absorb squeeze mk pad
      blockBound padded ε split_squeeze split_glue⟩

/-- **The public permutation constructs the random oracle.**  Derived from the
datum by `Indifferentiable.construct` (MauRen16 §4.2 Lemma 5), which is proved
in `AbstractCrypto`; nothing is re-proved here.  The ideal specification names
the oracle *with the simulator's local randomness alongside it*, which is what
a probabilistic simulator is in a deterministic-converter framework: the coins
are reachable only at `.adversary`, and only through `σ`. -/
theorem perm_constructs_random_oracle (ms : List M) (zero dflt : X)
    (absorb : X → X → X) (squeeze : X → D) (mk : D → X → X)
    (pad : M → List X) (blockBound : ℕ)
    (padded : ∀ m, (pad m).length ≤ blockBound) (ε : ℝ)
    (split_squeeze : ∀ d y, squeeze (mk d y) = d)
    (split_glue : ∀ y, mk (squeeze y) y = y) :
    ∃ π : Protocol Interface (signatures X M D),
      ({permResource (M := M) (D := D)} :
          Set (Phi Interface (signatures X M D))) —[π]→
        Relaxation.eball (ENNReal.ofReal ε)
          (Relaxation.star (indifferentiabilitySimulators (X := X) (M := M) (D := D))
            {oracleCoinsResource (X := X) (M := M) (D := D)}) :=
  (sponge_indifferentiable ms zero dflt absorb squeeze mk pad blockBound padded
    ε split_squeeze split_glue).construct

end Endpoints

end

end RandomSystemsCC.Symmetric.SpongeIndifferentiability
