/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BonehShoup.Ch9AE
import RandomSystems.CBCMAC

/-!
# Boneh–Shoup Part I: the constructions as CR18 converters

The chapter files declare each construction as an *algorithm* — a keyed
function — and attach the game oracle `uniformKeyed algorithm`.  That is the
book's own game-based reading, but it is the memoryless corner of the random-
system space: every such system is a stateless function evaluator
(`keyed_isRandomFunction`), so the RS layer does no work.

This file gives the modelling the repository already uses for CBC-MAC
(`RandomSystems/CBCMAC.lean`): **a construction is a converter, and the system
is that converter applied to a resource.**

## The resource discipline

In CR18 one does not model *the key*.  One models the **keyed primitive as a
resource**: `cbcReal = casc[CBC, 𝖱]` has no key anywhere, because the uniform
random function *is* the secret.  Consequences followed throughout:

* Independent keys become **independent resources in parallel**
  (`PFunPDS.par`), not a product key space.  `par R R` is the independent
  product, so ECBC's two keys are `par R R` with the same `R` written twice.
* Every construction is stated **over an abstract resource** and then read at
  the ideal object (`𝖱`, `𝖯`, `idealCipher`) or at a concrete keyed system
  (`prfSystem F`, `BlockCipher.system E`) — exactly the `cbcReal`/`cbcRealP`
  pair.
* A secret that is a *value* rather than a resource — Even–Mansour's pads,
  the cascade's initial key, CMAC's sub-keys, PMAC₀'s mask, the GGM root —
  is drawn from a **key port** placed in parallel, by the single combinator
  `keyedOver`.

## What is reused rather than rebuilt

`DDC.ofStep`, `DDC.simple` (Maurer's Def 4.20 simple converter),
`PFunPDS.applyDDC`, `PFunPDS.par`, and `RandomSystems.CR18.cbcStep` itself —
the CBC-MAC converter, which already takes a **block former** `bf`, so CMAC is
the same converter at a different `bf`.  Nothing here re-derives a converter
the repository already has.

## Junk histories

`ofStep` reads its step function only on protocol traces (DESIGN §10.5's
trace-tree discipline), so the combinators below choose an arbitrary value on
malformed answer lists.  Where a step is driven purely by `ys.length` the
Def 3.8 round bound `AnswersWithin` holds outright and is proved; the
tag-driven combinators satisfy it on traces only, and no `AnswersWithin` claim
is made for them.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter

universe u v w

/-! ## Reading tagged answers from a parallel resource -/

/-- The answers that came back from the left port of a parallel resource. -/
def leftAnswers {Y : Type u} {Y' : Type v} (ys : List (Y ⊕ Y')) : List Y :=
  ys.filterMap fun z => match z with | Sum.inl y => some y | Sum.inr _ => none

/-- The answers that came back from the right port of a parallel resource. -/
def rightAnswers {Y : Type u} {Y' : Type v} (ys : List (Y ⊕ Y')) : List Y' :=
  ys.filterMap fun z => match z with | Sum.inl _ => none | Sum.inr y => some y

/-! ## The two combinators -/

/-- **Key port.**  Draw a secret *value* from a key resource on the left port,
then run a converter parameterized by it against the right port.

This is what lets a construction whose secret is a value — Even–Mansour's
pads, the cascade's initial key, CMAC's sub-keys — keep the CR18 discipline
that converters are deterministic and all randomness lives in resources. -/
def withKeyStep {Kk : Type w} {U : Type u} {V X Y : Type v} [Inhabited V]
    (step : Kk → U → List Y → X ⊕ V) (u : U) (ys : List (Kk ⊕ Y)) :
    (Unit ⊕ X) ⊕ V :=
  match ys with
  | [] => Sum.inl (Sum.inl ())
  | Sum.inl k :: rest =>
      match step k u (rightAnswers rest) with
      | Sum.inl x => Sum.inl (Sum.inr x)
      | Sum.inr val => Sum.inr val
  | _ => Sum.inr default

/-- **A keyed construction over a resource**: the key port in parallel with
the primitive.  `keyedOver step R` samples `k` uniformly once and runs
`step k` against `R`. -/
def keyedOver {Kk : Type w} {U : Type u} {V X Y : Type v} [Inhabited V]
    [Fintype Kk] [Nonempty Kk]
    (step : Kk → U → List Y → X ⊕ V) (R : PFunPDS X Y) : PFunPDS U V :=
  PFunPDS.applyDDC (DDC.ofStep (withKeyStep step))
    (PFunPDS.par (uniformSource Kk) R)

/-- **Post-composition with one query to a second resource** — the shape of
Boneh–Shoup's encrypted PRF (§6.5) and of hash-then-PRF (§7.3): drive an inner
protocol against the left port, then feed its result through `post` into a
single query on the right port, and answer with that.

`encryptedPRF`, ECBC, NMAC and the PRF(UHF) composition are all this
combinator at different inner protocols. -/
def encStep {U : Type u} {V X Y X' Y' : Type v}
    (step : U → List Y → X ⊕ V) (post : V → X') (u : U) (ys : List (Y ⊕ Y')) :
    (X ⊕ X') ⊕ Y' :=
  match ys.getLast? with
  | some (Sum.inr y') => Sum.inr y'
  | _ =>
      match step u (leftAnswers ys) with
      | Sum.inl x => Sum.inl (Sum.inl x)
      | Sum.inr val => Sum.inl (Sum.inr (post val))

/-- **An inner protocol composed with an outer query**, over two independent
resources. -/
def encryptedOver {U : Type u} {V X Y X' Y' : Type v}
    (step : U → List Y → X ⊕ V) (post : V → X')
    (R : PFunPDS X Y) (R' : PFunPDS X' Y') : PFunPDS U Y' :=
  PFunPDS.applyDDC (DDC.ofStep (encStep step post)) (PFunPDS.par R R')

/-! ## §4.7.3 Even–Mansour and `EX`

Even–Mansour is *literally* Maurer's simple converter (CR18 Def 4.20):
translate the query by `P₁`, translate the answer by `P₂`. -/

variable {X : Type u} [AddCommGroup X]

/-- **The Even–Mansour converter at a fixed key**: `DDC.simple (· + P₁) (· + P₂)`. -/
def evenMansourConv (p₁ p₂ : X) : DDC X X X X :=
  DDC.simple (fun x => x + p₁) (fun y => y + p₂)

/-- **Even–Mansour over a resource** at a fixed pad pair. -/
def evenMansourOver (p₁ p₂ : X) (R : PFunPDS X X) : PFunPDS X X :=
  PFunPDS.applyDDC (evenMansourConv p₁ p₂) R

/-- **The Even–Mansour block cipher as a random system** (Boneh–Shoup §4.7.3):
the pads drawn from a key port, over an abstract permutation resource.  Read
at `PFunPDS.URP` this is exactly the ideal-permutation model in which
Theorem 4.14 is stated. -/
def evenMansourSystem [Fintype X] [DecidableEq X] (R : PFunPDS X X) : PFunPDS X X :=
  letI : Inhabited X := ⟨0⟩
  keyedOver (Kk := X × X) (fun k => DDC.simpleStep (fun x => x + k.1) (fun y => y + k.2)) R

/-- **`EX` as a random system**: the same construction over a *keyed* block
cipher resource rather than a fixed public permutation. -/
def exSystem [Fintype X] [DecidableEq X] {K : Type w} [Fintype K] [Nonempty K]
    (E : BlockCipher K X) : PFunPDS X X :=
  evenMansourSystem (E.system)

/-! ## §4.1.4 ECB and §4.4.4.1 deterministic counter mode -/

/-- **The ECB converter**: one inner query per message block, answering with
the block-wise images. -/
def ecbStep [Inhabited X] (m : List X) (ys : List X) : X ⊕ List X :=
  if ys.length < m.length then Sum.inl (m.getD ys.length default) else Sum.inr ys

omit [AddCommGroup X] in
/-- ECB answers within `L` rounds on messages of at most `L` blocks — CR18
Def 3.8's round bound. -/
theorem ecbStep_answersWithin [Inhabited X] {L : ℕ} (hL : ∀ m : List X, m.length ≤ L) :
    DDC.AnswersWithin (ecbStep (X := X)) L := by
  intro m ys hlen
  exact ⟨ys, by unfold ecbStep; rw [if_neg (by have := hL m; omega)]⟩

/-- **ECB mode over a resource** (Boneh–Shoup §4.1.4). -/
def ecbOver [Inhabited X] (R : PFunPDS X X) : PFunPDS (List X) (List X) :=
  PFunPDS.applyDDC (DDC.ofStep ecbStep) R

/-- **The deterministic counter-mode converter** (Boneh–Shoup §4.4.4.1): query
the resource at successive counter values, then XOR the answers into the
message.  The resource's inverse is never used. -/
def detCtrStep (ctr : ℕ → X) (m : List X) (ys : List X) : X ⊕ List X :=
  if ys.length < m.length then Sum.inl (ctr ys.length)
  else Sum.inr (xorKeystream ys m)

/-- Deterministic counter mode answers within `L` rounds. -/
theorem detCtrStep_answersWithin (ctr : ℕ → X) {L : ℕ}
    (hL : ∀ m : List X, m.length ≤ L) : DDC.AnswersWithin (detCtrStep ctr) L := by
  intro m ys hlen
  exact ⟨xorKeystream ys m, by unfold detCtrStep; rw [if_neg (by have := hL m; omega)]⟩

/-- **Deterministic counter mode over a resource.** -/
def detCtrOver (ctr : ℕ → X) (R : PFunPDS X X) : PFunPDS (List X) (List X) :=
  PFunPDS.applyDDC (DDC.ofStep (detCtrStep ctr)) R

/-! ## §4.5 Luby–Rackoff -/

/-- Read an answer off any of the three ports of `par (par R R) R`. -/
def leaf3 [Inhabited X] : ((X ⊕ X) ⊕ X) → X
  | Sum.inl (Sum.inl x) => x
  | Sum.inl (Sum.inr x) => x
  | Sum.inr x => x

/-- **The Luby–Rackoff converter** (Boneh–Shoup §4.5): three adaptive rounds
against three independent PRF resources,

  `w ← u ⊕ F(k₁, v)`,  `x ← v ⊕ F(k₂, w)`,  `y ← w ⊕ F(k₃, x)`.

Each round's query depends on the previous round's answer, so this is a
genuinely interactive converter — the `feedback` shape of DESIGN §10.2 at
three rounds and three ports. -/
def feistelStep [Inhabited X] (p : X × X) (ys : List ((X ⊕ X) ⊕ X)) :
    ((X ⊕ X) ⊕ X) ⊕ (X × X) :=
  match ys with
  | [] => Sum.inl (Sum.inl (Sum.inl p.2))
  | [y₁] => Sum.inl (Sum.inl (Sum.inr (p.1 + leaf3 y₁)))
  | [_, y₂] => Sum.inl (Sum.inr (p.2 + leaf3 y₂))
  | [y₁, y₂, y₃] => Sum.inr (p.2 + leaf3 y₂, p.1 + leaf3 y₁ + leaf3 y₃)
  | _ => Sum.inr (default, default)

/-- The Luby–Rackoff converter answers within three rounds. -/
theorem feistelStep_answersWithin [Inhabited X] :
    DDC.AnswersWithin (feistelStep (X := X)) 4 := by
  intro p ys hlen
  match ys with
  | [] => simp at hlen
  | [_] => simp at hlen
  | [_, _] => simp at hlen
  | [_, _, _] => simp at hlen
  | y₁ :: y₂ :: y₃ :: y₄ :: rest => exact ⟨(default, default), rfl⟩

/-- **The Luby–Rackoff block cipher over three resources** (Boneh–Shoup §4.5).
Read at `PFunPDS.URF` this is the object of the Luby–Rackoff theorem: three
rounds over independent uniform random functions is indistinguishable from a
uniform random permutation of `X²`. -/
def lubyRackoffOver [Inhabited X] (R : PFunPDS X X) : PFunPDS (X × X) (X × X) :=
  PFunPDS.applyDDC (DDC.ofStep feistelStep) (PFunPDS.par (PFunPDS.par R R) R)

/-! ## §4.6 The tree construction -/

/-- **The GGM tree converter at a fixed root** (Boneh–Shoup §4.6): walk down
the evaluation tree, expanding the current label with the PRG resource and
following the bits of the input. -/
def treeStepAt {K : Type v} [Inhabited K] (s : K) (x : List Bool) (ys : List (K × K)) :
    K ⊕ K :=
  let t := match ys.getLast? with
    | none => s
    | some p => if x.getD (ys.length - 1) false then p.2 else p.1
  if ys.length < x.length then Sum.inl t else Sum.inr t

/-- **The tree construction over a PRG resource** (Boneh–Shoup §4.6): the root
label drawn from a key port, every other label derived by the resource. -/
def treeOver {K : Type v} [Inhabited K] [Fintype K] [Nonempty K]
    (R : PFunPDS K (K × K)) : PFunPDS (List Bool) K :=
  keyedOver treeStepAt R

/-! ## §6.4.1 The CBC prefix-free PRF — the existing converter, unchanged -/

/-- **`F_CBC` over a resource** (Boneh–Shoup §6.4.1).  The converter is
`RandomSystems.CR18.cbcStep`, the CBC-MAC converter this repository already
has; only the choice of resource is new. -/
def cbcPRFOver {M : Type u} (bf : M → List X) (R : PFunPDS X X) : PFunPDS M X :=
  PFunPDS.applyDDC (DDC.ofStep (cbcStep bf)) R

/-- Read at the uniform random function, `cbcPRFOver` **is** `cbcReal` — the
system Maurer's CBC-MAC theorem (CR18 §6.2.3, Theorem 6.1) is about.  Stated
to pin the identification rather than to prove anything new. -/
theorem cbcPRFOver_urf_eq_cbcReal [Fintype X] [DecidableEq X] [Nonempty X]
    {M : Type u} (bf : M → List X) :
    cbcPRFOver bf (PFunPDS.URF (X := X) (Y := X)) = cbcReal bf :=
  rfl

/-- Read at the uniform random permutation, it is `cbcRealP` — the
block-cipher instantiation. -/
theorem cbcPRFOver_urp_eq_cbcRealP [Fintype X] [DecidableEq X] [Nonempty X]
    {M : Type u} (bf : M → List X) :
    cbcPRFOver bf (PFunPDS.URP X) = cbcRealP bf :=
  rfl

/-! ## §6.4.2 The cascade prefix-free PRF -/

/-- **The cascade converter at a fixed initial key** (Boneh–Shoup §6.4.2):
`t ← k; t ← F(t, aᵢ)`.  The running state is fed back as the resource's *key*
argument, which is why the cascade re-keys at every round. -/
def cascadeStepAt {K : Type v} {A : Type v} [Inhabited A] (k : K)
    (m : List A) (ts : List K) : (K × A) ⊕ K :=
  if ts.length < m.length then Sum.inl (ts.getLastD k, m.getD ts.length default)
  else Sum.inr (ts.getLastD k)

/-- **The cascade over a resource** (Boneh–Shoup §6.4.2): the initial key from
a key port, the compression from the resource. -/
def cascadeOver {K : Type v} {A : Type v} [Inhabited A] [Inhabited K]
    [Fintype K] [Nonempty K] (R : PFunPDS (K × A) K) : PFunPDS (List A) K :=
  keyedOver cascadeStepAt R

/-! ## §6.5 The encrypted PRF: ECBC and NMAC -/

/-- **ECBC over a resource** (Boneh–Shoup §6.5.1.1): CBC chaining on one
resource, then a single encrypting query on a second, independent one.

`par R R` is the *independent* product, so writing `R` twice is precisely the
book's requirement that ECBC's two keys be independent. -/
def ecbcOver {M : Type u} (bf : M → List X) (R : PFunPDS X X) : PFunPDS M X :=
  encryptedOver (cbcStep bf) id R R

/-- **NMAC over a resource** (Boneh–Shoup §6.5.1.2): the cascade, then the
final encrypting query through the pad `fpad`.

The inner resource is itself a parallel composite — the cascade's key port
beside its compression resource — which is the combinators composing.  The
outer resource `R'` is the second, independently keyed instance of the PRF, so
it already carries `k₂` and takes a bare `A` query. -/
def nmacOver {K : Type v} {A : Type v} [Inhabited A] [Inhabited K]
    [Fintype K] [Nonempty K] (fpad : K → A)
    (R : PFunPDS (K × A) K) (R' : PFunPDS A K) : PFunPDS (List A) K :=
  encryptedOver (withKeyStep cascadeStepAt) fpad
    (PFunPDS.par (uniformSource K) R) R'

/-! ## §6.10 CMAC — the CBC converter at a different block former -/

/-- **CMAC over a resource** (Boneh–Shoup §6.10).  CMAC *is* CBC chaining over
the randomized prefix-free encoding, so it is `cbcStep` at the block former
`cmacRpf`, with the sub-key pair drawn from a key port.

Nothing new is built: the converter is the one from `RandomSystems/CBCMAC.lean`. -/
def cmacOver {M : Type u} [Fintype X] [DecidableEq X]
    (blocks : M → List X × Bool) (R : PFunPDS X X) : PFunPDS M X :=
  letI : Inhabited X := ⟨0⟩
  keyedOver (Kk := X × X) (fun sk => cbcStep (fun m => cmacRpf blocks sk m)) R

/-! ## §6.11 PMAC₀ -/

/-- **The PMAC₀ converter at a fixed mask key** (Boneh–Shoup §6.11): every
block masked and queried independently on the left resource, the answers
XORed, then one query on the right resource.  No block waits for its
predecessor. -/
def pmac0StepAt {p : ℕ} {Y : Type v} {Z : Type v} [AddCommGroup Y] [Inhabited Z]
    (k : ZMod p) (m : List (ZMod p)) (ys : List (Y ⊕ Z)) : (ZMod p ⊕ Y) ⊕ Z :=
  let done := leftAnswers ys
  if done.length < m.length then
    Sum.inl (Sum.inl (m.getD done.length 0 + ((done.length + 1 : ℕ) : ZMod p) * k))
  else
    match ys.getLast? with
    | some (Sum.inr z) => Sum.inr z
    | _ => Sum.inl (Sum.inr (done.foldl (· + ·) 0))

/-- **PMAC₀ over two resources** (Boneh–Shoup §6.11). -/
def pmac0Over {p : ℕ} {Y : Type v} {Z : Type v} [AddCommGroup Y] [Inhabited Z]
    [NeZero p] (R : PFunPDS (ZMod p) Y) (R' : PFunPDS Y Z) :
    PFunPDS (List (ZMod p)) Z :=
  keyedOver (Kk := ZMod p) pmac0StepAt (PFunPDS.par R R')

/-! ## §8.4 Merkle–Damgård over a compression-function resource -/

/-- **The Merkle–Damgård converter** (Boneh–Shoup §8.4): chain the compression
resource over the padded blocks. -/
def mdStep {B : Type v} [Inhabited B] (iv : X) (blocks : List B) (ys : List X) :
    (X × B) ⊕ X :=
  if ys.length < blocks.length then
    Sum.inl (ys.getLastD iv, blocks.getD ys.length default)
  else Sum.inr (ys.getLastD iv)

/-- **Merkle–Damgård over a resource.**  Read at `PFunPDS.URF` this is the
random-oracle reading of the iterated hash; read at a concrete compression
function it is the deterministic hash of `Ch8Hash.lean`. -/
def mdOver {B : Type v} [Inhabited B] (iv : X) (R : PFunPDS (X × B) X) :
    PFunPDS (List B) X :=
  PFunPDS.applyDDC (DDC.ofStep (mdStep iv)) R

/-! ## §8.5.2 Davies–Meyer over the ideal cipher -/

/-- **The Davies–Meyer converter** (Boneh–Shoup §8.5.2): one query to the
cipher resource, keyed by the *message block*, with the chaining variable fed
forward — `h(x, y) := E(y, x) ⊕ x`.

Not a `simple` converter: the answer translation needs the outer query, since
`x` is added back after the call. -/
def dmStep {K : Type v} (q : X × K) (ys : List X) : (K × X) ⊕ X :=
  match ys with
  | [] => Sum.inl (q.2, q.1)
  | y :: _ => Sum.inr (y + q.1)

/-- Davies–Meyer answers within one round. -/
theorem dmStep_answersWithin {K : Type v} : DDC.AnswersWithin (dmStep (X := X) (K := K)) 1 := by
  intro q ys hlen
  match ys with
  | [] => simp at hlen
  | y :: _ => exact ⟨y + q.1, rfl⟩

/-- **Davies–Meyer over a cipher resource.**  Read at `idealCipher` this is
the ideal-cipher model in which Theorem 8.4 proves collision resistance — the
model is the resource. -/
def dmOver {K : Type v} (R : PFunPDS (K × X) X) : PFunPDS (X × K) X :=
  PFunPDS.applyDDC (DDC.ofStep dmStep) R

/-! ## §8.8.1 The sponge over an ideal permutation -/

/-- **The sponge converter** (Boneh–Shoup §8.8.1): absorb each padded block by
XORing it into the rate and permuting, then squeeze by permuting and reading
the rate off, until `v` bits have been produced.

The state is an abstract type `S`, *not* `List Bool`: the whole point of
reading the sponge at an ideal permutation is that `S` must be finite, and
`List Bool` is not.  `absorb` XORs a rate-width block into the state, `rate`
reads the leading `r` bits back off, and `S := Str Bool (r + c)` is the
intended instantiation. -/
def spongeStep {S : Type u} (zero : S) (absorb : S → List Bool → S)
    (rate : S → List Bool) (r v : ℕ) (M : List (List Bool)) (ys : List S) :
    S ⊕ List Bool :=
  let s := M.length
  let q := (v + r - 1) / r
  let h := ys.getLastD zero
  if ys.length < s then Sum.inl (absorb h (M.getD ys.length []))
  else if ys.length + 1 < s + q then Sum.inl h
  else Sum.inr ((((ys.drop (s - 1)).map rate).flatten).take v)

/-- **The sponge over a permutation resource** (Boneh–Shoup §8.8.1).  Read at
`PFunPDS.URP` — which now typechecks, since `S` is finite — this is the
**ideal permutation model**, exactly the setting of Theorem 8.6, so the sponge
becomes a genuine random-system composite rather than a bare function. -/
def spongeOver {S : Type u} (zero : S) (absorb : S → List Bool → S)
    (rate : S → List Bool) (r v : ℕ) (pad : List Bool → List (List Bool))
    (R : PFunPDS S S) : PFunPDS (List Bool) (List Bool) :=
  PFunPDS.applyDDC
    (DDC.ofStep fun M => spongeStep zero absorb rate r v (pad M)) R

/-! ## Bridges: the converter form computes the flat form

These are the theorems that make keeping both views honest.  They are *not*
`rfl`-by-redefinition: the left-hand side is a converter applied to a
resource through CR18 Def 3.9's fixed point, the right-hand side is the flat
keyed function from the chapter files, and `simple_apply` /
`applyDDC_simple_ofFunDist` are what connect them (DESIGN §10.2). -/

/-- **Maurer's simple converter over a keyed resource computes the composite
keyed function.**  Every construction expressible as `DDC.simple` — Even–
Mansour, `EX`, query/answer relabelings — collapses to its flat form by this
one lemma. -/
theorem applyDDC_simple_keyed {K : Type w} {U : Type u} {V X' Y' : Type v}
    (c : U → X') (d : Y' → V) (keyDist : Dist K) (F : K → X' → Y') :
    PFunPDS.applyDDC (DDC.simple c d) (keyed keyDist F)
      = keyed keyDist (fun k u => d (F k (c u))) := by
  unfold keyed
  rw [PFunPDS.applyDDC_simple_ofFunDist, Dist.fTransform_comp]
  rfl

/-- **Even–Mansour: the converter form is the flat block cipher.**  Applying
`evenMansourConv` to a keyed permutation resource yields the keyed function
`x ↦ E k (x + P₁) + P₂`, which is `evenMansour`/`ex` of `Ch4BlockCiphers.lean`. -/
theorem evenMansourOver_keyed {K : Type w} (p₁ p₂ : X) (keyDist : Dist K)
    (E : K → X → X) :
    evenMansourOver p₁ p₂ (keyed keyDist E)
      = keyed keyDist (fun k x => E k (x + p₁) + p₂) :=
  applyDDC_simple_keyed _ _ _ _

/-- **The converter form computes the flat cipher.**  Applying the
Even–Mansour converter to a block-cipher resource yields exactly the keyed
system of `evenMansour` from `Ch4BlockCiphers.lean` — so the two modellings of
§4.7.3 agree, and neither is a redefinition of the other. -/
theorem evenMansourOver_eq_evenMansour {K : Type w} (p₁ p₂ : X) (keyDist : Dist K)
    (E : BlockCipher K X) :
    evenMansourOver p₁ p₂ (keyed keyDist fun k => (E k : X → X))
      = keyed keyDist (fun k => (evenMansour (E k) (p₁, p₂) : X → X)) := by
  rw [evenMansourOver_keyed]
  rfl

end RandomSystems.BonehShoup
