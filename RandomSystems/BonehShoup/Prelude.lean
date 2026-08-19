/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Boneh–Shoup Part I as random systems: shared scaffolding

Boneh and Shoup, *A Graduate Course in Applied Cryptography* (v0.6, Jan 2023;
`papers/BonehShoup.pdf`).  This tree declares the **random system** underlying
each construction of Part I (Chapters 2–9, secret-key cryptography) and
nothing else: no security definitions, no advantage bounds, no theorems.  The
book's own attack games are already modeled elsewhere in this repository
(`RandomSystems.Complexity.GameBased` and friends); the point here is to fix
the *objects* those games would range over.

## What a "construction" becomes

A cipher, MAC, PRF or hash in the book is a family of deterministic algorithms
indexed by a key.  As a CR18 random system (`PFunPDS X Y`, a finite-support
law over deterministic systems) that is exactly `keyed`: sample the key once,
then answer every query with the keyed algorithm.  Schemes built *over* an
underlying primitive are instead declared as CR18 converters
(`PFunConverter.DDC`, Def. 3.8) and applied with `PFunPDS.applyDDC` (Def. 3.9),
following `RandomSystems.CR18.cbcReal` in `RandomSystems/CBCMAC.lean`: one
converter, then a choice of resource.  That way the same construction can be
read over a keyed primitive, over `𝖱`, or over `𝖯` without redefining it.

## Alphabets

Nothing here forces the query alphabet to be finite: `PFunPDS X Y` is a law
over deterministic `(X, Y)`-systems and is perfectly happy with `X = List G`.
Finiteness is needed only by the *ideal* reference objects — `PFunPDS.URF`
wants `Fintype (X → Y)` — so it is imposed on those, and only there.  The
book's `{0,1}^L` is carried abstractly as a finite `AddCommGroup`, with `⊕`
as the group operation; `Fin L → ZMod 2` is the intended instantiation, and
this is the same choice already made by `RandomSystemsCC.Symmetric.OTP`.
Deliberately *not* `BitVec L`: its `AddCommGroup` structure is addition mod
`2^L`, not XOR, so the group law would be the wrong one.

## Randomness

Schemes that toss coins per encryption (§5.4) do not get an ad-hoc coin
argument threaded through them.  They are converters over a **coin resource**
composed in parallel with the primitive, and the coin resource is `coins` —
which is literally a uniform random function.  See its docstring for why the
index type is where the finiteness lives.
-/

noncomputable section

namespace RandomSystems.BonehShoup

open RandomSystems (Dist)
open RandomSystems.CR18

universe u v w

/-! ## Strings

The book writes `{0,1}^L` for fixed-length strings and `{0,1}^{≤L}` for
strings of length at most `L`.  Both are carried here as lists over an
abstract symbol type, cut out by their length, so that the list operations the
constructions are written with apply directly. -/

/-- **The book's `{0,1}^L`**: strings of exactly length `L` over `A`. -/
abbrev Str (A : Type u) (L : ℕ) := {l : List A // l.length = L}

/-- **The book's `{0,1}^{≤L}`**: strings of length at most `L` over `A`,
including the empty string. -/
abbrev StrLE (A : Type u) (L : ℕ) := {l : List A // l.length ≤ L}

/-- **Partition a string into blocks of size `n`**, the last block short if
the length is not a multiple of `n`.  Used by the block-wise-to-bit-wise
conversion (§6.8), by CMAC's encoding (§6.10) and by Merkle–Damgård padding
(§8.4).  At `n = 0` there are no blocks, which keeps the recursion total. -/
def chunk {A : Type u} (n : ℕ) (l : List A) : List (List A) :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | n + 1, head :: tail =>
      (head :: tail).take (n + 1) :: chunk (n + 1) ((head :: tail).drop (n + 1))
  termination_by l.length
  decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-! ## Keyed systems

The generic shape of a secret-key primitive: one key, drawn once and fixed for
the lifetime of the system, and a deterministic algorithm evaluated at every
query.  This is CR18 Def. 3.15's "random function" specialized to a law that
factors through a key space. -/

/-- **A keyed random system.**  Sample `k` from `keyDist`, then answer every
query `x` with `F k x`.  The key is drawn *once*, so repeated queries are
answered consistently — which is what makes this a random system rather than a
fresh evaluation each time. -/
def keyed {K : Type w} {X : Type u} {Y : Type v}
    (keyDist : Dist K) (F : K → X → Y) : PFunPDS X Y :=
  PFunPDS.ofFunDist (Dist.fTransform F keyDist)

/-- **A uniformly keyed random system.**  The book always draws the key
uniformly from the key space (`k ←R K`), so this is the form nearly every
construction in Part I takes. -/
def uniformKeyed {K : Type w} [Fintype K] [Nonempty K] {X : Type u} {Y : Type v}
    (F : K → X → Y) : PFunPDS X Y :=
  keyed (Dist.uniform K) F

/-- A keyed system carries the mass of its key distribution, so a key law that
is a probability distribution yields a probability distribution over systems.
Stated once here so that no individual construction has to restate it. -/
@[simp] theorem keyed_isProbDist {K : Type w} {X : Type u} {Y : Type v}
    (keyDist : Dist K) (F : K → X → Y) :
    (keyed keyDist F : PFunPDS X Y).isProbDist ↔ keyDist.isProbDist := by
  unfold keyed
  rw [PFunPDS.isProbDist_ofFunDist_iff]
  exact ⟨fun h => by simpa [Dist.weight_fTransform] using h,
    fun h => by simpa [Dist.weight_fTransform] using h⟩

/-- A uniformly keyed system is a probability distribution over systems. -/
@[simp] theorem uniformKeyed_isProbDist {K : Type w} [Fintype K] [Nonempty K]
    {X : Type u} {Y : Type v} (F : K → X → Y) :
    (uniformKeyed F : PFunPDS X Y).isProbDist := by
  rw [uniformKeyed, keyed_isProbDist]
  exact Dist.uniform_isProbDist

/-- Every keyed system is a random function in the sense of CR18 Def. 3.15:
its support consists of stateless function evaluators. -/
theorem keyed_isRandomFunction {K : Type w} {X : Type u} {Y : Type v}
    (keyDist : Dist K) (F : K → X → Y) :
    PFunPDS.IsRandomFunction (keyed keyDist F : PFunPDS X Y) :=
  PFunPDS.ofFunDist_isRandomFunction _

/-! ## The coin resource

Constructions in §5.4 encrypt with fresh coins per message.  Rather than give
each such scheme its own randomness argument, the coins are a **resource**: an
independent system, composed in parallel (`PFunPDS.par`) with the primitive,
that the scheme's converter queries when it needs a fresh value.

Why the resource is indexed.  A `PFunPDS` is a *finite-support* law over
deterministic systems, and that is not a technicality that can be routed
around: a system answering `n` queries with independent uniform values from
`R` induces a transcript law with `|R|^n` atoms, while a law supported on `k`
deterministic systems induces at most `k`.  Taking `n` with `|R|^n > k`
refutes any finite-support representation of *unboundedly* many fresh coins.

What is representable is fresh randomness indexed by a *finite* type — and
that object already exists, as the uniform random function.  So `coins`
carries its budget in its index type `Ix`: the converter asks for coin `i` at
its `i`-th activation, `Ix = Fin q` bounds a `q`-query scheme, and repeated
requests for the same index are answered consistently, exactly as a URF. -/

/-- **The coin resource.**  A fresh uniform value of `R` per activation index:
`coins Ix R` is the uniform random function `Ix → R`.  A scheme needing
`q` independent coins takes `Ix = Fin q`.

This is definitionally `PFunPDS.URF`; it exists under its own name because it
plays a different role — a resource supplying randomness, not an ideal object
a construction is compared against — and because that role is what explains
the index type. -/
def coins (Ix : Type u) (R : Type v) [Fintype (Ix → R)] [Nonempty (Ix → R)] :
    PFunPDS Ix R :=
  PFunPDS.URF (X := Ix) (Y := R)

/-- The coin resource is a probability distribution over systems. -/
@[simp] theorem coins_isProbDist (Ix : Type u) (R : Type v)
    [Fintype (Ix → R)] [Nonempty (Ix → R)] :
    (coins Ix R).isProbDist :=
  PFunPDS.URF_isProbDist

end RandomSystems.BonehShoup
