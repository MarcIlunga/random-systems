/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Applications.Frost.Protocol
import Applications.Secp256k1

/-!
# Instantiating the FROST correctness theorems at a concrete group

This file is the **bridge** that makes the point of the whole
development concrete: the FROST correctness content is proved *once*,
abstractly, over any `[Field F] [AddCommGroup V] [Module F V]` with a
generator `g` (`AbstractCrypto.Frost`, `Applications.Frost.Protocol`
in the sibling `abstract-crypto` repository).  A concrete
instantiation — secp256k1 for the group, SHA-256 for the random oracle —
must therefore **not re-prove any security or correctness theorem**.  It
supplies only *structural* facts:

* the scalar set is a **field** — for `ZMod q`, exactly `Fact q.Prime`;
* the group is a **`ZMod q`-module** — for a prime-order group,
  `AddCommGroup.zmodModule` turns the single torsion fact
  `∀ P, q • P = 0` into the module structure (`x • g` then reads `gˣ`);
* a generator `g`.

Given those, every `Frost.*` theorem fires by *application*, with no new
proof.  `FrostGroup` below bundles exactly these obligations, and
`FrostGroup.completeness` restates FROST aggregation completeness at an
arbitrary such group as a one-line application of `Frost.verify_aggregate`
— the "instantiation is free" demonstration.

Two honest wrinkles, both *expected* and both *structural rather than
cryptographic*, are isolated here as named carrier obligations, exactly
as the library's carrier boundary anticipates (`LIBRARY_GUIDE.md`,
MauRen16 §5):

1. **`q` is prime** (`secp256k1_q_prime`).  `q` is a fixed 256-bit
   number; its primality is a finite check, but far past what the kernel
   or `norm_num` can run — so it enters as an axiom (a Pratt certificate
   would discharge it; that is deferred, not doubted).  It is *not* a
   security assumption.
2. **SHA-256 instantiates the random oracle**.  The RO is provably *not*
   realizable by a fixed public hash (MauRen16 §5); modeling SHA-256 as
   the RO resource is the standard idealization, an assumption at the
   carrier — the one genuine "miracle," expected for every ROM proof.

Nothing about unforgeability, simulation, or the aggregation algebra is
re-derived here — those live abstractly and transfer.
-/

open AbstractCrypto Frost Finset

namespace RandomSystemsCC.Frost

/-- A concrete realization of FROST's group: the structural interface a
carrier must satisfy for the abstract `Frost.*` theorems to fire.  It
carries *no* cryptographic content — only "scalars form a field of
order `q`" and "the group is a `ZMod q`-module with a generator." -/
structure FrostGroup where
  /-- The group order (the scalar field's cardinality). -/
  q : ℕ
  /-- `q` is prime — so `ZMod q` is a field.  A structural fact about a
  fixed number, not a hardness assumption. -/
  [qPrime : Fact (Nat.Prime q)]
  /-- The group carrier (the "exponentiation target"; `Additive G` for a
  multiplicative prime-order group `G`). -/
  V : Type
  [addCommGroup : AddCommGroup V]
  /-- The prime-order torsion fact: every element is killed by `q`.  This
  is what makes `V` a `ZMod q`-module. -/
  torsion : ∀ P : V, q • P = 0
  /-- A generator `g` (`x • g` reads `gˣ`). -/
  g : V

namespace FrostGroup

variable (G : FrostGroup)

instance : Fact (Nat.Prime G.q) := G.qPrime
instance : AddCommGroup G.V := G.addCommGroup

/-- The scalar field `ZMod q` — a field because `q` is prime
(mathlib's canonical instance, found from `Fact (Nat.Prime q)`). -/
example : Field (ZMod G.q) := inferInstance

/-- The group as a `ZMod q`-module, from the torsion fact — the single
structural obligation that "secp256k1 is a module" reduces to. -/
noncomputable instance instModule : Module (ZMod G.q) G.V :=
  AddCommGroup.zmodModule G.torsion

/-- **FROST aggregation completeness, instantiated** — the concrete
payoff.  For scalars in `ZMod q` and this group, the aggregate of a
quorum's honest signature shares passes plain Schnorr verification
against the group key `Y = gˣ`, whenever the Lagrange-weighted shares
reconstruct `x`.  The proof is *exactly* `Frost.verify_aggregate` at
`F := ZMod q`, `V := G.V`, `g := G.g`: no new reasoning, the abstract
theorem transferred. -/
theorem completeness {ι : Type} [DecidableEq ι] (S : Finset ι)
    (np : ι → NoncePair (ZMod G.q)) (ρ lam s : ι → ZMod G.q) (c x : ZMod G.q)
    (hx : ∑ l ∈ S, lam l * s l = x) :
    schnorrVerify G.g (x • G.g)
      (groupCommitment S (fun l => commitNonce G.g (np l)) ρ) c
      (aggregate S (fun l => signShare (np l) (ρ l) (lam l) (s l) c)) :=
  Frost.verify_aggregate G.g S np ρ lam s c x hx

/-- **Per-share verification, instantiated** — again a direct transfer of
`Frost.shareVerify_signShare`, no re-proof. -/
theorem share_verify (np : NoncePair (ZMod G.q))
    (ρ lam s c : ZMod G.q) :
    shareVerify G.g (commitNonce G.g np) (s • G.g) ρ lam c
      (signShare np ρ lam s c) :=
  Frost.shareVerify_signShare G.g np ρ lam s c

/-- **DKG quorum reconstruction, instantiated** — `Frost.dkg_reconstruct`
transferred: any two quorums of the combined DKG shares agree on the
joint secret. -/
theorem dkg_reconstruct_agree {ι κ : Type} [DecidableEq ι] (P : Finset κ)
    (a : κ → ℕ → ZMod G.q) {t : ℕ} (ht : 0 < t)
    {S S' : Finset ι} {v : ι → ZMod G.q}
    (hvS : Set.InjOn v S) (hvS' : Set.InjOn v S')
    (hS : t ≤ #S) (hS' : t ≤ #S') :
    ∑ i ∈ S, lagrangeZero S v i * (∑ j ∈ P, dealShare (a j) t (v i))
      = ∑ i ∈ S', lagrangeZero S' v i * (∑ j ∈ P, dealShare (a j) t (v i)) :=
  Frost.dkg_reconstruct_agree P a ht hvS hvS' hS hS'

end FrostGroup

/-! ### A fully-proved witness: the discrete-log-trivial group

`ZMod q` acting on itself, generator `1`, is a legitimate prime-order
group in which every abstract FROST identity holds — and it needs **no
axiom**: the torsion fact `q • x = 0` is `ZMod.natCast`-trivial.  This is
the cheapest possible carrier; it certifies the instantiation machinery
fires end-to-end.  (Cryptographically it is the trivial group — dlog is
the identity — but structurally it is exactly what the theorems ask for.)
-/

/-- The self-acting witness at any prime `q`. -/
noncomputable def selfGroup (q : ℕ) [Fact (Nat.Prime q)] : FrostGroup where
  q := q
  V := ZMod q
  torsion P := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  g := 1

/-- The witness genuinely instantiates completeness — no `sorry`, no
axiom (`selfGroup`'s torsion proof is `ZMod.natCast_self`).  Scalars are
written in `(selfGroup q).q` (definitionally `q`) so the group's module
instance resolves. -/
theorem selfGroup_completeness (q : ℕ) [Fact (Nat.Prime q)] {ι : Type}
    [DecidableEq ι] (S : Finset ι) (np : ι → NoncePair (ZMod (selfGroup q).q))
    (ρ lam s : ι → ZMod (selfGroup q).q) (c x : ZMod (selfGroup q).q)
    (hx : ∑ l ∈ S, lam l * s l = x) :
    schnorrVerify (selfGroup q).g (x • (selfGroup q).g)
      (groupCommitment S (fun l => commitNonce (selfGroup q).g (np l)) ρ) c
      (aggregate S (fun l => signShare (np l) (ρ l) (lam l) (s l) c)) :=
  (selfGroup q).completeness S np ρ lam s c x hx

/-! ### The secp256k1 scalar field and the named carrier obligations

The FROST(secp256k1, SHA-256) ciphersuite's scalar field is
`ZMod Secp256k1.q`.  Wiring the *actual* curve group into a `FrostGroup`
needs, beyond this file's abstract interface, the two structural facts
flagged in the module docstring — stated here as the explicit carrier
obligations, deliberately *not* proved (they are finite/idealization
facts, not security content):

* `secp256k1_q_prime` — primality of the group order (axiom pending a
  Pratt certificate);
* the affine point group `E(F_p)` as a `ZMod q`-module, i.e. the
  prime-order torsion `∀ P, q • P = 0` (the cofactor-1 fact) — which,
  once supplied, makes `E(F_p)` a `FrostGroup` by the interface above,
  with `g := basePoint`, and every `Frost.*` theorem then fires by
  `FrostGroup.completeness` and friends with no further proof.

The random oracle is instantiated by SHA-256 (via `hashToFieldQ` /
`expandMessageXmd` in `FrostRfc9591.lean`) at the resource layer — the
standard, unavoidable ROM idealization (MauRen16 §5). -/

/-- **Carrier obligation 1** — the order of secp256k1 is prime.  Held as
an axiom: a 256-bit primality check, discharge-able by a Pratt
certificate, well past the kernel's reach.  Structural, not a hardness
assumption. -/
axiom secp256k1_q_prime : Nat.Prime Secp256k1.q

/-- Obligation 1, in the form the FROST layer consumes it. -/
instance : Fact (Nat.Prime Secp256k1.q) := ⟨secp256k1_q_prime⟩

/-- The secp256k1 scalar field, `ZMod q`, is a field — mathlib's
canonical instance, now available from the obligation above. -/
example : Field (ZMod Secp256k1.q) := inferInstance

end RandomSystemsCC.Frost
