/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Frost.EndToEnd
import Applications.Frost.Protocol
import RandomSystems.Dist

/-!
# Distributed key generation (the DKG construction step)

Everything about FROST key generation, at the concrete random-systems
carrier: the threshold-key ideal as a resource, the DKG's reconstruction
algebra, the simulator's key programming, and the Gennaro–Jarecki–
Krawczyk–Rabin bias impossibility that fixes the ideal's shape.

The DKG step `ASSUMED —[π_dkg ; εDkg]→ KEYS∗Z` has a deterministic core
(discharged here) and one probabilistic residual (the random-oracle
programming coupling, the `DkgIndistinguishable` contract).

Contents:

* **The key ideal** (`keyResource`) — a uniform Shamir sharing on the
  carrier exposing per-party shares, the group key, and public-key shares,
  with VSS consistency (`keyAnswer_vss`), the group-key/constant relation
  (`keyAnswer_groupKey`), and single-dealer quorum reconstruction
  (`key_reconstruct`, via the proven `shamir_reconstruct_smul`).
* **The DKG reconstruction** — the multi-dealer (Komlo–Goldberg) joint key
  as the sum of dealer constants (`dkg_groupKey_eq`) and quorum
  reconstruction of the joint key in the exponent (`dkg_key_reconstruct`,
  via the proven `dkg_reconstruct`).
* **The simulator's key programming** (`dkgHonestContribution`,
  `key_matches`) — the ideal key is reachable for every adversarial bias
  (`dkg_key_bias_split`); the deterministic content of the DKG leaf for a
  dishonest set.
* **The impossibility** (`uniform_key_dkg_impossible`) — against a
  *uniform-key* ideal no simulator beats distance `1/2`, forcing the
  bias-absorbing ideal.

The residual `εDkg` — the transcript indistinguishability coupling — is the
`DkgIndistinguishable` contract; the algebra it rests on is proved here.
-/

namespace RandomSystemsCC.Frost

open AbstractCrypto AbstractCrypto.Frost
open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open Polynomial
open scoped ENNReal

/-! ## The threshold-key ideal as a carrier resource -/

namespace KeyResource

/-- Party queries of the threshold-key ideal. -/
inductive Query (n : ℕ) where
  | getShare
  | getGroupKey
  | pkShare (holder : Fin n)
  deriving DecidableEq

/-- Answers: a scalar (a share) or a group element (a key). -/
inductive Answer (F V : Type) where
  | scalar (value : F)
  | point (value : V)
  deriving DecidableEq

/-- The key ideal's signature universe: one code, party interfaces. -/
abbrev sig (F V : Type) (n : ℕ) : SignatureUniverse where
  Code := Unit
  input _ := Query n
  output _ := Answer F V

instance (F V : Type) (n : ℕ) : DecidableEq (sig F V n).Code := by
  change DecidableEq Unit; infer_instance

end KeyResource

/-- The sharing-polynomial evaluation `f(x) = Σ_{k<t} aₖ·xᵏ`. -/
def evalShare {G : FrostGroup} {t : ℕ} (poly : Fin t → ZMod G.q)
    (x : ZMod G.q) : ZMod G.q :=
  ∑ k : Fin t, poly k * x ^ (k : ℕ)

/-- The constant term is the evaluation at `0`. -/
theorem evalShare_zero {G : FrostGroup} {t : ℕ} (poly : Fin t → ZMod G.q)
    (ht : 0 < t) : evalShare poly 0 = poly ⟨0, ht⟩ := by
  rw [evalShare, Finset.sum_eq_single (⟨0, ht⟩ : Fin t)]
  · simp
  · intro k _ hk
    have : (k : ℕ) ≠ 0 := by intro h; exact hk (Fin.ext h)
    rw [zero_pow this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

open KeyResource in
/-- The resource's answer to one query, at a fixed sharing polynomial. -/
noncomputable def keyAnswer {G : FrostGroup} {n t : ℕ} (pid : Fin n → ZMod G.q)
    (poly : Fin t → ZMod G.q) : (i : Fin n) → Query n → Answer (ZMod G.q) G.V
  | i, .getShare => Answer.scalar (evalShare poly (pid i))
  | _, .getGroupKey => Answer.point (evalShare poly 0 • G.g)
  | _, .pkShare j => Answer.point (evalShare poly (pid j) • G.g)

open KeyResource in
/-- The deterministic key resource at a fixed sharing polynomial. -/
noncomputable def keyDDS {G : FrostGroup} {n t : ℕ} (pid : Fin n → ZMod G.q)
    (poly : Fin t → ZMod G.q) :
    DependentDDS (sig (ZMod G.q) G.V n) (fun _ : Fin n => ()) :=
  DependentDDS.functionEvaluator fun query => keyAnswer pid poly query.1 query.2

open KeyResource in
/-- **VSS consistency**: `pkShare j` returns `sⱼ·g` where `getShare` at
interface `j` returns `sⱼ` — the Feldman relation, by construction. -/
theorem keyAnswer_vss {G : FrostGroup} {n t : ℕ} (pid : Fin n → ZMod G.q)
    (poly : Fin t → ZMod G.q) (i j : Fin n) :
    keyAnswer pid poly i (.pkShare j) =
      match keyAnswer pid poly j .getShare with
      | .scalar s => Answer.point (s • G.g)
      | .point _ => keyAnswer pid poly i (.pkShare j) :=
  rfl

open KeyResource in
/-- **The group key is the constant coefficient in the exponent**,
`Y = a₀·g`. -/
theorem keyAnswer_groupKey {G : FrostGroup} {n t : ℕ} (pid : Fin n → ZMod G.q)
    (poly : Fin t → ZMod G.q) (i : Fin n) (ht : 0 < t) :
    keyAnswer pid poly i .getGroupKey = Answer.point (poly ⟨0, ht⟩ • G.g) := by
  rw [keyAnswer, evalShare_zero poly ht]

open scoped Classical in
/-- `ZMod q` is finite because `q` is prime. -/
noncomputable instance (G : FrostGroup) : Fintype (ZMod G.q) := by
  haveI : NeZero G.q := ⟨(Fact.out (p := Nat.Prime G.q)).pos.ne'⟩
  infer_instance

open KeyResource in
/-- The threshold-key ideal's law: a uniformly sampled sharing polynomial,
pushed through `keyDDS`. -/
noncomputable def keyLaw {G : FrostGroup} {n : ℕ} (t : ℕ)
    (pid : Fin n → ZMod G.q) :
    DependentPDS.Prob (sig (ZMod G.q) G.V n) (fun _ : Fin n => ()) :=
  ⟨Dist.fTransform (keyDDS pid) (Dist.uniform (Fin t → ZMod G.q)),
   Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

open KeyResource in
/-- The threshold-key ideal as a heterogeneous typed AC resource. -/
noncomputable def keyResource {G : FrostGroup} {n : ℕ} (t : ℕ)
    (pid : Fin n → ZMod G.q) :
    TypedFinite.Phi (Fin n) (sig (ZMod G.q) G.V n) :=
  ⟨fun _ => (), DependentRandomSystem.ofProb (keyLaw t pid)⟩

/-- The sharing polynomial in `Polynomial` form, bridging to the Lagrange
API. -/
noncomputable def sharePoly {G : FrostGroup} {t : ℕ} (poly : Fin t → ZMod G.q) :
    (ZMod G.q)[X] :=
  ∑ k : Fin t, Polynomial.C (poly k) * Polynomial.X ^ (k : ℕ)

theorem sharePoly_eval {G : FrostGroup} {t : ℕ} (poly : Fin t → ZMod G.q)
    (x : ZMod G.q) : (sharePoly poly).eval x = evalShare poly x := by
  simp [sharePoly, evalShare, Polynomial.eval_finset_sum]

theorem sharePoly_degree_lt {G : FrostGroup} {t : ℕ} (poly : Fin t → ZMod G.q)
    {m : ℕ} (h : t ≤ m) : (sharePoly poly).degree < m := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe m)]
  intro k _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast lt_of_lt_of_le k.isLt h

/-- **Single-dealer quorum reconstruction in the exponent**: a quorum of
size at least `t` with distinct identifiers recombines its public key
shares, Lagrange-weighted, to `Y = f(0)·g` (`shamir_reconstruct_smul`). -/
theorem key_reconstruct {G : FrostGroup} {n t : ℕ} (pid : Fin n → ZMod G.q)
    (poly : Fin t → ZMod G.q) {S : Finset (Fin n)}
    (hvs : Set.InjOn pid S) (hcard : t ≤ S.card) :
    ∑ i ∈ S, lagrangeZero S pid i • (evalShare poly (pid i) • G.g) =
      evalShare poly 0 • G.g := by
  have h := shamir_reconstruct_smul (F := ZMod G.q) (V := G.V) G.g
    (s := S) (v := pid) hvs (f := sharePoly poly)
    (sharePoly_degree_lt poly hcard)
  simpa only [sharePoly_eval] using h

/-! ## The multi-dealer DKG: reconstruction and the simulator's programming -/

namespace FrostGroup

variable (G : FrostGroup)

/-- The DKG's **combined share** at `x`: the sum over dealers of each
dealer's Shamir share. -/
def dkgShare {κ : Type} (P : Finset κ) (a : κ → ℕ → ZMod G.q) (t : ℕ)
    (x : ZMod G.q) : ZMod G.q :=
  ∑ j ∈ P, dealShare (a j) t x

/-- **The joint group key is the sum of the dealers' constants in the
exponent** — `Y = (Σⱼ aⱼ₀)·g` (`key_aggregation`). -/
theorem dkg_groupKey_eq {κ : Type} (P : Finset κ) (a : κ → ℕ → ZMod G.q) :
    (∑ j ∈ P, a j 0) • G.g = ∑ j ∈ P, (a j 0) • G.g :=
  key_aggregation G.g (fun j => a j 0)

/-- **Quorum reconstruction of the joint key, in the exponent** — the DKG's
threshold guarantee, `dkg_reconstruct` pushed through `• g`. -/
theorem dkg_key_reconstruct {κ ι : Type} [DecidableEq ι]
    (P : Finset κ) (a : κ → ℕ → ZMod G.q) {t : ℕ} (ht : 0 < t)
    {S : Finset ι} {v : ι → ZMod G.q} (hvs : Set.InjOn v S) (hcard : t ≤ S.card) :
    ∑ i ∈ S, lagrangeZero S v i • (G.dkgShare P a t (v i) • G.g) =
      (∑ j ∈ P, a j 0) • G.g := by
  rw [← dkg_reconstruct P a ht hvs hcard, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dkgShare, mul_smul]

/-- **The DKG simulator's key programming**: holding the ideal key `target`
and the dishonest contribution `dishon`, the simulator posts this honest
contribution so the reconstructed key hits `target`. -/
def dkgHonestContribution (target dishon : G.V) : G.V :=
  target - dishon

/-- **The programmed key matches the ideal** for *any* adversarial `dishon`
(`key_bias_absorb`) — the deterministic heart of the zero-distance DKG
simulator, which the uniform-key ideal cannot offer. -/
theorem key_matches (target dishon : G.V) :
    G.dkgHonestContribution target dishon + dishon = target :=
  key_bias_absorb target dishon

/-- The key programming is injective in the target. -/
theorem key_programming_injective (dishon : G.V) :
    Function.Injective (fun target => G.dkgHonestContribution target dishon) := by
  intro a b h
  simpa [dkgHonestContribution, sub_left_injective] using h

/-- **Honest/dishonest bias split** of the joint key in the exponent
(`key_bias_decomposition`): with `key_matches`, the simulator hits the ideal
key for every adversarial contribution. -/
theorem dkg_key_bias_split {κ : Type} [DecidableEq κ]
    {H D : Finset κ} (hdisj : Disjoint H D) (a : κ → ℕ → ZMod G.q) :
    (∑ j ∈ H ∪ D, a j 0) • G.g =
      (∑ j ∈ H, a j 0) • G.g + (∑ j ∈ D, a j 0) • G.g :=
  key_bias_decomposition G.g hdisj (fun j => a j 0)

/-- **The DKG coupling contract** (the residual probabilistic input): a
simulator run against the bias-absorbing key ideal produces a joint
transcript identically distributed to the real DKG (`εDkg = 0`).  The
machine-checked random-oracle-programming coupling discharges this; the
deterministic core it feeds (`key_matches`) is proved above. -/
def DkgIndistinguishable {Ω transcript : Type}
    (real sim : Ω → transcript) (coupled : Prop) : Prop :=
  coupled → ∀ ω, real ω = sim ω

end FrostGroup

/-! ## The Gennaro–Jarecki–Krawczyk–Rabin bias impossibility

Against a *uniform-key* ideal, no DKG simulator can be close: a rushing
adversary biases the group key and the ideal cannot follow.  This forces
the bias-absorbing key ideal. -/

namespace Setup

variable {F V Msg SId RoIn : Type} {n τ : ℕ} (S : Setup F V Msg SId RoIn n τ)

/-- **The DKG-bias distance lower bound.**  If the real DKG drives an
admitted distinguisher `bias` to at least `real` while every simulated
ideal caps it at `ideal`, then any `εDkg` for the DKG leaf is at least the
gap `real - ideal`. -/
theorem dkg_distanceLowerBound {t : ℕ} {εDkg : ℝ≥0∞}
    (hleaf : S.DkgLeaf t εDkg)
    {Z : Set (Fin n)} (hZ : Z ∈ (AdversaryStructure.threshold n t).sets)
    {R : Carrier F V Msg SId RoIn n τ} (hR : R ∈ S.net Z)
    {bias : Carrier F V Msg SId RoIn n τ → ℝ≥0∞}
    (hbias : bias ∈ S.dist.tests)
    {real ideal : ℝ≥0∞}
    (hreal : real ≤ bias (patternAttach Zᶜ S.dkg • R))
    (hideal : ∀ s ∈ zSub (M := Proto F V Msg SId RoIn n τ) tupleGamma Z,
      bias (s • S.keys) ≤ ideal) :
    real - ideal ≤ εDkg := by
  obtain ⟨s, hs, hdist⟩ := hleaf Z hZ R hR
  have hedistD : S.dist.edistD (patternAttach Zᶜ S.dkg • R) (s • S.keys) ≤ εDkg :=
    (S.distLe _ _).trans hdist
  have hadv :
      bias (patternAttach Zᶜ S.dkg • R) - bias (s • S.keys) ≤ εDkg :=
    S.dist.test_left_tsub_right_le_of_edistD_le hbias hedistD
  refine le_trans ?_ hadv
  exact tsub_le_tsub hreal (hideal s hs)

/-- **The uniform-key DKG impossibility** — stated honestly as a
*conditional* lower bound.  If the adversary forces `bias` to `1` while the
uniform-key ideal keeps it at `1/2 + η` for every simulator, no DKG leaf
beats `1/2 - η`.

**Honesty note.**  The bias gap here (`hforced`, `huniform`) is
**assumed**, not derived: this theorem does not attempt the concrete
uniform-key DKG construction and discover the obstruction — it takes the
Gennaro–Jarecki–Krawczyk–Rabin gap as a hypothesis and computes its
consequence.  To make the bias *appear as a proof obligation* one must
follow the `RandomSystemsCC.LiftingExample` method: declare the concrete
coins resource and DKG converter at the RS level, attempt the construction
`coins —[π_dkg]→ keyResource` by proving `π_dkg • coins = s • keyResource`,
and find that for a dishonest `Z` no post-hoc simulator `s` can reproduce
the adversarially-biased key `keyResource` holds uniform — that stuck goal
*is* the bias.  `hforced` (the actual GJKR attack) would then be a proved
lemma about `π_dkg`, not a hypothesis.  Until that concrete construction is
built, this is an honest conditional statement, not a derivation. -/
theorem uniform_key_dkg_impossible {t : ℕ} {εDkg η : ℝ≥0∞}
    (hleaf : S.DkgLeaf t εDkg)
    {Z : Set (Fin n)} (hZ : Z ∈ (AdversaryStructure.threshold n t).sets)
    {R : Carrier F V Msg SId RoIn n τ} (hR : R ∈ S.net Z)
    {bias : Carrier F V Msg SId RoIn n τ → ℝ≥0∞}
    (hbias : bias ∈ S.dist.tests)
    (hforced : 1 ≤ bias (patternAttach Zᶜ S.dkg • R))
    (huniform : ∀ s ∈ zSub (M := Proto F V Msg SId RoIn n τ) tupleGamma Z,
      bias (s • S.keys) ≤ 1 / 2 + η) :
    1 / 2 - η ≤ εDkg := by
  have hgap := S.dkg_distanceLowerBound hleaf hZ hR hbias hforced huniform
  rwa [← tsub_tsub, (by norm_num : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2)] at hgap

end Setup

end RandomSystemsCC.Frost
