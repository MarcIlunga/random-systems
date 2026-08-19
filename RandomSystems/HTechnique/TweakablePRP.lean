/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Derivation
import RandomSystems.HTechnique.StrongPRP

/-!
# The generic tweakable-PRP leg (`TweakablePRP`)

The PRP-RND leg of an H-technique proof (ePrint 2021/1441 §3.5, [HR03] App. C Lemma 6),
proven ONCE over a parametric fiber family `MsgK : Fin K → Type`:

* the worlds — `TweakablePRP.tprp` (`±p̃rp`, one uniform permutation per `(tweak, length)`) and
  `TweakablePRP.rnd` (`±rnd`, fresh-uniform length-preserving answers);
* the §3.4 no-pointless filter `TweakablePRP.NP` (`pinnedIO`-based) and the generic endpoint
  **`TweakablePRP.tprp_rnd`**: `Adv(±rnd, ±p̃rp) ≤ C(q,2)/N_min` under the filter, for any
  per-fiber cardinality lower bound `N_min`;
* the generic reveal-collapse spine of the extended-transcript main lemma
  (`section Collapse`, reveal-type `Z` generic): `TweakablePRP.idealExtZ_apply`,
  `TweakablePRP.idealTr_vanish`, `TweakablePRP.revealCollapseZ_le`, `TweakablePRP.pairMassZ_le_of_reveal`,
  `TweakablePRP.omegaSliceZ_le`.

`HCTR2.lean` instantiates the leg twice — block-aligned fibers `MsgK := Msg F`
(`N_min = |F|`, reveal `Z = F × F`) and bit-level fibers (`Z = F × F × (Fin q → F)`).
Any future length-preserving cipher proof can consume it without importing HCTR2.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.CR18

open RandomSystems.CR18 RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique (QueryDir)
open RandomSystems.HTechnique.HashThenPRF (choose2)

set_option linter.unusedSectionVars false

variable {T : Type} [Fintype T] [DecidableEq T]
variable {q : ℕ}

section GenericLeg

variable {K : ℕ} {MsgK : Fin K → Type}
  [∀ ℓ, Fintype (MsgK ℓ)] [∀ ℓ, DecidableEq (MsgK ℓ)] [∀ ℓ, Nonempty (MsgK ℓ)]

namespace TweakablePRP

/-- The generic query and response carriers: direction-tagged, tweaked, length-tagged
messages over the fiber family `MsgK`. -/
local notation:max "GQ" => QueryDir × T × Sigma MsgK
local notation:max "GM" => Sigma MsgK

/-- The `±p̃rp` response function over the generic fibers (twin of `tprpFun`). -/
def tprpFun (fam : ∀ p : T × Fin K, Equiv.Perm (MsgK p.2)) : GQ → GM := fun x =>
  match x.1 with
  | QueryDir.fwd => ⟨x.2.2.1, fam (x.2.1, x.2.2.1) x.2.2.2⟩
  | QueryDir.inv => ⟨x.2.2.1, (fam (x.2.1, x.2.2.1)).symm x.2.2.2⟩

/-- `±p̃rp` over the generic fibers (twin of `tprp`). -/
def tprp : ProbPDS GQ GM :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (∀ p : T × Fin K, Equiv.Perm (MsgK p.2)), Dist.uniform_isProbDist⟩
    (fun fam => tprpFun fam)

/-- The `±rnd` response function over the generic fibers (twin of `rndFun`). -/
def rndFun (g : ∀ x : GQ, MsgK x.2.2.1) : GQ → GM := fun x => ⟨x.2.2.1, g x⟩

/-- `±rnd` over the generic fibers (twin of `rnd`). -/
def rnd : ProbPDS GQ GM :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (∀ x : GQ, MsgK x.2.2.1), Dist.uniform_isProbDist⟩
    (fun g => rndFun g)

theorem tprp_KStepTotal : (tprp (MsgK := MsgK) (T := T)).KStepTotal q :=
  functionEvaluatorProb_KStepTotal _ _ q

theorem rnd_KStepTotal : (rnd (MsgK := MsgK) (T := T)).KStepTotal q :=
  functionEvaluatorProb_KStepTotal _ _ q

/-- The `(plaintext, ciphertext)` pair a length-matched query/response pins on its class
permutation (twin of `pinnedIO`). -/
def pinnedIO (x : GQ) (y : GM) : GM × GM :=
  match x.1 with
  | QueryDir.fwd => (⟨x.2.2.1, x.2.2.2⟩, y)
  | QueryDir.inv => (y, ⟨x.2.2.1, x.2.2.2⟩)

/-- The §3.4 filter over the generic carriers (twin of `NP`). -/
def NP (t : TranscriptPrefix GQ GM q) : Prop :=
  Function.Injective t.1.get ∧
  ∀ i j : Fin q, (t.1.get i).2.1 = (t.1.get j).2.1 →
    (t.2.get i).1 = (t.1.get i).2.2.1 → (t.2.get j).1 = (t.1.get j).2.2.1 →
    pinnedIO (t.1.get i) (t.2.get i) = pinnedIO (t.1.get j) (t.2.get j) → i = j

/-- Turn a concrete list of query/response pairs into the fixed-length
transcript carrier used by `NP`.  This is only a carrier adapter: it adds no
condition and preserves the list order exactly. -/
def transcriptOfPairs (l : List (GQ × GM)) : TranscriptPrefix GQ GM l.length :=
  (⟨l.map Prod.fst, by simp⟩, ⟨l.map Prod.snd, by simp⟩)

/-- The no-pointless predicate on a finite pair list of arbitrary length.
Resource-filtered transcripts have this shape after rejected queries are
discarded; `NPList` is the same predicate as `NP`, not a second HCTR2-specific
notion. -/
def NPList (l : List (GQ × GM)) : Prop :=
  NP (transcriptOfPairs l)

/-- The `(tweak, length)` index of query `i`. -/
private def idxOf (xs : Fin q → GQ) (i : Fin q) : T × Fin K :=
  ((xs i).2.1, (xs i).2.2.1)

/-- Number of *distinct* queries at `(tweak, length)` index `p`. -/
private def cq (xs : Fin q → GQ) (p : T × Fin K) : ℕ :=
  ((Finset.univ.image xs).filter (fun Q => (Q.2.1, Q.2.2.1) = p)).card

/-- The per-query constraint on the query's own `(tweak, length)` permutation. -/
private def constr (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q)
    (π : Equiv.Perm (MsgK (idxOf xs i).2)) : Prop :=
  (⟨(xs i).2.2.1, match (xs i).1 with
      | QueryDir.fwd => π (xs i).2.2.2
      | QueryDir.inv => π.symm (xs i).2.2.2⟩ : GM) = v i

private instance (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q) :
    DecidablePred (constr xs v i) := fun π => by
  unfold constr; infer_instance

/-- `tprpFun`'s answer to query `i` depends only on the family at `idxOf i`. -/
private theorem tprpFun_eq_iff (fam : ∀ p : T × Fin K, Equiv.Perm (MsgK p.2))
    (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q) :
    tprpFun fam (xs i) = v i ↔ constr xs v i (fam (idxOf xs i)) := by
  unfold tprpFun constr idxOf
  cases (xs i).1 <;> rfl

/-- **±p̃rp output mass factors over `(tweak, length)`.** -/
private theorem tprp_output_mass_prod (xs : Fin q → GQ) (v : Fin q → GM) :
    (Dist.uniform (∀ p : T × Fin K, Equiv.Perm (MsgK p.2))).mass
        (fun fam => ∀ i, tprpFun fam (xs i) = v i) =
      ∏ p : T × Fin K, (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
        (fun π => ∀ i (h : idxOf xs i = p), constr xs v i (h ▸ π)) := by
  classical
  rw [Dist.mass_congr _ (fun fam =>
    forall_congr' (fun i => tprpFun_eq_iff fam xs v i))]
  exact uniform_dpi_eval_mass (fun p => Equiv.Perm (MsgK p.2)) (idxOf xs)
    (constr xs v)

/-- **Fiber-quantified responses**: `w i` lives in query `i`'s own length class;
`embV` tags it into the total space, so every length-match is `rfl`. -/
private def embV (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1) : Fin q → GM :=
  fun i => ⟨(xs i).2.2.1, w i⟩

/-- Every length-matched response vector is `embV` of its fiber contents. -/
private theorem eq_embV (xs : Fin q → GQ) (v : Fin q → GM)
    (hmatch : ∀ i, (v i).1 = (xs i).2.2.1) :
    v = embV xs (fun i => hmatch i ▸ (v i).2) :=
  funext fun i => Sigma.ext (hmatch i) (eqRec_heq _ _).symm

/-- Perm input/output of query `i` in its own fiber, direction-routed. -/
private def fIO (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1) (i : Fin q) :
    MsgK (xs i).2.2.1 × MsgK (xs i).2.2.1 :=
  match (xs i).1 with
  | QueryDir.fwd => ((xs i).2.2.2, w i)
  | QueryDir.inv => (w i, (xs i).2.2.2)

/-- The factor's perm I/O at index `p`, transported into `MsgK p.2`. -/
private def facIO (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (p : T × Fin K) (k : {i // idxOf xs i = p}) : MsgK p.2 × MsgK p.2 :=
  (k.2.symm ▸ (fIO xs w k.1).1, k.2.symm ▸ (fIO xs w k.1).2)

/-- **The transport atom**: `k.2.symm ▸ ·` transports are equal iff their
sources are `HEq`. -/
private theorem transp_eq_iff {xs : Fin q → GQ} {p : T × Fin K}
    {k k' : {i // idxOf xs i = p}}
    {a : MsgK (xs k.1).2.2.1} {b : MsgK (xs k'.1).2.2.1} :
    ((k.2.symm ▸ a : MsgK p.2) = k'.2.symm ▸ b) ↔ HEq a b := by
  constructor
  · intro h
    have h1 : HEq (k.2.symm ▸ a : MsgK p.2) a := by
      simp only [eqRec_eq_cast]; exact cast_heq _ _
    have h2 : HEq (k'.2.symm ▸ b : MsgK p.2) b := by
      simp only [eqRec_eq_cast]; exact cast_heq _ _
    exact h1.symm.trans (h ▸ h2)
  · intro hab; apply eq_of_heq; simp only [eqRec_eq_cast]
    exact HEq.trans (cast_heq _ _) (HEq.trans hab (cast_heq _ _).symm)

/-- The per-query constraint at fiber-quantified responses is a plain perm
consistency `π(inp) = out` over the query's fiber. -/
private theorem constr_iff (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (i : Fin q) (π : Equiv.Perm (MsgK (idxOf xs i).2)) :
    constr xs (embV xs w) i π ↔ π (fIO xs w i).1 = (fIO xs w i).2 := by
  unfold constr fIO embV
  cases (xs i).1 <;>
  · dsimp only
    rw [Sigma.mk.injEq]
    simp only [heq_eq_eq, true_and]
    grind [Equiv.symm_apply_eq]

/-- Transport-normalized form of the factor constraint. -/
private theorem constr_transport (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (p : T × Fin K) (π : Equiv.Perm (MsgK p.2)) (i : Fin q)
    (h : idxOf xs i = p) :
    constr xs (embV xs w) i (h ▸ π) ↔
      π (h.symm ▸ (fIO xs w i).1) = h.symm ▸ (fIO xs w i).2 := by
  subst h; simpa using constr_iff xs w i π

/-- A factor's mass is a perm consistency over `MsgK p.2`. -/
private theorem factor_mass_eq (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (p : T × Fin K) :
    (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
        (fun π => ∀ i (h : idxOf xs i = p), constr xs (embV xs w) i (h ▸ π)) =
      (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
        (fun π => ∀ k : {i // idxOf xs i = p},
          π (facIO xs w p k).1 = (facIO xs w p k).2) :=
  Dist.mass_congr _ (fun π =>
    ⟨fun hf k => (constr_transport xs w p π k.1 k.2).mp (hf k.1 k.2),
      fun hf i h => (constr_transport xs w p π i h).mpr (hf ⟨i, h⟩)⟩)

/-- Within some `(tweak, length)` factor, two steps violate a partial
injection (fiber-quantified form). -/
private def BadW (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1) : Prop :=
  ∃ (p : T × Fin K) (k k' : {i // idxOf xs i = p}),
    ((facIO xs w p k).1 = (facIO xs w p k').1 ∧
      (facIO xs w p k).2 ≠ (facIO xs w p k').2) ∨
    ((facIO xs w p k).1 ≠ (facIO xs w p k').1 ∧
      (facIO xs w p k).2 = (facIO xs w p k').2)

/-- `Bad` on raw responses: some length-matched decomposition is bad
(mismatched responses carry no constraint — and no mass on either side). -/
private def BadV (xs : Fin q → GQ) (v : Fin q → GM) : Prop :=
  ∃ w : ∀ i, MsgK (xs i).2.2.1, v = embV xs w ∧ BadW xs w

/-- **Good-transcript partial injection**: on `¬BadW`, within a factor the two
`facIO` components determine each other. -/
private theorem good_iff {xs : Fin q → GQ} {w : ∀ i, MsgK (xs i).2.2.1}
    (hBad : ¬ BadW xs w) (p : T × Fin K) (k k' : {i // idxOf xs i = p}) :
    (facIO xs w p k).1 = (facIO xs w p k').1 ↔
      (facIO xs w p k).2 = (facIO xs w p k').2 := by
  constructor
  · intro h; by_contra hne; exact hBad ⟨p, k, k', Or.inl ⟨h, hne⟩⟩
  · intro h; by_contra hne; exact hBad ⟨p, k, k', Or.inr ⟨hne, h⟩⟩

/-- Transported contents agree when the queries agree. -/
private theorem transp_content_eq (xs : Fin q → GQ) (p : T × Fin K)
    (k k' : {i // idxOf xs i = p}) (hq : xs k.1 = xs k'.1) :
    (k.2.symm ▸ (xs k.1).2.2.2 : MsgK p.2) = (k'.2.symm ▸ (xs k'.1).2.2.2) :=
  transp_eq_iff.mpr
    (Sigma.ext_iff.mp (show (xs k.1).2.2 = (xs k'.1).2.2 by rw [hq])).2

/-- **`facIO.1` factors through the query** on `¬BadW` (⟹ `d ≤ cq`). -/
private theorem facIO_fst_eq (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (hBad : ¬ BadW xs w) (p : T × Fin K) {k k' : {i // idxOf xs i = p}}
    (hq : xs k.1 = xs k'.1) : (facIO xs w p k).1 = (facIO xs w p k').1 := by
  have hd : (xs k.1).1 = (xs k'.1).1 := by rw [hq]
  rcases hdk : (xs k.1).1 with _ | _
  · unfold facIO fIO
    simp only [hdk, hd ▸ hdk]; exact transp_content_eq xs p k k' hq
  · refine (good_iff hBad p k k').mpr ?_
    unfold facIO fIO
    simp only [hdk, hd ▸ hdk]; exact transp_content_eq xs p k k' hq

/-- `cq p = |subtype-image query|` (card bridge). -/
private theorem cq_eq_subtype_card (xs : Fin q → GQ) (p : T × Fin K) :
    cq xs p =
      (Finset.univ.image (fun k : {i // idxOf xs i = p} => xs k.1)).card := by
  unfold cq
  congr 1
  ext Q
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hp⟩; exact ⟨⟨i, hp⟩, rfl⟩
  · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩

/-- **Per-factor good bound**: `N_ℓ^{−cq} ≤ factor` on `¬BadW`. -/
private theorem perm_factor_ge_cq (xs : Fin q → GQ)
    (w : ∀ i, MsgK (xs i).2.2.1) (hBad : ¬ BadW xs w) (p : T × Fin K) :
    ((Fintype.card (MsgK p.2) : ℝ) ^ cq xs p)⁻¹ ≤
      (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
        (fun π => ∀ i (h : idxOf xs i = p), constr xs (embV xs w) i (h ▸ π)) := by
  refine le_trans ?_ (le_of_le_of_eq (uniform_perm_consistent_mass_ge_finset
    (fun k => (facIO xs w p k).1) (fun k => (facIO xs w p k).2)
    (fun k k' h => (good_iff hBad p k k').mp h)
    (fun k k' h => (good_iff hBad p k k').mpr h)
    (Finset.card_le_univ _)) (factor_mass_eq xs w p).symm)
  gcongr
  · exact_mod_cast Fintype.card_pos
  · rw [cq_eq_subtype_card]
    exact card_image_le_of_factors (fun k => (facIO xs w p k).1) (fun k => xs k.1)
      (fun k k' h => facIO_fst_eq xs w hBad p h)

/-- **Fiber-regroup identity**: the per-query length product over distinct
queries regroups into the per-factor `N_ℓ^{−cq}` product. -/
private theorem prod_image_fiber_eq (xs : Fin q → GQ) :
    ∏ Q ∈ Finset.univ.image xs, ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ =
      ∏ p : T × Fin K, ((Fintype.card (MsgK p.2) : ℝ) ^ cq xs p)⁻¹ := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun Q : GQ => (Q.2.1, Q.2.2.1)) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Finset.prod_congr rfl (g := fun _ => ((Fintype.card (MsgK p.2) : ℝ))⁻¹)
      (fun Q hQ => by
        rw [show Q.2.2.1 = p.2 from congrArg Prod.snd (Finset.mem_filter.mp hQ).2]),
    Finset.prod_const, inv_pow]
  rfl

/-- **The mismatch adapter**: an oracle whose response carries the query's own
length has zero output mass on a length-mismatched `v`. -/
private theorem output_mass_zero_of_mismatch {α : Type*} (D : Dist α)
    (f : α → GQ → GM) (hlen : ∀ a Q, (f a Q).1 = Q.2.2.1)
    (xs : Fin q → GQ) (v : Fin q → GM) {i0 : Fin q}
    (hi0 : (v i0).1 ≠ (xs i0).2.2.1) :
    D.mass (fun a => ∀ i, f a (xs i) = v i) = 0 :=
  mass_eq_zero_of_forall _ (fun a ha => absurd
    ((congrArg Sigma.fst (ha i0)).symm.trans (hlen a (xs i0))) hi0)

/-- `tprpFun` responds in the query's own length class. -/
private theorem tprpFun_fst (fam : ∀ p : T × Fin K, Equiv.Perm (MsgK p.2))
    (Q : GQ) : (tprpFun fam Q).1 = Q.2.2.1 := by
  unfold tprpFun; cases Q.1 <;> rfl

/-- URF response constraint (length-tagged), value form (twin of `rndConstr`). -/
def rndConstr (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q)
    (y : MsgK (xs i).2.2.1) : Prop :=
  (⟨(xs i).2.2.1, y⟩ : GM) = v i

instance (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q) :
    DecidablePred (rndConstr xs v i) := fun y => by
  unfold rndConstr; infer_instance

private theorem rndFun_eq_iff (g : ∀ x : GQ, MsgK x.2.2.1)
    (xs : Fin q → GQ) (v : Fin q → GM) (i : Fin q) :
    rndFun g (xs i) = v i ↔ rndConstr xs v i (g (xs i)) := by
  unfold rndFun rndConstr; rfl

/-- **±rnd output mass factors over the query alphabet.** -/
theorem rnd_output_mass_prod (xs : Fin q → GQ) (v : Fin q → GM) :
    (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => ∀ i, rndFun g (xs i) = v i) =
      ∏ Q : GQ, (Dist.uniform (MsgK Q.2.2.1)).mass
        (fun y => ∀ i (h : xs i = Q), rndConstr xs v i (h ▸ y)) := by
  classical
  rw [Dist.mass_congr _
    (fun g => forall_congr' (fun i => rndFun_eq_iff g xs v i))]
  exact uniform_dpi_eval_mass (fun Q : GQ => MsgK Q.2.2.1) xs (rndConstr xs v)

/-- Per-query ±rnd factor is `≤ N_ℓ⁻¹` on a hit query. -/
theorem rnd_factor_le (xs : Fin q → GQ) (v : Fin q → GM) (Q : GQ)
    (i0 : Fin q) (hi0 : xs i0 = Q) :
    (Dist.uniform (MsgK Q.2.2.1)).mass
        (fun y => ∀ i (h : xs i = Q), rndConstr xs v i (h ▸ y)) ≤
      ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ := by
  classical
  subst hi0
  rw [Dist.uniform_mass_eq_card_filter, ← one_div,
    div_le_div_iff_of_pos_right (by positivity)]
  have hcard : (Finset.univ.filter
      (fun y : MsgK (xs i0).2.2.1 =>
        ∀ i (h : xs i = xs i0), rndConstr xs v i (h ▸ y))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hca := ha i0 rfl
    have hcb := hb i0 rfl
    unfold rndConstr at hca hcb
    simpa using (Sigma.mk.injEq ..).mp (hca.trans hcb.symm) |>.2
  exact_mod_cast hcard

/-- **±rnd output mass is `≤ ∏_{Q ∈ image} N_ℓ⁻¹`** (product upper bound). -/
theorem rnd_output_le (xs : Fin q → GQ) (v : Fin q → GM) :
    (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => ∀ i, rndFun g (xs i) = v i) ≤
      ∏ Q ∈ Finset.univ.image xs, ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ := by
  classical
  rw [rnd_output_mass_prod]
  calc ∏ Q : GQ, (Dist.uniform (MsgK Q.2.2.1)).mass
        (fun y => ∀ i (h : xs i = Q), rndConstr xs v i (h ▸ y))
      ≤ ∏ Q : GQ, (if Q ∈ Finset.univ.image xs then
          ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ else 1) := by
        refine Finset.prod_le_prod
          (fun _ _ => Dist.uniform_nonNeg.mass_nonneg _) (fun Q _ => ?_)
        by_cases hQ : Q ∈ Finset.univ.image xs
        · rw [if_pos hQ]
          obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp hQ
          exact rnd_factor_le xs v Q i0 hi0
        · rw [if_neg hQ]
          calc _ ≤ (Dist.uniform (MsgK Q.2.2.1)).weight :=
              Dist.mass_le_weight Dist.uniform_nonNeg _
            _ = 1 := Dist.weight_uniform
    _ = ∏ Q ∈ Finset.univ.image xs, ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ := by
        rw [Finset.prod_ite_mem]; congr 1
        exact (Finset.univ.image xs).inter_eq_right.mpr (by simp)

/-- **Good output ratio**: on `¬BadV`, `±rnd ≤ ±p̃rp` pointwise. -/
private theorem good_output_ratio (xs : Fin q → GQ) (v : Fin q → GM)
    (hBad : ¬ BadV xs v) :
    (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => ∀ i, rndFun g (xs i) = v i) ≤
      (Dist.uniform (∀ p : T × Fin K, Equiv.Perm (MsgK p.2))).mass
        (fun fam => ∀ i, tprpFun fam (xs i) = v i) := by
  classical
  by_cases hmatch : ∀ i, (v i).1 = (xs i).2.2.1
  · obtain ⟨w, rfl⟩ : ∃ w, v = embV xs w := ⟨_, eq_embV xs v hmatch⟩
    have hBadW : ¬ BadW xs w := fun hb => hBad ⟨w, rfl, hb⟩
    refine le_trans (rnd_output_le xs _) ?_
    rw [tprp_output_mass_prod, prod_image_fiber_eq]
    exact Finset.prod_le_prod (fun _ _ => by positivity)
      (fun p _ => perm_factor_ge_cq xs w hBadW p)
  · push Not at hmatch
    obtain ⟨i0, hi0⟩ := hmatch
    exact (output_mass_zero_of_mismatch _ rndFun (fun _ _ => rfl)
      xs v hi0).trans_le (Dist.uniform_nonNeg.mass_nonneg _)

/-- **Same query ⟹ same response** on `¬BadW`. -/
private theorem w_heq (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (hBad : ¬ BadW xs w) {i j : Fin q} (hq : xs i = xs j) :
    HEq (w i) (w j) := by
  have hpq : idxOf xs i = idxOf xs j := by unfold idxOf; rw [hq]
  have hfst := facIO_fst_eq xs w hBad (idxOf xs i)
    (k := ⟨i, rfl⟩) (k' := ⟨j, hpq.symm⟩) hq
  have hsnd := (good_iff hBad _ ⟨i, rfl⟩ ⟨j, hpq.symm⟩).mp hfst
  unfold facIO fIO at hfst hsnd
  have hd : (xs i).1 = (xs j).1 := by rw [hq]
  rcases hdi : (xs i).1 with _ | _
  · simp only [hdi, hd ▸ hdi] at hsnd
    exact (transp_eq_iff (k := (⟨i, rfl⟩ : {k // idxOf xs k = idxOf xs i}))
      (k' := ⟨j, hpq.symm⟩)).mp hsnd
  · simp only [hdi, hd ▸ hdi] at hfst
    exact (transp_eq_iff (k := (⟨i, rfl⟩ : {k // idxOf xs k = idxOf xs i}))
      (k' := ⟨j, hpq.symm⟩)).mp hfst

/-- Per-query ±rnd factor `≥ N_ℓ⁻¹` on a hit query, on `¬BadW`; with
`rnd_factor_le` this pins it to `= N_ℓ⁻¹`. -/
private theorem rnd_factor_ge (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (hBad : ¬ BadW xs w) (Q : GQ) (i0 : Fin q) (hi0 : xs i0 = Q) :
    ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ ≤
      (Dist.uniform (MsgK Q.2.2.1)).mass
        (fun y => ∀ i (h : xs i = Q), rndConstr xs (embV xs w) i (h ▸ y)) := by
  classical
  subst hi0
  rw [Dist.uniform_mass_eq_card_filter, ← one_div,
    div_le_div_iff_of_pos_right (by positivity)]
  have hne : (Finset.univ.filter (fun y : MsgK (xs i0).2.2.1 =>
      ∀ i (h : xs i = xs i0), rndConstr xs (embV xs w) i (h ▸ y))).Nonempty := by
    refine ⟨w i0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i h
    unfold rndConstr
    exact Sigma.ext rfl (by
      simp only [eqRec_eq_cast]
      exact (cast_heq _ _).trans (w_heq xs w hBad h).symm)
  exact_mod_cast Finset.one_le_card.mpr hne

/-- **±rnd output mass `≥ ∏_{Q ∈ image} N_ℓ⁻¹`** on `¬BadW`. -/
private theorem rnd_output_ge (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (hBad : ¬ BadW xs w) :
    ∏ Q ∈ Finset.univ.image xs, ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ ≤
      (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => ∀ i, rndFun g (xs i) = embV xs w i) := by
  classical
  rw [rnd_output_mass_prod]
  calc ∏ Q ∈ Finset.univ.image xs, ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹
      = ∏ Q : GQ, (if Q ∈ Finset.univ.image xs then
          ((Fintype.card (MsgK Q.2.2.1) : ℝ))⁻¹ else 1) := by
        rw [Finset.prod_ite_mem]; congr 1
        exact ((Finset.univ.image xs).inter_eq_right.mpr (by simp)).symm
    _ ≤ ∏ Q : GQ, (Dist.uniform (MsgK Q.2.2.1)).mass
          (fun y => ∀ i (h : xs i = Q), rndConstr xs (embV xs w) i (h ▸ y)) := by
        refine Finset.prod_le_prod (fun _ _ => by positivity) (fun Q _ => ?_)
        by_cases hQ : Q ∈ Finset.univ.image xs
        · rw [if_pos hQ]
          obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp hQ
          exact rnd_factor_ge xs w hBad Q i0 hi0
        · rw [if_neg hQ]
          rw [show (fun y : MsgK Q.2.2.1 => ∀ i (h : xs i = Q),
              rndConstr xs (embV xs w) i (h ▸ y)) = fun _ => True from by
            funext y; simp only [eq_iff_iff, iff_true]
            intro i h
            exact absurd (Finset.mem_image_of_mem xs (Finset.mem_univ i)) (h ▸ hQ)]
          rw [mass_true_eq_weight, Dist.weight_uniform]

/-- The `(xs, w)`-level consequence of `NP`: same-factor equal constraints come
from equal queries (⟹ `cq ≤ d`). -/
private def NPW (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1) : Prop :=
  ∀ (p : T × Fin K) (k k' : {i // idxOf xs i = p}),
    (facIO xs w p k).1 = (facIO xs w p k').1 ∧
      (facIO xs w p k).2 = (facIO xs w p k').2 → xs k.1 = xs k'.1

/-- On `¬BadW ∧ NPW`, the perm-input count equals the query count (`d = cq`). -/
private theorem factor_card_eq (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (hBad : ¬ BadW xs w) (hNP : NPW xs w) (p : T × Fin K) :
    (Finset.univ.image
        (fun k : {i // idxOf xs i = p} => (facIO xs w p k).1)).card =
      cq xs p := by
  rw [cq_eq_subtype_card]
  exact le_antisymm
    (card_image_le_of_factors (fun k => (facIO xs w p k).1) (fun k => xs k.1)
      (fun k k' h => facIO_fst_eq xs w hBad p h))
    (card_image_le_of_factors (fun k => xs k.1) (fun k => (facIO xs w p k).1)
      (fun k k' h => hNP p k k' ⟨h, (good_iff hBad p k k').mp h⟩))

/-- **Per-factor switch**: `(1 − bday(cq))·factor ≤ N_ℓ^{−cq}` on `¬BadW ∧ NPW`. -/
private theorem perm_factor_switch (xs : Fin q → GQ)
    (w : ∀ i, MsgK (xs i).2.2.1) (hBad : ¬ BadW xs w) (hNP : NPW xs w)
    (p : T × Fin K) :
    (((1 - ((cq xs p * (cq xs p - 1) : ℕ) : NNReal)
        / ((2 * Fintype.card (MsgK p.2) : ℕ) : NNReal) : NNReal) : ℝ)) *
      (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
        (fun π => ∀ i (h : idxOf xs i = p), constr xs (embV xs w) i (h ▸ π)) ≤
      ((Fintype.card (MsgK p.2) : ℝ) ^ cq xs p)⁻¹ := by
  classical
  rw [factor_mass_eq xs w p,
    uniform_perm_consistent_mass_eq_finset _ _
      (fun k k' h => (good_iff hBad p k k').mp h)
      (fun k k' h => (good_iff hBad p k k').mpr h)
      (Finset.card_le_univ _),
    factor_card_eq xs w hBad hNP p]
  have hle : cq xs p ≤ Fintype.card (MsgK p.2) := by
    rw [← factor_card_eq xs w hBad hNP p]; exact Finset.card_le_univ _
  by_cases hb : ((cq xs p * (cq xs p - 1) : ℕ) : NNReal)
      / ((2 * Fintype.card (MsgK p.2) : ℕ) : NNReal) ≤ 1
  · have h := RandomSystems.CR18.Counting.switching_ratio_le
      hle Fintype.card_pos hb
    rw [one_div] at h
    exact_mod_cast h
  · rw [tsub_eq_zero_of_le (not_le.mp hb).le, NNReal.coe_zero, zero_mul]
    positivity

/-- `Σ_p cq(cq−1) ≤ q(q−1)`. -/
private theorem sum_cq_sq_le (xs : Fin q → GQ) :
    ∑ p : T × Fin K, cq xs p * (cq xs p - 1) ≤ q * (q - 1) := by
  classical
  refine RandomSystems.CR18.Counting.sum_mul_pred_le _ q ?_
  have hsum : ∑ p : T × Fin K, cq xs p = (Finset.univ.image xs).card := by
    unfold cq
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun Q : GQ => (Q.2.1, Q.2.2.1)) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  rw [hsum]
  exact le_trans Finset.card_image_le (by simp)

/-- `Σ_p bday(cq_p) ≤ C(q,2)/N_min` for any per-fiber cardinality lower bound
`N_min ≤ |MsgK ℓ|`. -/
private theorem sum_bday_le (xs : Fin q → GQ)
    (Nmin : ℕ) (hNpos : 0 < Nmin) (hNmin : ∀ ℓ, Nmin ≤ Fintype.card (MsgK ℓ)) :
    ∑ p : T × Fin K, ((cq xs p * (cq xs p - 1) : ℕ) : NNReal)
        / ((2 * Fintype.card (MsgK p.2) : ℕ) : NNReal) ≤
      (choose2 q : NNReal) / Nmin := by
  classical
  refine le_trans (Finset.sum_le_sum (fun p _ =>
    div_le_div_of_nonneg_left (zero_le _)
      (by exact_mod_cast Nat.mul_pos (by norm_num) hNpos)
      (by exact_mod_cast Nat.mul_le_mul_left (k := 2) (hNmin p.2))))
    (le_of_eq_of_le (b := (∑ p : T × Fin K,
      (cq xs p * (cq xs p - 1) : ℕ) :
        NNReal) / ((2 * Nmin : ℕ) : NNReal)) (Finset.sum_div _ _ _).symm ?_)
  have hdelb : (choose2 q : NNReal) / Nmin =
      ((q * (q - 1) : ℕ) : NNReal) / ((2 * Nmin : ℕ) : NNReal) := by
    have hqq : q * (q - 1) = 2 * Nat.choose q 2 := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self q).two_dvd]
    rw [choose2, hqq]; push_cast; rw [mul_div_mul_left _ _ two_ne_zero]
  rw [hdelb, ← Nat.cast_sum]
  gcongr
  exact_mod_cast sum_cq_sq_le xs

/-- **Switch output ratio**: `(1 − C(q,2)/N_min)·±p̃rp ≤ ±rnd` on `¬Bad ∧ NP`. -/
private theorem switch_output_ratio (xs : Fin q → GQ) (v : Fin q → GM)
    (hBad : ¬ BadV xs v) (hNP : ∀ w, v = embV xs w → NPW xs w)
    (Nmin : ℕ) (hNpos : 0 < Nmin) (hNmin : ∀ ℓ, Nmin ≤ Fintype.card (MsgK ℓ)) :
    (1 - ((choose2 q / Nmin : NNReal) : ℝ)) *
      (Dist.uniform (∀ p : T × Fin K, Equiv.Perm (MsgK p.2))).mass
        (fun fam => ∀ i, tprpFun fam (xs i) = v i) ≤
      (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => ∀ i, rndFun g (xs i) = v i) := by
  classical
  by_cases hmatch : ∀ i, (v i).1 = (xs i).2.2.1
  · obtain ⟨w, rfl⟩ : ∃ w, v = embV xs w := ⟨_, eq_embV xs v hmatch⟩
    have hBadW : ¬ BadW xs w := fun hb => hBad ⟨w, rfl, hb⟩
    refine le_trans ?_ (rnd_output_ge xs w hBadW)
    rw [tprp_output_mass_prod, prod_image_fiber_eq]
    have hlbNN : (1 - choose2 q / Nmin : NNReal) ≤
        ∏ p : T × Fin K, (1 - ((cq xs p * (cq xs p - 1) : ℕ) : NNReal)
          / ((2 * Fintype.card (MsgK p.2) : ℕ) : NNReal)) :=
      le_trans (tsub_le_tsub_left (sum_bday_le xs Nmin hNpos hNmin) 1)
        (Counting.nnreal_one_sub_sum_le_prod _ _)
    have hlb : (1 - ((choose2 q / Nmin : NNReal) : ℝ)) ≤
        ∏ p : T × Fin K, (((1 - ((cq xs p * (cq xs p - 1) : ℕ) : NNReal)
          / ((2 * Fintype.card (MsgK p.2) : ℕ) : NNReal) : NNReal) : ℝ)) := by
      refine le_trans ?_ (by exact_mod_cast NNReal.coe_le_coe.mpr hlbNN)
      rcases le_or_gt (choose2 q / (Nmin : NNReal)) 1 with he | he
      · simp [NNReal.coe_sub he]
      · have h1 : (1 : ℝ) < ((choose2 q / Nmin : NNReal) : ℝ) := by
          exact_mod_cast he
        exact le_trans (by linarith) (NNReal.coe_nonneg _)
    refine le_trans (mul_le_mul_of_nonneg_right hlb
      (Finset.prod_nonneg fun _ _ => Dist.uniform_nonNeg.mass_nonneg _)) ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod
      (fun p _ => mul_nonneg (NNReal.coe_nonneg _)
        (Dist.uniform_nonNeg.mass_nonneg _))
      (fun p _ => perm_factor_switch xs w hBadW (hNP w rfl) p)
  · push Not at hmatch
    obtain ⟨i0, hi0⟩ := hmatch
    rw [output_mass_zero_of_mismatch _ _ tprpFun_fst xs v hi0, mul_zero]
    exact Dist.uniform_nonNeg.mass_nonneg _

/-- `pinnedIO` at a fiber-quantified response is the length-tagged `facIO`. -/
private theorem pinnedIO_facIO (xs : Fin q → GQ) (w : ∀ i, MsgK (xs i).2.2.1)
    (p : T × Fin K) (k : {i // idxOf xs i = p}) :
    pinnedIO (xs k.1) (embV xs w k.1) =
      ((⟨p.2, (facIO xs w p k).1⟩ : GM), (⟨p.2, (facIO xs w p k).2⟩ : GM)) := by
  obtain ⟨i, hi⟩ := k
  subst hi
  unfold pinnedIO facIO fIO embV
  cases (xs i).1 <;> rfl

/-- The `NP` filter yields `NPW` on any length-matched decomposition of the
transcript: equal same-factor constraints pin equal `(plaintext, ciphertext)`
pairs, so the two steps coincide. -/
private theorem NPW_of_NP (t : TranscriptPrefix GQ GM q) (hnp : NP t)
    (w : ∀ i, MsgK ((functionOfVector t.1) i).2.2.1)
    (hv : functionOfVector t.2 = embV (functionOfVector t.1) w) :
    NPW (functionOfVector t.1) w := by
  intro p k k' hkk'
  obtain ⟨h1, h2⟩ := hkk'
  suffices h : k.1 = k'.1 by rw [h]
  have hlen : ∀ i, (t.2.get i).1 = (t.1.get i).2.2.1 := fun i => by
    rw [show t.2.get i = embV (functionOfVector t.1) w i from congrFun hv i]; rfl
  refine hnp.2 k.1 k'.1
    ((congrArg Prod.fst k.2).trans (congrArg Prod.fst k'.2).symm)
    (hlen k.1) (hlen k'.1) ?_
  calc pinnedIO (t.1.get k.1) (t.2.get k.1)
      = ((⟨p.2, (facIO (functionOfVector t.1) w p k).1⟩ : GM),
          (⟨p.2, (facIO (functionOfVector t.1) w p k).2⟩ : GM)) := by
        rw [show t.2.get k.1 = embV (functionOfVector t.1) w k.1 from
          congrFun hv k.1]
        exact pinnedIO_facIO (functionOfVector t.1) w p k
    _ = ((⟨p.2, (facIO (functionOfVector t.1) w p k').1⟩ : GM),
          (⟨p.2, (facIO (functionOfVector t.1) w p k').2⟩ : GM)) := by
        rw [h1, h2]
    _ = pinnedIO (t.1.get k'.1) (t.2.get k'.1) := by
        rw [show t.2.get k'.1 = embV (functionOfVector t.1) w k'.1 from
          congrFun hv k'.1]
        exact (pinnedIO_facIO (functionOfVector t.1) w p k').symm

variable [FiniteTranscriptSpace (QueryDir × T × Sigma MsgK) (Sigma MsgK) q]

/-- `Bad` on transcripts (PRP-RND side). -/
def BadTr (t : TranscriptPrefix GQ GM q) : Prop :=
  BadV (functionOfVector t.1) (functionOfVector t.2)

/-- **Good ratio, transcript level**: `tr(±rnd) ≤ tr(±p̃rp)` on `¬Bad`. -/
theorem good_ratio_transcript (xs : Fin q → GQ)
    (t : TranscriptPrefix GQ GM q) (hbad : ¬ BadTr t) :
    (tr(rnd (MsgK := MsgK) (T := T), xs)) t ≤
      (tr(tprp (MsgK := MsgK) (T := T), xs)) t := by
  classical
  unfold rnd tprp
  rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
    PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator]
  refine le_of_eq_of_le (one_mul _).symm
    (fixedInputLiftDist_ratio_at xs _ _ 1 t (fun hxv => ?_))
  have hxs : functionOfVector t.1 = xs := by
    rw [hxv]; exact functionOfVector_vectorOfFunction xs
  subst hxs
  rw [one_mul]
  simpa [Dist.fTransform_apply_eq_mass, funext_iff] using
    good_output_ratio (functionOfVector t.1) (functionOfVector t.2) hbad

/-- **Switch ratio, transcript level**: `(1 − δb)·tr(±p̃rp) ≤ tr(±rnd)` on
`NP ∧ ¬Bad`. -/
private theorem switch_ratio_transcript (xs : Fin q → GQ)
    (t : TranscriptPrefix GQ GM q) (hnp : NP t) (hbad : ¬ BadTr t)
    (Nmin : ℕ) (hNpos : 0 < Nmin) (hNmin : ∀ ℓ, Nmin ≤ Fintype.card (MsgK ℓ)) :
    (1 - ((choose2 q / Nmin : NNReal) : ℝ)) *
        (tr(tprp (MsgK := MsgK) (T := T), xs)) t ≤
      (tr(rnd (MsgK := MsgK) (T := T), xs)) t := by
  classical
  unfold rnd tprp
  rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
    PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator]
  refine fixedInputLiftDist_ratio_at xs _ _
    (1 - ((choose2 q / Nmin : NNReal) : ℝ)) t (fun hxv => ?_)
  have hxs : functionOfVector t.1 = xs := by
    rw [hxv]; exact functionOfVector_vectorOfFunction xs
  subst hxs
  simpa [Dist.fTransform_apply_eq_mass, funext_iff] using
    switch_output_ratio (functionOfVector t.1) (functionOfVector t.2) hbad
      (NPW_of_NP t hnp) Nmin hNpos hNmin

/-- The system factor of `±p̃rp` at a transcript is the perm-family mass of the
consistency event. -/
private theorem sysFactor_tprp (t : TranscriptPrefix GQ GM q) :
    sysFactor (tprp (MsgK := MsgK) (T := T)) t =
      (Dist.uniform (∀ p : T × Fin K, Equiv.Perm (MsgK p.2))).mass
        (fun fam => ∀ i, tprpFun fam (t.1.get i) = t.2.get i) := by
  unfold sysFactor PFunPDE.transcriptSystemFactor tprp PFunPDS.Prob.functionEvaluator
  rw [Dist.PMF, Dist.mass_fTransform]
  exact Dist.mass_congr _
    (fun fam => transcriptSystemEvent_functionEvaluatorRV_iff _ t.1 t.2 fam)

/-- A `(t, ℓ)`-factor is `0` when its I/O pairs violate a partial injection. -/
private theorem factor_zero_of_bad (xs : Fin q → GQ)
    (w : ∀ i, MsgK (xs i).2.2.1) (p : T × Fin K) (k k' : {i // idxOf xs i = p})
    (hcase :
      ((facIO xs w p k).1 = (facIO xs w p k').1 ∧
        (facIO xs w p k).2 ≠ (facIO xs w p k').2) ∨
      ((facIO xs w p k).1 ≠ (facIO xs w p k').1 ∧
        (facIO xs w p k).2 = (facIO xs w p k').2)) :
    (Dist.uniform (Equiv.Perm (MsgK p.2))).mass
      (fun π => ∀ i (h : idxOf xs i = p), constr xs (embV xs w) i (h ▸ π)) = 0 := by
  rw [factor_mass_eq xs w p]
  refine mass_eq_zero_of_forall _ (fun π hπ => ?_)
  rcases hcase with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · exact absurd (by rw [← hπ k, ← hπ k', hin]) hout
  · exact absurd (π.injective (by rw [hπ k, hπ k']; exact hout)) hin

/-- **`±p̃rp` never realizes a bad transcript**: the system factor vanishes. -/
private theorem tprp_no_bad (E : QQueryEnvironment GQ GM q) :
    (tr[q](tprp (MsgK := MsgK) (T := T), E.1)).mass BadTr = 0 := by
  classical
  refine mass_eq_zero_of_forall _ (fun t ht => ?_)
  obtain ⟨w, hw, p, k, k', hcase⟩ := ht
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    show sysFactor (tprp (MsgK := MsgK) (T := T)) t = 0 from ?_, zero_mul]
  rw [sysFactor_tprp,
    show (fun fam : ∀ p : T × Fin K, Equiv.Perm (MsgK p.2) =>
        ∀ i, tprpFun fam (t.1.get i) = t.2.get i)
      = (fun fam => ∀ i, tprpFun fam (functionOfVector t.1 i)
          = functionOfVector t.2 i) from rfl,
    hw, tprp_output_mass_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ p)
    (factor_zero_of_bad _ w p k k' hcase)

/-- **The adaptive bad bound** over `NP`-respecting environments:
`Pr[Bad ∣ tr(±rnd, E)] ≤ C(q,2)/N_min`, via the ratio trick. -/
theorem prp_rnd_bad_bound (E : QQueryEnvironment GQ GM q)
    (hE : EnvRespects NP E)
    (Nmin : ℕ) (hNpos : 0 < Nmin) (hNmin : ∀ ℓ, Nmin ≤ Fintype.card (MsgK ℓ)) :
    Pr[BadTr ∣ tr[q](rnd (MsgK := MsgK) (T := T), E.1)] ≤
      ((choose2 q / Nmin : NNReal) : ℝ) := by
  refine probBad_le_of_ratio
    (deterministicTranscriptDist_nonNeg _ E.1)
    (deterministicTranscriptDist_nonNeg _ E.1)
    BadTr _
    (deterministicTranscriptDist_weight_eq_one _ E rnd_KStepTotal)
    (deterministicTranscriptDist_weight_eq_one _ E tprp_KStepTotal)
    (tprp_no_bad E) (fun t hbad => ?_)
  by_cases hnp : NP t
  · refine deterministicTranscriptDist_ratio_of_fixedQuery_ratio_of_good
      (rnd (MsgK := MsgK) (T := T)) (tprp (MsgK := MsgK) (T := T))
      E (fun t' => BadTr t' ∨ ¬ NP t')
      ((choose2 q : NNReal) / Nmin) ?_ t (by simp [hbad, hnp])
    intro xs t' ht'
    rw [not_or, not_not] at ht'
    exact switch_ratio_transcript xs t' ht'.2 ht'.1 Nmin hNpos hNmin
  · rw [deterministicTranscriptDist_eq_zero_of_not_filt NP _ E hE t hnp,
      mul_zero]
    exact deterministicTranscriptDist_nonNeg _ E.1 t

/-- **The generic PRP-RND endpoint** (paper §3.5 / [HR03] App. C Lemma 6): over
any fiber family, `±rnd` is `C(q,2)/N_min`-close to `±p̃rp` against non-pointless
adversaries, for any per-fiber cardinality lower bound `N_min ≤ |MsgK ℓ|`.
Part 2 instantiates this at the bit-level fibers; the block-aligned
instantiation feeds `tprp_rnd` below. -/
theorem tprp_rnd (Nmin : ℕ) (hNpos : 0 < Nmin)
    (hNmin : ∀ ℓ, Nmin ≤ Fintype.card (MsgK ℓ)) :
    filteredAdaptiveTranscriptAdvantage (q := q) NP
      (tprp (MsgK := MsgK) (T := T)) rnd ≤
      ((choose2 q : NNReal) / Nmin : ℝ) := by
  have h := adv_le_of_fixedQuery_ratio_of_good_filtered NP
    (tprp (MsgK := MsgK) (T := T)) rnd BadTr 0
    ((choose2 q : NNReal) / Nmin)
    tprp_KStepTotal rnd_KStepTotal
    (fun xs t _ hbad => by
      rw [NNReal.coe_zero, sub_zero, one_mul]
      exact good_ratio_transcript xs t hbad)
    (fun E hE => prp_rnd_bad_bound E hE Nmin hNpos hNmin)
  simpa using h

/-! #### The generic reveal-collapse spine (shared by both parts' bad bounds)

The extended σ⁺ ideal world is `uniform Z ⊗ ±rnd coins` with the reveal read off the
`Z`-component; the collapse of the bad-mass analysis to per-transcript reveal bounds — and,
for response-functional cells, per-reveal coin bounds — is generic in the reveal type `Z`.
Part 1 instantiates it at `Z = F × F`; the bit level at `Z = F × F × (Fin q → F)` (the
`lastB` column), with the hybrid reveal reduced to this dummy form by pushforward. -/

section Collapse

variable {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable [DiscreteTranscriptSpace (QueryDir × T × Sigma MsgK) (Sigma MsgK) q]

/-- Admissible transcripts: filtered (`NP`), `E`-consistent, length-matched. -/
def admissible (E : QQueryEnvironment GQ GM q) (t : TranscriptPrefix GQ GM q) : Prop :=
  NP t ∧ E.1 ⊨ t ∧ ∀ i, (t.2.get i).1 = (t.1.get i).2.2.1

/-- **Off-admissibility vanishing** of the ideal transcript factor (reveal-type-free). -/
theorem idealTr_vanish (E : QQueryEnvironment GQ GM q) (hE : EnvRespects NP E)
    (t : TranscriptPrefix GQ GM q) (hadm : ¬ admissible E t) :
    (tr[q](rnd (MsgK := MsgK) (T := T), E.1)) t = 0 := by
  unfold rnd
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_functionEvaluator]
  by_cases hcon : E.1 ⊨ t
  · by_cases hm : ∀ i, (t.2.get i).1 = (t.1.get i).2.2.1
    · exact absurd ⟨hE t hcon, hcon, hm⟩ hadm
    · rw [mass_eq_zero_of_forall _
        (fun g hg => (hm fun i => by rw [← hg i]; rfl).elim), zero_mul]
  · rw [envFactor_eq_indicator, if_neg hcon, mul_zero]

/-- Generic ideal sampler: a uniform dummy reveal alongside the `±rnd` coins. -/
abbrev idealPZ : Dist.ProbDist (Z × (∀ x : GQ, MsgK x.2.2.1)) :=
  Dist.prodProbDist
    ⟨Dist.uniform Z, Dist.uniform_isProbDist⟩
    ⟨Dist.uniform (∀ x : GQ, MsgK x.2.2.1), Dist.uniform_isProbDist⟩

/-- Generic ideal sampled system: `±rnd` (the dummy is ignored). -/
abbrev idealFZ : PFunPDS.RV (Z × (∀ x : GQ, MsgK x.2.2.1)) GQ GM :=
  functionEvaluatorRV (fun p => rndFun p.2)

/-- Generic ideal reveal: the dummy. -/
def idealAugZ : (Z × (∀ x : GQ, MsgK x.2.2.1)) → TranscriptPrefix GQ GM q → Z :=
  fun p _ => p.1

local notation:max "idealExtZ" E:max =>
  extendedTranscriptDistRep (q := q) idealPZ idealFZ idealAugZ E

/-- **Generic ideal product factorization**: the extended law factors as
`uniform Z × ±rnd transcript mass` (`extendedTranscriptDistRep_indep`). -/
theorem idealExtZ_apply (E : PFunDDS.DDE GQ GM)
    (t : TranscriptPrefix GQ GM q) (z : Z) :
    (idealExtZ E) (t, z)
      = Dist.uniform Z z * (tr[q](rnd (MsgK := MsgK) (T := T), E)) t :=
  extendedTranscriptDistRep_indep _ _ (fun g => rndFun g) E t z

/-- **Generic reveal-collapse bridge**: a collision predicate bounded uniformly over the
reveal on every admissible transcript is bounded under the full ideal extended law. -/
theorem revealCollapseZ_le (E : QQueryEnvironment GQ GM q) (hE : EnvRespects NP E)
    (P : (TranscriptPrefix GQ GM q × Z) → Prop) (b : NNReal)
    (hb : ∀ t, admissible E t →
      (Dist.uniform Z).mass (fun z => P (t, z)) ≤ b) :
    (idealExtZ E.1).mass P ≤ b := by
  classical
  refine mass_le_of_fiber_snd _ _ _ (fun t z => idealExtZ_apply E.1 t z)
    (deterministicTranscriptDist_nonNeg _ E.1) ?_ P b b.coe_nonneg
    (fun t ht => hb t (Classical.byContradiction
      fun hadm => ht (idealTr_vanish E hE t hadm)))
  rw [← Dist.weight_eq_sum, deterministicTranscriptDist_weight_eq_one _ E rnd_KStepTotal]

/-- **Generic reveal-lift** for the pair-cell leaves. -/
theorem pairMassZ_le_of_reveal (E : QQueryEnvironment GQ GM q) (hE : EnvRespects NP E)
    (P : (TranscriptPrefix GQ GM q × Z) → Prop)
    (G : TranscriptPrefix GQ GM q → Z → Prop) (b : NNReal)
    (hG : ∀ t, admissible E t → (Dist.uniform Z).mass (G t) ≤ b)
    (himp : ∀ t z, P (t, z) → G t z) :
    (idealExtZ E.1).mass P ≤ b :=
  revealCollapseZ_le E hE P b (fun t hadm =>
    le_trans (CR18.mass_mono Dist.uniform_nonNeg (himp t)) (hG t hadm))

/-- **Generic ω-slice collapse** for the response-functional cells. -/
theorem omegaSliceZ_le (E : QQueryEnvironment GQ GM q)
    (P : (TranscriptPrefix GQ GM q × Z) → Prop) (b : NNReal)
    (hb : ∀ z : Z,
      (Dist.uniform (∀ x : GQ, MsgK x.2.2.1)).mass
        (fun g => P (envRun E (rndFun g), z)) ≤ b) :
    (idealExtZ E.1).mass P ≤ b := by
  classical
  refine mass_le_of_fiber_fst _ _ _ (fun t z => idealExtZ_apply E.1 t z)
    (fun z => Dist.uniform_nonNeg z) ?_ P b b.coe_nonneg
    (fun z _ => ?_)
  · rw [← Dist.weight_eq_sum, Dist.weight_uniform]
  · unfold rnd
    rw [deterministicTranscriptDist_functionEvaluator_eq_fTransform _ (fun g => rndFun g) E,
      Dist.mass_fTransform]
    exact hb z

end Collapse

end TweakablePRP

end GenericLeg

end RandomSystems.CR18
