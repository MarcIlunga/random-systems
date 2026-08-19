import SequenceHash.RandomSystems.Converter
import SequenceHash.RandomSystems.Finite
import SequenceHash.RandomSystems.MDHash
import RandomSystems.AbsorbDPI
import RandomSystems.Complexity.AdvantageSeq
import RandomSystems.Complexity.ConverterBridge
import RandomSystems.CBCMAC
import RandomSystems.FunctionEvaluator

/-!
# Gaži--Pietrzak--Rybár NMAC model in the pure CR18 idiom

This file models the construction and the bound from Gaži, Pietrzak, and
Rybár, *The Exact PRF-Security of NMAC and HMAC* (2014), §2.2, §3.1, and
Appendix A.

The paper keeps two interfaces distinct:

* the deterministic compression family is `f : C × B → C` (curried below as
  `C → B → C`), so the cascade can use each chaining value as the next key;
* the PRF experiment samples one `K : C` and exposes `f_K : B → C`.

Consequently, the cascade is evaluated directly with the whole deterministic
family `f`; it is not a converter over one sampled `f_K`.  NMAC then samples
the independent pair `(K₁,K₂)` and exposes the resulting function on block
strings.  `sequenceMACReal` generalizes only this key mixture: its `keyDist`
parameter is the joint distribution induced by a concrete SequenceMAC key
schedule, while `nmacReal` is exactly the paper's independent-uniform pair.

All systems are `PFunPDS`, adaptive security is the filtered CR18 distance
`Δ(⌈q⌉ ·, ⌈q⌉ ·)`, and non-adaptive security is stated pointwise over fixed
query tuples.  No H-technique advantage wrapper is used.
-/

noncomputable section

open scoped BigOperators NNReal RandomSystems.CR18

namespace SequenceHash.MACPRF

open RandomSystems RandomSystems.CR18

variable {B C : Type*}
  [Fintype B] [Nonempty B] [DecidableEq B]
  [Fintype C] [Nonempty C] [DecidableEq C]

/-- Messages in the paper's `(q, ℓ)` experiment: block strings containing at
most `ℓ` blocks.  Restricting the carrier to these strings is the finite-law
presentation of the paper's rule that every adversarial query has length at
most `ℓ`. -/
abbrev BlockString (B : Type*) (ℓ : ℕ) := {m : List B // m.length ≤ ℓ}

noncomputable instance instFintypeBlockString [Fintype B] (ℓ : ℕ) :
    Fintype (BlockString B ℓ) :=
  (List.finite_length_le B ℓ).fintype

instance instNonemptyBlockString (B : Type*) (ℓ : ℕ) :
    Nonempty (BlockString B ℓ) :=
  ⟨⟨[], by simp⟩⟩

/-- Gaži et al. §2.2: `f : {0,1}^c × {0,1}^b → {0,1}^c`.

The first input is the key/chaining value.  This is the paper-faithful answer
to the `C × B → C` versus `B → C` question: the family has domain `C × B`;
only its sampled-key PRF interface below has exposed domain `B`. -/
abbrev CompressionFamily (C B : Type*) := C → B → C

/-- Gaži et al. §2.2 cascade:
`y₀ := K`, `yᵢ := f(yᵢ₋₁,mᵢ)`, and `Cascᶠ(K,m₁‖...‖mℓ) := yℓ`.
In particular the empty cascade returns `K`. -/
def cascade (f : CompressionFamily C B) (K : C) (m : List B) : C :=
  mdIterate f K m

/-- Gaži et al. §2.2 NMAC.  `pad` abstracts the paper's injective trailing-zero
map `x ↦ x ‖ 0^(b-c)` (under its standing assumption `b ≥ c`). -/
def nmac (f : CompressionFamily C B) (pad : C ↪ B)
    (keys : C × C) (m : List B) : C :=
  f keys.2 (pad (cascade f keys.1 m))

/-- The deterministic compression table viewed as a CR18 resource.  Its
exposed domain really is `C × B`, matching the paper's type for `f`.  NMAC's
cascade is defined directly from this same family above; the PRF experiment
below is a different interface obtained by sampling the first component. -/
noncomputable def compressionResource (f : CompressionFamily C B) :
    PFunPDS (C × B) C :=
  PFunPDS.pure
    (PFunDDS.functionEvaluator (fun x : C × B => f x.1 x.2))

/-- Gaži et al. §2.1's ideal compression function: a uniform random function
from `C × B` to `C`.  Theorem 1 does not compare against this object; it
compares the sampled-key interface `compReal` against the fixed-input URF
`compIdeal` (`r` in the paper). -/
noncomputable def idealCompression : PFunPDS (C × B) C :=
  PFunPDS.URF (X := C × B) (Y := C)

/-- The compression-family PRF experiment from §2.2/Thm. 1: sample
`K ← C`, then expose the fixed-input-length function `f_K : B → C`.

This system intentionally has exposed domain `B`, not `C × B`: the key is
sampled by the experiment, exactly as in the paper's PRF definition. -/
noncomputable def compReal (f : CompressionFamily C B) : PFunPDS B C :=
  PFunPDS.ofFunDist
    (Dist.fTransform (fun K : C => f K) (Dist.uniform C))

/-- The paper's fixed-input-length URF `r : B → C`, used as the ideal system
in the compression-family PRF and NA-PRF experiments. -/
noncomputable def compIdeal : PFunPDS B C :=
  PFunPDS.URF (X := B) (Y := C)

omit [Fintype B] [Nonempty B] [DecidableEq B] [DecidableEq C] in
theorem compReal_isProbDist (f : CompressionFamily C B) :
    (compReal f).isProbDist := by
  unfold compReal
  cr18_prob

/-- A joint inner/outer key mixture.  A concrete SequenceMAC key schedule is
represented by the distribution it induces on `(K₁,K₂)`; no unmentioned key
derivation is invented here. -/
noncomputable def sequenceMACReal (ℓ : ℕ) (f : CompressionFamily C B)
    (pad : C ↪ B) (keyDist : RandomSystems.Dist (C × C)) :
    PFunPDS (BlockString B ℓ) C :=
  PFunPDS.ofFunDist
    (Dist.fTransform
      (fun keys : C × C => fun m : BlockString B ℓ =>
        nmac f pad keys m.1)
      keyDist)

/-- Gaži et al. §2.2 NMAC key structure: `K₁,K₂ ← C` independently and
uniformly. -/
noncomputable def nmacReal (ℓ : ℕ) (f : CompressionFamily C B)
    (pad : C ↪ B) : PFunPDS (BlockString B ℓ) C :=
  sequenceMACReal ℓ f pad
    (Dist.prod (Dist.uniform C) (Dist.uniform C))

/-- The variable-input-length URF `R` in §2.1/§2.2, restricted to the message
carrier visible in the `(q,ℓ)` experiment. -/
noncomputable def macIdeal (ℓ : ℕ) : PFunPDS (BlockString B ℓ) C :=
  PFunPDS.URF (X := BlockString B ℓ) (Y := C)

/-- The SequenceMAC-to-NMAC key-schedule hop, expressed only as a filtered
pure-CR18 distance.  For the paper's NMAC distribution itself this term is
definitionally the distance from `nmacReal` to itself. -/
noncomputable def epsKS (q ℓ : ℕ) (f : CompressionFamily C B)
    (pad : C ↪ B) (keyDist : RandomSystems.Dist (C × C)) : ℝ :=
  Δ(⌈q⌉ sequenceMACReal ℓ f pad keyDist,
    ⌈q⌉ nmacReal ℓ f pad)

/-- Gaži et al. §2.2 fixed-input-length non-adaptive PRF assumption, rendered
without an adversary/game object: for every tuple of `q` queries fixed before
the replies are seen, the two fixed-query transcript laws are within
`εna`. -/
def CompNASecure (q : ℕ) (f : CompressionFamily C B) (εna : NNReal) : Prop :=
  ∀ xs : Fin q → B,
    statDist
      (PFunPDS.Prob.fixedQueryTranscriptDist
        (S := ⟨compReal f, compReal_isProbDist f⟩) xs)
      (PFunPDS.Prob.fixedQueryTranscriptDist
        (S := ⟨compIdeal,
          PFunPDS.URF_isProbDist (X := B) (Y := C)⟩) xs) ≤ εna

/-- The adaptive compression-family PRF term `ε` in Theorem 1, expressed as
the paper's maximal `q`-query distinguishing distance in pure CR18 notation. -/
noncomputable def epsComp (q : ℕ) (f : CompressionFamily C B) : ℝ :=
  Δ(⌈q⌉ compReal f, ⌈q⌉ compIdeal)

/-! ## Gaži Appendix A: the two non-adaptive cascade hybrids -/

/-- The paper's `Cascᶠ_K` law: sample the initial chaining key uniformly and
expose the cascade on block strings of length at most `d`. -/
noncomputable def cascadeReal (d : ℕ) (f : CompressionFamily C B) :
    PFunPDS.Prob (BlockString B d) C :=
  PFunPDS.Prob.functionEvaluator
    (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
    (fun K m => cascade f K m.1)

/-- The paper's `R` comparator for the cascade experiment. -/
noncomputable def cascadeIdeal (d : ℕ) :
    PFunPDS.Prob (BlockString B d) C :=
  ⟨macIdeal d, PFunPDS.URF_isProbDist⟩

/-- The `qf_K̄` system in Appendix A: `q` independently keyed copies of the
compression family, addressed by a row and a block. -/
noncomputable def multiCompReal (q : ℕ) (f : CompressionFamily C B) :
    PFunPDS.Prob (Fin q × B) C :=
  PFunPDS.Prob.functionEvaluator
    (⟨Dist.uniform (Fin q → C), Dist.uniform_isProbDist⟩ :
      Dist.ProbDist (Fin q → C))
    (fun keys x => f (keys x.1) x.2)

/-- The `q r` system in Appendix A: `q` independent uniformly random rows.
A uniform function on `Fin q × B` is exactly that product law. -/
noncomputable def multiCompIdeal (q : ℕ) :
    PFunPDS.Prob (Fin q × B) C :=
  PFunPDS.Prob.urf

/-- Scheme-agnostic adaptive strong multi-user compression distance. -/
noncomputable def epsCompMU (q u : ℕ) (f : CompressionFamily C B) : ℝ :=
  Δ(⌈q⌉ (multiCompReal u f).val, ⌈q⌉ (multiCompIdeal u).val)

/-- The non-adaptive distinguishing distance for one fixed `q`-query tuple,
kept as a direct statistical distance between CR18 transcript laws. -/
noncomputable def fixedQueryDelta {X Y : Type*} {q : ℕ} [Fintype X] [Fintype Y]
    [Fintype (CR18TranscriptPrefix X Y q)]
    (S T : PFunPDS.Prob X Y) (xs : Fin q → X) : ℝ :=
  (statDist
    (PFunPDS.Prob.fixedQueryTranscriptDist S xs)
    (PFunPDS.Prob.fixedQueryTranscriptDist T xs) : NNReal)

/-- Every fixed query tuple in the `u`-user compression worlds is charged by
the single adaptive strong-MU distance. -/
theorem multiComp_fixedQueryDelta_le_epsCompMU
    (q u : ℕ) (f : CompressionFamily C B)
    (zs : Fin q → (Fin u × B)) :
    fixedQueryDelta (multiCompReal u f) (multiCompIdeal u) zs ≤
      epsCompMU q u f := by
  unfold fixedQueryDelta
  rw [show multiCompReal u f = PFunPDS.Prob.functionEvaluator
      (⟨Dist.uniform (Fin u → C), Dist.uniform_isProbDist⟩ :
        Dist.ProbDist (Fin u → C))
      (fun keys x => f (keys x.1) x.2) from rfl,
    show multiCompIdeal u = PFunPDS.Prob.urf from rfl]
  rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
    PFunPDS.Prob.fixedQueryTranscriptDist_urf]
  unfold fixedInputLiftDist
  rw [statDist_fTransform_injective _ _ _
    (fixedInputTranscriptPrefix_injective zs), PFunPDS.uniformP_val]
  let Df : RandomSystems.Dist ((Fin u × B) → C) := Dist.fTransform
    (fun keys : Fin u → C => fun x : Fin u × B => f (keys x.1) x.2)
    (Dist.uniform (Fin u → C))
  have h := Complexity.statDist_evalDist_le_maxAdvantage_filterQueries_ofFunDist
    zs
    Df
    (Dist.uniform ((Fin u × B) → C))
    (Dist.fTransform_isProbDist _ Dist.uniform_isProbDist)
    Dist.uniform_isProbDist
  rw [Dist.fTransform_comp] at h
  have hreal : PFunPDS.ofFunDist Df = (multiCompReal u f).val := by
    unfold Df multiCompReal PFunPDS.Prob.functionEvaluator Dist.PMF
      PFunPDS.ofFunDist functionEvaluatorRV
    rw [Dist.fTransform_comp]
    rfl
  have hideal : PFunPDS.ofFunDist (Dist.uniform ((Fin u × B) → C)) =
      (multiCompIdeal u).val := by
    rfl
  rw [hreal, hideal] at h
  exact h

/-- Prefix-freeness of the distinct query values in one fixed query tuple.
Repeated queries are harmless and are identified before applying the paper's
NA-PF reduction. -/
def PrefixFreeQueries {q d : ℕ} (xs : Fin q → BlockString B d) : Prop :=
  PrefixFree (fun m : Set.range xs => m.1.1)

theorem gazi_uniform_restrict {I J A : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A] (e : I ↪ J) :
    Dist.fTransform (fun F : J → A ↦ fun i ↦ F (e i)) (Dist.uniform (J → A)) =
      Dist.uniform (I → A) := by
  exact uniform_restrict e

/-- A positive-query single-user compression experiment is the restriction of
the existing `q`-user experiment to one row.  Query-filtered converter DPI
therefore charges the outer NMAC call by the same strong-MU distance. -/
theorem epsComp_le_epsCompMU (q : ℕ) (f : CompressionFamily C B)
    (hq : 0 < q) :
    epsComp q f ≤ epsCompMU q q f := by
  classical
  let j0 : Fin q := ⟨0, hq⟩
  let c : B ↪ (Fin q × B) :=
    ⟨fun b => (j0, b), fun _ _ h => congrArg Prod.snd h⟩
  let Df : RandomSystems.Dist ((Fin q × B) → C) := Dist.fTransform
    (fun keys : Fin q → C => fun x : Fin q × B => f (keys x.1) x.2)
    (Dist.uniform (Fin q → C))
  have hrealBase : PFunPDS.ofFunDist Df = (multiCompReal q f).val := by
    unfold Df multiCompReal PFunPDS.Prob.functionEvaluator Dist.PMF
      PFunPDS.ofFunDist functionEvaluatorRV
    rw [Dist.fTransform_comp]
    rfl
  have hidealBase :
      PFunPDS.ofFunDist (Dist.uniform ((Fin q × B) → C)) =
        (multiCompIdeal q).val := by
    rfl
  have hcoord : Dist.fTransform (fun keys : Fin q → C => keys j0)
      (Dist.uniform (Fin q → C)) = Dist.uniform C := by
    let nonces : Fin 1 → Fin q := fun _ => j0
    have hvec := uniformFunction_eval_uniform (Y := C) nonces
      (by intro a b _; exact Subsingleton.elim a b)
    let e : (Fin 1 → C) ≃ C := Equiv.funUnique (Fin 1) C
    calc
      Dist.fTransform (fun keys : Fin q → C => keys j0)
          (Dist.uniform (Fin q → C)) =
          Dist.fTransform e
            (Dist.fTransform (fun keys : Fin q → C => fun _ : Fin 1 => keys j0)
              (Dist.uniform (Fin q → C))) := by
            rw [Dist.fTransform_comp]
            rfl
      _ = Dist.fTransform e (Dist.uniform (Fin 1 → C)) := by rw [hvec]
      _ = Dist.uniform C := Dist.fTransform_equiv_uniform e
  have hreal : PFunPDS.applyDDC
      (PFunConverter.DDC.simple c (id : C → C)) (multiCompReal q f).val =
      compReal f := by
    rw [← hrealBase, PFunPDS.applyDDC_simple_ofFunDist]
    unfold compReal Df
    rw [Dist.fTransform_comp, ← hcoord, Dist.fTransform_comp]
    rfl
  have hideal : PFunPDS.applyDDC
      (PFunConverter.DDC.simple c (id : C → C)) (multiCompIdeal q).val =
      compIdeal := by
    rw [← hidealBase, PFunPDS.applyDDC_simple_ofFunDist]
    unfold compIdeal PFunPDS.URF
    rw [show (fun F : (Fin q × B) → C => fun b => id (F (c b))) =
      (fun F : (Fin q × B) → C => fun b => F (c b)) from rfl]
    rw [gazi_uniform_restrict (A := C) c]
  have hone : PFunConverter.DDC.AnswersWithin
      (PFunConverter.DDC.simpleStep c (id : C → C)) 1 := by
    intro b ys hys
    cases ys with
    | nil => simp at hys
    | cons y ys => exact ⟨y, rfl⟩
  have hdpi := maxAdvantage_filterQueries_applyDDC_le
    (PFunConverter.DDC.simpleStep c (id : C → C)) hone q
    (multiCompReal q f).val (multiCompIdeal q).val
    (by rw [← hrealBase]; exact PFunPDS.ofFunDist_isRandomFunction _)
    PFunPDS.URF_isRandomFunction
  change PFunPDS.applyDDC
      (PFunConverter.DDC.ofStep
        (PFunConverter.DDC.simpleStep c (id : C → C)))
      (multiCompReal q f).val = compReal f at hreal
  change PFunPDS.applyDDC
      (PFunConverter.DDC.ofStep
        (PFunConverter.DDC.simpleStep c (id : C → C)))
      (multiCompIdeal q).val = compIdeal at hideal
  rw [hreal, hideal] at hdpi
  simpa [epsComp, epsCompMU, Nat.mul_one] using hdpi

theorem gazi_eval_prod_uniform {P I J A : Type*}
    [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] [Nonempty A]
    (addr : P ↪ I ⊕ J) :
    Dist.fTransform
        (fun z : (I → A) × (J → A) ↦ fun p ↦
          (Equiv.sumArrowEquivProdArrow I J A).symm z (addr p))
        (Dist.prod (Dist.uniform (I → A)) (Dist.uniform (J → A))) =
      Dist.uniform (P → A) := by
  classical
  let E := Equiv.sumArrowEquivProdArrow I J A
  have hE : Dist.fTransform E (Dist.uniform (I ⊕ J → A)) =
      Dist.uniform ((I → A) × (J → A)) := Dist.fTransform_equiv_uniform E
  rw [Dist.prod_uniform, ← hE, Dist.fTransform_comp]
  have hfun :
      (fun z : (I → A) × (J → A) ↦ fun p ↦
        (Equiv.sumArrowEquivProdArrow I J A).symm z (addr p)) ∘ E =
        (fun F : I ⊕ J → A ↦ fun p ↦ F (addr p)) := by
    funext F p
    simp [E]
  rw [hfun, gazi_uniform_restrict (I := P) (J := I ⊕ J) (A := A) addr]

theorem gazi_prod_map_right {U A Z : Type*} [Fintype U] [Fintype A]
    [Fintype Z] [DecidableEq Z]
    (P : RandomSystems.Dist U) (X : RandomSystems.Dist A) (g : A → Z) :
    Dist.prod P (Dist.fTransform g X) =
      Dist.fTransform (fun p : U × A ↦ (p.1, g p.2)) (Dist.prod P X) := by
  classical
  ext p
  rcases p with ⟨u, z⟩
  simp only [Dist.prod_apply, Dist.fTransform_apply_eq_sum]
  norm_cast
  simp_rw [show ∀ p : U × A, Dist.prod P X p = P p.1 * X p.2 from
    fun p ↦ Dist.prod_apply P X p.1 p.2]
  change P u * (∑ a ∈ (Finset.univ : Finset A).filter (fun a ↦ g a = z), X a) =
    ∑ p ∈ (Finset.univ : Finset (U × A)).filter
      (fun p ↦ (p.1, g p.2) = (u, z)), P p.1 * X p.2
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun p _ ↦ p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact congrArg Prod.snd hp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    intro p' hp' hpp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    apply Prod.ext
    · exact (congrArg Prod.fst hp).trans (congrArg Prod.fst hp').symm
    · exact hpp'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    refine ⟨(u, a), ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      using (show g a = z from ha)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [congrArg Prod.fst hp]

theorem gazi_statDist_le_adjacent_sum {A : Type*}
    [Fintype A] [Nonempty A] [DecidableEq A]
    (laws : ℕ → RandomSystems.Dist A) (n : ℕ) :
    statDist (laws 0) (laws n) ≤
      ∑ i ∈ Finset.range n, statDist (laws i) (laws (i + 1)) := by
  induction n with
  | zero => rw [statDist_self]; simp
  | succ n ih =>
      calc
        statDist (laws 0) (laws (n + 1)) ≤
            statDist (laws 0) (laws n) + statDist (laws n) (laws (n + 1)) :=
          statDist_triangle _ _ _
        _ ≤ (∑ i ∈ Finset.range n, statDist (laws i) (laws (i + 1))) +
            statDist (laws n) (laws (n + 1)) := add_le_add ih (le_refl _)
        _ = ∑ i ∈ Finset.range (n + 1), statDist (laws i) (laws (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- **Gaži Appendix A, Lemma 6 / Eq. (10), law-level form.** Replacing the
`q` independently keyed compression rows one row at a time costs at most
`q εna`.  The adjacent systems are the oracle-index hybrid `A₃⁽ⁱ⁾`; their
endpoint distance is discharged by the framework telescoping inequality. -/
theorem gazi_lemma6_row_hybrid
    (q : ℕ) (f : CompressionFamily C B) (εna : NNReal)
    (hna : CompNASecure q f εna) (zs : Fin q → (Fin q × B)) :
    fixedQueryDelta (multiCompReal q f) (multiCompIdeal q) zs
      ≤ (q : ℝ) * (εna : ℝ) := by
  classical
  let piLaw {I : Type} [Fintype I]
      (D : I → RandomSystems.Dist (Fin q → C)) :
      RandomSystems.Dist (I → (Fin q → C)) :=
    Finsupp.equivFunOnFinite.symm (fun x ↦ ∏ i, D i (x i))
  have piLaw_apply {I : Type} [Fintype I]
      (D : I → RandomSystems.Dist (Fin q → C)) (x : I → (Fin q → C)) :
      piLaw D x = ∏ i, D i (x i) := by
    rfl
  have piLaw_weight {I : Type} [Fintype I] [DecidableEq I]
      (D : I → RandomSystems.Dist (Fin q → C)) :
      (piLaw D).weight = ∏ i, (D i).weight := by
    rw [Dist.weight_eq_sum]
    simp only [piLaw_apply]
    calc
      (∑ x : I → (Fin q → C), ∏ i, D i (x i)) =
          ∑ x ∈ Fintype.piFinset (fun _ : I ↦ Finset.univ),
            ∏ i, D i (x i) := by rw [Fintype.piFinset_univ]
      _ = ∏ i, ∑ a : Fin q → C, D i a :=
        (Finset.prod_univ_sum (fun _ : I ↦ Finset.univ)
          (fun i a ↦ D i a)).symm.trans (by simp)
      _ = ∏ i, (D i).weight := by simp [Dist.weight_eq_sum]
  have piLaw_split {I : Type} [Fintype I] [DecidableEq I]
      (D : I → RandomSystems.Dist (Fin q → C)) (i : I) :
      piLaw D = Dist.fTransform
        ((Equiv.prodComm ((j : {j // j ≠ i}) → (Fin q → C)) (Fin q → C)).trans
          (Equiv.piSplitAt i (fun _ ↦ Fin q → C)).symm)
        (Dist.prod (piLaw (fun j : {j // j ≠ i} ↦ D j.1)) (D i)) := by
    ext x
    let e :=
      ((Equiv.prodComm ((j : {j // j ≠ i}) → (Fin q → C)) (Fin q → C)).trans
        (Equiv.piSplitAt i (fun _ ↦ Fin q → C)).symm)
    have hx := Dist.fTransform_injective_apply
      (Dist.prod (piLaw (fun j : {j // j ≠ i} ↦ D j.1)) (D i))
      e e.injective (e.symm x)
    rw [e.apply_symm_apply] at hx
    rw [hx, Dist.prod_apply]
    simp only [piLaw_apply]
    rw [show (∏ j, D j (x j)) =
        (∏ j ∈ (Finset.univ : Finset I).erase i, D j (x j)) * D i (x i) by
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]]
    have hact : (e.symm x).2 = x i := by simp [e]
    rw [hact]
    have hrest :
        (∏ j ∈ (Finset.univ : Finset I).erase i, D j (x j)) =
          ∏ j : {j // j ≠ i}, D j.1 ((e.symm x).1 j) := by
      apply Finset.prod_bij (fun j hj ↦
        (⟨j, (Finset.mem_erase.mp hj).1⟩ : {j // j ≠ i}))
      · intro j hj
        simp
      · intro a ha b hb hab
        exact Subtype.ext_iff.mp hab
      · intro j hj
        refine ⟨j.1, by simp [j.2], ?_⟩
        rfl
      · intro j hj
        simp [e]
    rw [hrest]
  have piLaw_change_one {I : Type} [Fintype I] [DecidableEq I]
      (D D' : I → RandomSystems.Dist (Fin q → C)) (i : I)
      (hother : ∀ j, j ≠ i → D j = D' j)
      (hprob : ∀ j, j ≠ i → (D j).isProbDist) :
      statDist (piLaw D) (piLaw D') = statDist (D i) (D' i) := by
    let e :=
      ((Equiv.prodComm ((j : {j // j ≠ i}) → (Fin q → C)) (Fin q → C)).trans
        (Equiv.piSplitAt i (fun _ ↦ Fin q → C)).symm)
    let R := piLaw (fun j : {j // j ≠ i} ↦ D j.1)
    have hR' : piLaw (fun j : {j // j ≠ i} ↦ D' j.1) = R := by
      congr 2
      funext j
      exact (hother j.1 j.2).symm
    rw [piLaw_split D i, piLaw_split D' i, hR']
    rw [statDist_fTransform_injective _ _ e e.injective]
    rw [statDist_prod_left]
    have hRw : R.weight = 1 := by
      change (piLaw (fun j : {j // j ≠ i} ↦ D j.1)).weight = 1
      rw [piLaw_weight]
      have hw : ∀ j : {j // j ≠ i}, (D j.1).weight = 1 :=
        fun j ↦ hprob j.1 j.2
      simp_rw [hw]
      simp
    rw [hRw, one_mul]
  have piLaw_map_C (D : Fin q → RandomSystems.Dist C)
      (g : Fin q → C → (Fin q → C)) :
      piLaw (fun i ↦ Dist.fTransform (g i) (D i)) =
        Dist.fTransform (fun x i ↦ g i (x i))
          (Finsupp.equivFunOnFinite.symm
            (fun x : Fin q → C ↦ ∏ i, D i (x i))) := by
    ext y
    simp only [piLaw_apply, Dist.fTransform_apply_eq_sum]
    norm_cast
    change (∏ i : Fin q,
        ∑ a ∈ (Finset.univ : Finset C).filter (fun a ↦ g i a = y i), D i a) =
      ∑ x ∈ (Finset.univ : Finset (Fin q → C)).filter
        (fun x ↦ (fun i ↦ g i (x i)) = y), ∏ i, D i (x i)
    rw [Finset.prod_univ_sum
      (fun i : Fin q ↦ Finset.univ.filter (fun a ↦ g i a = y i))
      (fun i a ↦ D i a)]
    apply Finset.sum_congr
    · ext x
      simp [Fintype.mem_piFinset, funext_iff]
    · intro x hx
      rfl
  have piLaw_map_BC (D : Fin q → RandomSystems.Dist (B → C))
      (g : Fin q → (B → C) → (Fin q → C)) :
      piLaw (fun i ↦ Dist.fTransform (g i) (D i)) =
        Dist.fTransform (fun x i ↦ g i (x i))
          (Finsupp.equivFunOnFinite.symm
            (fun x : Fin q → (B → C) ↦ ∏ i, D i (x i))) := by
    ext y
    simp only [piLaw_apply, Dist.fTransform_apply_eq_sum]
    norm_cast
    change (∏ i : Fin q,
        ∑ a ∈ (Finset.univ : Finset (B → C)).filter (fun a ↦ g i a = y i), D i a) =
      ∑ x ∈ (Finset.univ : Finset (Fin q → (B → C))).filter
        (fun x ↦ (fun i ↦ g i (x i)) = y), ∏ i, D i (x i)
    rw [Finset.prod_univ_sum
      (fun i : Fin q ↦ Finset.univ.filter (fun a ↦ g i a = y i))
      (fun i a ↦ D i a)]
    apply Finset.sum_congr
    · ext x
      simp [Fintype.mem_piFinset, funext_iff]
    · intro x hx
      rfl
  have piLaw_const_uniform_C :
      Finsupp.equivFunOnFinite.symm
          (fun x : Fin q → C ↦ ∏ _i : Fin q, Dist.uniform C (x _i)) =
        Dist.uniform (Fin q → C) := by
    ext x
    simp only [Dist.uniform_apply]
    norm_cast
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun]
    simp only [Nat.cast_pow]
    simp [one_div, inv_pow]
  have piLaw_const_uniform_BC :
      Finsupp.equivFunOnFinite.symm
          (fun x : Fin q → (B → C) ↦
            ∏ _i : Fin q, Dist.uniform (B → C) (x _i)) =
        Dist.uniform (Fin q → (B → C)) := by
    ext x
    simp only [Dist.uniform_apply]
    norm_cast
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun]
    simp only [Nat.cast_pow]
    simp [one_div, inv_pow]
  let bs : Fin q → B := fun j ↦ (zs j).2
  let PR : RandomSystems.Dist (Fin q → C) :=
    Dist.fTransform (fun K : C ↦ fun j ↦ f K (bs j)) (Dist.uniform C)
  let PI : RandomSystems.Dist (Fin q → C) :=
    Dist.fTransform (fun r : B → C ↦ fun j ↦ r (bs j)) (Dist.uniform (B → C))
  have hPRI : statDist PR PI ≤ εna := by
    have hreal :
        (⟨compReal f, compReal_isProbDist f⟩ : PFunPDS.Prob B C) =
          PFunPDS.Prob.functionEvaluator
            (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
            (fun K : C ↦ f K) := by
      apply Subtype.ext
      unfold compReal PFunPDS.Prob.functionEvaluator Dist.PMF functionEvaluatorRV
        PFunPDS.ofFunDist
      change Dist.fTransform PFunDDS.functionEvaluator
          (Dist.fTransform (fun K : C ↦ f K) (Dist.uniform C)) =
        Dist.fTransform (fun K : C ↦ PFunDDS.functionEvaluator (f K)) (Dist.uniform C)
      rw [Dist.fTransform_comp]
      rfl
    have hideal :
        (⟨compIdeal, PFunPDS.URF_isProbDist⟩ : PFunPDS.Prob B C) =
          PFunPDS.Prob.urf := by rfl
    have h := hna bs
    rw [hreal, hideal] at h
    rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
      PFunPDS.Prob.fixedQueryTranscriptDist_urf] at h
    unfold fixedInputLiftDist at h
    rw [statDist_fTransform_injective _ _ _
      (fixedInputTranscriptPrefix_injective bs)] at h
    simpa [compReal, compIdeal, PR, PI, bs] using h
  let D : ℕ → Fin q → RandomSystems.Dist (Fin q → C) := fun k r ↦
    if k ≤ r.1 then PR else PI
  let H : ℕ → RandomSystems.Dist (Fin q → C) := fun k ↦
    Dist.fTransform (fun rows j ↦ rows (zs j).1 j) (piLaw (D k))
  have hstep : ∀ i : Fin q, statDist (H i.1) (H (i.1 + 1)) ≤ εna := by
    intro i
    refine le_trans (statDist_fTransform_le _ _ _) ?_
    have hone : statDist (piLaw (D i.1)) (piLaw (D (i.1 + 1))) =
        statDist PR PI := by
      have hchange := piLaw_change_one (D i.1) (D (i.1 + 1)) i
        (by
          intro j hji
          simp only [D]
          split_ifs
          · rfl
          · omega
          · omega
          · rfl)
        (by
          intro j hji
          simp only [D]
          split_ifs
          · exact Dist.fTransform_isProbDist _ Dist.uniform_isProbDist
          · exact Dist.fTransform_isProbDist _ Dist.uniform_isProbDist)
      simpa [D] using hchange
    exact hone.trans_le hPRI
  let MR : RandomSystems.Dist (Fin q → C) :=
    Dist.fTransform (fun keys : Fin q → C ↦ fun j ↦ f (keys (zs j).1) (zs j).2)
      (Dist.uniform (Fin q → C))
  let MI : RandomSystems.Dist (Fin q → C) :=
    Dist.fTransform (fun r : (Fin q × B) → C ↦ fun j ↦ r (zs j))
      (Dist.uniform ((Fin q × B) → C))
  have hH0 : H 0 = MR := by
    have hD0 : piLaw (D 0) =
        Dist.fTransform
          (fun keys : Fin q → C ↦ fun r ↦ fun j ↦ f (keys r) (bs j))
          (Dist.uniform (Fin q → C)) := by
      calc
        piLaw (D 0) = piLaw (fun _ : Fin q ↦ PR) := by congr 2
        _ = Dist.fTransform
            (fun keys : Fin q → C ↦ fun r ↦ fun j ↦ f (keys r) (bs j))
            (Finsupp.equivFunOnFinite.symm
              (fun x : Fin q → C ↦ ∏ i, Dist.uniform C (x i))) := by
              rw [piLaw_map_C]
        _ = _ := by rw [piLaw_const_uniform_C]
    simp only [H]
    rw [hD0, Dist.fTransform_comp]
    unfold MR
    congr 1
  have hHq : H q = MI := by
    have hDq : piLaw (D q) =
        Dist.fTransform
          (fun rows : Fin q → (B → C) ↦ fun r ↦ fun j ↦ rows r (bs j))
          (Dist.uniform (Fin q → (B → C))) := by
      calc
        piLaw (D q) = piLaw (fun _ : Fin q ↦ PI) := by
          congr 2
          funext r
          simp [D, r.isLt]
        _ = Dist.fTransform
            (fun rows : Fin q → (B → C) ↦ fun r ↦ fun j ↦ rows r (bs j))
            (Finsupp.equivFunOnFinite.symm
              (fun x : Fin q → (B → C) ↦ ∏ i, Dist.uniform (B → C) (x i))) := by
              rw [piLaw_map_BC]
        _ = _ := by rw [piLaw_const_uniform_BC]
    have hcurry : Dist.fTransform (Equiv.curry (Fin q) B C)
        (Dist.uniform ((Fin q × B) → C)) =
        Dist.uniform (Fin q → (B → C)) :=
      Dist.fTransform_equiv_uniform (Equiv.curry (Fin q) B C)
    simp only [H]
    rw [hDq, ← hcurry, Dist.fTransform_comp, Dist.fTransform_comp]
    unfold MI
    congr 1
  have hout : statDist MR MI ≤ (q : NNReal) * εna := by
    rw [← hH0, ← hHq]
    calc
      statDist (H 0) (H q) ≤
          ∑ i ∈ Finset.range q, statDist (H i) (H (i + 1)) :=
        gazi_statDist_le_adjacent_sum H q
      _ ≤ ∑ _i ∈ Finset.range q, εna := by
        apply Finset.sum_le_sum
        intro i hi
        exact hstep ⟨i, Finset.mem_range.mp hi⟩
      _ = (q : NNReal) * εna := by simp
  unfold fixedQueryDelta
  rw [show multiCompReal q f = PFunPDS.Prob.functionEvaluator
      (⟨Dist.uniform (Fin q → C), Dist.uniform_isProbDist⟩ :
        Dist.ProbDist (Fin q → C))
      (fun keys x ↦ f (keys x.1) x.2) from rfl,
    show multiCompIdeal q = PFunPDS.Prob.urf from rfl]
  rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
    PFunPDS.Prob.fixedQueryTranscriptDist_urf]
  unfold fixedInputLiftDist
  rw [statDist_fTransform_injective _ _ _
    (fixedInputTranscriptPrefix_injective zs)]
  change ((statDist MR MI : NNReal) : ℝ) ≤ (q : ℝ) * (εna : ℝ)
  exact_mod_cast hout

/-- **Gaži Appendix A, Lemma 5 / Eq. (9), law-level form.** For fixed
prefix-free queries, the length-position hybrid reduces cascade-versus-URF
distance to `d` copies of the `q`-row experiment.  `rowBound` is precisely the
conclusion supplied by Lemma 6. -/
theorem gazi_lemma5_depth_hybrid
    (q d : ℕ) (f : CompressionFamily C B) (xs : Fin q → BlockString B d)
    (hpf : PrefixFreeQueries xs) (rowBound : ℝ)
    (hrows : ∀ zs : Fin q → (Fin q × B),
      fixedQueryDelta (multiCompReal q f) (multiCompIdeal q) zs ≤ rowBound) :
    fixedQueryDelta (cascadeReal d f) (cascadeIdeal d) xs
      ≤ (d : ℝ) * rowBound := by
  classical
  let Pref (k : ℕ) := Set.range (fun j : Fin q ↦ (xs j).1.take k)
  let prefAt (k : ℕ) (j : Fin q) : Pref k :=
    ⟨(xs j).1.take k, ⟨j, rfl⟩⟩
  let row (k : ℕ) : Pref k ↪ Fin q :=
    (Fintype.equivFin (Pref k)).toEmbedding.trans
      (Fin.castLEEmb (by simpa [Pref] using
        (Fintype.card_range_le (fun j : Fin q ↦ (xs j).1.take k))))
  let H (k : ℕ) : RandomSystems.Dist (Fin q → C) :=
    Dist.fTransform
      (fun keys : Fin q → C ↦ fun j ↦
        mdIterate f (keys (row k (prefAt k j))) ((xs j).1.drop k))
      (Dist.uniform (Fin q → C))
  have same_side (k : ℕ) (a b : Fin q)
      (hab : (xs a).1.take k = (xs b).1.take k) :
      ((xs a).1.length ≤ k ↔ (xs b).1.length ≤ k) := by
    have one (a b : Fin q)
        (hab : (xs a).1.take k = (xs b).1.take k)
        (ha : (xs a).1.length ≤ k) : (xs b).1.length ≤ k := by
      by_contra hb
      have hbk : k < (xs b).1.length := by omega
      have hpref : (xs a).1 <+: (xs b).1 := by
        rw [← List.take_of_length_le ha, hab]
        exact List.take_prefix k (xs b).1
      let ma : Set.range xs := ⟨xs a, ⟨a, rfl⟩⟩
      let mb : Set.range xs := ⟨xs b, ⟨b, rfl⟩⟩
      have hne : ma ≠ mb := by
        intro heq
        have hx : xs a = xs b := congrArg Subtype.val heq
        have hl : (xs a).1.length = (xs b).1.length := by rw [hx]
        omega
      exact (hpf ma mb hne) hpref
    exact ⟨one a b hab, one b a hab.symm⟩
  let finish (k : ℕ) (state : Pref k → C) : Fin q → C := fun j ↦
    mdIterate f (state (prefAt k j)) ((xs j).1.drop k)
  have hHuniform (k : ℕ) :
      H k = Dist.fTransform (finish k) (Dist.uniform (Pref k → C)) := by
    rw [← gazi_uniform_restrict (I := Pref k) (J := Fin q) (A := C) (row k),
      Dist.fTransform_comp]
    unfold H finish
    congr 1
  have hstep (k : ℕ) (hk : k < d) :
      ((statDist (H k) (H (k + 1)) : NNReal) : ℝ) ≤ rowBound := by
    let zs : Fin q → (Fin q × B) := fun j ↦
      (row k (prefAt k j),
        if hj : k < (xs j).1.length then (xs j).1.get ⟨k, hj⟩
        else Classical.choice inferInstance)
    let MR : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform
        (fun keys : Fin q → C ↦ fun j ↦ f (keys (zs j).1) (zs j).2)
        (Dist.uniform (Fin q → C))
    let MI : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform (fun R : (Fin q × B) → C ↦ fun j ↦ R (zs j))
        (Dist.uniform ((Fin q × B) → C))
    have hrow : ((statDist MR MI : NNReal) : ℝ) ≤ rowBound := by
      have h := hrows zs
      unfold fixedQueryDelta at h
      rw [show multiCompReal q f = PFunPDS.Prob.functionEvaluator
          (⟨Dist.uniform (Fin q → C), Dist.uniform_isProbDist⟩ :
            Dist.ProbDist (Fin q → C))
          (fun keys x ↦ f (keys x.1) x.2) from rfl,
        show multiCompIdeal q = PFunPDS.Prob.urf from rfl] at h
      rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
        PFunPDS.Prob.fixedQueryTranscriptDist_urf] at h
      unfold fixedInputLiftDist at h
      rw [statDist_fTransform_injective _ _ _
        (fixedInputTranscriptPrefix_injective zs)] at h
      exact h
    let post : ((Fin q → C) × (Fin q → C)) → (Fin q → C) := fun z j ↦
      if hj : k < (xs j).1.length then
        mdIterate f (z.2 j) ((xs j).1.drop (k + 1))
      else z.1 (row k (prefAt k j))
    let PR : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform post (Dist.prod (Dist.uniform (Fin q → C)) MR)
    let PI : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform post (Dist.prod (Dist.uniform (Fin q → C)) MI)
    have hpost : ((statDist PR PI : NNReal) : ℝ) ≤ rowBound := by
      have hdpi : statDist PR PI ≤
          statDist (Dist.prod (Dist.uniform (Fin q → C)) MR)
            (Dist.prod (Dist.uniform (Fin q → C)) MI) :=
        statDist_fTransform_le _ _ _
      rw [statDist_prod_left,
        show (Dist.uniform (Fin q → C)).weight = 1 from Dist.uniform_isProbDist,
        one_mul] at hdpi
      exact le_trans (by exact_mod_cast hdpi) hrow
    let rep (p : Pref k) : Fin q := Classical.choose p.property
    have rep_take (p : Pref k) : (xs (rep p)).1.take k = p.1 := by
      exact Classical.choose_spec p.property
    have side (p : Pref k) (j : Fin q) (hj : prefAt k j = p) :
        ((xs j).1.length ≤ k ↔ (xs (rep p)).1.length ≤ k) := by
      apply same_side
      rw [show (xs j).1.take k = p.1 from congrArg Subtype.val hj, rep_take]
    let addrR : Pref k ↪ (Fin q ⊕ Fin q) :=
      { toFun := fun p ↦
          if (xs (rep p)).1.length ≤ k then Sum.inl (row k p)
          else Sum.inr (row k p)
        inj' := by
          intro a b hab
          have hr := congrArg (Sum.elim id id) hab
          simp only [apply_ite, Sum.elim_inl, Sum.elim_inr] at hr
          split_ifs at hr <;> exact (row k).injective hr }
    have hstateR := gazi_eval_prod_uniform (P := Pref k) (I := Fin q) (J := Fin q)
      (A := C) addrR
    have hPR : PR = H k := by
      rw [hHuniform]
      rw [← hstateR, Dist.fTransform_comp]
      unfold PR MR
      rw [gazi_prod_map_right, Dist.fTransform_comp]
      congr 1
      funext z j
      have hs := side (prefAt k j) j rfl
      by_cases hj : k < (xs j).1.length
      · have hlong : ¬(xs (rep (prefAt k j))).1.length ≤ k := by
          intro hr
          exact (not_le_of_gt hj) (hs.mpr hr)
        simp [post, finish, addrR, zs, hj, hlong]
        rw [← List.cons_getElem_drop_succ (l := (xs j).1) (n := k) (h := hj)]
        change _ = mdIterate f _ ([((xs j).1.get ⟨k, hj⟩)] ++
          (xs j).1.drop (k + 1))
        rw [mdIterate_append]
        rw [Equiv.sumArrowEquivProdArrow_symm_apply_inr]
        simp [mdIterate]
      · have hshort : (xs (rep (prefAt k j))).1.length ≤ k :=
          hs.mp (by omega)
        simp [post, finish, addrR, zs, hj, hshort]
        rw [List.drop_eq_nil_of_le (by omega)]
        rfl
    let repI (p : Pref (k + 1)) : Fin q := Classical.choose p.property
    have repI_take (p : Pref (k + 1)) :
        (xs (repI p)).1.take (k + 1) = p.1 :=
      Classical.choose_spec p.property
    let parent (p : Pref (k + 1)) : Pref k := prefAt k (repI p)
    let addrI : Pref (k + 1) ↪ (Fin q ⊕ (Fin q × B)) :=
      { toFun := fun p ↦
          if hp : (xs (repI p)).1.length ≤ k then Sum.inl (row k (parent p))
          else Sum.inr (row k (parent p),
            (xs (repI p)).1.get ⟨k, by omega⟩)
        inj' := by
          intro a b hab
          by_cases ha : (xs (repI a)).1.length ≤ k
          · by_cases hb : (xs (repI b)).1.length ≤ k
            · have hp : parent a = parent b := by
                apply (row k).injective
                dsimp at hab
                rw [dif_pos ha, dif_pos hb] at hab
                exact Sum.inl.inj hab
              apply Subtype.ext
              rw [← repI_take a, ← repI_take b,
                List.take_of_length_le (by omega : (xs (repI a)).1.length ≤ k + 1),
                List.take_of_length_le (by omega : (xs (repI b)).1.length ≤ k + 1)]
              have hpv := congrArg Subtype.val hp
              simpa [parent, prefAt, List.take_of_length_le ha,
                List.take_of_length_le hb] using hpv
            · simp [ha, hb] at hab
          · by_cases hb : (xs (repI b)).1.length ≤ k
            · simp [ha, hb] at hab
            · have hpair :
                  (row k (parent a), (xs (repI a)).1.get ⟨k, by omega⟩) =
                    (row k (parent b), (xs (repI b)).1.get ⟨k, by omega⟩) := by
                dsimp at hab
                rw [dif_neg ha, dif_neg hb] at hab
                exact Sum.inr.inj hab
              have hp : parent a = parent b := by
                apply (row k).injective
                exact congrArg (fun z : Fin q × B ↦ z.1) hpair
              have hblock :
                  (xs (repI a)).1.get ⟨k, by omega⟩ =
                    (xs (repI b)).1.get ⟨k, by omega⟩ :=
                congrArg (fun z : Fin q × B ↦ z.2) hpair
              apply Subtype.ext
              rw [← repI_take a, ← repI_take b]
              have hpv := congrArg Subtype.val hp
              simp only [parent, prefAt] at hpv
              have hla : k < (xs (repI a)).1.length := by omega
              have hlb : k < (xs (repI b)).1.length := by omega
              calc
                (xs (repI a)).1.take (k + 1) =
                    (xs (repI a)).1.take k ++ [(xs (repI a)).1.get ⟨k, hla⟩] := by
                  rw [List.take_add_one]
                  simp [hla]
                _ = (xs (repI b)).1.take k ++
                    [(xs (repI b)).1.get ⟨k, hlb⟩] := by rw [hpv, hblock]
                _ = (xs (repI b)).1.take (k + 1) := by
                  rw [List.take_add_one]
                  simp [hlb] }
    have hstateI := gazi_eval_prod_uniform (P := Pref (k + 1)) (I := Fin q)
      (J := Fin q × B) (A := C) addrI
    have hPI : PI = H (k + 1) := by
      rw [hHuniform]
      rw [← hstateI, Dist.fTransform_comp]
      unfold PI MI
      rw [gazi_prod_map_right, Dist.fTransform_comp]
      congr 1
      funext z j
      have ht : (xs (repI (prefAt (k + 1) j))).1.take (k + 1) =
          (xs j).1.take (k + 1) := repI_take (prefAt (k + 1) j)
      have hparentJ : parent (prefAt (k + 1) j) = prefAt k j := by
        apply Subtype.ext
        have htake := congrArg (List.take k) ht
        simpa [parent, prefAt, List.take_take] using htake
      have hparentJ' : prefAt k (repI (prefAt (k + 1) j)) = prefAt k j := by
        simpa [parent] using hparentJ
      by_cases hj : k < (xs j).1.length
      · have hrepLong : ¬(xs (repI (prefAt (k + 1) j))).1.length ≤ k := by
          intro hr
          have hs := same_side (k + 1) (repI (prefAt (k + 1) j)) j ht
          have hj' : (xs j).1.length ≤ k + 1 := hs.mp (by omega)
          have heq : xs (repI (prefAt (k + 1) j)) = xs j := by
            apply Subtype.ext
            rw [← List.take_of_length_le (by omega :
              (xs (repI (prefAt (k + 1) j))).1.length ≤ k + 1), ht,
              List.take_of_length_le hj']
          have : (xs j).1.length ≤ k := by simpa [heq] using hr
          omega
        have hblockJ :
            (xs (repI (prefAt (k + 1) j))).1.get ⟨k, by omega⟩ =
              (xs j).1.get ⟨k, hj⟩ := by
          have hrepLt : k < (xs (repI (prefAt (k + 1) j))).1.length := by omega
          have hopt := congrArg (fun l : List B ↦ l[k]?) ht
          change ((xs (repI (prefAt (k + 1) j))).1.take (k + 1))[k]? =
            ((xs j).1.take (k + 1))[k]? at hopt
          rw [List.getElem?_take_of_lt (by omega : k < k + 1),
            List.getElem?_take_of_lt (by omega : k < k + 1)] at hopt
          simpa [hrepLt, hj] using hopt
        simp [post, finish, addrI, parent, zs, hj, hrepLong]
        rw [Equiv.sumArrowEquivProdArrow_symm_apply_inr, hparentJ']
        have hb : (xs (repI (prefAt (k + 1) j))).1[k] = (xs j).1[k] := hblockJ
        rw [hb]
      · have hrepShort : (xs (repI (prefAt (k + 1) j))).1.length ≤ k := by
          have hjle : (xs j).1.length ≤ k := by omega
          have hrepLe :
              (xs (repI (prefAt (k + 1) j))).1.length ≤ k + 1 :=
            (same_side (k + 1) j (repI (prefAt (k + 1) j)) ht.symm).mp (by omega)
          have heq : xs (repI (prefAt (k + 1) j)) = xs j := by
            apply Subtype.ext
            rw [← List.take_of_length_le hrepLe, ht,
              List.take_of_length_le (by omega : (xs j).1.length ≤ k + 1)]
          simpa [heq] using hjle
        simp [post, finish, addrI, parent, zs, hj, hrepShort]
        rw [List.drop_eq_nil_of_le (by omega)]
        rw [Equiv.sumArrowEquivProdArrow_symm_apply_inl, hparentJ']
        rfl
    rw [← hPR, ← hPI]
    exact hpost
  by_cases hq : q = 0
  · subst q
    have hrb : 0 ≤ rowBound := by
      have h := hrows (fun j : Fin 0 ↦ Fin.elim0 j)
      exact le_trans (NNReal.coe_nonneg _) h
    have hzero : fixedQueryDelta (cascadeReal d f) (cascadeIdeal d) xs = 0 := by
      unfold fixedQueryDelta
      rw [show cascadeReal d f = PFunPDS.Prob.functionEvaluator
          (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
          (fun K m ↦ cascade f K m.1) from rfl,
        show cascadeIdeal d = PFunPDS.Prob.urf from rfl]
      rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
        PFunPDS.Prob.fixedQueryTranscriptDist_urf]
      unfold fixedInputLiftDist
      rw [statDist_fTransform_injective _ _ _
        (fixedInputTranscriptPrefix_injective xs)]
      rw [PFunPDS.uniformP_val]
      have heq :
          Dist.fTransform (fun K : C ↦ fun j : Fin 0 ↦ cascade f K (xs j).1)
              (Dist.uniform C) =
            Dist.fTransform (fun R : BlockString B d → C ↦ fun j : Fin 0 ↦ R (xs j))
              (Dist.uniform (BlockString B d → C)) := by
        apply Finsupp.ext
        intro y
        have hy : y = fun j : Fin 0 ↦ Fin.elim0 j := Subsingleton.elim _ _
        subst y
        have hleft : ∀ a : C,
            (fun j : Fin 0 ↦ cascade f a (xs j).1) = fun j ↦ Fin.elim0 j :=
          fun _ ↦ Subsingleton.elim _ _
        have hright : ∀ a : BlockString B d → C,
            (fun j : Fin 0 ↦ a (xs j)) = fun j ↦ Fin.elim0 j :=
          fun _ ↦ Subsingleton.elim _ _
        simp only [Dist.fTransform_apply_eq_sum, hleft, hright]
        simp only [Finset.filter_true]
        rw [← Dist.weight_eq_sum, ← Dist.weight_eq_sum]
        exact Dist.uniform_isProbDist.trans Dist.uniform_isProbDist.symm
      rw [heq, statDist_self]
      rfl
    rw [hzero]
    positivity
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let j0 : Fin q := ⟨0, hqpos⟩
    let p0 : Pref 0 := prefAt 0 j0
    have pref0_eq (p : Pref 0) : p = p0 := by
      apply Subtype.ext
      rcases p.property with ⟨j, hj⟩
      rw [← hj]
      simp [p0, prefAt]
    let E0 : C ≃ (Pref 0 → C) :=
      { toFun := fun K _ ↦ K
        invFun := fun state ↦ state p0
        left_inv := by intro K; rfl
        right_inv := by
          intro state
          funext p
          rw [pref0_eq p] }
    let CR : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform (fun K : C ↦ fun j ↦ cascade f K (xs j).1) (Dist.uniform C)
    have hH0 : H 0 = CR := by
      rw [hHuniform]
      rw [← Dist.fTransform_equiv_uniform E0, Dist.fTransform_comp]
      unfold finish CR cascade
      congr 1
    let Q := Set.range xs
    let msgOf (p : Pref d) : BlockString B d :=
      ⟨p.1, by
        rcases p.property with ⟨j, hj⟩
        rw [← hj]
        exact List.length_take_le d (xs j).1⟩
    have msgOf_mem (p : Pref d) : msgOf p ∈ Q := by
      rcases p.property with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      change (xs j).1 = p.1
      exact (List.take_of_length_le (xs j).2).symm.trans hj
    let ed : Pref d ≃ Q :=
      { toFun := fun p ↦ ⟨msgOf p, msgOf_mem p⟩
        invFun := fun m ↦
          ⟨m.1.1, by
            rcases m.property with ⟨j, hj⟩
            refine ⟨j, ?_⟩
            rw [← hj]
            exact List.take_of_length_le (xs j).2⟩
        left_inv := by intro p; apply Subtype.ext; rfl
        right_inv := by intro m; apply Subtype.ext; apply Subtype.ext; rfl }
    let qAt (j : Fin q) : Q := ⟨xs j, ⟨j, rfl⟩⟩
    have ed_prefAt (j : Fin q) : ed (prefAt d j) = qAt j := by
      apply Subtype.ext
      apply Subtype.ext
      change (xs j).1.take d = (xs j).1
      exact List.take_of_length_le (xs j).2
    let E : (Q → C) ≃ (Pref d → C) :=
      Equiv.arrowCongr ed.symm (Equiv.refl C)
    let QI : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform (fun R : Q → C ↦ fun j ↦ R (qAt j)) (Dist.uniform (Q → C))
    have hHdQ : H d = QI := by
      rw [hHuniform]
      rw [← Dist.fTransform_equiv_uniform E, Dist.fTransform_comp]
      unfold QI finish
      congr 1
      funext R j
      change mdIterate f (R (ed (prefAt d j))) ((xs j).1.drop d) = R (qAt j)
      rw [List.drop_eq_nil_of_le (xs j).2]
      simp only [mdIterate]
      change R (ed (prefAt d j)) = R (qAt j)
      rw [ed_prefAt]
    let Qemb : Q ↪ BlockString B d :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let CI : RandomSystems.Dist (Fin q → C) :=
      Dist.fTransform (fun R : BlockString B d → C ↦ fun j ↦ R (xs j))
        (Dist.uniform (BlockString B d → C))
    have hCIQ : CI = QI := by
      unfold CI QI
      rw [← gazi_uniform_restrict (I := Q) (J := BlockString B d) (A := C) Qemb,
        Dist.fTransform_comp]
      congr 1
    have hHd : H d = CI := hHdQ.trans hCIQ.symm
    have hout : ((statDist CR CI : NNReal) : ℝ) ≤ (d : ℝ) * rowBound := by
      rw [← hH0, ← hHd]
      calc
        ((statDist (H 0) (H d) : NNReal) : ℝ) ≤
            ((∑ i ∈ Finset.range d,
              statDist (H i) (H (i + 1)) : NNReal) : ℝ) := by
          exact_mod_cast gazi_statDist_le_adjacent_sum H d
        _ = ∑ i ∈ Finset.range d,
            ((statDist (H i) (H (i + 1)) : NNReal) : ℝ) := by simp
        _ ≤ ∑ _i ∈ Finset.range d, rowBound := by
          apply Finset.sum_le_sum
          intro i hi
          exact hstep i (Finset.mem_range.mp hi)
        _ = (d : ℝ) * rowBound := by simp
    unfold fixedQueryDelta
    rw [show cascadeReal d f = PFunPDS.Prob.functionEvaluator
        (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
        (fun K m ↦ cascade f K m.1) from rfl,
      show cascadeIdeal d = PFunPDS.Prob.urf from rfl]
    rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
      PFunPDS.Prob.fixedQueryTranscriptDist_urf]
    unfold fixedInputLiftDist
    rw [statDist_fTransform_injective _ _ _
      (fixedInputTranscriptPrefix_injective xs), PFunPDS.uniformP_val]
    exact hout

/-- **Gaži Proposition 1.** The two Appendix-A hybrids compose: the depth
hybrid contributes `d`, and the row hybrid contributes `q`. -/
theorem cascade_na_pf_fixedQuery_bound
    (q d : ℕ) (f : CompressionFamily C B) (εna : NNReal)
    (hna : CompNASecure q f εna) (xs : Fin q → BlockString B d)
    (hpf : PrefixFreeQueries xs) :
    fixedQueryDelta (cascadeReal d f) (cascadeIdeal d) xs
      ≤ (((d * q : ℕ) : ℝ) * (εna : ℝ)) := by
  calc
    fixedQueryDelta (cascadeReal d f) (cascadeIdeal d) xs
        ≤ (d : ℝ) * ((q : ℝ) * (εna : ℝ)) :=
      gazi_lemma5_depth_hybrid q d f xs hpf ((q : ℝ) * (εna : ℝ))
        (gazi_lemma6_row_hybrid q f εna hna)
    _ = (((d * q : ℕ) : ℝ) * (εna : ℝ)) := by
      push_cast
      ring

/-! ## Gaži Theorem 1: outer call and collision reduction -/

/-- The intermediate `Cascᶠ_{K₁} ▷ r` world from §3.1: the inner key is
uniform, while the independent outer function is a URF. -/
noncomputable def nmacOuterRandom (d : ℕ) (f : CompressionFamily C B)
    (pad : C ↪ B) : PFunPDS (BlockString B d) C :=
  PFunPDS.ofFunDist
    (Dist.fTransform
      (fun p : C × (B → C) => fun m : BlockString B d =>
        p.2 (pad (cascade f p.1 m.1)))
      (Dist.prod (Dist.uniform C) (Dist.uniform (B → C))))

/-- Append one common delimiter block.  The extra block is the paper's
prefix-free extension in §3.1. -/
def appendDelimiter (d : ℕ) (b : B) (m : BlockString B d) :
    BlockString B (d + 1) :=
  ⟨m.1 ++ [b], by simpa using Nat.add_le_add_right m.2 1⟩

/-- Appending a delimiter is injective on messages. -/
theorem appendDelimiter_injective (d : ℕ) (b : B) :
    Function.Injective (appendDelimiter (B := B) d b) := by
  intro m m' h
  apply Subtype.ext
  have hlist := congrArg Subtype.val h
  simpa [appendDelimiter] using hlist

/-- If the block alphabet is larger than the strict unordered query-pair set,
every fixed `q`-tuple admits a common delimiter whose one-block extensions are
prefix-free.  Each unordered pair forbids at most one block: the block after
the shorter message when that message is a strict prefix of the longer one. -/
theorem exists_prefixFree_appendDelimiter_of_pairCount_lt (q d : ℕ)
    (xs : Fin q → BlockString B d)
    (hcard : (queryPairSet q).card < Fintype.card B) :
    ∃ b : B, PrefixFreeQueries (fun i => appendDelimiter d b (xs i)) := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let next : Fin q × Fin q → B := fun p =>
    if (xs p.1).1.length < (xs p.2).1.length then
      (xs p.2).1.getD (xs p.1).1.length b₀
    else (xs p.1).1.getD (xs p.2).1.length b₀
  by_contra hnone
  simp only [PrefixFreeQueries, PrefixFree] at hnone
  push Not at hnone
  have hsurj : Function.Surjective
      (fun p : {p // p ∈ queryPairSet q} => next p.1) := by
    intro b
    obtain ⟨m, m', hmm', hpre⟩ := hnone b
    rcases m.property with ⟨i, hi⟩
    rcases m'.property with ⟨j, hj⟩
    have hpre' : (appendDelimiter d b (xs i)).1 <+:
        (appendDelimiter d b (xs j)).1 := by
      simpa [hi, hj] using hpre
    have hext_ne : appendDelimiter d b (xs i) ≠ appendDelimiter d b (xs j) := by
      intro heq
      apply hmm'
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg Subtype.val hi).symm.trans
        ((congrArg Subtype.val heq).trans (congrArg Subtype.val hj))
    have hxs_ne : xs i ≠ xs j := fun h => hext_ne (congrArg (appendDelimiter d b) h)
    have hlen_le : (xs i).1.length ≤ (xs j).1.length := by
      have := hpre'.length_le
      simp only [appendDelimiter, List.length_append, List.length_singleton] at this
      omega
    have hlen : (xs i).1.length < (xs j).1.length := by
      refine lt_of_le_of_ne hlen_le ?_
      intro heq
      have hext_eq : appendDelimiter d b (xs i) = appendDelimiter d b (xs j) := by
        apply Subtype.ext
        exact hpre'.eq_of_length (by simp [appendDelimiter, heq])
      exact hext_ne hext_eq
    have helem := hpre'.getElem (i := (xs i).1.length) (by simp [appendDelimiter])
    have hnext : (xs j).1.getD (xs i).1.length b₀ = b := by
      rw [List.getD_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hlen]
      simpa [appendDelimiter, hlen] using helem.symm
    rcases lt_or_gt_of_ne (fun hij => hxs_ne (congrArg xs hij)) with hij | hji
    · refine ⟨⟨(i, j), by simp [queryPairSet, hij]⟩, ?_⟩
      change next (i, j) = b
      unfold next
      rw [if_pos hlen]
      exact hnext
    · refine ⟨⟨(j, i), by simp [queryPairSet, hji]⟩, ?_⟩
      change next (j, i) = b
      unfold next
      rw [if_neg (not_lt_of_ge (Nat.le_of_lt hlen))]
      exact hnext
  have hle := Fintype.card_le_of_surjective _ hsurj
  rw [Fintype.card_coe] at hle
  omega

/-- The original coarse `q²` delimiter criterion, retained for the R2 proof. -/
theorem exists_prefixFree_appendDelimiter (q d : ℕ)
    (xs : Fin q → BlockString B d) (hcard : q ^ 2 < Fintype.card B) :
    ∃ b : B, PrefixFreeQueries (fun i => appendDelimiter d b (xs i)) := by
  apply exists_prefixFree_appendDelimiter_of_pairCount_lt q d xs
  have hle : (queryPairSet q).card ≤ q ^ 2 := by
    calc
      (queryPairSet q).card ≤ (Finset.univ : Finset (Fin q × Fin q)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = q ^ 2 := by simp [pow_two]
  omega

/-- The random-outer NMAC world is exactly the visible part of the shared
seeded hash-then-URF condition-C game. -/
theorem nmacOuterRandom_eq_ignoreMBO (d : ℕ) (f : CompressionFamily C B)
    (pad : C ↪ B) :
    nmacOuterRandom d f pad =
      PFunPDS.ignoreMBO (seededHashThenURFGame (O := C) (Dist.uniform C)
        (fun K (m : BlockString B d) => pad (cascade f K m.1))) := by
  rw [seededHashThenURFGame_ignoreMBO]
  rfl

/-- Birthday bound for collisions of a uniform function on a fixed query
tuple, excluding repeated inputs. -/
theorem uniform_fixedQuery_collision_le (q : ℕ)
    {I : Type*} [Fintype I] [DecidableEq I] (xs : Fin q → I) :
    (Dist.uniform (I → C)).mass (fun r =>
      ∃ i j : Fin q, i ≠ j ∧ xs i ≠ xs j ∧ r (xs i) = r (xs j)) ≤
      pairCollisionUnionBound C q := by
  classical
  let P : Finset (Fin q × Fin q) := queryPairSet q
  let E : (Fin q × Fin q) → (I → C) → Prop := fun p r =>
    xs p.1 ≠ xs p.2 ∧ r (xs p.1) = r (xs p.2)
  refine mass_le_pairCollisionUnionBound_of_cover_injOn C
    (Dist.uniform (I → C)) q P E
    (fun r => ∃ i j : Fin q, i ≠ j ∧ xs i ≠ xs j ∧ r (xs i) = r (xs j))
    id ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨i, j, hij, hxs, hout⟩ := hr
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨(i, j), by simp [P, queryPairSet, hlt], hxs, hout⟩
    · exact ⟨(j, i), by simp [P, queryPairSet, hgt], hxs.symm, hout.symm⟩
  · intro p hp
    by_cases hxs : xs p.1 ≠ xs p.2
    · exact (mass_mono (Dist.uniform (I → C)) fun r hr => hr.2).trans_eq
        (uniform_function_pair_eq_mass_of_codomain hxs)
    · exact Dist.mass_le_of_forall_not _ (fun r hr => hxs hr.1) _
  · intro p hp
    simpa [P] using hp
  · exact Function.Injective.injOn (Function.injective_id)

/-- The first hop in Gaži §3.1: replace the outer `f_{K₂}` by `r`.  The
independent inner key is part of the probabilistic converter, and the
one-call converter DPI preserves the `q`-query budget. -/
theorem gazi_outer_prf_hop
    (q d : ℕ) (f : CompressionFamily C B) (pad : C ↪ B) :
    Δ(⌈q⌉ nmacReal d f pad, ⌈q⌉ nmacOuterRandom d f pad)
      ≤ epsComp q f := by
  classical
  let c : C → BlockString B d → B := fun K m => pad (cascade f K m.1)
  let S : C → PFunPDS (BlockString B d) C := fun K =>
    PFunPDS.applyDDC (PFunConverter.DDC.simple (c K) (id : C → C)) (compReal f)
  let T : C → PFunPDS (BlockString B d) C := fun K =>
    PFunPDS.applyDDC (PFunConverter.DDC.simple (c K) (id : C → C)) compIdeal
  have hone (K : C) :
      PFunConverter.DDC.AnswersWithin
        (PFunConverter.DDC.simpleStep (c K) (id : C → C)) 1 := by
    intro m ys hys
    cases ys with
    | nil => simp at hys
    | cons y ys => exact ⟨y, rfl⟩
  have hpoint (K : C) : Δ(⌈q⌉ S K, ⌈q⌉ T K) ≤ epsComp q f := by
    simpa [S, T, epsComp, Nat.mul_one] using
      (maxAdvantage_filterQueries_applyDDC_le
        (PFunConverter.DDC.simpleStep (c K) (id : C → C))
        (hone K) q
        (compReal f) compIdeal
        (PFunPDS.ofFunDist_isRandomFunction _)
        PFunPDS.URF_isRandomFunction)
  have hS (K : C) : S K = PFunPDS.ofFunDist
      (Dist.fTransform (fun K₂ : C => fun m : BlockString B d =>
        f K₂ (pad (cascade f K m.1))) (Dist.uniform C)) := by
    rw [show S K = PFunPDS.applyDDC
      (PFunConverter.DDC.simple (c K) (id : C → C)) (compReal f) from rfl]
    unfold compReal
    rw [PFunPDS.applyDDC_simple_ofFunDist, Dist.fTransform_comp]
    rfl
  have hT (K : C) : T K = PFunPDS.ofFunDist
      (Dist.fTransform (fun r : B → C => fun m : BlockString B d =>
        r (pad (cascade f K m.1))) (Dist.uniform (B → C))) := by
    rw [show T K = PFunPDS.applyDDC
      (PFunConverter.DDC.simple (c K) (id : C → C)) compIdeal from rfl]
    unfold compIdeal PFunPDS.URF
    rw [PFunPDS.applyDDC_simple_ofFunDist]
    rfl
  let mix (U : C → PFunPDS (BlockString B d) C) :
      PFunPDS (BlockString B d) C :=
    (Dist.uniform C).sum fun K w => w • U K
  have hnmac : nmacReal d f pad = mix S := by
    unfold nmacReal sequenceMACReal
    have hprod :
        Dist.fTransform
            (fun p : C × C => fun m : BlockString B d =>
              f p.2 (pad (cascade f p.1 m.1)))
            (Dist.prod (Dist.uniform C) (Dist.uniform C)) =
          (Dist.uniform C).sum (fun K w => w •
            Dist.fTransform (fun K₂ : C => fun m : BlockString B d =>
              f K₂ (pad (cascade f K m.1))) (Dist.uniform C)) := by
      apply Finsupp.ext
      intro z
      rw [Dist.fTransform_apply_eq_mass, Dist.mass_prod_eq_double_sum]
      simp only [Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        Dist.fTransform_apply_eq_mass, Dist.mass]
      apply Finsupp.sum_congr
      intro K hK
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro K₂ hK₂
      by_cases hz : (fun m : BlockString B d =>
        f K₂ (pad (cascade f K m.1))) = z <;> simp [hz]
    change PFunPDS.ofFunDist
      (Dist.fTransform
        (fun p : C × C => fun m : BlockString B d =>
          f p.2 (pad (cascade f p.1 m.1)))
        (Dist.prod (Dist.uniform C) (Dist.uniform C))) = mix S
    rw [hprod]
    unfold mix PFunPDS.ofFunDist
    let V : C → NNReal → RandomSystems.Dist (BlockString B d → C) :=
      fun K w => w • Dist.fTransform
        (fun K₂ : C => fun m : BlockString B d =>
          f K₂ (pad (cascade f K m.1))) (Dist.uniform C)
    change (Finsupp.mapDomain.addMonoidHom PFunDDS.functionEvaluator)
      ((Dist.uniform C).sum V) = _
    rw [map_finsuppSum
      (Finsupp.mapDomain.addMonoidHom PFunDDS.functionEvaluator)
      (Dist.uniform C) V]
    apply Finsupp.sum_congr
    intro K hK
    rw [hS]
    dsimp [V]
    unfold PFunPDS.ofFunDist Dist.fTransform
    rw [Finsupp.mapDomain_smul]
    rfl
  have houter : nmacOuterRandom d f pad = mix T := by
    unfold nmacOuterRandom
    have hprod :
        Dist.fTransform
            (fun p : C × (B → C) => fun m : BlockString B d =>
              p.2 (pad (cascade f p.1 m.1)))
            (Dist.prod (Dist.uniform C) (Dist.uniform (B → C))) =
          (Dist.uniform C).sum (fun K w => w •
            Dist.fTransform (fun r : B → C => fun m : BlockString B d =>
              r (pad (cascade f K m.1))) (Dist.uniform (B → C))) := by
      apply Finsupp.ext
      intro z
      rw [Dist.fTransform_apply_eq_mass, Dist.mass_prod_eq_double_sum]
      simp only [Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        Dist.fTransform_apply_eq_mass, Dist.mass]
      apply Finsupp.sum_congr
      intro K hK
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro r hr
      by_cases hz : (fun m : BlockString B d =>
        r (pad (cascade f K m.1))) = z <;> simp [hz]
    rw [hprod]
    unfold mix PFunPDS.ofFunDist
    let V : C → NNReal → RandomSystems.Dist (BlockString B d → C) :=
      fun K w => w • Dist.fTransform
        (fun r : B → C => fun m : BlockString B d =>
          r (pad (cascade f K m.1))) (Dist.uniform (B → C))
    change (Finsupp.mapDomain.addMonoidHom PFunDDS.functionEvaluator)
      ((Dist.uniform C).sum V) = _
    rw [map_finsuppSum
      (Finsupp.mapDomain.addMonoidHom PFunDDS.functionEvaluator)
      (Dist.uniform C) V]
    apply Finsupp.sum_congr
    intro K hK
    rw [hT]
    dsimp [V]
    unfold PFunPDS.ofFunDist Dist.fTransform
    rw [Finsupp.mapDomain_smul]
    rfl
  rw [hnmac, houter]
  refine maxAdvantage_le_of_forall_advantage_le fun D hD => ?_
  have hfilter (U : C → PFunPDS (BlockString B d) C) :
      (⌈q⌉ mix U) = mix (fun K => (⌈q⌉ U K)) := by
    unfold PFunPDS.filterQueries mix
    change (Finsupp.mapDomain.addMonoidHom (PFunDDS.filterQueries q))
      ((Dist.uniform C).sum fun K w => w • U K) = _
    rw [map_finsuppSum
      (Finsupp.mapDomain.addMonoidHom (PFunDDS.filterQueries q))]
    apply Finsupp.sum_congr
    intro K hK
    change Finsupp.mapDomain (PFunDDS.filterQueries q)
      ((Dist.uniform C) K • U K) =
        (Dist.uniform C) K •
          Finsupp.mapDomain (PFunDDS.filterQueries q) (U K)
    rw [Finsupp.mapDomain_smul]
  have hverdict (U : C → PFunPDS (BlockString B d) C) :
      verdictProb D (mix U) =
        (Dist.uniform C).sum (fun K w => w * verdictProb D (U K)) := by
    unfold verdictProb GamePerf.winProb mix
    calc
      (D.sum fun dd dp =>
          ((Dist.uniform C).sum fun K w => w • U K).sum fun g gp =>
            dp * gp * if PFunDDS.verdict dd g then 1 else 0) =
        D.sum (fun dd dp => (Dist.uniform C).sum fun K w =>
          (w • U K).sum fun g gp =>
            dp * gp * if PFunDDS.verdict dd g then 1 else 0) := by
          apply Finsupp.sum_congr
          intro dd hdd
          rw [Finsupp.sum_sum_index]
          · intro g
            simp
          · intro g a b
            by_cases hv : PFunDDS.verdict dd g <;> simp [hv]
            ring
      _ = D.sum (fun dd dp => (Dist.uniform C).sum fun K w =>
          w * (U K).sum fun g gp =>
            dp * gp * if PFunDDS.verdict dd g then 1 else 0) := by
          apply Finsupp.sum_congr
          intro dd hdd
          apply Finsupp.sum_congr
          intro K hK
          rw [Finsupp.sum_smul_index]
          · rw [Finsupp.mul_sum]
            apply Finsupp.sum_congr
            intro g hg
            ring
          · intro g
            simp
      _ = (Dist.uniform C).sum (fun K w => D.sum fun dd dp =>
          w * (U K).sum fun g gp =>
            dp * gp * if PFunDDS.verdict dd g then 1 else 0) :=
        Finsupp.sum_comm D (Dist.uniform C) _
      _ = (Dist.uniform C).sum (fun K w => w * D.sum fun dd dp =>
          (U K).sum fun g gp =>
            dp * gp * if PFunDDS.verdict dd g then 1 else 0) := by
          apply Finsupp.sum_congr
          intro K hK
          rw [Finsupp.mul_sum]
  have hmix_adv :
      advantage D (⌈q⌉ mix S) (⌈q⌉ mix T) =
        (Dist.uniform C).sum (fun K w => (w : ℝ) *
          advantage D (⌈q⌉ S K) (⌈q⌉ T K)) := by
    rw [hfilter, hfilter]
    unfold advantage
    rw [hverdict, hverdict]
    have hcoe (F : C → NNReal → NNReal) :
        (((Dist.uniform C).sum F : NNReal) : ℝ) =
          (Dist.uniform C).sum (fun K w => ((F K w : NNReal) : ℝ)) := by
      simp [Finsupp.sum]
    rw [hcoe, hcoe]
    simp only [NNReal.coe_mul]
    rw [← Finsupp.sum_sub]
    apply Finsupp.sum_congr
    intro K hK
    ring
  rw [hmix_adv]
  calc
    (Dist.uniform C).sum (fun K w => (w : ℝ) *
        advantage D (⌈q⌉ S K) (⌈q⌉ T K))
      ≤ (Dist.uniform C).sum (fun _K w => (w : ℝ) * epsComp q f) := by
        apply Finsupp.sum_le_sum
        intro K hK
        gcongr
        exact (advantage_le_maxAdvantage D _ _ hD).trans (hpoint K)
    _ = epsComp q f := by
      rw [← Finsupp.sum_mul]
      have hw : (Dist.uniform C).sum (fun _K w => (w : ℝ)) = 1 := by
        have h := (Dist.uniform_isProbDist : (Dist.uniform C).weight = 1)
        change (Dist.uniform C).weight = 1 at h
        rw [Dist.weight_eq_finsupp_sum] at h
        simpa [Finsupp.sum] using congrArg NNReal.toReal h
      rw [hw, one_mul]

/-- The remaining §3.1 chain after the outer-call hop, retaining the exact
strict-pair birthday term.  `cascadeBound` is any uniform fixed-query cascade
bound; the original R2 scalar is supplied by the corollary below. -/
theorem gazi_outer_random_collision_bound_exact
    (q d : ℕ) (f : CompressionFamily C B) (pad : C ↪ B)
    (cascadeBound : NNReal)
    (hcascade : ∀ xs : Fin q → BlockString B (d + 1),
      PrefixFreeQueries xs →
      fixedQueryDelta (cascadeReal (d + 1) f) (cascadeIdeal (d + 1)) xs
        ≤ (cascadeBound : ℝ)) :
    Δ(⌈q⌉ nmacOuterRandom d f pad, ⌈q⌉ macIdeal d)
      ≤ (cascadeBound : ℝ) + (pairCollisionUnionBound C q : ℝ) := by
  classical
  let H : C → BlockString B d → B := fun K m => pad (cascade f K m.1)
  let εleaf : NNReal := cascadeBound + pairCollisionUnionBound C q
  have hleaf : ∀ w : PFunDDS.Winner (BlockString B d) C, IsBlind w →
      (Dist.uniform C).mass (fun K =>
        seededHashCollision H K (blindQueryList w q)) ≤ εleaf := by
    intro w hw
    let l := blindQueryList w q
    have hlen : l.length ≤ q := blindQueryList_length_le w q
    by_cases hcard : Fintype.card C ≤ (queryPairSet q).card
    · refine (Dist.mass_le_one Dist.uniform_isProbDist _).trans ?_
      have hCpos : (0 : NNReal) < (Fintype.card C : NNReal) := by positivity
      have hratio : (1 : NNReal) ≤ pairCollisionUnionBound C q := by
        unfold pairCollisionUnionBound
        rw [le_div_iff₀ hCpos]
        simpa only [one_mul] using (by exact_mod_cast hcard)
      exact le_trans hratio (le_add_left (le_refl _))
    · have hC : (queryPairSet q).card < Fintype.card C := by omega
      have hCB : Fintype.card C ≤ Fintype.card B :=
        Fintype.card_le_of_injective pad pad.injective
      have hB : (queryPairSet q).card < Fintype.card B := lt_of_lt_of_le hC hCB
      by_cases hl : l = []
      · have hnone : ∀ K : C, ¬ seededHashCollision H K l := by
          intro K hbad
          obtain ⟨m, hm, -⟩ := hbad
          simp [hl] at hm
        exact (Dist.mass_le_of_forall_not _ hnone _).trans (zero_le _)
      · let m₀ : BlockString B d := l.getLast hl
        let xs : Fin q → BlockString B d := fun i => l.getD i.1 m₀
        obtain ⟨b, hpf⟩ :=
          exists_prefixFree_appendDelimiter_of_pairCount_lt q d xs hB
        let zs : Fin q → BlockString B (d + 1) :=
          fun i => appendDelimiter d b (xs i)
        let CR : RandomSystems.Dist (Fin q → C) :=
          Dist.fTransform (fun K : C => fun i => cascade f K (zs i).1)
            (Dist.uniform C)
        let CI : RandomSystems.Dist (Fin q → C) :=
          Dist.fTransform (fun R : BlockString B (d + 1) → C =>
            fun i => R (zs i)) (Dist.uniform (BlockString B (d + 1) → C))
        let Coll : (Fin q → C) → Prop := fun v =>
          ∃ i j : Fin q, i ≠ j ∧ zs i ≠ zs j ∧ v i = v j
        have hquery (m : BlockString B d) (hm : m ∈ l) :
            ∃ i : Fin q, xs i = m := by
          have hi : l.idxOf m < q :=
            lt_of_lt_of_le (List.idxOf_lt_length_of_mem hm) hlen
          refine ⟨⟨l.idxOf m, hi⟩, ?_⟩
          unfold xs
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm)]
          exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
        have hbad_to_coll : ∀ K, seededHashCollision H K l →
            Coll (fun i => cascade f K (zs i).1) := by
          intro K hbad
          obtain ⟨m, hm, m', hm', hmm', hcas⟩ := hbad
          obtain ⟨i, hi⟩ := hquery m hm
          obtain ⟨j, hj⟩ := hquery m' hm'
          have hij : i ≠ j := by
            intro hij
            apply hmm'
            rw [← hi, ← hj, hij]
          have hzs : zs i ≠ zs j := by
            unfold zs
            intro heq
            apply hmm'
            rw [← hi, ← hj]
            exact appendDelimiter_injective d b heq
          refine ⟨i, j, hij, hzs, ?_⟩
          have hcas' : cascade f K m.1 = cascade f K m'.1 := by
            apply pad.injective
            simpa [H] using hcas
          have hcasxs : mdIterate f K (xs i).1 = mdIterate f K (xs j).1 := by
            change cascade f K (xs i).1 = cascade f K (xs j).1
            rw [hi, hj]
            exact hcas'
          change cascade f K (zs i).1 = cascade f K (zs j).1
          unfold zs appendDelimiter cascade
          rw [mdIterate_append, mdIterate_append]
          rw [hcasxs]
        have hreal : (Dist.uniform C).mass (fun K => seededHashCollision H K l) ≤
            CR.mass Coll := by
          calc
            (Dist.uniform C).mass (fun K => seededHashCollision H K l) ≤
                (Dist.uniform C).mass
                  (fun K => Coll (fun i => cascade f K (zs i).1)) :=
              mass_mono _ hbad_to_coll
            _ = CR.mass Coll := by
              unfold CR
              rw [Dist.mass_fTransform]
        have hsd : ((statDist CR CI : NNReal) : ℝ) ≤ (cascadeBound : ℝ) := by
          have h := hcascade zs (by simpa [zs] using hpf)
          unfold fixedQueryDelta at h
          rw [show cascadeReal (d + 1) f = PFunPDS.Prob.functionEvaluator
              (⟨Dist.uniform C, Dist.uniform_isProbDist⟩ : Dist.ProbDist C)
              (fun K m => cascade f K m.1) from rfl,
            show cascadeIdeal (d + 1) = PFunPDS.Prob.urf from rfl] at h
          rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator,
            PFunPDS.Prob.fixedQueryTranscriptDist_urf] at h
          unfold fixedInputLiftDist at h
          rw [statDist_fTransform_injective _ _ _
            (fixedInputTranscriptPrefix_injective zs), PFunPDS.uniformP_val] at h
          exact h
        have hideal : CI.mass Coll ≤ pairCollisionUnionBound C q := by
          unfold CI Coll
          rw [Dist.mass_fTransform]
          exact uniform_fixedQuery_collision_le q zs
        have hmass : ((CR.mass Coll : NNReal) : ℝ) ≤
            (cascadeBound : ℝ) + (pairCollisionUnionBound C q : ℝ) := by
          have hgap := mass_sub_mass_le_statDist CR CI Coll
          have hideal' : ((CI.mass Coll : NNReal) : ℝ) ≤
              (pairCollisionUnionBound C q : ℝ) := by exact_mod_cast hideal
          linarith
        exact le_trans hreal (by exact_mod_cast hmass)
  have hmain := maxAdvantage_filterQueries_seededHashThenURF_le
    (O := C) (Dist.uniform C) H q εleaf Dist.uniform_isProbDist hleaf
  rw [← nmacOuterRandom_eq_ignoreMBO d f pad] at hmain
  change Δ(⌈q⌉ nmacOuterRandom d f pad, ⌈q⌉ macIdeal d) ≤ _ at hmain
  simpa [εleaf, macIdeal, H] using hmain

/-- The original R2 collision leg.  It instantiates the exact core with the
Gaži cascade scalar and then performs only the paper's coarse birthday
weakening. -/
theorem gazi_outer_random_collision_bound
    (q d : ℕ) (f : CompressionFamily C B) (pad : C ↪ B)
    (εna : NNReal)
    (hcascade : ∀ xs : Fin q → BlockString B (d + 1),
      PrefixFreeQueries xs →
      fixedQueryDelta (cascadeReal (d + 1) f) (cascadeIdeal (d + 1)) xs
        ≤ ((((d + 1) * q : ℕ) : ℝ) * (εna : ℝ))) :
    Δ(⌈q⌉ nmacOuterRandom d f pad, ⌈q⌉ macIdeal d)
      ≤ (((d + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by
  let cascadeBound : NNReal := (((d + 1) * q : ℕ) : NNReal) * εna
  have hexact := gazi_outer_random_collision_bound_exact q d f pad
    cascadeBound (by simpa [cascadeBound] using hcascade)
  calc
    Δ(⌈q⌉ nmacOuterRandom d f pad, ⌈q⌉ macIdeal d) ≤
        (cascadeBound : ℝ) + (pairCollisionUnionBound C q : ℝ) := hexact
    _ ≤ (((d + 1) * q : ℕ) : ℝ) * (εna : ℝ) +
        ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by
      dsimp [cascadeBound]
      push_cast
      gcongr
      have hbirthday : (pairCollisionUnionBound C q : ℝ) ≤
          (q : ℝ) ^ 2 / (Fintype.card C : ℝ) := by
        calc
          (pairCollisionUnionBound C q : ℝ) ≤
              (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card C : ℝ) :=
            pairCollisionUnionBound_le_birthday C q
          _ ≤ (q : ℝ) ^ 2 / (Fintype.card C : ℝ) := by
            apply (div_le_div_iff_of_pos_right (by positivity)).2
            nlinarith [sq_nonneg (q : ℝ)]
      simpa only [Nat.cast_pow] using hbirthday

/-- Backendal's strong multi-user NMAC bound.  The depth hybrid is unchanged,
but each layer is charged directly to the existing `q`-user compression
worlds.  In particular, the row hybrid of `gazi_lemma6_row_hybrid` is not used. -/
theorem nmac_prf_bound_strong_mu
    (q ℓ : ℕ) (f : CompressionFamily C B) (pad : C ↪ B) :
    Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ macIdeal ℓ)
      ≤ (ℓ + 2 : ℝ) * epsCompMU q q f
        + (pairCollisionUnionBound C q : ℝ) := by
  classical
  have hepsMU : 0 ≤ epsCompMU q q f := by
    let zs : Fin q → (Fin q × B) := fun i => (i, Classical.arbitrary B)
    have hfixed : 0 ≤
        fixedQueryDelta (multiCompReal q f) (multiCompIdeal q) zs := by
      unfold fixedQueryDelta
      positivity
    exact hfixed.trans (multiComp_fixedQueryDelta_le_epsCompMU q q f zs)
  cases q with
  | zero =>
      have hrealProb : (nmacReal ℓ f pad).isProbDist := by
        unfold nmacReal sequenceMACReal
        cr18_prob
      have hidealProb : (macIdeal ℓ : PFunPDS (BlockString B ℓ) C).isProbDist := by
        exact PFunPDS.URF_isProbDist
      have hrealTotal : CondEquiv.TotalOnNonempty (nmacReal ℓ f pad) := by
        unfold nmacReal sequenceMACReal
        exact PFunPDS.ofFunDist_totalOnNonempty _
      have hidealTotal : CondEquiv.TotalOnNonempty
          (macIdeal ℓ : PFunPDS (BlockString B ℓ) C) := by
        exact PFunPDS.URF_totalOnNonempty
      let dummy : BlockString B ℓ := ⟨[], by simp⟩
      have hnorm := deltaFilteredFiniteQueryNormalization_of_totalOnNonempty
        dummy 0 (nmacReal ℓ f pad) (macIdeal ℓ) hrealTotal hidealTotal
      have hweight : (⌈0⌉ nmacReal ℓ f pad).weight =
          (⌈0⌉ macIdeal ℓ).weight :=
        Dist.weight_eq_weight_of_isProbDist
          ((PFunPDS.isProbDist_filterQueries_iff 0 (nmacReal ℓ f pad)).mpr hrealProb)
          ((PFunPDS.isProbDist_filterQueries_iff 0 (macIdeal ℓ)).mpr hidealProb)
      have hzero : Δ(⌈0⌉ nmacReal ℓ f pad, ⌈0⌉ macIdeal ℓ) ≤ (0 : ℝ) :=
        maxAdvantage_filterQueries_zero_le_of_deltaFilteredFiniteQueryNormalization
          (nmacReal ℓ f pad) (macIdeal ℓ) (by positivity) hweight hnorm
      exact hzero.trans (by positivity)
  | succ q =>
      let q' := q + 1
      let εmu : NNReal := ⟨epsCompMU q' q' f, by simpa [q'] using hepsMU⟩
      have hcascade : ∀ xs : Fin q' → BlockString B (ℓ + 1),
          PrefixFreeQueries xs →
          fixedQueryDelta (cascadeReal (ℓ + 1) f) (cascadeIdeal (ℓ + 1)) xs
            ≤ ((ℓ + 1 : ℕ) : ℝ) * epsCompMU q' q' f := by
        intro xs hpf
        exact gazi_lemma5_depth_hybrid q' (ℓ + 1) f xs hpf
          (epsCompMU q' q' f)
          (multiComp_fixedQueryDelta_le_epsCompMU q' q' f)
      let cascadeBound : NNReal := (ℓ + 1 : NNReal) * εmu
      have hcollision := gazi_outer_random_collision_bound_exact q' ℓ f pad
        cascadeBound (by simpa [cascadeBound, εmu] using hcascade)
      have houter :
          Δ(⌈q'⌉ nmacReal ℓ f pad, ⌈q'⌉ nmacOuterRandom ℓ f pad) ≤
            epsCompMU q' q' f :=
        (gazi_outer_prf_hop q' ℓ f pad).trans
          (epsComp_le_epsCompMU q' f (by simp [q']))
      calc
        Δ(⌈q'⌉ nmacReal ℓ f pad, ⌈q'⌉ macIdeal ℓ) ≤
            Δ(⌈q'⌉ nmacReal ℓ f pad, ⌈q'⌉ nmacOuterRandom ℓ f pad) +
              Δ(⌈q'⌉ nmacOuterRandom ℓ f pad, ⌈q'⌉ macIdeal ℓ) :=
          maxAdvantage_triangle _ _ _
        _ ≤ epsCompMU q' q' f +
              ((cascadeBound : ℝ) + (pairCollisionUnionBound C q' : ℝ)) :=
          add_le_add houter hcollision
        _ = (ℓ + 2 : ℝ) * epsCompMU q' q' f +
              (pairCollisionUnionBound C q' : ℝ) := by
          have hbound : (cascadeBound : ℝ) =
              ((ℓ + 1 : ℕ) : ℝ) * epsCompMU q' q' f := by
            simp [cascadeBound, εmu]
          rw [hbound]
          push_cast
          ring

/-- **Gaži--Pietrzak--Rybár 2014, Theorem 1 (Eq. (1)).**

This is the paper theorem itself, with the computational running-time clauses
erased and its two PRF assumptions represented by `epsComp` and
`CompNASecure`. -/
theorem nmac_prf_bound
    (q ℓ : ℕ) (f : CompressionFamily C B) (pad : C ↪ B)
    (εna : NNReal) (hna : CompNASecure q f εna) :
    Δ(⌈q⌉ nmacReal ℓ f pad,
        ⌈q⌉ macIdeal ℓ)
      ≤ epsComp q f
        + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by
  have hcascade : ∀ xs : Fin q → BlockString B (ℓ + 1),
      PrefixFreeQueries xs →
      fixedQueryDelta (cascadeReal (ℓ + 1) f) (cascadeIdeal (ℓ + 1)) xs
        ≤ ((((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)) := by
    intro xs hpf
    exact cascade_na_pf_fixedQuery_bound q (ℓ + 1) f εna hna xs hpf
  let systems : Complexity.SystemTrace (BlockString B ℓ) C
    | 0 => ⌈q⌉ nmacReal ℓ f pad
    | 1 => ⌈q⌉ nmacOuterRandom ℓ f pad
    | _ => ⌈q⌉ macIdeal ℓ
  have htriangle :
      Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ macIdeal ℓ)
        ≤ Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ nmacOuterRandom ℓ f pad)
          + Δ(⌈q⌉ nmacOuterRandom ℓ f pad, ⌈q⌉ macIdeal ℓ) := by
    have h := Complexity.maxAdvantage_le_adjacent_sum systems 2
    rw [Complexity.adjacentMaxAdvantageSum,
      Finset.sum_range_succ, Finset.sum_range_succ] at h
    simp [systems] at h
    exact h
  calc
    Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ macIdeal ℓ)
        ≤ Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ nmacOuterRandom ℓ f pad)
          + Δ(⌈q⌉ nmacOuterRandom ℓ f pad, ⌈q⌉ macIdeal ℓ) :=
      htriangle
    _ ≤ epsComp q f
          + ((((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
            + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ)) :=
      add_le_add (gazi_outer_prf_hop q ℓ f pad)
        (gazi_outer_random_collision_bound q ℓ f pad εna hcascade)
    _ = epsComp q f
          + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
          + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by ring

/-- **Theorem 1 plus the explicit SequenceMAC key-mixture hop.**

The NMAC part is exactly
`ε + (ℓ+1)q εna + q²/|C|`.  Here `|C| = 2^c`, so the last term is the paper's
`q²/2^c`.  `epsKS` is zero when `keyDist` is the independent-uniform NMAC
distribution and otherwise cleanly isolates the separate SequenceMAC key
schedule that the paper does not define.

The proof body is the later reduction/hybrid task; the statement and every
object type are the paper model. -/
-- GUARDRAIL (R2 goal)
theorem sequenceMAC_prf_bound
    (q ℓ : ℕ) (f : CompressionFamily C B) (pad : C ↪ B)
    (keyDist : RandomSystems.Dist (C × C)) (εna : NNReal)
    (hna : CompNASecure q f εna) :
    Δ(⌈q⌉ sequenceMACReal ℓ f pad keyDist,
        ⌈q⌉ macIdeal ℓ)
      ≤ epsKS q ℓ f pad keyDist
        + epsComp q f
        + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by
  calc
    Δ(⌈q⌉ sequenceMACReal ℓ f pad keyDist, ⌈q⌉ macIdeal ℓ)
        ≤ epsKS q ℓ f pad keyDist
          + Δ(⌈q⌉ nmacReal ℓ f pad, ⌈q⌉ macIdeal ℓ) := by
      unfold epsKS
      exact maxAdvantage_triangle _ _ _
    _ ≤ epsKS q ℓ f pad keyDist
          + (epsComp q f
            + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
            + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ)) := by
      gcongr
      exact nmac_prf_bound q ℓ f pad εna hna
    _ = epsKS q ℓ f pad keyDist
          + epsComp q f
          + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
          + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ) := by ring

end SequenceHash.MACPRF
