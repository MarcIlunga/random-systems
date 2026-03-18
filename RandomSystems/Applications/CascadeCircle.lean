/-
Cascade for random functions (basic PRF-style bound).

Goal (paper-faithful): model the MauPie04 `∘` operator for random functions
and prove a birthday-bound style security statement:

  g ∘ f is close to a random function, because collisions in f(x_i) are unlikely.

This file is a *work-in-progress scaffold*:
- It defines the cascade PDS and the instrumented ("chain") PDS exposing the
  intermediate values `u_i = f(x_i)`.
- It states the intended `advantageOn` theorem on injective input sequences.

We keep this file out of `RandomSystems.lean` for now so it does not affect the
main build until the final bound is filled in.
-/
import RandomSystems.Advantage
import RandomSystems.ConditionBased
import RandomSystems.Instances.URF
import RandomSystems.Instances.URFfunEval
import RandomSystems.Applications.PRPPRFSwitching
import RandomSystems.Dist

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

namespace MauPie04CascadeFun

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
variable {q : ℕ}

/-! ### PDS definitions -/

private def circleFun (p : (X → X) × (X → X)) : X → X :=
  fun x => p.2 (p.1 x)

private def circleChainFun (p : (X → X) × (X → X)) : X → X × X :=
  fun x =>
    let u := p.1 x
    (u, p.2 u)

/-- Tag-only cascade PDS: sample independent `f,g : X → X` and answer with `g (f x)`. -/
def URFfunCircle : PDS X X q where
  dist :=
    Dist.fTransform
      (fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleFun (X := X) p))
      (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))

/-- Instrumented cascade PDS: output both `u = f x` and `v = g u` per query. -/
def URFfunCircleChain : PDS X (X × X) q where
  dist :=
    Dist.fTransform
      (fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))
      (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))

/-! ### Projection from chain transcripts to tag transcripts -/

def chainTranscriptToTagTranscript : Transcript X (X × X) q → Transcript X X q :=
  fun t i => ((t i).1, ((t i).2).2)

lemma URFfunCircle_transcriptDist_eq_fTransform_chainTranscriptDist
    (inputs : Fin q → X) :
    (URFfunCircle (X := X) (q := q)).transcriptDist inputs =
      Dist.fTransform (chainTranscriptToTagTranscript (X := X) (q := q))
        ((URFfunCircleChain (X := X) (q := q)).transcriptDist inputs) := by
  classical
  ext t
  -- Collapse both sides into a single pushforward from the same base distribution on `(f,g)`,
  -- then use that projecting the chain transcript is definitionally the tag transcript.
  have hmaps :
      (fun p : (X → X) × (X → X) =>
          DDS.transcript (DDS.ofFunq (q := q) (circleFun (X := X) p)) inputs)
        =
      (fun p : (X → X) × (X → X) =>
          chainTranscriptToTagTranscript (X := X) (q := q)
            (DDS.transcript (DDS.ofFunq (q := q) (circleChainFun (X := X) p)) inputs)) := by
    funext p
    funext i
    simp [DDS.transcript, DDS.ofFunq, chainTranscriptToTagTranscript, circleFun, circleChainFun]
  have hmaps' :
      ((fun s : DDS X X q => s.transcript inputs) ∘
          (fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleFun (X := X) p)))
        =
      (chainTranscriptToTagTranscript (X := X) (q := q) ∘
          (fun s : DDS X (X × X) q => s.transcript inputs) ∘
          (fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))) := by
    funext p
    -- Expand both compositions and use `hmaps` pointwise.
    simpa [Function.comp] using congrArg (fun f => f p) hmaps
  -- Unfold both transcript distributions and regroup using functoriality.
  simp [PDS.transcriptDist, URFfunCircle, URFfunCircleChain, Dist.fTransform_comp, hmaps']

/-! ### Bad event (condition): collision among intermediate values `u_i` -/

def noIntermediateCollision : TranscriptCondition X (X × X) q where
  holds := fun t => Function.Injective (fun i => ((t i).2).1)
  dec := inferInstance

/-! ### Generic helper: `fTransform` apply as a fiber sum

This is now available as `Dist.fTransform_apply_eq_sum` in `RandomSystems.Dist`. -/

/-! ### Pointwise condition-based bound (specialized to a fixed input sequence) -/

private theorem statDist_le_conditionFailure_single_for_inputs
    {X Y : Type*} {q : ℕ}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]
    (S T : PDS X Y q) (A : TranscriptCondition X Y q) (inputs : Fin q → X)
    (h_cond : ∀ t : Transcript X Y q, A.holds t → S.transcriptDist inputs t = T.transcriptDist inputs t) :
    statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤
    conditionFailureProb S A inputs := by
  -- Same proof as `RandomSystems.statDist_le_conditionFailure_single`, but only for this `inputs`.
  simp only [statDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => A.holds t)]
  have h_zero :
      ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => A.holds t),
          (S.transcriptDist inputs t - T.transcriptDist inputs t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h_cond t ht, tsub_self]
  rw [h_zero, zero_add]
  calc
    ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
        (S.transcriptDist inputs t - T.transcriptDist inputs t)
        ≤ ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (fun t => ¬A.holds t),
            S.transcriptDist inputs t := by
              apply Finset.sum_le_sum
              intro t _
              exact tsub_le_self
    _ ≤ conditionFailureProb S A inputs := by
          rw [← conditionFailureProb_eq_transcriptDist_filter]

/-! ### Output-vector factoring for chain transcripts -/

private def outputVec (inputs : Fin q → X) (s : DDS X (X × X) q) : Fin q → X × X :=
  fun i => (DDS.transcript s inputs i).2

private def transcriptEmbed (inputs : Fin q → X) (ys : Fin q → X × X) : Transcript X (X × X) q :=
  fun i => (inputs i, ys i)

omit [Fintype X] [DecidableEq X] [Nonempty X] in
private theorem transcript_factors (inputs : Fin q → X) :
    (fun s : DDS X (X × X) q => DDS.transcript s inputs) =
      transcriptEmbed (X := X) (q := q) inputs ∘ outputVec (X := X) (q := q) inputs := by
  funext s
  funext i
  simp [DDS.transcript, outputVec, transcriptEmbed]

omit [Fintype X] [DecidableEq X] [Nonempty X] in
private theorem transcriptEmbed_injective (inputs : Fin q → X) :
    Function.Injective (transcriptEmbed (X := X) (q := q) inputs) := by
  intro ys₁ ys₂ h
  funext i
  have := congrArg Prod.snd (congrArg (fun t => t i) h)
  simp [transcriptEmbed] at this
  exact this

-- Use the generic fiber-sum lemma `PDS.transcriptDist_apply_eq_sum` from `RandomSystems.PDS`.

omit [Nonempty X] in
private theorem transcriptDist_eq_zero_of_input_mismatch (S : PDS X (X × X) q) (inputs : Fin q → X)
    (t : Transcript X (X × X) q) (i : Fin q) (h : (t i).1 ≠ inputs i) :
    S.transcriptDist inputs t = 0 := by
  classical
  rw [PDS.transcriptDist_apply_eq_sum (S := S) (inputs := inputs) (t := t)]
  -- The fiber is empty: every transcript at `inputs` has input component `inputs i` at index `i`.
  have : (Finset.univ : Finset (DDS X (X × X) q)).filter (fun s => DDS.transcript s inputs = t) = ∅ := by
    ext s
    constructor
    · intro hs
      have hs' : DDS.transcript s inputs = t := (Finset.mem_filter.mp hs).2
      have := congrArg (fun tr => (tr i).1) hs'
      -- But `(DDS.transcript s inputs i).1 = inputs i` by definition.
      have ht : inputs i = (t i).1 := by
        simpa [DDS.transcript] using this
      exact (h ht.symm).elim
    · intro hs
      simp at hs
  simp [this]

/-! ### Collision bound for uniform output vectors -/

omit [Nonempty X] in
private theorem uniform_vec_pair_collision_le (i j : Fin q) (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin q → X)).filter (fun u => u i = u j)).card *
        (Fintype.card X) ≤
      Fintype.card (Fin q → X) := by
  classical
  set C : Finset (Fin q → X) := (Finset.univ : Finset (Fin q → X)).filter (fun u => u i = u j)
  -- Injection `C × X ↪ (Fin q → X)` by updating coordinate `i`.
  let φ : (Fin q → X) × X → (Fin q → X) := fun p => Function.update p.1 i p.2
  have h_maps : ∀ p ∈ C ×ˢ (Finset.univ : Finset X), φ p ∈ (Finset.univ : Finset (Fin q → X)) := by
    intro _ _; exact Finset.mem_univ _
  have h_inj : Set.InjOn φ ↑(C ×ˢ (Finset.univ : Finset X)) := by
    intro ⟨u₁, x₁⟩ hp₁ ⟨u₂, x₂⟩ hp₂ hφ
    have hx : x₁ = x₂ := by
      have := congrArg (fun f => f i) hφ
      simpa [φ] using this
    have hu : u₁ = u₂ := by
      -- For coordinates `k ≠ i`, `update` does nothing.
      have h_other : ∀ k : Fin q, k ≠ i → u₁ k = u₂ k := by
        intro k hk
        have := congrArg (fun f => f k) hφ
        simpa [φ, Function.update_of_ne hk] using this
      -- At coordinate `i`, recover values from the collision property at `j`.
      have hji : j ≠ i := Ne.symm hij
      have hu₁ij : u₁ i = u₁ j := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).1).2
      have hu₂ij : u₂ i = u₂ j := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).1).2
      have hj : u₁ j = u₂ j := h_other j hji
      have hi : u₁ i = u₂ i := hu₁ij.trans (hj.trans hu₂ij.symm)
      funext k
      by_cases hk : k = i
      · subst hk; exact hi
      · exact h_other k hk
    exact Prod.ext hu hx
  have h_card_le := Finset.card_le_card_of_injOn φ h_maps h_inj
  -- Unpack the product cardinality.
  have : C.card * Fintype.card X ≤ Fintype.card (Fin q → X) := by
    simpa [Finset.card_product, Finset.card_univ, C] using h_card_le
  simpa [C] using this

private theorem uniform_vec_collision_prob_le_birthday :
    (∑ u ∈ (Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u),
        (Dist.uniform (Fin q → X)) u) ≤
      birthdayBound q (Fintype.card X) := by
  classical
  -- Under uniform: bad mass = |bad| / |all|.
  simp only [Dist.uniform]
  have h_sum_eq :
      (∑ u ∈ (Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u),
          (Finsupp.equivFunOnFinite.invFun
            (fun _ : Fin q → X => (1 : NNReal) / ↑(Fintype.card (Fin q → X)))) u)
        =
      ((Finset.univ.filter (fun u : Fin q → X => ¬Function.Injective u)).card : NNReal) /
        (Fintype.card (Fin q → X) : NNReal) := by
    simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [h_sum_eq]
  -- Union bound: non-injective implies a collision between some i<j.
  set pairs := (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)
  set collision := fun (p : Fin q × Fin q) =>
    (Finset.univ : Finset (Fin q → X)).filter (fun u => u p.1 = u p.2)
  have h_nat_ub :
      ((Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u)).card ≤
        ∑ p ∈ pairs, (collision p).card := by
    have h_subset :
        (Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u) ⊆
          pairs.biUnion collision := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [Function.Injective] at hu
      push_neg at hu
      obtain ⟨a, b, hab, hne⟩ := hu
      rw [Finset.mem_biUnion]
      by_cases h : a < b
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
      · have hba : b < a := lt_of_le_of_ne (Fin.not_lt.mp h) (Ne.symm hne)
        exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩⟩
    calc ((Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u)).card
        ≤ (pairs.biUnion collision).card := Finset.card_le_card h_subset
      _ ≤ ∑ p ∈ pairs, (collision p).card := Finset.card_biUnion_le
  -- Move from Nat inequality to an NNReal inequality with common denominator.
  have h_union_bound :
      ((Finset.univ.filter (fun u : Fin q → X => ¬Function.Injective u)).card : NNReal) /
          (Fintype.card (Fin q → X) : NNReal)
        ≤
      ∑ p ∈ pairs, ((collision p).card : NNReal) / (Fintype.card (Fin q → X) : NNReal) := by
    calc
      ((Finset.univ.filter (fun u : Fin q → X => ¬Function.Injective u)).card : NNReal) /
          (Fintype.card (Fin q → X) : NNReal)
        ≤
      (∑ p ∈ pairs, ((collision p).card : NNReal)) / (Fintype.card (Fin q → X) : NNReal) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast h_nat_ub
      _ = _ := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
  -- Each pair collision probability ≤ 1/|X|.
  have h_each_pair :
      ∀ p ∈ pairs, ((collision p).card : NNReal) / (Fintype.card (Fin q → X) : NNReal) ≤
        (1 : NNReal) / (Fintype.card X : NNReal) := by
    intro p hp
    rcases p with ⟨i, j⟩
    have hij : i ≠ j := by
      have : i < j := (Finset.mem_filter.mp hp).2
      exact Fin.ne_of_lt this
    have h_nat := uniform_vec_pair_collision_le (X := X) (q := q) i j hij
    have h_all_pos : (0 : NNReal) < (Fintype.card (Fin q → X) : NNReal) :=
      Nat.cast_pos.mpr (Fintype.card_pos (α := Fin q → X))
    have h_X_pos : (0 : NNReal) < (Fintype.card X : NNReal) :=
      Nat.cast_pos.mpr (Fintype.card_pos (α := X))
    -- Rewrite and convert.
    rw [div_le_div_iff₀ h_all_pos h_X_pos]
    simp only [one_mul]
    -- `collision (i,j)` is exactly the finset in `uniform_vec_pair_collision_le`.
    have h_nat' : (collision (i, j)).card * Fintype.card X ≤ Fintype.card (Fin q → X) := by
      -- `Fintype.card (Fin q → X) = |X|^q`.
      simpa [collision, Fintype.card_fun, Fintype.card_fin] using h_nat
    exact_mod_cast h_nat'
  -- Sum of C(q,2) copies of 1/|X| equals birthdayBound.
  have h_sum_pairs :
      ∑ p ∈ pairs, (1 : NNReal) / (Fintype.card X : NNReal) =
        birthdayBound q (Fintype.card X) := by
    rw [Finset.sum_const, nsmul_eq_mul, birthdayBound]
    have h_card := card_strictLTPairs (q := q)
    rw [mul_one_div]
    rw [show (q * (q - 1) : ℕ) = pairs.card * 2 from h_card.symm]
    push_cast
    ring
  -- Combine.
  exact le_trans h_union_bound (le_trans (Finset.sum_le_sum h_each_pair) (le_of_eq h_sum_pairs))

/-!
## Intended theorem (to be proved)

For injective input sequences, `u_i = f(x_i)` is a vector of *uniform* samples;
collisions happen with probability at most `birthdayBound q |X|`. Conditioned on
no collision in `u`, the chain transcript is uniform over `X×X` outputs and hence
the tag transcript matches `URFfun`.

We express the final statement as a restricted advantage bound over injective inputs.
!-/

-- TODO: fill in (requires a shared, non-private `eval_nonces_uniform` lemma and
-- a clean collision bound for uniform vectors, or a reuse of `urf_collision_bound_general`
-- via an output-uniformity bridge).
theorem urfFunCircle_advantageOn_injective_le_birthday :
    advantageOn (URFfunCircle (X := X) (q := q)) (Instances.URFfun (X := X) (Y := X) (q := q))
      (fun inputs => Function.Injective inputs) ≤
    birthdayBound q (Fintype.card X) := by
  classical
  -- We bound statDist pointwise on injective input sequences, then take the sup.
  refine advantageOn_le_of_pointwise
    (S := URFfunCircle (X := X) (q := q))
    (T := Instances.URFfun (X := X) (Y := X) (q := q))
    (Good := fun inputs => Function.Injective inputs)
    (ε := birthdayBound q (Fintype.card X)) ?_
  intro inputs h_inputs_inj

  -- Abbreviations: chain system and ideal "pair-valued URFfun".
  let SChain : PDS X (X × X) q := URFfunCircleChain (X := X) (q := q)
  let TChain : PDS X (X × X) q := Instances.URFfun (X := X) (Y := (X × X)) (q := q)

  -- Step 1: Rewrite both tag transcript distributions as projections of chain transcript distributions.
  have h_tag_circle :
      (URFfunCircle (X := X) (q := q)).transcriptDist inputs =
        Dist.fTransform (chainTranscriptToTagTranscript (X := X) (q := q)) (SChain.transcriptDist inputs) := by
    simpa [SChain] using
      (URFfunCircle_transcriptDist_eq_fTransform_chainTranscriptDist (X := X) (q := q) inputs)

  -- For the ideal system: projecting a uniform `(X→X×X)` oracle to its second component
  -- yields a uniform `(X→X)` oracle.
  have h_funproj_uniform :
      Dist.fTransform (fun h : X → X × X => fun x => (h x).2) (Dist.uniform (X → X × X))
        = Dist.uniform (X → X) := by
    -- Use the explicit equivalence `(X→X×X) ≃ (X→X)×(X→X)` and `Dist.fTransform_snd_uniform`.
    let e : (X → X × X) ≃ (X → X) × (X → X) :=
      { toFun := fun h => (fun x => (h x).1, fun x => (h x).2)
        invFun := fun p => fun x => (p.1 x, p.2 x)
        left_inv := by intro h; ext x <;> rfl
        right_inv := by intro p; ext x <;> rfl }
    have hproj : (fun h : X → X × X => fun x => (h x).2) = Prod.snd ∘ e := by
      rfl
    calc
      Dist.fTransform (fun h : X → X × X => fun x => (h x).2) (Dist.uniform (X → X × X))
          = Dist.fTransform Prod.snd (Dist.fTransform e (Dist.uniform (X → X × X))) := by
              simp [hproj, Dist.fTransform_comp]
      _ = Dist.fTransform Prod.snd (Dist.uniform ((X → X) × (X → X))) := by
              rw [Dist.fTransform_equiv_uniform e]
      _ = Dist.uniform (X → X) := by
              simpa using (Dist.fTransform_snd_uniform (A' := (X → X)) (B' := (X → X)))

  have h_tag_ideal :
      (Instances.URFfun (X := X) (Y := X) (q := q)).transcriptDist inputs =
        Dist.fTransform (chainTranscriptToTagTranscript (X := X) (q := q)) (TChain.transcriptDist inputs) := by
    classical
    -- Same idea as for `URFfunCircle`, but we explicitly rewrite the uniform `(X → X)` oracle
    -- as the projection of a uniform `(X → X × X)` oracle.
    ext t
    -- Put both sides in "single pushforward from a uniform function space" form.
    let A : (X → X) → Transcript X X q :=
      fun f => DDS.transcript (DDS.ofFunq (q := q) f) inputs
    let proj₂ : (X → X × X) → (X → X) :=
      fun h => fun x => (h x).2
    let B : (X → X × X) → Transcript X X q :=
      fun h =>
        chainTranscriptToTagTranscript (X := X) (q := q)
          (DDS.transcript (DDS.ofFunq (q := q) h) inputs)

    have hL :
        (Instances.URFfun (X := X) (Y := X) (q := q)).transcriptDist inputs =
          Dist.fTransform A (Dist.uniform (X → X)) := by
      -- `transcriptDist` is the pushforward of `URFfun.dist` by `DDS.transcript`.
      -- Then use pushforward functoriality to collapse the two `fTransform`s.
      unfold PDS.transcriptDist Instances.URFfun
      simpa [A, Function.comp] using
        (Dist.fTransform_comp
          (g := fun s : DDS X X q => DDS.transcript s inputs)
          (f := fun f : X → X => DDS.ofFunq (q := q) f)
          (X := Dist.uniform (X → X)))

    have hR :
        Dist.fTransform (chainTranscriptToTagTranscript (X := X) (q := q)) (TChain.transcriptDist inputs) =
          Dist.fTransform B (Dist.uniform (X → X × X)) := by
      unfold PDS.transcriptDist TChain Instances.URFfun
      -- First collapse `transcriptDist`, then collapse the outer projection by functoriality.
      have h_inner :
          Dist.fTransform (fun s : DDS X (X × X) q => DDS.transcript s inputs)
              (Dist.fTransform (fun f : X → X × X => DDS.ofFunq (q := q) f) (Dist.uniform (X → X × X)))
            =
          Dist.fTransform
              ((fun s : DDS X (X × X) q => DDS.transcript s inputs) ∘ fun f : X → X × X => DDS.ofFunq (q := q) f)
              (Dist.uniform (X → X × X)) :=
        Dist.fTransform_comp
          (g := fun s : DDS X (X × X) q => DDS.transcript s inputs)
          (f := fun f : X → X × X => DDS.ofFunq (q := q) f)
          (X := Dist.uniform (X → X × X))
      -- Now apply `chainTranscriptToTagTranscript` to that collapsed pushforward.
      -- (This is just another use of `fTransform_comp`.)
      simpa [B, Function.comp, h_inner, Instances.URFfunOf] using
        (Dist.fTransform_comp
          (g := chainTranscriptToTagTranscript (X := X) (q := q))
          (f := ((fun s : DDS X (X × X) q => DDS.transcript s inputs) ∘ fun f : X → X × X => DDS.ofFunq (q := q) f))
          (X := Dist.uniform (X → X × X)))

    -- Replace `uniform (X → X)` by the pushforward of `uniform (X → X × X)` through `proj₂`.
    rw [hL, hR, ← h_funproj_uniform]
    -- Compose pushforwards and identify the two maps.
    rw [Dist.fTransform_comp (g := A) (f := proj₂) (X := Dist.uniform (X → X × X))]
    have hmaps : A ∘ proj₂ = B := by
      funext h
      ext i <;> simp [A, B, proj₂, chainTranscriptToTagTranscript, DDS.transcript, DDS.ofFunq]
    simp [hmaps]

  have h_data :
      statDist ((URFfunCircle (X := X) (q := q)).transcriptDist inputs)
          ((Instances.URFfun (X := X) (Y := X) (q := q)).transcriptDist inputs)
        ≤ statDist (SChain.transcriptDist inputs) (TChain.transcriptDist inputs) := by
    -- Data processing: statDist cannot increase under `fTransform`.
    simpa [h_tag_circle, h_tag_ideal] using
      (statDist_fTransform_le (SChain.transcriptDist inputs) (TChain.transcriptDist inputs)
        (chainTranscriptToTagTranscript (X := X) (q := q)))

  -- Step 2: On good transcripts (no intermediate collision), the chain systems match exactly.
  have h_chain_eq_on_good :
      ∀ t : Transcript X (X × X) q,
        noIntermediateCollision (X := X) (q := q).holds t →
          SChain.transcriptDist inputs t = TChain.transcriptDist inputs t := by
    intro t ht_good
    by_cases h_inputs : ∀ i : Fin q, (t i).1 = inputs i
    · -- Reduce both transcript masses to the corresponding output-vector masses.
      let ys : Fin q → X × X := fun i => (t i).2
      have ht_embed : t = transcriptEmbed (X := X) (q := q) inputs ys := by
        funext i
        exact Prod.ext (h_inputs i) rfl
      have ht_u_inj : Function.Injective (fun i => (ys i).1) := by
        -- `noIntermediateCollision` says `i ↦ ((t i).2).1` is injective.
        simpa [ys, noIntermediateCollision] using ht_good

      -- Output distributions: `Dist.fTransform (outputVec inputs)` of the PDS dist.
      have h_chain_mass :
          SChain.transcriptDist inputs t =
            (Dist.fTransform (outputVec (X := X) (q := q) inputs) SChain.dist) ys := by
        -- Factor transcript map as `transcriptEmbed ∘ outputVec`, then apply injectivity.
        simp only [PDS.transcriptDist, SChain]
        rw [show (fun s : DDS X (X × X) q => DDS.transcript s inputs) =
            transcriptEmbed (X := X) (q := q) inputs ∘ outputVec (X := X) (q := q) inputs from
            transcript_factors (X := X) (q := q) inputs]
        rw [← Dist.fTransform_comp]
        rw [ht_embed]
        simpa using
          (fTransform_injective_apply
            (X := Dist.fTransform (outputVec (X := X) (q := q) inputs) SChain.dist)
            (f := transcriptEmbed (X := X) (q := q) inputs)
            (hf := transcriptEmbed_injective (X := X) (q := q) inputs)
            ys)

      have h_ideal_mass :
          TChain.transcriptDist inputs t =
            (Dist.fTransform (outputVec (X := X) (q := q) inputs) TChain.dist) ys := by
        simp only [PDS.transcriptDist, TChain]
        rw [show (fun s : DDS X (X × X) q => DDS.transcript s inputs) =
            transcriptEmbed (X := X) (q := q) inputs ∘ outputVec (X := X) (q := q) inputs from
            transcript_factors (X := X) (q := q) inputs]
        rw [← Dist.fTransform_comp]
        rw [ht_embed]
        simpa using
          (fTransform_injective_apply
            (X := Dist.fTransform (outputVec (X := X) (q := q) inputs) TChain.dist)
            (f := transcriptEmbed (X := X) (q := q) inputs)
            (hf := transcriptEmbed_injective (X := X) (q := q) inputs)
            ys)

      -- Compute both output masses: ideal is uniform on vectors, chain is uniform on good `ys`.
      have h_ideal_out :
          (Dist.fTransform (outputVec (X := X) (q := q) inputs) TChain.dist) ys =
            (Dist.uniform (Fin q → X × X)) ys := by
        -- Reduce to evaluation of a uniform random function at injective inputs.
        -- `outputVec inputs (DDS.ofFunq h)` is `i ↦ h (inputs i)`.
        have : Dist.fTransform (outputVec (X := X) (q := q) inputs) TChain.dist =
            Dist.fTransform (fun h : X → X × X => fun i => h (inputs i)) (Dist.uniform (X → X × X)) := by
          -- Collapse the nested pushforward and identify the resulting map.
          classical
          -- `TChain.dist` is `fTransform (DDS.ofFunq) (uniform (X → X×X))`.
          simp [TChain, Instances.URFfun, Instances.URFfunOf, Dist.fTransform_comp]
          -- Show `outputVec inputs (DDS.ofFunq h) = (i ↦ h (inputs i))`.
          have hmap :
              (outputVec (X := X) (q := q) inputs ∘ fun h : X → X × X => DDS.ofFunq (q := q) h)
                =
              (fun h : X → X × X => fun i => h (inputs i)) := by
            funext h
            funext i
            simp [outputVec, DDS.transcript, DDS.ofFunq]
          simp [hmap]
        -- Now apply the shared uniformity lemma.
        have h_eval :=
          congrArg (fun D => D ys) (RandomSystems.Instances.eval_nonces_uniform
            (X := X) (Y := (X × X)) (n := q) inputs h_inputs_inj)
        simpa [this] using h_eval

      have h_chain_out :
          (Dist.fTransform (outputVec (X := X) (q := q) inputs) SChain.dist) ys =
            (Dist.uniform (Fin q → X × X)) ys := by
        -- Count fibers under the uniform distribution on `(f,g)`.
        -- If `u` is injective, the number of `(f,g)` producing `ys=(u,v)` is
        -- `|X|^(|X|-q) * |X|^(|X|-q)`, hence probability `1/|X|^(2q)`.
        let u : Fin q → X := fun i => (ys i).1
        let v : Fin q → X := fun i => (ys i).2
        have hu_inj : Function.Injective u := ht_u_inj

        -- Express the output distribution as a pushforward from the uniform pair distribution.
        have h_out_as_push :
            Dist.fTransform (outputVec (X := X) (q := q) inputs) SChain.dist =
              Dist.fTransform
                (fun p : (X → X) × (X → X) => fun i => circleChainFun (X := X) p (inputs i))
                (Dist.uniform ((X → X) × (X → X))) := by
          classical
          -- Collapse the nested pushforward and identify the resulting map.
          simp [SChain, URFfunCircleChain, Dist.prod_uniform, Dist.fTransform_comp]
          have hmap :
              (outputVec (X := X) (q := q) inputs ∘
                  fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))
                =
              (fun p : (X → X) × (X → X) => fun i => circleChainFun (X := X) p (inputs i)) := by
            funext p
            funext i
            simp [outputVec, DDS.transcript, DDS.ofFunq, circleChainFun]
          simp [hmap]

        -- Compute the fiber cardinality.
        have h_fiber :
            ((Finset.univ : Finset ((X → X) × (X → X))).filter
              (fun p => (fun i => circleChainFun (X := X) p (inputs i)) = ys)).card
              =
            ((Finset.univ : Finset (X → X)).filter (fun f => (fun i => f (inputs i)) = u)).card *
            ((Finset.univ : Finset (X → X)).filter (fun g => (fun i => g (u i)) = v)).card := by
          classical
          -- Constraints separate: `f(inputs)=u` and `g(u)=v`.
          have :
              (Finset.univ : Finset ((X → X) × (X → X))).filter
                  (fun p => (fun i => circleChainFun (X := X) p (inputs i)) = ys)
                =
              ((Finset.univ : Finset (X → X)).filter (fun f => (fun i => f (inputs i)) = u)) ×ˢ
                ((Finset.univ : Finset (X → X)).filter (fun g => (fun i => g (u i)) = v)) := by
            ext p
            rcases p with ⟨f, g⟩
            constructor
            · intro hp
              -- `hp` is membership in the LHS filter, so it contains the defining equality.
              have hp' : (fun i => circleChainFun (X := X) (f, g) (inputs i)) = ys := by
                simpa [Finset.mem_filter] using (Finset.mem_filter.mp hp).2
              have hf : (fun i => f (inputs i)) = u := by
                funext i
                have hi := congrArg (fun h => h i) hp'
                have hi_fst := congrArg Prod.fst hi
                simpa [circleChainFun, u] using hi_fst
              have hg : (fun i => g (u i)) = v := by
                funext i
                have hi := congrArg (fun h => h i) hp'
                have hi_snd := congrArg Prod.snd hi
                have hi_fst := congrArg Prod.fst hi
                have : u i = f (inputs i) := by
                  simpa [circleChainFun, u] using hi_fst.symm
                simpa [circleChainFun, v, this] using hi_snd
              -- Now package as membership in the product.
              refine Finset.mem_product.2 ?_
              exact ⟨by simp [Finset.mem_filter, hf], by simp [Finset.mem_filter, hg]⟩
            · intro hp
              -- Unpack membership in the product into the two constraints.
              rcases (Finset.mem_product.mp hp) with ⟨hf_mem, hg_mem⟩
              have hf : (fun i => f (inputs i)) = u := by
                simpa [Finset.mem_filter] using (Finset.mem_filter.mp hf_mem).2
              have hg : (fun i => g (u i)) = v := by
                simpa [Finset.mem_filter] using (Finset.mem_filter.mp hg_mem).2
              -- Rebuild membership in the LHS filter.
              refine Finset.mem_filter.2 ?_
              refine ⟨Finset.mem_univ _, ?_⟩
              funext i
              apply Prod.ext
              · exact congrArg (fun h => h i) hf
              ·
                have hfi : f (inputs i) = u i := congrArg (fun h => h i) hf
                have hgi : g (u i) = v i := congrArg (fun h => h i) hg
                simpa [circleChainFun, v, hfi] using hgi
          simp [this, Finset.card_product]

        have h_fiber_f :
            ((Finset.univ : Finset (X → X)).filter (fun f => (fun i => f (inputs i)) = u)).card =
              Fintype.card X ^ (Fintype.card X - q) := by
          simpa [u] using
            (RandomSystems.Instances.card_fiber_multipoint (X := X) (Y := X) (n := q) inputs u h_inputs_inj)

        have h_fiber_g :
            ((Finset.univ : Finset (X → X)).filter (fun g => (fun i => g (u i)) = v)).card =
              Fintype.card X ^ (Fintype.card X - q) := by
          simpa [u, v] using
            (RandomSystems.Instances.card_fiber_multipoint (X := X) (Y := X) (n := q) u v hu_inj)

        -- Evaluate both sides at `ys` using the fiber form of `fTransform` on uniform.
        -- `uniform` mass is constant, so value is `card(fiber) / card(total)`.
        have h_uniform_pair :
            Dist.fTransform
                (fun p : (X → X) × (X → X) => fun i => circleChainFun (X := X) p (inputs i))
                (Dist.uniform ((X → X) × (X → X))) ys
              =
            ((Finset.univ.filter (fun p : (X → X) × (X → X) =>
                (fun i => circleChainFun (X := X) p (inputs i)) = ys)).card : NNReal) /
              (Fintype.card ((X → X) × (X → X)) : NNReal) := by
          classical
          -- Fiber-count form of a pushforward of the uniform distribution.
          -- `fTransform_apply_eq_sum` gives a sum over the fiber, and uniformity collapses it to
          -- `fiber.card * (1 / |total|)`.
          have h_sum :=
            Dist.fTransform_apply_eq_sum
              (A := (X → X) × (X → X)) (B := (Fin q → X × X))
              (f := fun p : (X → X) × (X → X) => fun i => circleChainFun (X := X) p (inputs i))
              (X := Dist.uniform ((X → X) × (X → X))) ys
          -- Rewrite the fiber sum as a constant-mass sum and simplify.
          rw [h_sum]
          simp [Dist.uniform, Finsupp.equivFunOnFinite, Finset.sum_const, nsmul_eq_mul,
            div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
        have h_uniform_vec :
            (Dist.uniform (Fin q → X × X)) ys =
              (1 : NNReal) / (Fintype.card (Fin q → X × X) : NNReal) := by
          simp [Dist.uniform, Finsupp.equivFunOnFinite]

        -- Convert the chain-side expression to the uniform vector mass by arithmetic on cards.
        -- This is the same computation as in `eval_nonces_uniform`.
        -- We keep it explicit to match the paper: `|fiber| / |total| = 1 / |X×X|^q`.
        have h_total_pair :
            Fintype.card ((X → X) × (X → X)) = (Fintype.card X ^ Fintype.card X) * (Fintype.card X ^ Fintype.card X) := by
          simp [Fintype.card_prod]

        -- Finish: use the computed fiber sizes.
        -- (We do the NNReal arithmetic with casts and `ring`.)
        -- First rewrite using `h_out_as_push`.
        have : (Dist.fTransform (outputVec (X := X) (q := q) inputs) SChain.dist) ys =
            Dist.fTransform
              (fun p : (X → X) × (X → X) => fun i => circleChainFun (X := X) p (inputs i))
              (Dist.uniform ((X → X) × (X → X))) ys := by
          simp [h_out_as_push]
        -- Now compute.
        rw [this, h_uniform_pair]
        -- Rewrite fiber card and simplify.
        -- Reduce to a pure cardinality arithmetic identity.
        simp [h_fiber, h_fiber_f, h_fiber_g, h_total_pair, Dist.uniform,
          Nat.cast_mul, Nat.cast_pow, Fintype.card_fin, Fintype.card_prod]
        -- Finish the remaining arithmetic.
        have hq_le : q ≤ Fintype.card X := by
          -- From injectivity of `inputs : Fin q → X`.
          have := Fintype.card_le_of_injective inputs h_inputs_inj
          simpa [Fintype.card_fin] using this
        set a : NNReal := (Fintype.card X : NNReal)
        set n : ℕ := Fintype.card X
        have ha0 : a ≠ 0 := by
          -- `|X| > 0`.
          dsimp [a]
          exact_mod_cast (Fintype.card_pos (α := X)).ne'
        have hn : n - q + q = n := Nat.sub_add_cancel hq_le
        have hdecomp : a ^ n = a ^ (n - q) * a ^ q := by
          calc
            a ^ n = a ^ ((n - q) + q) := by simp [hn]
            _ = a ^ (n - q) * a ^ q := by simp [pow_add]
        have hx0 : a ^ (n - q) ≠ 0 := pow_ne_zero _ ha0
        have hxx0 : a ^ (n - q) * a ^ (n - q) ≠ 0 := mul_ne_zero hx0 hx0
        calc
          a ^ (n - q) * a ^ (n - q) / (a ^ n * a ^ n)
              = a ^ (n - q) * a ^ (n - q) / ((a ^ (n - q) * a ^ q) * (a ^ (n - q) * a ^ q)) := by
                  simp [hdecomp]
          _ = a ^ (n - q) * a ^ (n - q) / ((a ^ (n - q) * a ^ (n - q)) * (a ^ q * a ^ q)) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (1 : NNReal) / (a ^ q * a ^ q) := by
                  -- Cancel the nonzero factor `a^(n-q) * a^(n-q)`.
                  simpa [mul_assoc] using
                    (mul_div_mul_left (a := (1 : NNReal)) (b := a ^ q * a ^ q) (c := a ^ (n - q) * a ^ (n - q)) hxx0)
          _ = ((a * a) ^ q)⁻¹ := by
                  simp [div_eq_mul_inv, mul_pow, mul_inv_rev, mul_comm]

      -- Combine.
      rw [h_chain_mass, h_ideal_mass, h_chain_out, h_ideal_out]
    · -- Input mismatch: both sides are 0.
      have hi : ∃ i : Fin q, (t i).1 ≠ inputs i := by
        classical
        -- pick any index where mismatch happens
        simpa using (not_forall.mp h_inputs)
      rcases hi with ⟨i, hi⟩
      have hS0 : SChain.transcriptDist inputs t = 0 :=
        transcriptDist_eq_zero_of_input_mismatch (X := X) (q := q) (S := SChain) inputs t i hi
      have hT0 : TChain.transcriptDist inputs t = 0 :=
        transcriptDist_eq_zero_of_input_mismatch (X := X) (q := q) (S := TChain) inputs t i hi
      simp [hS0, hT0]

  have h_chain_le_failure :
      statDist (SChain.transcriptDist inputs) (TChain.transcriptDist inputs) ≤
        conditionFailureProb SChain (noIntermediateCollision (X := X) (q := q)) inputs := by
    exact statDist_le_conditionFailure_single_for_inputs
      (S := SChain) (T := TChain) (A := noIntermediateCollision (X := X) (q := q))
      inputs h_chain_eq_on_good

  -- Step 3: Bound the failure probability by the birthday bound.
  have h_failure_le_birthday :
      conditionFailureProb SChain (noIntermediateCollision (X := X) (q := q)) inputs ≤
        birthdayBound q (Fintype.card X) := by
    -- Regroup failure mass by the intermediate vector `u`.
    let uVec : Transcript X (X × X) q → (Fin q → X) := fun t i => ((t i).2).1
    have h_failure_as_u :
        conditionFailureProb SChain (noIntermediateCollision (X := X) (q := q)) inputs =
          ∑ u ∈ (Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u),
              (Dist.fTransform uVec (SChain.transcriptDist inputs)) u := by
      -- Use `conditionFailureProb_eq_transcriptDist_filter` + `fTransform_filter_sum`.
      have :
          ∑ t ∈ (Finset.univ : Finset (Transcript X (X × X) q)).filter
                (fun t => ¬(noIntermediateCollision (X := X) (q := q)).holds t),
              (SChain.transcriptDist inputs) t
            =
          ∑ u ∈ (Finset.univ : Finset (Fin q → X)).filter (fun u => ¬Function.Injective u),
              (Dist.fTransform uVec (SChain.transcriptDist inputs)) u := by
        simpa [uVec, noIntermediateCollision, Function.comp] using
          (fTransform_filter_sum (f := uVec) (X := SChain.transcriptDist inputs)
            (P := fun u : Fin q → X => ¬Function.Injective u)).symm
      simpa [conditionFailureProb_eq_transcriptDist_filter] using this
    -- Show `u` is uniform under `SChain` (for injective inputs), then apply the collision bound.
    have h_uDist :
        Dist.fTransform uVec (SChain.transcriptDist inputs) = Dist.uniform (Fin q → X) := by
      -- `u` depends only on the first sampled function `f`; marginalize `g` away.
      have h_proj_f :
          Dist.fTransform (Prod.fst : (X → X) × (X → X) → (X → X))
              (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))
            = Dist.uniform (X → X) := by
        -- `prod uniform uniform` is uniform on the product, so `fst` marginal is uniform.
        simpa [Dist.prod_uniform] using
          (Dist.fTransform_fst_uniform (A' := (X → X)) (B' := (X → X)))

      -- Compute the `u` distribution as evaluation of a uniform random function at injective inputs.
      -- First rewrite `uVec ∘ transcript` as `p ↦ (i ↦ (p.1 (inputs i)))`.
      have h_u_as_pair :
          Dist.fTransform uVec (SChain.transcriptDist inputs) =
            Dist.fTransform (fun p : (X → X) × (X → X) => fun i => (p.1 (inputs i)))
              (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X))) := by
        classical
        -- Unfold and collapse the nested pushforwards explicitly.
        unfold PDS.transcriptDist SChain URFfunCircleChain
        -- First collapse `fTransform uVec (fTransform transcript ·)`.
        rw [Dist.fTransform_comp
          (g := uVec)
          (f := fun s : DDS X (X × X) q => DDS.transcript s inputs)
          (X := Dist.fTransform
            (fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))
            (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X))))]
        -- Then collapse the `DDS.ofFunq` pushforward.
        rw [Dist.fTransform_comp
          (g := uVec ∘ fun s : DDS X (X × X) q => DDS.transcript s inputs)
          (f := fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))
          (X := Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))]
        -- Identify the composite map with `p ↦ (i ↦ p.1(inputs i))`.
        have hmap :
            ((uVec ∘ fun s : DDS X (X × X) q => DDS.transcript s inputs) ∘
                fun p : (X → X) × (X → X) => DDS.ofFunq (q := q) (circleChainFun (X := X) p))
              =
            (fun p : (X → X) × (X → X) => fun i => p.1 (inputs i)) := by
          funext p
          funext i
          simp [uVec, circleChainFun, DDS.transcript, DDS.ofFunq, Function.comp]
        simp [hmap]

      -- Now push forward along `fst` and use `h_proj_f`.
      have h_u_as_f :
          Dist.fTransform uVec (SChain.transcriptDist inputs) =
            Dist.fTransform (fun f : X → X => fun i => f (inputs i)) (Dist.uniform (X → X)) := by
        calc
          Dist.fTransform uVec (SChain.transcriptDist inputs)
              = Dist.fTransform (fun f : X → X => fun i => f (inputs i))
                  (Dist.fTransform Prod.fst (Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))) := by
                  -- Functoriality: evaluate after projecting to `fst`.
                  rw [h_u_as_pair]
                  symm
                  exact Dist.fTransform_comp (g := fun f : X → X => fun i => f (inputs i)) (f := Prod.fst)
                    (X := Dist.prod (Dist.uniform (X → X)) (Dist.uniform (X → X)))
          _ = Dist.fTransform (fun f : X → X => fun i => f (inputs i)) (Dist.uniform (X → X)) := by
                  simp [h_proj_f]

      -- Finally apply uniformity of evaluation at injective inputs.
      simpa [h_u_as_f] using
        (RandomSystems.Instances.eval_nonces_uniform (X := X) (Y := X) (n := q) inputs h_inputs_inj)
    -- Apply the uniform-vector collision bound.
    rw [h_failure_as_u]
    simpa [h_uDist] using uniform_vec_collision_prob_le_birthday (X := X) (q := q)

  -- Final combination.
  calc
    statDist ((URFfunCircle (X := X) (q := q)).transcriptDist inputs)
        ((Instances.URFfun (X := X) (Y := X) (q := q)).transcriptDist inputs)
        ≤ statDist (SChain.transcriptDist inputs) (TChain.transcriptDist inputs) := h_data
    _ ≤ conditionFailureProb SChain (noIntermediateCollision (X := X) (q := q)) inputs := h_chain_le_failure
    _ ≤ birthdayBound q (Fintype.card X) := h_failure_le_birthday

end MauPie04CascadeFun

end RandomSystems.Applications
