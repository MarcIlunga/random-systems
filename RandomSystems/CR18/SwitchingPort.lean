/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.AdvMetric
import RandomSystems.Applications.PRPPRFSwitchingGeneral

-- PORTED from hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:3328-3966 (`GAP2_switching`)
-- + HCTR2/Proofs/Concrete/Switching.lean:144-181 (`factorial_ratio_eq_descFactorial_inv`,
--   `switching_ratio_le`) + h-technique HTechnique/CountingLemmas.lean:31-127
--   (Weierstrass / falling-factorial / birthday counting core, inline-ported because
--   random-systems does not depend on h-technique) — UPSTREAM-CANDIDATE landed 2026-06-11

/-!
# URP–URF switching (birthday bound) over an arbitrary finite alphabet

CR18 Lemma 4.19 / the classical PRF–PRP switching lemma, stated on the *CR18
stack*: objects are `RandomSystems.CR18.DDS`, the real library `RandomFunction.URF`
and `RandomPermutation.URP` (Definition 3.15), and distinguishers are admissible
CR18 `DDE` environments with a decision bit on the real `DDE.transcript`, fuel-capped
at `q` queries.  The main theorem is

  `AdvWith (ddeDS A A q Adm) id URF URP ≤ q² / (2·|A|)`

for ANY finite alphabet `A` and ANY admissibility predicate `Adm` on environments.

The proof is a fuel-induction transcript factorization: a `q`-fuel transcript against
a function evaluator is determined by (and determines) the table's values on the
realized inputs, giving the fiber counts `N^(N-r)` (functions) and `(N-r)!`
(permutations) per reachable transcript; the per-transcript one-sided H-coefficient
step then reduces to the falling-factorial birthday inequality.

## Dedupe (DONE at integration, 2026-06-11)

The draft carried local `DStruct`/`performance`/`AdvWith` mirrors (the
`Game`/`Indist` layer was in flux during drafting); at integration they were
DELETED.  This module now uses the library `Def47.DistinctionStructure`
(`RandomSystems/CR18/Game.lean`) and the SHARED advantage
`RandomSystems.CR18.AdvWith` (`RandomSystems/CR18/AdvMetric.lean`, connected
to the keystone Δ by `advWith_eq_keystone`).  Only the converter-free,
switching-specific structure remains local:

* `SwitchingPort.ddeDS` — the generic `q`-budgeted DDE distinction structure
  (objects `DDS X Y`, distinguishers = admissible `DDE` environments with a
  decision bit on the real `DDE.transcript`).

## Main results

* `falling_factorial_lower_bound` — `(N)_q ≥ N^q · (1 - q(q-1)/(2N))`
* `birthday_bound` — `1 - (N)_q/N^q ≤ q(q-1)/(2N)`
* `factorial_ratio_eq_descFactorial_inv` — `(N-q)!/N! = 1/(N)_q` in `NNReal`
* `switching_ratio_le` — `(1-ε)·((N-q)!/N!) ≤ 1/N^q` with the birthday `ε`
* `advWith_urf_urp_le_birthday` — the generic URP–URF switching bound
  (old name: `GAP2_switching`)
* `Lem419.urp_urf_switching` — CR18 Lemma 4.19, the REAL statement:
  `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ` for the actual Example 3.5 bitstring systems
  `Ex35.R n n` / `Ex35.P n` (no abstract δ, no bridge hypothesis)
-/

noncomputable section

open scoped BigOperators NNReal Classical

namespace RandomSystems.CR18.SwitchingPort

/-! ## Counting core

Inline port of `HTechnique.CountingLemmas` (h-technique repo,
HTechnique/CountingLemmas.lean:31-127); random-systems does not depend on
h-technique, so the four pure-real lemmas are reproduced here verbatim.
Reference: Jha–Nandi §8.1 (Proposition 8.1). -/

/-- **Weierstrass product inequality**: `∏ᵢ (1 - aᵢ) ≥ 1 - ∑ᵢ aᵢ`
    when all `aᵢ ∈ [0, 1]`.
    (PORTED from HTechnique.CountingLemmas.prod_one_sub_ge_one_sub_sum.) -/
theorem prod_one_sub_ge_one_sub_sum {n : ℕ} (a : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ a i) (h_le_one : ∀ i, a i ≤ 1) :
    ∏ i, (1 - a i) ≥ 1 - ∑ i, a i := by
  -- Induct on the number of factors. The induction step is the elementary
  -- inequality `(1 - S)(1 - x) ≥ 1 - S - x`, using `S*x ≥ 0`.
  induction n with
  | zero => simp
  | succ m ih =>
    -- Split the last factor and last summand off the product/sum over `Fin`.
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    set b := fun i : Fin m => a (Fin.castSucc i)
    have h_ih := ih b (fun i => h_nonneg _) (fun i => h_le_one _)
    -- The product inequality loses exactly the nonnegative cross term
    -- `(∑ b i) * a_last`.
    have h_sum_nonneg : 0 ≤ ∑ i : Fin m, b i :=
      Finset.sum_nonneg (fun i _ => h_nonneg _)
    nlinarith [h_nonneg (Fin.last m), h_le_one (Fin.last m),
               mul_nonneg h_sum_nonneg (h_nonneg (Fin.last m))]

/-- If `0 ≤ f(k) ≤ 1` for all `k < q`, then
    `∏_{k<q} (1 - f(k)) ≥ 1 - ∑_{k<q} f(k)`.
    (PORTED from HTechnique.CountingLemmas.chain_product_lower_bound.) -/
theorem chain_product_lower_bound {q : ℕ} (f : ℕ → ℝ)
    (h_nonneg : ∀ k < q, 0 ≤ f k) (h_le_one : ∀ k < q, f k ≤ 1) :
    ∏ k ∈ Finset.range q, (1 - f k) ≥ 1 - ∑ k ∈ Finset.range q, f k := by
  -- Convert the range-indexed statement to the `Fin q` version of the
  -- Weierstrass inequality.
  rw [← Fin.prod_univ_eq_prod_range, ← Fin.sum_univ_eq_sum_range]
  exact prod_one_sub_ge_one_sub_sum _
    (fun i => h_nonneg i.val (i.isLt))
    (fun i => h_le_one i.val (i.isLt))

private lemma sum_div_range (N q : ℕ) (h_N_pos : (0 : ℝ) < N) :
    ∑ k ∈ Finset.range q, ((k : ℝ) / N) = (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  -- Closed form for `(0 + ... + (q-1)) / N`.
  induction q with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring

/-- **Falling factorial lower bound**: `(N)_q ≥ N^q · (1 - q(q-1)/(2N))`.
    (PORTED from HTechnique.CountingLemmas.falling_factorial_lower_bound;
    this is the birthday core of the switching bound.) -/
theorem falling_factorial_lower_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    (∏ k ∈ Finset.range q, ((N : ℝ) - k)) ≥
      (N : ℝ) ^ q * (1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N)) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  -- Factor each term as `N * (1 - k/N)`, leaving `N^q` times a product of
  -- small losses.
  have h_factor : ∏ k ∈ Finset.range q, ((N : ℝ) - k) =
      (N : ℝ) ^ q * ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) := by
    conv_lhs => arg 2; ext k; rw [show (N : ℝ) - (k : ℝ) = (N : ℝ) * (1 - (k : ℝ) / N) from by field_simp]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h_factor]
  -- Apply Weierstrass to the losses `k/N`. The assumption `q ≤ N` ensures
  -- every loss is in `[0, 1]`.
  have h_chain := chain_product_lower_bound (fun k => (k : ℝ) / N)
    (fun k _ => div_nonneg (Nat.cast_nonneg k) (le_of_lt h_N_pos))
    (fun k hk => by
      rw [div_le_one h_N_pos]; exact_mod_cast (Nat.lt_of_lt_of_le hk h_le).le)
  -- Replace the sum of losses by its closed form.
  rw [sum_div_range N q h_N_pos] at h_chain
  exact mul_le_mul_of_nonneg_left (GE.ge.le h_chain) (pow_nonneg (le_of_lt h_N_pos) q)

/-- **Birthday bound**: `1 - (N)_q / N^q ≤ q(q-1)/(2N)`.
    (PORTED from HTechnique.CountingLemmas.birthday_bound.) -/
theorem birthday_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have h_Nq_pos : (0 : ℝ) < (N : ℝ) ^ q := pow_pos h_N_pos q
  have h_ffact := falling_factorial_lower_bound h_le h_pos
  -- Divide the falling-factorial lower bound by `N^q`.
  have h_div : (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≥
      1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
    rw [ge_iff_le, le_div_iff₀ h_Nq_pos]
    linarith
  -- Rearranging gives the usual birthday-collision upper bound.
  linarith

/-! ## The switching numeric ratio (`NNReal`)

Ported from hctr2-verification HCTR2/Proofs/Concrete/Switching.lean:144-181.
These are the alphabet-free numeric supports of the per-transcript H-coefficient
comparison: the ideal-permutation transcript mass is the inverse falling factorial
`(N-q)!/N! = 1/(N)_q`, and `(1-ε)` of it is dominated by the random-function mass
`1/N^q` with the birthday `ε`. -/

/-- The ideal/real mass ratio as a falling factorial: `(N-q)!/N! = (N)_q⁻¹`.
    (PORTED from HCTR2.Proofs.Concrete.factorial_ratio_eq_descFactorial_inv.) -/
theorem factorial_ratio_eq_descFactorial_inv {N q : ℕ} (h_le : q ≤ N) :
    ((N - q).factorial : NNReal) / (N.factorial : NNReal)
      = ((N.descFactorial q : NNReal))⁻¹ := by
  have hN : (N.factorial : NNReal)
      = ((N - q).factorial : NNReal) * (N.descFactorial q : NNReal) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial h_le]
  rw [hN, div_mul_eq_div_div, div_self (by exact_mod_cast (N - q).factorial_pos.ne'), one_div]

/-- **The switching numeric ratio.** `(1-ε)·((N-q)!/N!) ≤ 1/N^q` with the
birthday `ε`, the heart of the PRP-RND switching bound.  The real-number core is
`falling_factorial_lower_bound`.
(PORTED from HCTR2.Proofs.Concrete.switching_ratio_le.) -/
theorem switching_ratio_le {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N)
    (h_eps : (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal) ≤ 1) :
    (1 - (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal))
        * (((N - q).factorial : NNReal) / (N.factorial : NNReal))
      ≤ 1 / (N : NNReal) ^ q := by
  rw [factorial_ratio_eq_descFactorial_inv h_le, ← one_div, mul_one_div,
    div_le_div_iff₀ (by exact_mod_cast Nat.descFactorial_pos.mpr h_le)
      (pow_pos (by exact_mod_cast h_pos) q), one_mul, ← NNReal.coe_le_coe]
  have hdesc : ((N.descFactorial q : NNReal) : ℝ) = ∏ k ∈ Finset.range q, ((N : ℝ) - k) := by
    rw [NNReal.coe_natCast, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun k hk => ?_)
    rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) h_le))]
  have heps : ((q * (q - 1) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)
      = (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; norm_num
    · rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_mul]
      push_cast
      ring
  rw [hdesc, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_sub h_eps,
    NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, heps]
  have hfall := falling_factorial_lower_bound h_le h_pos
  nlinarith [hfall]

/-! ## The budgeted DDE distinction structure

Stated directly against the library `Def47.DistinctionStructure`
(`RandomSystems/CR18/Game.lean`); the advantage is the shared
`RandomSystems.CR18.AdvWith` (`RandomSystems/CR18/AdvMetric.lean`).
`ddeDS` mirrors hctr2-verification HCTR2/Proofs/CR18/Sketch.lean:252-283. -/

/-- THE generic budgeted distinction structure — full reuse of the CR18
distinguisher formalization: objects are `DDS X Y`, distinguishers are
(`Adm`-admissible real `CR18.DDE` environment, decision bit on the real
`DDE.transcript`), κ = decide(transcript), fuel = `q` (so at most `q` queries by
construction, and the never-querying environment witnesses nonemptiness for any
reasonable `Adm`).
(PORTED from hctr2-verification Sketch.lean `ddeDS`.) -/
def ddeDS (X Y : Type) (q : ℕ)
    (Adm : RandomSystems.CR18.DDE X Y → Prop) : Def47.DistinctionStructure where
  O := RandomSystems.CR18.DDS X Y
  D := {e : RandomSystems.CR18.DDE X Y // Adm e} ×
        (RandomSystems.CR18.DDE.TranscriptPrefix X Y → Bool)
  κ := fun d o => d.2 (RandomSystems.CR18.DDE.transcript o d.1.val q)

/-! ## The URP–URF switching theorem -/

/-- **URP–URF switching, generic alphabet** (CR18 Lemma 4.19, §1.5/§3.4 of the
HCTR2 random-systems proof): for the REAL library objects `RandomFunction.URF`
and `RandomPermutation.URP` and ANY `q`-budgeted `ddeDS` distinguisher class,

  `Δ(R_A, P_A) ≤ q² / (2·|A|)`.

The proof factorizes the fuel-`q` transcript against a function evaluator: the
transcript is determined by the table's values on the realized inputs (fiber
characterization), giving per-transcript fiber counts `N^(N-r)` for functions and
`(N-r)!` for permutations (`card_perm_fiber`); the per-transcript one-sided
H-coefficient step then reduces to `falling_factorial_lower_bound`, and convexity
over weight-1 probabilistic distinguishers finishes.
(PORTED from hctr2-verification Sketch.lean `GAP2_switching`; the library-level
`Lem419.urp_urf_switching` below instantiates this at `A := Fin (2 ^ n)`.) -/
theorem advWith_urf_urp_le_birthday (A : Type) [Fintype A] [DecidableEq A] [Nonempty A] (q : ℕ)
    (Adm : RandomSystems.CR18.DDE A A → Prop) :
    AdvWith (ddeDS A A q Adm)
        (id : PDS A A → RandomSystems.Dist (ddeDS A A q Adm).O)
        (RandomSystems.CR18.RandomFunction.URF (X := A) (Y := A))
        (RandomSystems.CR18.RandomPermutation.URP A)
      ≤ (q^2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hRHS0 : (0 : ℝ) ≤ (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by positivity
  -- ===== per-environment / per-decision deterministic core: statDist-style bound =====
  have hMain : ∀ (e : RandomSystems.CR18.DDE A A)
      (dec : RandomSystems.CR18.DDE.TranscriptPrefix A A → Bool),
      ((RandomPermutation.URP A).sum fun o ow =>
          (ow : ℝ) * if dec (DDE.transcript o e q) then 1 else 0)
        - ((RandomFunction.URF (X := A) (Y := A)).sum fun o ow =>
            (ow : ℝ) * if dec (DDE.transcript o e q) then 1 else 0)
      ≤ (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by
    intro e dec
    -- (a) the fully defined function evaluator answers `some (g x)` on the last input
    have hfd : ∀ (g : A → A) (l : List A) (hne : l ≠ [])
        (h : l ∈ (DDS.fullyDefined (DDS.functionEvaluator g)).dom),
        (DDS.fullyDefined (DDS.functionEvaluator g)).output l h
          = some (g (l.getLast hne)) := by
      intro g l hne h
      show (DDS.fullyDefined (DDS.functionEvaluator g)).respond l h = _
      rw [RandomSystems.CR18.DDS.fullyDefined_respond]
      rw [dif_pos (show DDS.keptPrefix (DDS.functionEvaluator g) l.dropLast
          ++ [l.getLast h] ∈ (DDS.functionEvaluator g).dom by
            simp [RandomSystems.CR18.DDS.functionEvaluator])]
      show some (g ((DDS.keptPrefix (DDS.functionEvaluator g) l.dropLast
          ++ [l.getLast h]).getLast _)) = _
      rw [List.getLast_append_singleton]
    -- (b) one transcript step against a function evaluator
    have hext : ∀ (g : A → A) (t : RandomSystems.CR18.DDE.TranscriptPrefix A A) (x : A),
        RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x
          = ⟨t.inputs ++ [x], t.outputs ++ [some (g x)]⟩ := by
      intro g t x
      have hout : (RandomSystems.CR18.DDE.extendWithInput
            (DDS.functionEvaluator g) t x).outputs = t.outputs ++ [some (g x)] := by
        show t.outputs ++ [(DDS.fullyDefined (DDS.functionEvaluator g)).output
            (t.inputs ++ [x]) _] = t.outputs ++ [some (g x)]
        rw [hfd g (t.inputs ++ [x]) (by simp) _, List.getLast_append_singleton]
      have hin : (RandomSystems.CR18.DDE.extendWithInput
          (DDS.functionEvaluator g) t x).inputs = t.inputs ++ [x] := rfl
      calc RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x
          = ⟨(RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x).inputs,
             (RandomSystems.CR18.DDE.extendWithInput
               (DDS.functionEvaluator g) t x).outputs⟩ := rfl
        _ = ⟨t.inputs ++ [x], t.outputs ++ [some (g x)]⟩ := by rw [hout, hin]
    -- (c) the accumulated inputs are a prefix of the final ones
    have hrun_pref : ∀ (g : A → A) (fuel : ℕ)
        (t : RandomSystems.CR18.DDE.TranscriptPrefix A A),
        t.inputs <+: (RandomSystems.CR18.DDE.runTranscript
          (DDS.functionEvaluator g) e fuel t).inputs := by
      intro g fuel
      induction fuel with
      | zero =>
        intro t
        simp [RandomSystems.CR18.DDE.runTranscript]
      | succ n ih =>
        intro t
        cases hx : e t.outputs with
        | none => simp [RandomSystems.CR18.DDE.runTranscript, hx]
        | some x =>
          have hstep : RandomSystems.CR18.DDE.runTranscript
                (DDS.functionEvaluator g) e (n + 1) t
              = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g) e n
                  (RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x) := by
            simp [RandomSystems.CR18.DDE.runTranscript, hx]
          rw [hstep]
          refine List.IsPrefix.trans ?_ (ih _)
          rw [hext g t x]
          exact List.prefix_append _ _
    -- (d) fuel bounds the number of inputs
    have hrun_len : ∀ (g : A → A) (fuel : ℕ)
        (t : RandomSystems.CR18.DDE.TranscriptPrefix A A),
        (RandomSystems.CR18.DDE.runTranscript
            (DDS.functionEvaluator g) e fuel t).inputs.length
          ≤ t.inputs.length + fuel := by
      intro g fuel
      induction fuel with
      | zero =>
        intro t
        simp [RandomSystems.CR18.DDE.runTranscript]
      | succ n ih =>
        intro t
        cases hx : e t.outputs with
        | none =>
          simp only [RandomSystems.CR18.DDE.runTranscript, hx]
          omega
        | some x =>
          have hstep : RandomSystems.CR18.DDE.runTranscript
                (DDS.functionEvaluator g) e (n + 1) t
              = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g) e n
                  (RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x) := by
            simp [RandomSystems.CR18.DDE.runTranscript, hx]
          rw [hstep, hext g t x]
          have h2 := ih ⟨t.inputs ++ [x], t.outputs ++ [some (g x)]⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at h2
          omega
    -- (e) every output is `some (g ·)` of the matching input
    have hrun_out : ∀ (g : A → A) (fuel : ℕ)
        (t : RandomSystems.CR18.DDE.TranscriptPrefix A A),
        t.outputs = t.inputs.map (fun x => some (g x)) →
        (RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g) e fuel t).outputs
          = (RandomSystems.CR18.DDE.runTranscript
              (DDS.functionEvaluator g) e fuel t).inputs.map (fun x => some (g x)) := by
      intro g fuel
      induction fuel with
      | zero =>
        intro t ht
        simpa [RandomSystems.CR18.DDE.runTranscript] using ht
      | succ n ih =>
        intro t ht
        cases hx : e t.outputs with
        | none => simpa [RandomSystems.CR18.DDE.runTranscript, hx] using ht
        | some x =>
          have hstep : RandomSystems.CR18.DDE.runTranscript
                (DDS.functionEvaluator g) e (n + 1) t
              = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g) e n
                  (RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g) t x) := by
            simp [RandomSystems.CR18.DDE.runTranscript, hx]
          rw [hstep, hext g t x]
          exact ih _ (by simp [ht])
    -- (f) AGREEMENT: tables agreeing on the realized inputs give the SAME run
    have hagree : ∀ (fuel : ℕ) (g₁ g₂ : A → A)
        (t : RandomSystems.CR18.DDE.TranscriptPrefix A A),
        (∀ x ∈ (RandomSystems.CR18.DDE.runTranscript
            (DDS.functionEvaluator g₁) e fuel t).inputs, g₁ x = g₂ x) →
        RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g₂) e fuel t
          = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g₁) e fuel t := by
      intro fuel
      induction fuel with
      | zero =>
        intro g₁ g₂ t _
        simp [RandomSystems.CR18.DDE.runTranscript]
      | succ n ih =>
        intro g₁ g₂ t hagr
        cases hx : e t.outputs with
        | none => simp [RandomSystems.CR18.DDE.runTranscript, hx]
        | some x =>
          have hstep₁ : RandomSystems.CR18.DDE.runTranscript
                (DDS.functionEvaluator g₁) e (n + 1) t
              = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g₁) e n
                  (RandomSystems.CR18.DDE.extendWithInput
                    (DDS.functionEvaluator g₁) t x) := by
            simp [RandomSystems.CR18.DDE.runTranscript, hx]
          have hstep₂ : RandomSystems.CR18.DDE.runTranscript
                (DDS.functionEvaluator g₂) e (n + 1) t
              = RandomSystems.CR18.DDE.runTranscript (DDS.functionEvaluator g₂) e n
                  (RandomSystems.CR18.DDE.extendWithInput
                    (DDS.functionEvaluator g₂) t x) := by
            simp [RandomSystems.CR18.DDE.runTranscript, hx]
          have hmem : x ∈ (RandomSystems.CR18.DDE.runTranscript
              (DDS.functionEvaluator g₁) e (n + 1) t).inputs := by
            rw [hstep₁]
            refine (hrun_pref g₁ n _).subset ?_
            rw [hext g₁ t x]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
          have hgx : g₁ x = g₂ x := hagr x hmem
          have hextEq : RandomSystems.CR18.DDE.extendWithInput
                (DDS.functionEvaluator g₂) t x
              = RandomSystems.CR18.DDE.extendWithInput (DDS.functionEvaluator g₁) t x := by
            rw [hext g₁ t x, hext g₂ t x, hgx]
          rw [hstep₂, hstep₁, hextEq]
          refine ih g₁ g₂ _ fun y hy => hagr y ?_
          rw [hstep₁]
          exact hy
    -- (g) transcript-level specializations
    have hlenq : ∀ g : A → A,
        (DDE.transcript (DDS.functionEvaluator g) e q).inputs.length ≤ q := by
      intro g
      have h2 := hrun_len g q RandomSystems.CR18.DDE.TranscriptPrefix.empty
      simpa [RandomSystems.CR18.DDE.transcript,
        RandomSystems.CR18.DDE.TranscriptPrefix.empty] using h2
    have houts : ∀ g : A → A,
        (DDE.transcript (DDS.functionEvaluator g) e q).outputs
          = (DDE.transcript (DDS.functionEvaluator g) e q).inputs.map
              (fun x => some (g x)) :=
      fun g => hrun_out g q RandomSystems.CR18.DDE.TranscriptPrefix.empty
        (by simp [RandomSystems.CR18.DDE.TranscriptPrefix.empty])
    -- (h) FIBER characterization: same transcript ⟺ agreement on the realized inputs
    have hfiber : ∀ g₀ g : A → A,
        DDE.transcript (DDS.functionEvaluator g) e q
            = DDE.transcript (DDS.functionEvaluator g₀) e q
          ↔ ∀ x ∈ (DDE.transcript (DDS.functionEvaluator g₀) e q).inputs, g x = g₀ x := by
      intro g₀ g
      constructor
      · intro hT x hx
        have h₁ := houts g
        rw [hT, houts g₀] at h₁
        have h₂ := List.map_inj_left.mp h₁.symm x hx
        exact Option.some_injective _ h₂
      · intro hagr
        exact hagree q g₀ g RandomSystems.CR18.DDE.TranscriptPrefix.empty
          (fun x hx => (hagr x hx).symm)
    -- (i) realized-input set bounds
    have hrA : ∀ σ₀ : Equiv.Perm A,
        (DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card
          ≤ Fintype.card A := fun _ => Finset.card_le_univ _
    have hrq : ∀ σ₀ : Equiv.Perm A,
        (DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card
          ≤ q := fun σ₀ => le_trans (List.toFinset_card_le _) (hlenq σ₀.toFun)
    -- (j) FUNCTION fiber count: N^(N-r)
    have hcF : ∀ σ₀ : Equiv.Perm A,
        (Finset.univ.filter fun g : A → A =>
            DDE.transcript (DDS.functionEvaluator g) e q
              = DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).card
          = Fintype.card A ^ (Fintype.card A
              - (DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card) := by
      intro σ₀
      set R := (DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset
        with hR
      have hset : (Finset.univ.filter fun g : A → A =>
            DDE.transcript (DDS.functionEvaluator g) e q
              = DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q)
          = Fintype.piFinset (fun x : A =>
              if x ∈ R then ({σ₀.toFun x} : Finset A) else Finset.univ) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        rw [hfiber σ₀.toFun g]
        constructor
        · intro h x
          by_cases hx : x ∈ R
          · rw [if_pos hx]
            exact Finset.mem_singleton.mpr (h x (List.mem_toFinset.mp hx))
          · rw [if_neg hx]
            exact Finset.mem_univ _
        · intro h x hx
          have hx' := h x
          rw [if_pos (List.mem_toFinset.mpr hx)] at hx'
          exact Finset.mem_singleton.mp hx'
      have hcard : ∀ x : A,
          (if x ∈ R then ({σ₀.toFun x} : Finset A) else Finset.univ).card
            = if x ∈ R then 1 else Fintype.card A := by
        intro x
        split <;> simp
      have hcompl : (Finset.univ.filter fun x : A => ¬ x ∈ R) = Rᶜ := by
        ext x
        simp [Finset.mem_compl]
      rw [hset, Fintype.card_piFinset, Finset.prod_congr rfl fun x _ => hcard x,
        Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hcompl,
        Finset.card_compl]
    -- (k) PERMUTATION fiber count: (N-r)!
    have hcP : ∀ σ₀ : Equiv.Perm A,
        (Finset.univ.filter fun σ : Equiv.Perm A =>
            DDE.transcript (DDS.functionEvaluator σ.toFun) e q
              = DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).card
          = (Fintype.card A
              - (DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card).factorial := by
      intro σ₀
      set R := (DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset
        with hR
      have hmem : ∀ i : Fin (Fintype.card R),
          (((Fintype.equivFin R).symm i : R) : A) ∈ R :=
        fun i => ((Fintype.equivFin R).symm i).2
      have hinj : Function.Injective
          (fun i : Fin (Fintype.card R) => (((Fintype.equivFin R).symm i : R) : A)) := by
        intro i j hij
        exact (Fintype.equivFin R).symm.injective (Subtype.ext hij)
      have hsurj : ∀ x ∈ R, ∃ i : Fin (Fintype.card R),
          (((Fintype.equivFin R).symm i : R) : A) = x := by
        intro x hx
        exact ⟨Fintype.equivFin R ⟨x, hx⟩, by simp⟩
      have hset : (Finset.univ.filter fun σ : Equiv.Perm A =>
            DDE.transcript (DDS.functionEvaluator σ.toFun) e q
              = DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q)
          = Finset.univ.filter fun σ : Equiv.Perm A =>
              ∀ i : Fin (Fintype.card R),
                σ (((Fintype.equivFin R).symm i : R) : A)
                  = σ₀ (((Fintype.equivFin R).symm i : R) : A) := by
        refine Finset.filter_congr fun σ _ => ?_
        rw [hfiber σ₀.toFun σ.toFun]
        constructor
        · intro h i
          exact h _ (List.mem_toFinset.mp (hmem i))
        · intro h x hx
          obtain ⟨i, rfl⟩ := hsurj x (List.mem_toFinset.mpr hx)
          exact h i
      have hle : Fintype.card R ≤ Fintype.card A := by
        rw [Fintype.card_coe]
        exact hrA σ₀
      rw [hset]
      exact (Applications.card_perm_fiber
        (fun i : Fin (Fintype.card R) => (((Fintype.equivFin R).symm i : R) : A)) hinj
        (fun i => σ₀ (((Fintype.equivFin R).symm i : R) : A))
        (σ₀.injective.comp hinj) hle).trans (by rw [Fintype.card_coe])
    -- (l) pull both correlations back to the seed distributions
    have hpullP : ((RandomPermutation.URP A).sum fun o ow =>
          (ow : ℝ) * if dec (DDE.transcript o e q) then 1 else 0)
        = ∑ σ : Equiv.Perm A, (1 / (Fintype.card (Equiv.Perm A) : ℝ))
            * if dec (DDE.transcript (DDS.functionEvaluator σ.toFun) e q) then 1 else 0 := by
      have hmap : RandomPermutation.URP A
          = Finsupp.mapDomain (fun σ : Equiv.Perm A => DDS.functionEvaluator σ.toFun)
              (Dist.uniform (Equiv.Perm A)) := rfl
      rw [hmap, Finsupp.sum_mapDomain_index (fun o => by simp)
          (fun o m₁ m₂ => by push_cast; ring),
        Finsupp.sum_fintype _ _ (fun σ => by simp)]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Dist.uniform_apply]
      push_cast
      ring
    have hpullF : ((RandomFunction.URF (X := A) (Y := A)).sum fun o ow =>
          (ow : ℝ) * if dec (DDE.transcript o e q) then 1 else 0)
        = ∑ g : A → A, (1 / (Fintype.card (A → A) : ℝ))
            * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0 := by
      have hmap : RandomFunction.URF (X := A) (Y := A)
          = Finsupp.mapDomain (DDS.functionEvaluator : (A → A) → DDS A A)
              (Dist.uniform (A → A)) := rfl
      rw [hmap, Finsupp.sum_mapDomain_index (fun o => by simp)
          (fun o m₁ m₂ => by push_cast; ring),
        Finsupp.sum_fintype _ _ (fun g => by simp)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Dist.uniform_apply]
      push_cast
      ring
    -- (m) the abstract per-transcript arithmetic (one-sided H-technique step)
    have harith : ∀ (Fc P G Q ε' : ℝ), 0 < Fc → 0 < P → 0 < G → 0 < Q →
        (1 - ε') * Q ≤ P →
        Fc * (1 / (Fc * P)) - G * (1 / (G * Q)) ≤ ε' * (Fc * (1 / (Fc * P))) := by
      intro Fc P G Q ε' hF hP hG hQ hkey
      have e1 : Fc * (1 / (Fc * P)) = 1 / P := by
        field_simp
      have e2 : G * (1 / (G * Q)) = 1 / Q := by
        field_simp
      rw [e1, e2]
      have h2 : (1 - ε') / P ≤ 1 / Q := by
        rw [div_le_div_iff₀ hP hQ]
        nlinarith
      have h3 : ε' * (1 / P) = 1 / P - (1 - ε') / P := by
        ring
      rw [h3]
      linarith
    -- (n) per-transcript comparison over the permutation image
    have hτbound : ∀ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
          DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
        ((Finset.univ.filter fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
            * ((1 / (Fintype.card (Equiv.Perm A) : ℝ)) * if dec τ then 1 else 0)
          - ((Finset.univ.filter fun g : A → A =>
              DDE.transcript (DDS.functionEvaluator g) e q = τ).card : ℝ)
            * ((1 / (Fintype.card (A → A) : ℝ)) * if dec τ then 1 else 0)
        ≤ ((q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)))
            * (((Finset.univ.filter fun σ : Equiv.Perm A =>
                DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
              * (1 / (Fintype.card (Equiv.Perm A) : ℝ))) := by
      intro τ hτ
      obtain ⟨σ₀, -, rfl⟩ := Finset.mem_image.mp hτ
      by_cases hdec : dec (DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q)
      · simp only [if_pos hdec, mul_one]
        rw [hcP σ₀, hcF σ₀, Fintype.card_perm, Fintype.card_fun]
        have hrn : (DDE.transcript
            (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card
              ≤ Fintype.card A := hrA σ₀
        have hdescR : ((Nat.descFactorial (Fintype.card A)
              ((DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card) : ℕ) : ℝ)
            = ∏ k ∈ Finset.range ((DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card),
                ((Fintype.card A : ℝ) - (k : ℝ)) := by
          rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
          refine Finset.prod_congr rfl fun k hk => ?_
          rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) hrn))]
        have hP : (0 : ℝ) < ∏ k ∈ Finset.range ((DDE.transcript
              (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card),
              ((Fintype.card A : ℝ) - (k : ℝ)) := by
          rw [← hdescR]
          exact_mod_cast Nat.descFactorial_pos.mpr hrn
        have hfact : ((Fintype.card A).factorial : ℝ)
            = (((Fintype.card A - (DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card).factorial : ℕ) : ℝ)
              * ∏ k ∈ Finset.range ((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card),
                  ((Fintype.card A : ℝ) - (k : ℝ)) := by
          rw [← hdescR, ← Nat.cast_mul, Nat.factorial_mul_descFactorial hrn]
        have hpow : (Fintype.card A : ℝ) ^ (Fintype.card A)
            = (Fintype.card A : ℝ) ^ (Fintype.card A - (DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card)
              * (Fintype.card A : ℝ) ^ ((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card) := by
          rw [← pow_add]
          congr 1
          omega
        have hfall : (1 - (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)))
              * (Fintype.card A : ℝ) ^ ((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card)
            ≤ ∏ k ∈ Finset.range ((DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card),
                ((Fintype.card A : ℝ) - (k : ℝ)) := by
          have hW := falling_factorial_lower_bound
            (N := Fintype.card A)
            (q := (DDE.transcript
              (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card)
            hrn Fintype.card_pos
          have hrcast : (((DDE.transcript
              (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ)
              ≤ (q : ℝ) := by
            exact_mod_cast hrq σ₀
          have hr0 : (0 : ℝ) ≤ (((DDE.transcript
              (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          have hnum : (((DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ)
                * ((((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ) - 1)
              ≤ (q ^ 2 : ℝ) := by
            nlinarith
          have hmono : (((DDE.transcript
                (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ)
                * ((((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ) - 1)
                / (2 * (Fintype.card A : ℝ))
              ≤ (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by
            gcongr
          calc (1 - (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)))
                * (Fintype.card A : ℝ) ^ ((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card)
              ≤ (1 - (((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ)
                  * ((((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ) - 1)
                  / (2 * (Fintype.card A : ℝ)))
                * (Fintype.card A : ℝ) ^ ((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card) := by
                refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hNpos.le _)
                linarith
            _ = (Fintype.card A : ℝ) ^ ((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card)
                * (1 - (((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ)
                  * ((((DDE.transcript
                    (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card : ℕ) : ℝ) - 1)
                  / (2 * (Fintype.card A : ℝ))) := mul_comm _ _
            _ ≤ ∏ k ∈ Finset.range ((DDE.transcript
                  (DDS.functionEvaluator σ₀.toFun) e q).inputs.toFinset.card),
                  ((Fintype.card A : ℝ) - (k : ℝ)) := hW
        push_cast
        rw [hfact, hpow]
        exact harith _ _ _ _ _
          (by exact_mod_cast Nat.factorial_pos _)
          hP
          (pow_pos hNpos _)
          (pow_pos hNpos _)
          hfall
      · simp only [if_neg hdec, mul_zero, sub_self]
        have hb : (0 : ℝ) ≤ ((Finset.univ.filter fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q
                = DDE.transcript (DDS.functionEvaluator σ₀.toFun) e q).card : ℝ)
            * (1 / (Fintype.card (Equiv.Perm A) : ℝ)) := by
          positivity
        positivity
    -- (o) assemble: fiberwise split, per-τ bound, mass-1 collapse
    rw [hpullP, hpullF]
    have hPsplit : (∑ σ : Equiv.Perm A, (1 / (Fintype.card (Equiv.Perm A) : ℝ))
            * if dec (DDE.transcript (DDS.functionEvaluator σ.toFun) e q) then 1 else 0)
        = ∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            ((Finset.univ.filter fun σ : Equiv.Perm A =>
                DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (Equiv.Perm A) : ℝ)) * if dec τ then 1 else 0) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (fun σ _ => Finset.mem_image_of_mem
          (fun σ : Equiv.Perm A => DDE.transcript (DDS.functionEvaluator σ.toFun) e q)
          (Finset.mem_univ σ))
        (fun σ => (1 / (Fintype.card (Equiv.Perm A) : ℝ))
          * if dec (DDE.transcript (DDS.functionEvaluator σ.toFun) e q) then 1 else 0)]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hconst : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm A =>
          DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ),
          (1 / (Fintype.card (Equiv.Perm A) : ℝ))
              * (if dec (DDE.transcript (DDS.functionEvaluator σ.toFun) e q)
                  then (1 : ℝ) else 0)
            = (1 / (Fintype.card (Equiv.Perm A) : ℝ)) * (if dec τ then (1 : ℝ) else 0) := by
        intro σ hσ
        rw [(Finset.mem_filter.mp hσ).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hFsplit : (∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            ((Finset.univ.filter fun g : A → A =>
                DDE.transcript (DDS.functionEvaluator g) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (A → A) : ℝ)) * if dec τ then 1 else 0))
        ≤ ∑ g : A → A, (1 / (Fintype.card (A → A) : ℝ))
            * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0 := by
      have hstep : (∑ g ∈ Finset.univ.filter (fun g : A → A =>
            DDE.transcript (DDS.functionEvaluator g) e q
              ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
                  DDE.transcript (DDS.functionEvaluator σ.toFun) e q)),
            (1 / (Fintype.card (A → A) : ℝ))
              * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0)
          ≤ ∑ g : A → A, (1 / (Fintype.card (A → A) : ℝ))
              * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun g _ _ => ?_
        have hite : (0 : ℝ) ≤ if dec (DDE.transcript
            (DDS.functionEvaluator g) e q) then (1 : ℝ) else 0 := by
          split <;> norm_num
        exact mul_nonneg (by positivity) hite
      refine le_trans (le_of_eq ?_) hstep
      rw [← Finset.sum_fiberwise_of_maps_to
        (fun g hg => (Finset.mem_filter.mp hg).2)
        (fun g => (1 / (Fintype.card (A → A) : ℝ))
          * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0)]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have hff : ((Finset.univ.filter (fun g : A → A =>
            DDE.transcript (DDS.functionEvaluator g) e q
              ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
                  DDE.transcript (DDS.functionEvaluator σ.toFun) e q))).filter
            (fun g => DDE.transcript (DDS.functionEvaluator g) e q = τ))
          = Finset.univ.filter fun g : A → A =>
              DDE.transcript (DDS.functionEvaluator g) e q = τ := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨by rw [h]; exact hτ, h⟩
      have hconst : ∀ g ∈ Finset.univ.filter (fun g : A → A =>
          DDE.transcript (DDS.functionEvaluator g) e q = τ),
          (1 / (Fintype.card (A → A) : ℝ))
              * (if dec (DDE.transcript (DDS.functionEvaluator g) e q)
                  then (1 : ℝ) else 0)
            = (1 / (Fintype.card (A → A) : ℝ)) * (if dec τ then (1 : ℝ) else 0) := by
        intro g hg
        rw [(Finset.mem_filter.mp hg).2]
      rw [hff, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    calc (∑ σ : Equiv.Perm A, (1 / (Fintype.card (Equiv.Perm A) : ℝ))
            * if dec (DDE.transcript (DDS.functionEvaluator σ.toFun) e q) then 1 else 0)
          - (∑ g : A → A, (1 / (Fintype.card (A → A) : ℝ))
              * if dec (DDE.transcript (DDS.functionEvaluator g) e q) then 1 else 0)
        ≤ (∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            ((Finset.univ.filter fun σ : Equiv.Perm A =>
                DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (Equiv.Perm A) : ℝ)) * if dec τ then 1 else 0))
          - (∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
              DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            ((Finset.univ.filter fun g : A → A =>
                DDE.transcript (DDS.functionEvaluator g) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (A → A) : ℝ)) * if dec τ then 1 else 0)) := by
          rw [hPsplit]
          exact sub_le_sub_left hFsplit _
      _ = ∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
            DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            (((Finset.univ.filter fun σ : Equiv.Perm A =>
                DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (Equiv.Perm A) : ℝ)) * if dec τ then 1 else 0)
            - ((Finset.univ.filter fun g : A → A =>
                DDE.transcript (DDS.functionEvaluator g) e q = τ).card : ℝ)
              * ((1 / (Fintype.card (A → A) : ℝ)) * if dec τ then 1 else 0)) :=
          (Finset.sum_sub_distrib _ _).symm
      _ ≤ ∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
            DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
            ((q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)))
              * (((Finset.univ.filter fun σ : Equiv.Perm A =>
                  DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
                * (1 / (Fintype.card (Equiv.Perm A) : ℝ))) :=
          Finset.sum_le_sum hτbound
      _ ≤ (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by
          rw [← Finset.mul_sum]
          have hsum2 : (∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
                DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
              ((Finset.univ.filter fun σ : Equiv.Perm A =>
                  DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ)
                * (1 / (Fintype.card (Equiv.Perm A) : ℝ))) = 1 := by
            rw [← Finset.sum_mul]
            rw [show (∑ τ ∈ Finset.univ.image (fun σ : Equiv.Perm A =>
                  DDE.transcript (DDS.functionEvaluator σ.toFun) e q),
                ((Finset.univ.filter fun σ : Equiv.Perm A =>
                    DDE.transcript (DDS.functionEvaluator σ.toFun) e q = τ).card : ℝ))
                = ((Fintype.card (Equiv.Perm A) : ℕ) : ℝ) from by
              rw [← Nat.cast_sum]
              congr 1
              rw [← Finset.card_univ]
              exact (Finset.card_eq_sum_card_fiberwise
                (fun σ _ => Finset.mem_image_of_mem
                  (fun σ : Equiv.Perm A =>
                    DDE.transcript (DDS.functionEvaluator σ.toFun) e q)
                  (Finset.mem_univ σ))).symm]
            rw [mul_one_div, div_self
              (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm A)).ne')]
          rw [hsum2, mul_one]
  -- ===== convexity over the weight-1 probabilistic distinguishers =====
  unfold AdvWith
  refine Real.sSup_le ?_ hRHS0
  rintro x ⟨D, hD, rfl⟩
  have hD1 : (∑ d ∈ D.support, (D d : ℝ)) = 1 := by
    have h1 : ((D.sum fun _ w => w : NNReal) : ℝ) = 1 := by
      rw [hD]
      norm_num
    simpa [Finsupp.sum, NNReal.coe_sum] using h1
  simp only [id_eq]
  have hperf : (ddeDS A A q Adm).performance
      (RandomFunction.URF (X := A) (Y := A), RandomPermutation.URP A) D
        = (D.sum fun d dw => (RandomPermutation.URP A).sum fun o ow =>
            (dw : ℝ) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0)
          - (D.sum fun d dw =>
              (RandomFunction.URF (X := A) (Y := A)).sum fun o ow =>
                (dw : ℝ) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0) := rfl
  have hterm : ∀ d : (ddeDS A A q Adm).D, ∀ w : NNReal,
      ((RandomPermutation.URP A).sum fun o ow =>
          (w : ℝ) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0)
        - ((RandomFunction.URF (X := A) (Y := A)).sum fun o ow =>
            (w : ℝ) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0)
      ≤ (w : ℝ) * ((q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ))) := by
    intro d w
    obtain ⟨⟨e, he⟩, dc⟩ := d
    have hκ : ∀ o : RandomSystems.CR18.DDS A A,
        (ddeDS A A q Adm).κ (⟨⟨e, he⟩, dc⟩) o = dc (DDE.transcript o e q) :=
      fun _ => rfl
    have hfac : ∀ V : RandomSystems.Dist (RandomSystems.CR18.DDS A A),
        (V.sum fun o ow =>
            (w : ℝ) * (ow : ℝ) * if dc (DDE.transcript o e q) then 1 else 0)
          = (w : ℝ) * (V.sum fun o ow =>
              (ow : ℝ) * if dc (DDE.transcript o e q) then 1 else 0) := by
      intro V
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun o _ => by ring
    simp only [hκ]
    rw [hfac, hfac, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hMain e dc) w.coe_nonneg
  rw [hperf, ← Finsupp.sum_sub, Finsupp.sum]
  calc (∑ d ∈ D.support,
        (((RandomPermutation.URP A).sum fun o ow =>
            ((D d : ℝ)) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0)
          - ((RandomFunction.URF (X := A) (Y := A)).sum fun o ow =>
              ((D d : ℝ)) * (ow : ℝ) * if (ddeDS A A q Adm).κ d o then 1 else 0)))
      ≤ ∑ d ∈ D.support, (D d : ℝ) * ((q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ))) :=
        Finset.sum_le_sum fun d _ => hterm d (D d)
    _ = (∑ d ∈ D.support, (D d : ℝ)) * ((q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ))) :=
        (Finset.sum_mul _ _ _).symm
    _ = (q ^ 2 : ℝ) / (2 * (Fintype.card A : ℝ)) := by
        rw [hD1, one_mul]

end RandomSystems.CR18.SwitchingPort

/-!
## CR18 Lemma 4.19 — the URP–URF switching lemma (real statement)

CR18 §4.11.3 (source line 5720):

> **Lemma 4.19.** `Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ`.

`Rₙ,ₙ` and `Pₙ` are the REAL bitstring URF/URP of CR18 Example 3.5
(`Ex35.R n n` / `Ex35.P n`, `RandomSystems/CR18/PDS.lean`); the `[q]` query
cap is the fuel bound built into the `SwitchingPort.ddeDS` distinguisher
class; Δ is the shared `AdvWith` advantage
(`RandomSystems/CR18/AdvMetric.lean`).  The bound `q² / (2 · 2ⁿ)` IS Maurer's
`½ q² 2⁻ⁿ`.

This REPLACES the former hollow `Lem419.urp_urf_switching` of `Indist.lean`,
whose δ was an abstract `NNReal` tied to URF/URP only through an assumed
`hBridge : δ ≤ pcoll(2ⁿ, q)`.  The statement below is about the actual
systems, with NO bridge hypothesis: it is `advWith_urf_urp_le_birthday` (the
ported transcript-factorization proof) instantiated at `A := Fin (2 ^ n)`.
The numerical companions (`Lem419.pcoll_bound`,
`Lem419.birthdayBound_le_pcoll_bound`, the Lem 4.18 `pcoll` chain) remain in
`Indist.lean`.

The alternative CR18 proof route (Thm 4.17: `Δ ≤ Γ(b[q]R̂ₙ,ₙ)` via the
collision MBO of Example 4.15, then `Γ ≤ pcoll(2ⁿ, q) ≤ ½q²2⁻ⁿ` by Lem 4.18)
is partially formalized through `advWith_le_gamma` (`AdvMetric.lean`); note it
bounds the advantage over the §4.10.2 strategy class
(`Lem416.distinctionStructure`), while this lemma bounds the advantage over
the fuel-capped `ddeDS` environment class — the ported, self-contained
transcript-factorization proof is the primary derivation of Lemma 4.19.
-/

namespace RandomSystems.CR18.Lem419

/-- **CR18 Lemma 4.19 (URP–URF switching lemma)** — the REAL statement:
`Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ` for the actual CR18 Example 3.5 systems
`Rₙ,ₙ = Ex35.R n n` (uniform random function on `{0,1}ⁿ`) and
`Pₙ = Ex35.P n` (uniform random permutation of `{0,1}ⁿ`), the advantage taken
over any `Adm`-admissible, `q`-fuel-capped `ddeDS` distinguisher class.

**CR18 source:** Lemma 4.19 (source line 5720):
  "Δ([q]Rₙ,ₙ, [q]Pₙ) ≤ ½ q² 2⁻ⁿ."

No abstract δ, no `hBridge`: this is
`SwitchingPort.advWith_urf_urp_le_birthday` (the ported `GAP2_switching`
transcript-factorization proof) at the bitstring alphabet `A := Fin (2 ^ n)`,
where `|A| = 2ⁿ`. -/
theorem urp_urf_switching (n q : ℕ)
    (Adm : DDE (Fin (2 ^ n)) (Fin (2 ^ n)) → Prop) :
    AdvWith (SwitchingPort.ddeDS (Fin (2 ^ n)) (Fin (2 ^ n)) q Adm)
        (id : PDS (Fin (2 ^ n)) (Fin (2 ^ n)) →
          Dist (SwitchingPort.ddeDS (Fin (2 ^ n)) (Fin (2 ^ n)) q Adm).O)
        (Ex35.R n n) (Ex35.P n)
      ≤ (q ^ 2 : ℝ) / (2 * 2 ^ n) := by
  have h := SwitchingPort.advWith_urf_urp_le_birthday (Fin (2 ^ n)) q Adm
  rw [Fintype.card_fin] at h
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast] at h
  exact h

end RandomSystems.CR18.Lem419

end
