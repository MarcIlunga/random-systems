/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Uniform
import AbstractCrypto.Relaxations

/-!
# MauRen16 Lemma 6: public randomness cannot be expanded by a single bit

Maurer–Renner, *From Indifferentiability to Constructive Cryptography (and
Back)*, §5, **Lemma 6** (p. 14):

> Let `k ∈ ℕ` and `ε < 1/4`.  Then `PRᵏ ↛ PRᵏ⁺¹⟦ᵋ`.

This is the estate's first *impossibility* result, so unlike every construction
statement it is a negation of an existential over all constructors, and the
distinguisher has to be exhibited concretely.  The abstract carrier `Φ` of
`AbstractCrypto` cannot host a probabilistic `PRᵏ` on its own — it is a bare
`MulAction` with a pseudo-emetric — so this module builds the smallest concrete
carrier on which MauRen16's own argument is valid and instantiates the abstract
`outboundHull` / `eball` / construction vocabulary on it.

## The carrier, and why it is the right one

`PRᵏ` "chooses `Z` uniformly at random from the set `{0,1}ᵏ`" and "any party can
read `Z`" (p. 13).  Every resource in the lemma is therefore a **read-only
register with three interfaces**: the two honest parties `A`, `A'` and the
dishonest party `E` (p. 14, "It suffices to consider two honest parties, which
we label by `A` and `A'`, as well as one dishonest party, labelled by `E`").
So a resource is a joint law of the three readings — `Boundary k` — and a
converter is a randomized map of the reading it is attached to.

Two restrictions are built into that carrier; both are spelled out because one
of them is a genuine gap in the printed proof.

* **Converters read once.**  Against `PRᵏ` this is without loss of generality:
  the register answers every read with the same `Z`, so a converter's whole
  behaviour there is a randomized function of `Z`.  Against the *ideal*
  resource it is not vacuous, and it is exactly the step the paper leaves
  implicit — see finding 2 below.
* **Resources are read-only.**  Given one-shot converters only the first answer
  of each interface is ever observed, so this costs nothing beyond the above.

## Interface alphabets, and where the `2ᵏ` comes from

The honest alphabet is `ℕ` (a bit string is modelled by its value; the paper's
`D₁` performs equality tests only, so nothing else about strings is used).  It
has to be one single type because a converter changes the interface it sits on:
`πᴬ` turns `PRᵏ`'s `k`-bit reading into a `(k+1)`-bit one.

Eve's alphabet is pinned to `Fin (2 ^ k)` — `PRᵏ`'s own `k`-bit register, which
a left-interface constructor never touches.  This is forced, not chosen:
`d(πPRᵏ, ℛ)` compares two resources through one distinguisher, so `ℛ` must
offer `πPRᵏ`'s interfaces, and `πPRᵏ`'s right interface *is* `PRᵏ`'s.  The
membership condition of `ℛ⟦` only constrains `ℛ⊣` — the *blocked* resource,
which has no right interface at all (MauRen16 §3.4) — so it never forces `ℛ` to
share `PRᵏ⁺¹`'s right interface.  This is precisely the paper's "`π'` … takes as
input only a `k`-bit string", promoted from an unstated assumption to a typing
fact, and it is where the `2ᵏ` of the min-entropy step comes from.  `PRᵏ⁺¹`
therefore enters only through its blocked form (`PRsucc`, whose right register
is constant); `mem_outboundHull_iff_map_eq` shows the resulting specification
depends on the honest marginal alone, so nothing hangs on that choice.

## What is formal and what is modelling

Fully formal: the converter monoid and its action, the distinguishing
pseudo-emetric (MauRen16 fn. 9, absolute value and all), the concrete `D₁` of
p. 14, both probability bounds, the `⟦` relaxation of §3.4 instantiated here,
the exponentiated min-entropy chain-rule instance, and the final negation.
Assumed as modelling: the carrier described above.

The entropy layer itself — min-entropy, conditional min-entropy and eq. (11) in
logarithmic form — is **not** here: it lives at tower level L2 on
`RandomSystems.Dist`, in `RandomSystems/Entropy.lean` (`DESIGN.md` §12).  §4
below keeps only the `ℝ≥0∞`/`PMF` guessing probability that this proof's
carrier forces, and says why.

## Two findings about the printed proof

1. **The displayed real-side identity does not hold** (p. 14).  The paper bounds
   `Pr[Z_A = Z_A' ≠ Z_E]` by `Pr[Z_A = Z_A'] · Pr[Z_E ≠ Z_A']` and then equates
   `Pr[Z_E = Z_A']` with `Pr[Z_A = Z_A']`.  Those are different numbers:
   conditioned on `Z`, writing `q` for `πᴬ`'s law and `p` for `πᴬ'`'s, the
   first is `∑ₐ p(a)²` and the second `∑ₐ q(a)·p(a)`.  The bound `1/4` survives,
   but by a different route: the event has probability `∑ₐ q(a)·p(a)·(1-p(a))`,
   so `x(1-x) ≤ 1/4` has to be applied *inside* the sum, not to a marginal.
   `real_probZero` proves the corrected form; `mul_le_quarter_of_add_eq_one` is
   the `x(1-x) ≤ 1/4` step, in the subtraction-free shape `u + v = 1 → u·v ≤ 1/4`.
2. **`D₁` needs `π'` to read at most `k` bits, and that is not automatic.**  If
   converters may query twice, take `k = 1`, let `πᴬ = πᴬ'` be "read twice,
   output `w₁w₂`", and let `ℛ`'s right interface answer the `i`-th read with the
   `i`-th bit of `Z_A`.  On `πPR¹π'` all three readings are `ZZ`; on `ℛπ'` all
   three are `Z_A`.  `D₁` returns `0` with probability `1` on both, so its
   advantage is `0` and the printed proof yields nothing.  That `π` is of course
   still ruled out — its `Z_A` lives in `{00, 11}` while `ℛ`'s is uniform on
   four values, which the fixed test "are the two bits of `Z_A` equal?"
   separates with advantage `1/2` — but that test depends on `π`, whereas the
   whole elegance of MauRen16's argument is that `D₁` does not.  The one-shot
   carrier is what makes the single universal `D₁` sufficient.

## The independence of the two honest parties is the whole content

`constructs_of_correlated_honest_pair` is the sharpness receipt: one converter
that samples a single `(k+1)`-bit string and hands it to *both* honest
interfaces constructs `PRᵏ⁺¹⟦` exactly, at `ε = 0`.  So Lemma 6 is precisely a
statement about `π` being "a pair of converters `πᴬ` and `πᴬ'`" (p. 14) held by
two parties with independent randomness — not about the amount of randomness in
the system.

## Distribution model

`PMF`, not the estate's `RandomSystems.Dist`.  `Dist` exists because the
H-technique needs sub-distributions (`RandomSystems.PDS`: "Mathlib's `PMF` is
the wrong model: it forces total mass `1`"); here total mass `1` is exactly
right, and what is needed instead is a monad with `bind_bind`/`map_bind`, which
`Dist` does not carry.
-/

namespace RandomSystemsCC.MauRen16

open scoped ENNReal Pointwise
open AbstractCrypto

universe u

/-! ## 1. Converters -/

/-- A **converter** on a boundary `Ω`: it reads the value the resource offers
there and answers with a (possibly randomized) value of the same kind.  This is
the one-shot read-only specialization of MauRen11's `Γ` discussed in the module
header. -/
def Converter (Ω : Type u) : Type u := Ω → PMF Ω

namespace Converter

variable {Ω : Type u}

noncomputable instance : One (Converter Ω) := ⟨fun x => PMF.pure x⟩

noncomputable instance : Mul (Converter Ω) := ⟨fun f g x => (g x).bind f⟩

@[simp] theorem one_apply (x : Ω) : (1 : Converter Ω) x = PMF.pure x := rfl

@[simp] theorem mul_apply (f g : Converter Ω) (x : Ω) : (f * g) x = (g x).bind f := rfl

noncomputable instance : Monoid (Converter Ω) where
  mul_assoc f g h := by
    funext x
    show (h x).bind (fun y => (g y).bind f) = ((h x).bind g).bind f
    exact (PMF.bind_bind _ _ _).symm
  one_mul f := by
    funext x
    show (f x).bind (fun y => PMF.pure y) = f x
    exact PMF.bind_pure _
  mul_one f := by
    funext x
    show (PMF.pure x).bind f = f x
    exact PMF.pure_bind _ _

/-- Attaching a converter to a resource is `bind`: sample the resource's
reading, then answer it. -/
noncomputable instance : MulAction (Converter Ω) (PMF Ω) where
  smul f μ := μ.bind f
  one_smul μ := PMF.bind_pure μ
  mul_smul _ _ _ := (PMF.bind_bind _ _ _).symm

theorem smul_def (f : Converter Ω) (μ : PMF Ω) : f • μ = μ.bind f := rfl

end Converter

/-! ## 2. Expectations of `ℝ≥0∞`-valued observables -/

/-- `𝔼_μ[G]` for a nonnegative observable.  Every probability below is the
expectation of an indicator-like observable, and the rewriting rules in this
section are all that the two bounds need. -/
noncomputable def expect {Ω : Type u} (μ : PMF Ω) (G : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, μ x * G x

namespace expect

variable {Ω Ω' : Type u}

theorem pure_eq (x : Ω) (G : Ω → ℝ≥0∞) : expect (PMF.pure x) G = G x := by
  rw [expect]
  refine (tsum_eq_single x fun y hy => ?_).trans ?_
  · simp [PMF.pure_apply, hy]
  · simp [PMF.pure_apply]

theorem bind_eq (μ : PMF Ω) (F : Ω → PMF Ω') (G : Ω' → ℝ≥0∞) :
    expect (μ.bind F) G = expect μ fun x => expect (F x) G := by
  simp only [expect, PMF.bind_apply]
  calc ∑' y : Ω', (∑' a : Ω, μ a * F a y) * G y
      = ∑' (y : Ω') (a : Ω), μ a * (F a y * G y) := by
        refine tsum_congr fun y => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun a => mul_assoc _ _ _
    _ = ∑' (a : Ω) (y : Ω'), μ a * (F a y * G y) := ENNReal.tsum_comm
    _ = ∑' a : Ω, μ a * ∑' y : Ω', F a y * G y :=
        tsum_congr fun a => ENNReal.tsum_mul_left

theorem map_eq (μ : PMF Ω) (φ : Ω → Ω') (G : Ω' → ℝ≥0∞) :
    expect (μ.map φ) G = expect μ fun x => G (φ x) := by
  rw [← PMF.bind_pure_comp, bind_eq]
  refine tsum_congr fun x => ?_
  show μ x * expect (PMF.pure (φ x)) G = μ x * G (φ x)
  rw [pure_eq]

theorem const_eq (μ : PMF Ω) (c : ℝ≥0∞) : expect μ (fun _ => c) = c := by
  simp only [expect, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem mono {μ : PMF Ω} {G G' : Ω → ℝ≥0∞} (h : ∀ x, G x ≤ G' x) :
    expect μ G ≤ expect μ G' :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

theorem le_of_forall_le {μ : PMF Ω} {G : Ω → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, G x ≤ c) :
    expect μ G ≤ c :=
  (mono h).trans_eq (const_eq μ c)

theorem congr_of_apply_eq_zero {μ : PMF Ω} {G G' : Ω → ℝ≥0∞}
    (h : ∀ x, μ x ≠ 0 → G x = G' x) : expect μ G = expect μ G' :=
  tsum_congr fun x => by
    by_cases hx : μ x = 0
    · simp [hx]
    · rw [h x hx]

theorem add_eq (μ : PMF Ω) (G G' : Ω → ℝ≥0∞) :
    expect μ G + expect μ G' = expect μ fun x => G x + G' x := by
  simp only [expect, mul_add]
  exact ENNReal.tsum_add.symm

end expect

/-! ## 3. The distinguishing pseudo-emetric

MauRen16 fn. 9: "`d(R,S) = sup_{D ∈ 𝒟} Δᴰ(R,S)`, where `Δᴰ(R,S)` is the absolute
value of the difference of the probability that `D` returns `0` when connected
to `R` and the probability that it returns `0` when connected to `S`".

`𝒟` is taken to be *all* randomized single-observation tests.  The paper only
requires that `𝒟` contain "the execution of basic algorithms giving inputs and
receiving outputs and performing equality checks, such as `D₁`"; taking every
such test makes `d` a pseudo-emetric with no side conditions, and the lower
bound proved below is witnessed by the paper's `D₁` alone. -/

/-- The probability that the randomized test `T` returns `0` on `μ`. -/
noncomputable def probZero {Ω : Type u} (T : Ω → PMF Bool) (μ : PMF Ω) : ℝ≥0∞ :=
  expect μ fun x => T x false

/-- The probability that the randomized test `T` returns `1` on `μ`. -/
noncomputable def probOne {Ω : Type u} (T : Ω → PMF Bool) (μ : PMF Ω) : ℝ≥0∞ :=
  expect μ fun x => T x true

theorem probZero_add_probOne {Ω : Type u} (T : Ω → PMF Bool) (μ : PMF Ω) :
    probZero T μ + probOne T μ = 1 := by
  rw [probZero, probOne, expect.add_eq]
  refine (expect.congr_of_apply_eq_zero (G' := fun _ => 1) fun x _ => ?_).trans
    (expect.const_eq μ 1)
  have h := (T x).tsum_coe
  rw [tsum_bool] at h
  show T x false + T x true = 1
  exact h

/-- MauRen16 fn. 9's `d`, on the read-only carrier: the supremum over randomized
tests of `|Pr[T = 0 | μ] − Pr[T = 0 | ν]|`, the absolute value written as the
join of the two truncated differences. -/
noncomputable def testDist {Ω : Type u} (μ ν : PMF Ω) : ℝ≥0∞ :=
  ⨆ T : Ω → PMF Bool, (probZero T μ - probZero T ν) ⊔ (probZero T ν - probZero T μ)

/-- The witness form used by the impossibility: a single test bounds `d` from
below.  This is where MauRen16's `D₁` enters. -/
theorem le_testDist {Ω : Type u} {μ ν : PMF Ω} (T : Ω → PMF Bool) :
    probZero T μ - probZero T ν ≤ testDist μ ν :=
  le_trans le_sup_left (le_iSup (fun T : Ω → PMF Bool =>
    (probZero T μ - probZero T ν) ⊔ (probZero T ν - probZero T μ)) T)

theorem testDist_comm {Ω : Type u} (μ ν : PMF Ω) : testDist μ ν = testDist ν μ :=
  iSup_congr fun _ => sup_comm _ _

noncomputable scoped instance instPseudoEMetricSpace {Ω : Type u} :
    PseudoEMetricSpace (PMF Ω) where
  edist := testDist
  edist_self μ := by simp [testDist]
  edist_comm := testDist_comm
  edist_triangle μ ν ρ := by
    refine iSup_le fun T => sup_le ?_ ?_
    · calc probZero T μ - probZero T ρ
          ≤ (probZero T μ - probZero T ν) + (probZero T ν - probZero T ρ) :=
            tsub_le_tsub_add_tsub
        _ ≤ testDist μ ν + testDist ν ρ := add_le_add (le_testDist T) (le_testDist T)
    · calc probZero T ρ - probZero T μ
          ≤ (probZero T ρ - probZero T ν) + (probZero T ν - probZero T μ) :=
            tsub_le_tsub_add_tsub
        _ ≤ testDist ν ρ + testDist μ ν :=
            add_le_add ((le_testDist T).trans_eq (testDist_comm ρ ν))
              ((le_testDist T).trans_eq (testDist_comm ν μ))
        _ = testDist μ ν + testDist ν ρ := add_comm _ _

theorem edist_eq_testDist {Ω : Type u} (μ ν : PMF Ω) : edist μ ν = testDist μ ν := rfl

/-! ## 4. The conditional guessing probability, on this file's `PMF` carrier

MauRen16's Appendix, *Min-entropy sampling*:

> `H_min(X|Y) = -log₂ max_f Pr[X = f(Y)]`, where the maximum ranges over all
> functions `f` from the alphabet `𝒴` of `Y` to the alphabet `𝒳` of `X`.  …
> Among them is a chain rule, which implies
>
>   `H_min(X|Y) ≥ H_min(X) - log₂ |𝒴|`.   (11)

**The entropy layer this section used to carry now lives at L2**, on the
library's own `Dist`, in `RandomSystems/Entropy.lean`
(`Dist.condGuessProb`, `Dist.minEntropy`, `Dist.condMinEntropy`, and eq. (11)
as `Dist.minEntropy_marginal_sub_logb_card_le_condMinEntropy`).  Per
`DESIGN.md` §12 there is exactly one copy of each, and it is not here.

What remains here is the `ℝ≥0∞`/`PMF` instance of the *guessing probability*
alone, because Lemma 6 consumes it on a carrier the finitely supported `Dist`
does not express: `𝒳 = ℕ` is infinite, and the guessing strategy is an
arbitrary `Converter ℕ`, i.e. a `PMF ℕ` with no finiteness assumption.  It
carries the same name as the L2 notion because it *is* the same notion, at a
different generality; the bound below is the same one-line argument as
`Dist.condGuessProb_le_card_mul_guessProb_marginal`.

The `e` prefix is mathlib's marker for the `ℝ≥0∞`-valued twin of a real-valued
quantity (`variance`/`evariance`, `Mathlib/Probability/Moments/Variance.lean`);
`econdGuessProb` is `Dist.condGuessProb` in that register. -/

/-- `2^{-H_min(X|Y)}`: the optimal probability of guessing the first component
from the second, on `PMF` — the `ℝ≥0∞` instance of
`RandomSystems.Dist.condGuessProb`.  MauRen16 maximizes over deterministic
guessing functions `f : 𝒴 → 𝒳`; the supremum here is over *randomized*
strategies `𝒴 → PMF 𝒳`, which is the same number and is the form Lemma 6
consumes, since the converter `π'` that does the guessing is itself
probabilistic. -/
noncomputable def econdGuessProb {α γ : Type u} (μ : PMF (α × γ)) : ℝ≥0∞ :=
  ⨆ s : γ → PMF α, ∑' x : α × γ, μ x * s x.2 x.1

/-- The `X`-marginal of a joint law. -/
noncomputable def marginalFst {α γ : Type u} (μ : PMF (α × γ)) : PMF α :=
  μ.map Prod.fst

theorem marginalFst_apply {α γ : Type u} (μ : PMF (α × γ)) (a : α) :
    marginalFst μ a = ∑' c, μ (a, c) := by
  rw [marginalFst, PMF.map_apply, ENNReal.tsum_prod']
  refine (tsum_eq_single a fun a' ha' => ?_).trans (tsum_congr fun c => if_pos rfl)
  exact ENNReal.tsum_eq_zero.mpr fun c => if_neg fun h => ha' h.symm

theorem apply_le_marginalFst {α γ : Type u} (μ : PMF (α × γ)) (a : α) (c : γ) :
    μ (a, c) ≤ marginalFst μ a :=
  (marginalFst_apply μ a).symm ▸ ENNReal.le_tsum c

/-- **MauRen16 eq. (11)**, `H_min(X|Y) ≥ H_min(X) - log₂ |𝒴|`, in its
exponentiated — and therefore edge-case-free — form
`2^{-H_min(X|Y)} ≤ |𝒴| · 2^{-H_min(X)}`.  The logarithmic form is
`RandomSystems.Dist.minEntropy_marginal_sub_logb_card_le_condMinEntropy`, at L2.

The proof is the one line the paper's "conditioning on `k` bits cannot decrease
the min-entropy by more than `k` bits" abbreviates: on each `y` a guess is right
with probability at most `max_x Pr[X = x]`, and there are `|𝒴|` values of `y`. -/
theorem econdGuessProb_le_card_mul_iSup {α γ : Type u} [Fintype γ] (μ : PMF (α × γ)) :
    econdGuessProb μ ≤ (Fintype.card γ : ℝ≥0∞) * ⨆ a, marginalFst μ a := by
  refine iSup_le fun s => ?_
  calc ∑' x : α × γ, μ x * s x.2 x.1
      = ∑' (c : γ) (a : α), μ (a, c) * s c a := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ ≤ ∑' _ : γ, ⨆ a, marginalFst μ a := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        calc ∑' a : α, μ (a, c) * s c a
            ≤ ∑' a : α, (⨆ a', marginalFst μ a') * s c a :=
              ENNReal.tsum_le_tsum fun a =>
                mul_le_mul' ((apply_le_marginalFst μ a c).trans (le_iSup _ a)) le_rfl
          _ = (⨆ a', marginalFst μ a') * ∑' a : α, s c a := ENNReal.tsum_mul_left
          _ = ⨆ a', marginalFst μ a' := by rw [(s c).tsum_coe, mul_one]
    _ = (Fintype.card γ : ℝ≥0∞) * ⨆ a, marginalFst μ a := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 5. The two-honest-one-dishonest boundary and its resources -/

/-- The boundary of MauRen16 §5's resources: what `A`, `A'` and `E` read.  The
honest alphabet is `ℕ` (bit strings by value — `D₁` only tests equality); Eve's
is `PRᵏ`'s own `k`-bit register, which no left-interface constructor touches. -/
abbrev Boundary (k : ℕ) : Type := ℕ × ℕ × Fin (2 ^ k)

/-- `PRᵏ`, MauRen16 §5: "public randomness of size `k`.  The resource chooses
`Z` uniformly at random from the set `{0,1}ᵏ` of `k`-bit strings.  Any party can
read `Z`" — so all three interfaces read the same uniform `Z`. -/
noncomputable def PR (k : ℕ) : PMF (Boundary k) :=
  (PMF.uniformOfFintype (Fin (2 ^ k))).map fun z : Fin (2 ^ k) => ((z.val, z.val, z) : Boundary k)

/-- `PRᵏ⁺¹` *as seen at `PRᵏ`'s boundary*: the honest interfaces read one
uniform `(k+1)`-bit string, and the right register is constant.

Only `PRᵏ⁺¹⊣` is ever used — the membership condition of `ℛ⟦` constrains the
*blocked* resource, which has no right interface (MauRen16 §3.4) — and blocking
replaces the right register by a constant, so this stands for the genuine
`PRᵏ⁺¹` of any wider carrier.  `mem_outboundHull_iff_map_eq` shows the resulting
specification depends on the honest marginal alone. -/
noncomputable def PRsucc (k : ℕ) : PMF (Boundary k) :=
  (PMF.uniformOfFintype (Fin (2 ^ (k + 1)))).map
    fun z : Fin (2 ^ (k + 1)) => ((z.val, z.val, 0) : Boundary k)

/-- MauRen16 p. 14: a constructor "corresponds to a converter `π` for the left
interface, understood as a pair of converters `πᴬ` and `πᴬ'` for the two honest
parties".  Two parties, hence two *independent* sources of randomness — which
`constructs_of_correlated_honest_pair` shows is the whole content of Lemma 6. -/
noncomputable def honestPair (k : ℕ) (f g : Converter ℕ) : Converter (Boundary k) :=
  fun x => (f x.1).bind fun a => (g x.2.1).map fun b => (a, b, x.2.2)

/-- Eve's converters, acting on the right register only. -/
noncomputable def eveLift (k : ℕ) : Converter (Fin (2 ^ k)) →* Converter (Boundary k) where
  toFun e := fun x => (e x.2.2).map fun c => (x.1, x.2.1, c)
  map_one' := by
    funext x
    show ((1 : Converter (Fin (2 ^ k))) x.2.2).map _ = PMF.pure x
    rw [Converter.one_apply, PMF.pure_map]
  map_mul' e e' := by
    funext x
    show ((e' x.2.2).bind e).map _ = ((e' x.2.2).map _).bind _
    rw [PMF.map_bind, PMF.bind_map]
    rfl

/-- MauRen16 §3.4's `Σ` for this boundary: the converters a dishonest `E` may
apply at the right interface. -/
noncomputable def eveConverters (k : ℕ) : Submonoid (Converter (Boundary k)) :=
  MonoidHom.mrange (eveLift k)

/-- MauRen16 §3.4's blocking converter `⊣`: it shuts the right interface by
answering it with a constant. -/
noncomputable def blockRight (k : ℕ) : Converter (Boundary k) :=
  eveLift k fun _ => PMF.pure 0

theorem blockRight_mul_of_mem {k : ℕ} {β : Converter (Boundary k)}
    (hβ : β ∈ eveConverters k) : blockRight k * β = blockRight k := by
  rw [eveConverters, MonoidHom.mem_mrange] at hβ
  obtain ⟨e, rfl⟩ := hβ
  rw [blockRight, ← map_mul]
  congr 1
  funext c
  exact PMF.bind_const _ _

/-- **Every resource on this boundary is right-outbound.**  MauRen16 §3.4 calls
`R` right-outbound when no converter attached to the right interface can have an
effect at the left one; on a read-only boundary that holds automatically, so
`ℛ⟦` reduces to "agrees with `ℛ` at the honest interfaces, arbitrary at Eve's" —
exactly the leakage-tolerant class the paper wants, since `ℛ⟦` "includes all
resources that leak partial or all information about Alice's queries to Eve"
(p. 9). -/
theorem rightOutbound_all (k : ℕ) (S : PMF (Boundary k)) :
    Relaxation.RightOutbound (eveConverters k) (blockRight k) S :=
  fun _ hβ => by rw [blockRight_mul_of_mem hβ]

/-- Blocking the right interface keeps the honest readings and zeroes Eve's. -/
theorem blockRight_smul (k : ℕ) (S : PMF (Boundary k)) :
    blockRight k • S = S.map fun x => (x.1, x.2.1, 0) := by
  rw [Converter.smul_def, ← PMF.bind_pure_comp]
  congr 1
  funext x
  show ((PMF.pure (0 : Fin (2 ^ k))).map fun c => (x.1, x.2.1, c)) = _
  rw [PMF.pure_map]
  rfl

/-- MauRen16 §3.4's `ℛ⟦` at `ℛ = {PRᵏ⁺¹}`, unfolded: membership says exactly
that the honest marginal is `PRᵏ⁺¹`'s, Eve's interface being unconstrained. -/
theorem mem_outboundHull_iff_map_eq (k : ℕ) (S : PMF (Boundary k)) :
    S ∈ Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k} ↔
      (S.map fun x => (x.1, x.2.1, 0)) = PRsucc k := by
  have hPR : ((PRsucc k).map fun x => (x.1, x.2.1, 0)) = PRsucc k := by
    rw [PRsucc, PMF.map_comp]
    rfl
  rw [Relaxation.mem_outboundHull_iff, Set.smul_set_singleton, Set.mem_singleton_iff,
    blockRight_smul, blockRight_smul, hPR]
  exact ⟨fun h => h.2, fun h => ⟨rightOutbound_all k S, h⟩⟩

/-- Non-vacuity: `PRᵏ⁺¹` itself lies in `PRᵏ⁺¹⟦`, so the specification Lemma 6
rules out is not empty. -/
theorem PRsucc_mem_outboundHull (k : ℕ) :
    PRsucc k ∈ Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k} := by
  rw [mem_outboundHull_iff_map_eq, PRsucc, PMF.map_comp]
  rfl

/-! ## 6. MauRen16's distinguisher `D₁` and the two probability bounds -/

/-- **MauRen16 p. 14, Distinguisher `D₁`**:

> read the `(k+1)`-bit strings `Z_A` and `Z_A'` from the left interface;
> read the `(k+1)`-bit string `Z_E` from the right interface;
> **if** `Z_A ≠ Z_A'` **then** return `0`; halt;
> **else if** `Z_A ≠ Z_E` **then** return `1`; halt;
> return `0`

with `π'` inlined: `Z_E` is obtained by running `g = πᴬ'` on the right register,
which is what the paper's `π'` does — "`π'` answers a query by `E` in the same
way as `π` would answer a query by `A'`".  The paper first appends `π'` to both
resources and then invokes non-expansion of `d` to return to the original pair;
inlining it into the test performs that step once, and it is what keeps Eve's
interface at its own `k`-bit type. -/
noncomputable def D1 (k : ℕ) (g : Converter ℕ) : Boundary k → PMF Bool :=
  fun x => if x.1 = x.2.1 then (g (x.2.2 : ℕ)).map fun e => decide (x.1 ≠ e) else PMF.pure false

theorem D1_apply_false (k : ℕ) (g : Converter ℕ) (x : Boundary k) :
    D1 k g x false = if x.1 = x.2.1 then g (x.2.2 : ℕ) x.1 else 1 := by
  rw [D1]
  split
  · rw [PMF.map_apply]
    refine (tsum_eq_single x.1 fun e he => if_neg ?_).trans (if_pos ?_)
    · simpa using fun h => he h.symm
    · simp
  · simp

theorem D1_apply_true (k : ℕ) (g : Converter ℕ) (x : Boundary k) :
    D1 k g x true =
      if x.1 = x.2.1 then ∑' e, g (x.2.2 : ℕ) e * (if x.1 = e then 0 else 1) else 0 := by
  rw [D1]
  split
  · rw [PMF.map_apply]
    refine tsum_congr fun e => ?_
    by_cases h : x.1 = e <;> simp [h]
  · simp

/-- `x(1-x) ≤ 1/4` — MauRen16 p. 14's "`1/4` is the maximum of the function
`x ↦ x(1-x)` for `0 ≤ x ≤ 1`" — in the subtraction-free shape the proof
produces: the two complementary masses add up to `1`. -/
theorem mul_le_quarter_of_add_eq_one {u v : ℝ≥0∞} (h : u + v = 1) : u * v ≤ 1 / 4 := by
  have hu : u ≠ ⊤ := by intro h'; rw [h'] at h; simp at h
  have hv : v ≠ ⊤ := by intro h'; rw [h'] at h; simp at h
  refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp ?_
  have h2 : u.toReal + v.toReal = 1 := by rw [← ENNReal.toReal_add hu hv, h]; simp
  rw [ENNReal.toReal_mul, show ((1 : ℝ≥0∞) / 4).toReal = 1 / 4 by simp]
  nlinarith [ENNReal.toReal_nonneg (a := u), ENNReal.toReal_nonneg (a := v),
    sq_nonneg (u.toReal - v.toReal)]

theorem quarter_add_three_quarter : (3 : ℝ≥0∞) / 4 + 1 / 4 = 1 := by
  refine (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp
  norm_num

/-- **The real side.**  "Hence `D₁` returns `0` with probability at least `3/4`"
(MauRen16 p. 14).

Conditioned on `Z` and on `πᴬ`'s output `a`, the two remaining readings are
independent draws from `πᴬ'`'s law, so the probability of `Z_A = Z_A' ≠ Z_E` is
`u · v` with `u + v = 1`, hence at most `1/4`.  See finding 1 in the module
header: the paper's own displayed identity for this step does not hold. -/
theorem real_probZero (k : ℕ) (f g : Converter ℕ) :
    3 / 4 ≤ probZero (D1 k g) (honestPair k f g • PR k) := by
  have key : probOne (D1 k g) (honestPair k f g • PR k) ≤ 1 / 4 := by
    rw [probOne, Converter.smul_def, expect.bind_eq, PR, expect.map_eq]
    refine expect.le_of_forall_le fun z => ?_
    rw [honestPair, expect.bind_eq]
    refine expect.le_of_forall_le fun a => ?_
    rw [expect.map_eq]
    have hsplit : expect (g z.val) (fun b => D1 k g ((a, b, z) : Boundary k) true)
        = (∑' b, g z.val b * (if a = b then 1 else 0)) *
          ∑' e, g z.val e * (if a = e then 0 else 1) := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun b => ?_
      show g z.val b * D1 k g ((a, b, z) : Boundary k) true
        = g z.val b * (if a = b then 1 else 0) * ∑' e, g z.val e * (if a = e then 0 else 1)
      rw [D1_apply_true]
      by_cases h : a = b <;> simp [h]
    rw [hsplit]
    refine mul_le_quarter_of_add_eq_one ?_
    rw [← ENNReal.tsum_add]
    refine (tsum_congr fun b => ?_).trans (g z.val).tsum_coe
    rw [← mul_add]
    by_cases h : a = b <;> simp [h]
  have hsum := probZero_add_probOne (D1 k g) (honestPair k f g • PR k)
  rw [ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (by finiteness) key) hsum]
  refine le_trans (le_of_eq ?_) (tsub_le_tsub_left key 1)
  exact (ENNReal.sub_eq_of_eq_add (by finiteness) quarter_add_three_quarter.symm).symm

/-! ### The ideal side -/

theorem le_map_apply {α β : Type u} (μ : PMF α) (φ : α → β) (a : α) :
    μ a ≤ (μ.map φ) (φ a) := by
  rw [PMF.map_apply]
  exact le_trans (le_of_eq (if_pos rfl).symm) (ENNReal.le_tsum a)

/-- If `μ` factors through an injective `φ`, no atom of the image is heavier
than the heaviest atom of `μ`. -/
theorem map_apply_le_of_injective {α β : Type u} {φ : α → β} (hφ : Function.Injective φ)
    (μ : PMF α) {c : ℝ≥0∞} (h : ∀ a, μ a ≤ c) (b : β) : (μ.map φ) b ≤ c := by
  rw [PMF.map_apply]
  by_cases hb : ∃ a, b = φ a
  · obtain ⟨a, rfl⟩ := hb
    rw [tsum_eq_single a fun a' ha' => if_neg fun hEq => ha' (hφ hEq).symm, if_pos rfl]
    exact h a
  · rw [ENNReal.tsum_eq_zero.mpr fun a => if_neg fun hEq => hb ⟨a, hEq⟩]
    exact zero_le c

theorem PRsucc_apply_of_ne (k : ℕ) {a b : ℕ} (h : a ≠ b) (c : Fin (2 ^ k)) :
    PRsucc k (a, b, c) = 0 := by
  rw [PRsucc, PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun z => if_neg fun hEq => h ?_
  simp only [Prod.mk.injEq] at hEq
  exact hEq.1.trans hEq.2.1.symm

theorem marginalFst_le (k : ℕ) {S : PMF (Boundary k)}
    (hS : (S.map fun x => (x.1, x.2.1, 0)) = PRsucc k) (a : ℕ) :
    (S.map Prod.fst) a ≤ ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  have hmap : S.map Prod.fst
      = (PMF.uniformOfFintype (Fin (2 ^ (k + 1)))).map fun z : Fin (2 ^ (k + 1)) => z.val := by
    have hfst : S.map Prod.fst
        = (S.map fun x : Boundary k => ((x.1, x.2.1, 0) : Boundary k)).map Prod.fst := by
      rw [PMF.map_comp]; rfl
    refine hfst.trans ((congrArg (PMF.map Prod.fst) hS).trans ?_)
    rw [PRsucc, PMF.map_comp]; rfl
  rw [hmap]
  refine map_apply_le_of_injective Fin.val_injective _ (fun z => ?_) a
  rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
  push_cast
  exact le_rfl

/-- **The ideal side.**  "`Z_A = Z_A'` holds by definition of `ℛ`, and `Z_A` is a
uniformly random `(k+1)`-bit string, whereas `Z_E` is a `(k+1)`-bit string
computed by `π'`. … `Z_E` depends on a string `W` of length at most `k`. …
`Pr[Z_A = Z_E] ≤ 2^{-H_min(Z_A|W)}` … `H_min(Z_A|W) ≥ H_min(Z_A) − k = 1`.  We
conclude that `Pr[Z_A = Z_E] ≤ 1/2`.  Hence, when connected to `ℛπ'`, `D₁`
returns `0` with probability at most `1/2`" (MauRen16 pp. 14–15). -/
theorem ideal_probZero (k : ℕ) (g : Converter ℕ) {S : PMF (Boundary k)}
    (hS : S ∈ Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k}) :
    probZero (D1 k g) S ≤ 1 / 2 := by
  rw [mem_outboundHull_iff_map_eq] at hS
  have hdiag : ∀ x : Boundary k, S x ≠ 0 → x.1 = x.2.1 := by
    intro x hx
    by_contra hne
    refine hx (le_antisymm ?_ (zero_le _))
    have h2 := DFunLike.congr_fun hS ((x.1, x.2.1, 0) : Boundary k)
    rw [PRsucc_apply_of_ne k hne 0] at h2
    exact le_trans (le_map_apply S _ x) (le_of_eq h2)
  have step1 : probZero (D1 k g) S = expect S fun x => g (x.2.2 : ℕ) x.1 := by
    rw [probZero]
    exact expect.congr_of_apply_eq_zero fun x hx => by
      rw [D1_apply_false, if_pos (hdiag x hx)]
  have step2 : expect S (fun x => g (x.2.2 : ℕ) x.1)
      ≤ econdGuessProb (S.map fun x : Boundary k => (x.1, x.2.2)) := by
    rw [← expect.map_eq S (fun x : Boundary k => (x.1, x.2.2))
      (fun y : ℕ × Fin (2 ^ k) => g (y.2 : ℕ) y.1)]
    exact le_iSup (fun s : Fin (2 ^ k) → PMF ℕ =>
      ∑' y : ℕ × Fin (2 ^ k), (S.map fun x : Boundary k => (x.1, x.2.2)) y * s y.2 y.1)
      (fun c => g (c : ℕ))
  have step4 : marginalFst (S.map fun x : Boundary k => (x.1, x.2.2)) = S.map Prod.fst := by
    rw [marginalFst, PMF.map_comp]; rfl
  calc probZero (D1 k g) S = expect S fun x => g (x.2.2 : ℕ) x.1 := step1
    _ ≤ econdGuessProb (S.map fun x : Boundary k => (x.1, x.2.2)) := step2
    _ ≤ (Fintype.card (Fin (2 ^ k)) : ℝ≥0∞) *
          ⨆ a, marginalFst (S.map fun x : Boundary k => (x.1, x.2.2)) a :=
        econdGuessProb_le_card_mul_iSup _
    _ ≤ (Fintype.card (Fin (2 ^ k)) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
        refine mul_le_mul' le_rfl ?_
        rw [step4]
        exact iSup_le (marginalFst_le k hS)
    _ = 1 / 2 := by
        simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
          ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
        simp

/-! ## 7. Lemma 6 -/

/-- The distinguishing advantage of MauRen16's `D₁` between `πPRᵏ` and any
member of `PRᵏ⁺¹⟦`, from the two bounds: `3/4 − 1/2 = 1/4`. -/
theorem quarter_le_edist (k : ℕ) (f g : Converter ℕ) {S : PMF (Boundary k)}
    (hS : S ∈ Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k}) :
    1 / 4 ≤ edist (honestPair k f g • PR k) S := by
  rw [edist_eq_testDist]
  refine le_trans (le_of_eq ?_) (le_trans (tsub_le_tsub (real_probZero k f g)
    (ideal_probZero k g hS)) (le_testDist (D1 k g)))
  refine (ENNReal.sub_eq_of_eq_add (by finiteness) ?_).symm
  refine (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp
  norm_num

/-- **MauRen16 Lemma 6.**  "Let `k ∈ ℕ` and `ε < 1/4`.  Then `PRᵏ ↛ PRᵏ⁺¹⟦ᵋ`."

A negation of an existential over all constructors: for *every* pair of
converters `f = πᴬ`, `g = πᴬ'` held by the two honest parties, `πPRᵏ` is more
than `ε` away from every right-outbound resource that agrees with `PRᵏ⁺¹` at the
honest interfaces, however much it leaks to Eve.  The single witness is the
paper's `D₁`. -/
theorem lemma6 (k : ℕ) {ε : ℝ≥0∞} (hε : ε < 1 / 4) (f g : Converter ℕ) :
    ¬ Constructs (honestPair k f g) ({PR k} : Set (PMF (Boundary k)))
      (Relaxation.eball ε
        (Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k})) := by
  intro h
  obtain ⟨S, hS, hd⟩ :=
    Relaxation.mem_eball_iff.mp (h (Set.smul_mem_smul_set rfl))
  exact absurd ((quarter_le_edist k f g hS).trans hd) (not_le.mpr hε)

/-! ## 8. Sharpness: the two honest parties' independence is the whole content -/

/-- A single converter that samples one `(k+1)`-bit string and hands it to *both*
honest interfaces.  This is not a legal constructor in MauRen16's model — `πᴬ`
and `πᴬ'` are held by two different parties (p. 14) — but it is a legal
converter for the pair of honest interfaces taken together. -/
noncomputable def correlatedHonest (k : ℕ) : Converter (Boundary k) :=
  fun x => (PMF.uniformOfFintype (Fin (2 ^ (k + 1)))).map
    fun z : Fin (2 ^ (k + 1)) => ((z.val, z.val, x.2.2) : Boundary k)

/-- **Sharpness of Lemma 6.**  With shared honest randomness, `PRᵏ` constructs
`PRᵏ⁺¹⟦` *exactly* — at `ε = 0`, for every `k`.  So Lemma 6 is precisely a
statement about the constructor being a pair of independently randomized
converters, and not about the amount of randomness available in the system. -/
theorem constructs_of_correlated_honest_pair (k : ℕ) :
    Constructs (correlatedHonest k) ({PR k} : Set (PMF (Boundary k)))
      (Relaxation.outboundHull (eveConverters k) (blockRight k) {PRsucc k}) := by
  show correlatedHonest k • ({PR k} : Set (PMF (Boundary k))) ⊆ _
  rw [Set.smul_set_singleton, Set.singleton_subset_iff, mem_outboundHull_iff_map_eq,
    Converter.smul_def, PMF.map_bind]
  refine Eq.trans ?_ (PMF.bind_const (PR k) (PRsucc k))
  congr 1
  funext x
  rw [correlatedHonest, PMF.map_comp, PRsucc]
  rfl

end RandomSystemsCC.MauRen16
