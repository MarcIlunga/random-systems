/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.AdvantageSeq
import RandomSystems.Complexity.ConverterBridge
import RandomSystems.Complexity.IidGames

/-!
# Boneh-Shoup chapter 3: PRG and stream-cipher games

Attack Game 3.1 is a one-sample distinguishing game: the adversary receives
either `G s` for random seed `s`, or a random output pad.  The stream-cipher
proof in Theorem 3.1 is the corresponding converter proof: map the received pad
to the ciphertext `mask pad m`, use the PRG bound on both message branches, and
use the one-time-pad/random-pad fact in the middle game.
-/

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)
open scoped BigOperators NNReal

noncomputable section

universe u v w z

namespace PRG

variable {Seed : Type u} {Pad : Type v}

/-- Boneh-Shoup Attack Game 3.1, Experiment 0: sample a seed and output `G s`. -/
def real (G : Seed → Pad) (seedDist : Dist Seed) : PFunPDS Unit Pad :=
  sampleSystem (Dist.fTransform G seedDist)

/-- Boneh-Shoup Attack Game 3.1, Experiment 1: output a random pad. -/
def random (padDist : Dist Pad) : PFunPDS Unit Pad :=
  sampleSystem padDist

/-- The two-experiment PRG distinguishing game. -/
def distinguishing (G : Seed → Pad) (seedDist : Dist Seed) (padDist : Dist Pad) :
    DistinguishingGame Unit Pad :=
  (real G seedDist, random padDist)

/-- The bit-guessing recast of Attack Game 3.1. -/
def bitGuessGame (G : Seed → Pad) (seedDist : Dist Seed) (padDist : Dist Pad) :
    BitGuessGame Unit Pad :=
  distinguishingAsBitGuess (distinguishing G seedDist padDist)

/-- The CR18 signed maximal PRG advantage. -/
abbrev Advantage (G : Seed → Pad) (seedDist : Dist Seed) (padDist : Dist Pad) : ℝ :=
  Δ(real G seedDist, random padDist)

namespace NextBit

/-- Fixed-length PRG outputs for Boneh-Shoup Attack Game 3.2. -/
abbrev Output (L : Nat) : Type :=
  Fin L → Bool

/-- The prefix visible before predicting bit `i`.  The type enforces that the
predictor cannot inspect the challenge bit or later bits. -/
abbrev PrefixView {L : Nat} (i : Fin L) : Type :=
  {j : Fin L // j.val < i.val} → Bool

def viewPrefix {L : Nat} (r : Output L) (i : Fin L) : PrefixView i :=
  fun j => r j.1

def prefixFromRest {L : Nat} (i : Fin L)
    (rest : {j : Fin L // j ≠ i} → Bool) : PrefixView i :=
  fun j => rest ⟨j.1, by
    intro h
    have hval : j.1.val = i.val := congrArg Fin.val h
    omega⟩

/-- Boneh-Shoup Attack Game 3.2 adversary: choose the next-bit index first,
then guess from the strict prefix. -/
structure Adversary (L : Nat) where
  index : Fin L
  guess : PrefixView index → Bool

def wins {L : Nat} (A : Adversary L) (r : Output L) : Bool :=
  A.guess (viewPrefix r A.index) == r A.index

/-- The literal statistical test: accept when the next-bit prediction succeeds. -/
def successTest {L : Nat} (A : Adversary L) : SampleSolver (Output L) :=
  fun r => wins A r

/-- The same wrapper with the verdict bit flipped, used for CR18's signed
orientation `∆(S,T)=Pr[T]-Pr[S]`. -/
def failureTest {L : Nat} (A : Adversary L) : SampleSolver (Output L) :=
  fun r => !wins A r

noncomputable def successDistinguisher {L : Nat} (A : Adversary L) :
    DistinguisherSolver Unit (Output L) :=
  pointDistinguisher (sampleDDD (successTest A))

noncomputable def failureDistinguisher {L : Nat} (A : Adversary L) :
    DistinguisherSolver Unit (Output L) :=
  pointDistinguisher (sampleDDD (failureTest A))

/-- Winning probability in Attack Game 3.2 against an output distribution. -/
noncomputable def predictionProb {L : Nat} (A : Adversary L)
    (D : Dist (Output L)) : NNReal :=
  D.mass (fun r => wins A r = true)

def boolGraphEquiv {A : Type*} (g : A → Bool) :
    A ≃ {p : Bool × A // g p.2 = p.1} where
  toFun a := ⟨(g a, a), rfl⟩
  invFun p := p.1.2
  left_inv := by
    intro a
    rfl
  right_inv := by
    rintro ⟨⟨b, a⟩, h⟩
    dsimp at h ⊢
    subst b
    rfl

/-- A uniform independent bit equals any function of the side information with
probability exactly `1/2`. -/
theorem uniform_bool_graph_mass {A : Type*} [Fintype A] [Nonempty A]
    (g : A → Bool) :
    (Dist.prod (Dist.uniform Bool) (Dist.uniform A)).mass
        (fun p : Bool × A => g p.2 = p.1) =
      (1 : NNReal) / 2 := by
  classical
  rw [Dist.prod_uniform]
  rw [Dist.uniform_mass_eq_card_filter]
  have hfilter : ((Finset.univ : Finset (Bool × A)).filter
      (fun p : Bool × A => g p.2 = p.1)).card = Fintype.card A := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (boolGraphEquiv g).symm
  rw [hfilter, Fintype.card_prod, Fintype.card_bool]
  field_simp [Nat.cast_ne_zero.mpr (Fintype.card_pos (α := A)).ne']
  rw [Nat.cast_mul]
  ring

theorem predictionProb_uniform {L : Nat} (A : Adversary L) :
    predictionProb A (Dist.uniform (Output L)) = (1 : NNReal) / 2 := by
  classical
  let split := Equiv.piSplitAt A.index (fun _ : Fin L => Bool)
  let sideGuess : ({j : Fin L // j ≠ A.index} → Bool) → Bool :=
    fun rest => A.guess (prefixFromRest A.index rest)
  unfold predictionProb
  rw [show (Dist.uniform (Output L)).mass (fun r => wins A r = true) =
      (Dist.uniform (Output L)).mass (fun r => sideGuess (split r).2 = (split r).1) by
    apply Dist.mass_congr
    intro r
    have hprefix : viewPrefix r A.index =
        prefixFromRest A.index (fun j => r j.1) := by
      funext j
      rfl
    simp [wins, sideGuess, split, hprefix, Equiv.piSplitAt_apply]]
  rw [← Dist.mass_fTransform (f := split) (X := Dist.uniform (Output L))
    (P := fun p : Bool × ({j : Fin L // j ≠ A.index} → Bool) =>
      sideGuess p.2 = p.1)]
  rw [Dist.fTransform_equiv_uniform, ← Dist.prod_uniform]
  exact uniform_bool_graph_mass sideGuess

theorem verdictProb_success_sampleSystem {L : Nat} (A : Adversary L)
    (D : Dist (Output L)) :
    verdictProb (successDistinguisher A) (sampleSystem D) =
      predictionProb A D := by
  unfold successDistinguisher successTest predictionProb
  rw [verdictProb_sampleDDD_sampleSystem]

theorem verdictProb_failure_sampleSystem {L : Nat} (A : Adversary L)
    {D : Dist (Output L)} (hD : D.isProbDist) :
    (verdictProb (failureDistinguisher A) (sampleSystem D) : ℝ) =
      1 - (predictionProb A D : ℝ) := by
  classical
  unfold failureDistinguisher failureTest
  rw [verdictProb_sampleDDD_sampleSystem]
  have hcomp : D.mass (fun a => (!wins A a) = true) =
      D.mass (fun a => ¬ wins A a = true) := by
    apply Dist.mass_congr
    intro a
    cases wins A a <;> simp
  rw [hcomp]
  have hsum := Dist.mass_add_compl D (fun a => wins A a = true)
  rw [hD] at hsum
  unfold predictionProb
  have hsumR : (D.mass (fun a => wins A a = true) : ℝ) +
      (D.mass (fun a => ¬ wins A a = true) : ℝ) = 1 := by
    exact_mod_cast hsum
  linarith

/-- The literal success test realizes the lower signed next-bit bias as a PRG
distinguishing advantage. -/
theorem success_advantage {Seed : Type u} {L : Nat}
    (G : Seed → Output L) (seedDist : Dist Seed) (A : Adversary L) :
    advantage (successDistinguisher A)
      (real G seedDist) (random (Dist.uniform (Output L))) =
      (1 / 2 : ℝ) - (predictionProb A (Dist.fTransform G seedDist) : ℝ) := by
  unfold real random advantage
  rw [verdictProb_success_sampleSystem, verdictProb_success_sampleSystem,
    predictionProb_uniform]
  norm_num

/-- The flipped test realizes the upper signed next-bit bias as a PRG
distinguishing advantage.  The seed distribution is typed as a probability
distribution, so the complement calculation has no extra probability hypothesis. -/
theorem failure_advantage {Seed : Type u} {L : Nat}
    (G : Seed → Output L) (seedDist : Dist.ProbDist Seed) (A : Adversary L) :
    advantage (failureDistinguisher A)
      (real G seedDist.val) (random (Dist.uniform (Output L))) =
      (predictionProb A (Dist.fTransform G seedDist.val) : ℝ) - (1 / 2 : ℝ) := by
  have hReal : (Dist.fTransform G seedDist.val).isProbDist := by
    unfold Dist.isProbDist
    rw [Dist.weight_fTransform, seedDist.property]
  unfold real random advantage
  rw [verdictProb_failure_sampleSystem A hReal]
  rw [verdictProb_failure_sampleSystem A Dist.uniform_isProbDist]
  rw [predictionProb_uniform]
  norm_num [NNReal.coe_div]
  ring_nf

theorem lowBias_le_prg_advantage {Seed : Type u} {L : Nat}
    (G : Seed → Output L) (seedDist : Dist Seed) (A : Adversary L) :
    (1 / 2 : ℝ) - (predictionProb A (Dist.fTransform G seedDist) : ℝ) ≤
      Δ(real G seedDist, random (Dist.uniform (Output L))) := by
  rw [← success_advantage G seedDist A]
  exact advantage_le_maxAdvantage (successDistinguisher A)
    (real G seedDist) (random (Dist.uniform (Output L)))
    (pointDistinguisher_isProbDist (sampleDDD (successTest A)))

theorem highBias_le_prg_advantage {Seed : Type u} {L : Nat}
    (G : Seed → Output L) (seedDist : Dist.ProbDist Seed) (A : Adversary L) :
    (predictionProb A (Dist.fTransform G seedDist.val) : ℝ) - (1 / 2 : ℝ) ≤
      Δ(real G seedDist.val, random (Dist.uniform (Output L))) := by
  rw [← failure_advantage G seedDist A]
  exact advantage_le_maxAdvantage (failureDistinguisher A)
    (real G seedDist.val) (random (Dist.uniform (Output L)))
    (pointDistinguisher_isProbDist (sampleDDD (failureTest A)))

namespace DistinguisherPredictor

variable {Side : Type u}

def predictorOutput (d : Side × Bool → Bool) (xb : Side × Bool) (r : Bool) : Bool :=
  if d (xb.1, r) then r else !r

/-- Boneh-Shoup Lemma 3.5 predictor success probability.  The sample is
`(x,b) ← D`, with an independent fresh uniform bit `r`; the predictor returns
`r` when `d (x,r)` accepts, and `!r` otherwise. -/
def winProb (d : Side × Bool → Bool) (D : Dist (Side × Bool)) : NNReal :=
  (Dist.prod D (Dist.uniform Bool)).mass (fun p : (Side × Bool) × Bool =>
    predictorOutput d p.1 p.2 = p.1.2)

/-- Boneh-Shoup Lemma 3.5 signed gap
`Pr[d(x,b)=1] - Pr[d(x,r)=1]`, where `r` is fresh and independent. -/
def gap (d : Side × Bool → Bool) (D : Dist (Side × Bool)) : ℝ :=
  (D.mass (fun xb => d xb = true) : ℝ) -
    ((Dist.prod D (Dist.uniform Bool)).mass
      (fun p : (Side × Bool) × Bool => d (p.1.1, p.2) = true) : ℝ)

theorem lemma35 (d : Side × Bool → Bool) {D : Dist (Side × Bool)}
    (hD : D.isProbDist) :
    (winProb d D : ℝ) = (1 / 2 : ℝ) + gap d D := by
  classical
  let winNN : Side × Bool → ℝ≥0 → ℝ≥0 := fun xb w =>
    w * ((if d xb = true then (1 : NNReal) else 0) +
      (if d (xb.1, !xb.2) = false then (1 : NNReal) else 0)) / 2
  let actualNN : Side × Bool → ℝ≥0 → ℝ≥0 := fun xb w =>
    if d xb = true then w else 0
  let randomNN : Side × Bool → ℝ≥0 → ℝ≥0 := fun xb w =>
    w * ((if d (xb.1, false) = true then (1 : NNReal) else 0) +
      (if d (xb.1, true) = true then (1 : NNReal) else 0)) / 2
  have hpoint : ∀ xb w,
      ((winNN xb w : NNReal) : ℝ) =
        (w : ℝ) / 2 + (((actualNN xb w : NNReal) : ℝ) -
          ((randomNN xb w : NNReal) : ℝ)) := by
    intro xb w
    unfold winNN actualNN randomNN
    cases xb with
    | mk x b =>
      cases b <;>
        by_cases h0 : d (x, false) <;>
        by_cases h1 : d (x, true) <;>
        simp [h0, h1] <;> ring_nf
  have hwin : winProb d D = D.sum winNN := by
    unfold winProb winNN predictorOutput
    rw [Dist.mass_prod_eq_double_sum]
    apply Finsupp.sum_congr
    intro xb _
    rw [Finsupp.sum_fintype]
    · cases xb with
      | mk x b =>
        cases b <;>
          simp [Dist.uniform_apply] <;>
          by_cases h0 : d (x, false) <;>
          by_cases h1 : d (x, true) <;>
          simp [h0, h1] <;> ring_nf
    · intro r
      simp
  have hrand :
      (Dist.prod D (Dist.uniform Bool)).mass
        (fun p : (Side × Bool) × Bool => d (p.1.1, p.2) = true) =
        D.sum randomNN := by
    unfold randomNN
    rw [Dist.mass_prod_eq_double_sum]
    apply Finsupp.sum_congr
    intro xb _
    rw [Finsupp.sum_fintype]
    · cases xb with
      | mk x b =>
        cases b <;>
          simp [Dist.uniform_apply] <;>
          by_cases h0 : d (x, false) <;>
          by_cases h1 : d (x, true) <;>
          simp [h0, h1] <;> ring_nf
    · intro r
      simp
  have hactual : D.mass (fun xb => d xb = true) = D.sum actualNN := by
    unfold Dist.mass actualNN
    apply Finsupp.sum_congr
    intro xb _
    by_cases h : d xb = true <;> simp [h]
  have hsum : ((D.sum winNN : NNReal) : ℝ) =
      ((D.sum (fun _ w => w) : NNReal) : ℝ) / 2 +
        (((D.sum actualNN : NNReal) : ℝ) - ((D.sum randomNN : NNReal) : ℝ)) := by
    unfold Finsupp.sum
    simp
    calc
      ∑ x ∈ D.support, ↑(winNN x (D x)) =
          ∑ x ∈ D.support,
            ((D x : ℝ) / 2 + (((actualNN x (D x) : NNReal) : ℝ) -
              ((randomNN x (D x) : NNReal) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hpoint]
      _ = (∑ x ∈ D.support, ↑(D x)) / 2 +
          ((∑ x ∈ D.support, ↑(actualNN x (D x))) -
            (∑ x ∈ D.support, ↑(randomNN x (D x)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
  have hweight : ((D.sum (fun _ w => w) : NNReal) : ℝ) = 1 := by
    unfold Dist.isProbDist Dist.weight at hD
    exact_mod_cast hD
  rw [hwin]
  unfold gap
  rw [hactual, hrand]
  rw [← hweight]
  exact hsum

variable {Out : Type v}

/-- Preserve the side information induced by `split`, but replace the selected
bit by a fresh independent uniform bit.  This is the distribution used in the
hybrid-to-prediction step of the next-bit converse. -/
def freshBitDist (split : Out ≃ Side × Bool) (D : Dist Out) : Dist Out :=
  Dist.fTransform
    (fun p : (Side × Bool) × Bool => split.symm (p.1.1, p.2))
    (Dist.prod (Dist.fTransform split D) (Dist.uniform Bool))

def splitWinProb (split : Out ≃ Side × Bool) (test : Out → Bool) (D : Dist Out) :
    NNReal :=
  winProb (fun xb => test (split.symm xb)) (Dist.fTransform split D)

def splitGap (split : Out ≃ Side × Bool) (test : Out → Bool) (D : Dist Out) : ℝ :=
  (D.mass (fun out => test out = true) : ℝ) -
    ((freshBitDist split D).mass (fun out => test out = true) : ℝ)

theorem lemma35_split (split : Out ≃ Side × Bool) (test : Out → Bool)
    {D : Dist Out} (hD : D.isProbDist) :
    (splitWinProb split test D : ℝ) = (1 / 2 : ℝ) + splitGap split test D := by
  classical
  have hsplit : (Dist.fTransform split D).isProbDist :=
    Dist.fTransform_isProbDist split hD
  unfold splitWinProb splitGap freshBitDist
  rw [lemma35 (d := fun xb => test (split.symm xb)) hsplit]
  unfold gap
  have hactual :
      (Dist.fTransform split D).mass (fun xb => test (split.symm xb) = true) =
        D.mass (fun out => test out = true) := by
    rw [Dist.mass_fTransform]
    apply Dist.mass_congr
    intro out
    simp
  have hrand :
      ((Dist.prod (Dist.fTransform split D) (Dist.uniform Bool)).mass
        (fun p : (Side × Bool) × Bool => test (split.symm (p.1.1, p.2)) = true)) =
        (Dist.fTransform (fun p : (Side × Bool) × Bool => split.symm (p.1.1, p.2))
          (Dist.prod (Dist.fTransform split D) (Dist.uniform Bool))).mass
          (fun out => test out = true) := by
    rw [Dist.mass_fTransform]
  rw [hactual, ← hrand]

end DistinguisherPredictor

end NextBit

namespace ParallelComposition

variable {Output : Type v}

/-- Boneh-Shoup Theorem 3.2's hybrid premise: adjacent hybrids differ by at
most the same per-use PRG bound.  `hybrids 0` is the all-PRG world and
`hybrids n` is the all-random world. -/
abbrev Hyp (hybrids : SystemTrace Unit Output) (n : Nat) (stepBound : ℝ) : Prop :=
  ∀ i, i < n → Δ(hybrids i, hybrids (i + 1)) ≤ stepBound

/-- Boneh-Shoup Theorem 3.2's linear-degradation conclusion. -/
abbrev Goal (hybrids : SystemTrace Unit Output) (n : Nat) (stepBound : ℝ) : Prop :=
  Δ(hybrids 0, hybrids n) ≤ n * stepBound

theorem bound_from_hybrids {hybrids : SystemTrace Unit Output} {n : Nat}
    {stepBound : ℝ} (h : Hyp hybrids n stepBound) :
    Goal hybrids n stepBound := by
  have hsteps : AdjacentMaxAdvantageBounded hybrids n (fun _ => stepBound) := by
    exact h
  have htrace : MaxAdvantageTraceBound hybrids n
      (∑ i ∈ Finset.range n, stepBound) :=
    AdjacentMaxAdvantageBounded.traceBound hsteps
  simpa [Goal, MaxAdvantageTraceBound, Finset.sum_const, nsmul_eq_mul] using htrace

end ParallelComposition

end PRG

namespace StreamCipher

variable {Seed : Type u} {Pad : Type v} {Msg : Type w} {Ciph : Type z}

/-- Apply a fixed encryption branch to a pad-sampling system. -/
def encryptWithPad (mask : Pad → Msg → Ciph) (m : Msg)
    (pads : PFunPDS Unit Pad) : PFunPDS Unit Ciph :=
  oneCallApplyPDS (fun _ : Unit => ()) (fun _ pad => mask pad m) pads

/-- Stream-cipher encryption of a fixed message using the PRG pad. -/
def real (G : Seed → Pad) (seedDist : Dist Seed) (mask : Pad → Msg → Ciph)
    (m : Msg) : PFunPDS Unit Ciph :=
  encryptWithPad mask m (PRG.real G seedDist)

/-- Stream-cipher encryption of a fixed message using a truly random pad. -/
def random (padDist : Dist Pad) (mask : Pad → Msg → Ciph) (m : Msg) :
    PFunPDS Unit Ciph :=
  encryptWithPad mask m (PRG.random padDist)

/-- Semantic-security distinguishing game for two fixed challenge messages. -/
def semanticDistinguishing (G : Seed → Pad) (seedDist : Dist Seed)
    (mask : Pad → Msg → Ciph) (m₀ m₁ : Msg) :
    DistinguishingGame Unit Ciph :=
  (real G seedDist mask m₀, real G seedDist mask m₁)

/-- Bit-guessing form of the same semantic-security game. -/
def semanticBitGuess (G : Seed → Pad) (seedDist : Dist Seed)
    (mask : Pad → Msg → Ciph) (m₀ m₁ : Msg) :
    BitGuessGame Unit Ciph :=
  distinguishingAsBitGuess (semanticDistinguishing G seedDist mask m₀ m₁)

/-- The one-time-pad/random-pad middle-game fact: encrypting either fixed
message with a random pad gives the same ciphertext system. -/
abbrev RandomPadHides (padDist : Dist Pad) (mask : Pad → Msg → Ciph)
    (m₀ m₁ : Msg) : Prop :=
  random padDist mask m₀ = random padDist mask m₁

/-- Hypothesis for Boneh-Shoup Theorem 3.1 in CR18 form.  The only inputs are:
the random-pad middle-game fact and the two signed PRG bounds needed for the
left and right converter hops. -/
abbrev Hyp (G : Seed → Pad) (seedDist : Dist Seed) (padDist : Dist Pad)
    (mask : Pad → Msg → Ciph) (m₀ m₁ : Msg) (leftBound rightBound : ℝ) : Prop :=
  RandomPadHides padDist mask m₀ m₁ ∧
    Δ(PRG.real G seedDist, PRG.random padDist) ≤ leftBound ∧
    Δ(PRG.random padDist, PRG.real G seedDist) ≤ rightBound

/-- Goal for the stream-cipher semantic-security bound. -/
abbrev Goal (G : Seed → Pad) (seedDist : Dist Seed) (mask : Pad → Msg → Ciph)
    (m₀ m₁ : Msg) (leftBound rightBound : ℝ) : Prop :=
  Δ(real G seedDist mask m₀, real G seedDist mask m₁) ≤ leftBound + rightBound

theorem bound_from_prg {G : Seed → Pad} {seedDist : Dist Seed} {padDist : Dist Pad}
    {mask : Pad → Msg → Ciph} {m₀ m₁ : Msg} {leftBound rightBound : ℝ}
    (h : Hyp G seedDist padDist mask m₀ m₁ leftBound rightBound) :
    Goal G seedDist mask m₀ m₁ leftBound rightBound := by
  obtain ⟨hmask, hleft, hright⟩ := h
  let systems : SystemTrace Unit Ciph
    | 0 => real G seedDist mask m₀
    | 1 => random padDist mask m₀
    | 2 => random padDist mask m₁
    | _ => real G seedDist mask m₁
  have h0 : Δ(systems 0, systems 1) ≤ leftBound := by
    change Δ(encryptWithPad mask m₀ (PRG.real G seedDist),
      encryptWithPad mask m₀ (PRG.random padDist)) ≤ leftBound
    exact le_trans
      (maxAdvantage_oneCallApplyPDS_le (fun _ : Unit => ()) (fun _ pad => mask pad m₀)
        (PRG.real G seedDist) (PRG.random padDist))
      hleft
  have h1 : Δ(systems 1, systems 2) ≤ 0 := by
    change Δ(random padDist mask m₀, random padDist mask m₁) ≤ 0
    simpa [hmask] using maxAdvantage_self_le_zero (random padDist mask m₀)
  have h2 : Δ(systems 2, systems 3) ≤ rightBound := by
    change Δ(encryptWithPad mask m₁ (PRG.random padDist),
      encryptWithPad mask m₁ (PRG.real G seedDist)) ≤ rightBound
    exact le_trans
      (maxAdvantage_oneCallApplyPDS_le (fun _ : Unit => ()) (fun _ pad => mask pad m₁)
        (PRG.random padDist) (PRG.real G seedDist))
      hright
  have htrace : Δ(systems 0, systems 3) ≤ leftBound + 0 + rightBound :=
    maxAdvantage_three_hop_le systems h0 h1 h2
  change Δ(systems 0, systems 3) ≤ leftBound + rightBound
  simpa [add_assoc] using htrace

end StreamCipher

end

end Complexity
end RandomSystems.CR18
