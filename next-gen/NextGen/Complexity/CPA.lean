/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.Tactics
import NextGen.Complexity.GameBased
import NextGen.Complexity.ConverterBridge
import NextGen.Theorem417

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)

noncomputable section

universe u v w z g

/-- A fixed-message-space symmetric encryption scheme.

`Msg` is the admissible message space for this CPA game.  This is the
fixed-length reading used in Boneh-Shoup's basic games: all messages in this
type are valid challenge messages for the same game.  A variable-length
`Bin*` model should be a separate CPA surface whose challenge query type carries
the equal-length side condition.  The message sampler is needed for
Boneh-Shoup Exercise 3.3's real/random-message experiment. -/
class CPAScheme (E : Type u) where
  Key : Type v
  Msg : Type w
  Ciph : Type z
  keyDist : E → Dist Key
  msgDist : E → Dist Msg
  keyDist_isProbDist : ∀ S : E, (keyDist S).isProbDist
  msgDist_isProbDist : ∀ S : E, (msgDist S).isProbDist
  enc : E → Key → Msg → Ciph
  dec : E → Key → Ciph → Option Msg

/-- A CPA left/right challenge game over a fixed admissible message space. -/
class CPAGame (E : Type u) [CPAScheme E] (G : Type g) where
  leftRaw : G → PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E)
  rightRaw : G → PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E)

namespace RRM

def realRaw {E : Type u} [CPAScheme E] (S : E) :
    PFunPDS (CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  Dist.fTransform
    (fun k : CPAScheme.Key E =>
      PFunDDS.functionEvaluator fun m : CPAScheme.Msg E =>
        CPAScheme.enc S k m)
    (CPAScheme.keyDist S)

def randomRaw {E : Type u} [CPAScheme E] (S : E) :
    PFunPDS (CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  Dist.fTransform
    (fun km : CPAScheme.Key E × CPAScheme.Msg E =>
      PFunDDS.functionEvaluator fun _ : CPAScheme.Msg E =>
        CPAScheme.enc S km.1 km.2)
    (Dist.prod (CPAScheme.keyDist S) (CPAScheme.msgDist S))

def real {E : Type u} [CPAScheme E] (q : Nat) (S : E) :
    PFunPDS (CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  PFunPDS.filterQueries q (realRaw S)

def random {E : Type u} [CPAScheme E] (q : Nat) (S : E) :
    PFunPDS (CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  PFunPDS.filterQueries q (randomRaw S)

end RRM

namespace CPA

def leftRaw {E : Type u} [CPAScheme E] (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  Dist.fTransform
    (fun k : CPAScheme.Key E =>
      PFunDDS.functionEvaluator fun q : CPAScheme.Msg E × CPAScheme.Msg E =>
        CPAScheme.enc S k q.1)
    (CPAScheme.keyDist S)

def rightRaw {E : Type u} [CPAScheme E] (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  Dist.fTransform
    (fun k : CPAScheme.Key E =>
      PFunDDS.functionEvaluator fun q : CPAScheme.Msg E × CPAScheme.Msg E =>
        CPAScheme.enc S k q.2)
    (CPAScheme.keyDist S)

def left {E : Type u} [CPAScheme E] (q : Nat) (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  PFunPDS.filterQueries q (leftRaw S)

def right {E : Type u} [CPAScheme E] (q : Nat) (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  PFunPDS.filterQueries q (rightRaw S)

instance instCPAGameScheme (E : Type u) [CPAScheme E] : CPAGame E E where
  leftRaw := leftRaw
  rightRaw := rightRaw

def distinguishingRaw {E : Type u} [CPAScheme E] {G : Type g} [CPAGame E G] (S : G) :
    DistinguishingGame (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  (CPAGame.leftRaw S, CPAGame.rightRaw S)

def distinguishing {E : Type u} [CPAScheme E] {G : Type g} [CPAGame E G]
    (q : Nat) (S : G) :
    DistinguishingGame (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  (PFunPDS.filterQueries q (CPAGame.leftRaw S),
    PFunPDS.filterQueries q (CPAGame.rightRaw S))

abbrev twoQueryDistinguishing {E : Type u} [CPAScheme E] {G : Type g} [CPAGame E G]
    (S : G) :
    DistinguishingGame (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  distinguishing 2 S

end CPA

namespace CPAExample51

variable {E : Type u} [CPAScheme E]

abbrev CorrectScheme (S : E) : Prop :=
  ∀ (k : CPAScheme.Key E) (m : CPAScheme.Msg E),
    CPAScheme.dec S k (CPAScheme.enc S k m) = some m

theorem enc_injective_of_correct {S : E} (hcorrect : CorrectScheme S)
    {k : CPAScheme.Key E} {m m' : CPAScheme.Msg E} (hne : m ≠ m') :
    CPAScheme.enc S k m ≠ CPAScheme.enc S k m' := by
  intro henc
  apply hne
  have hleft := hcorrect k m
  have hright := hcorrect k m'
  rw [henc] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

variable [DecidableEq (CPAScheme.Ciph E)]

/-- Boneh-Shoup Exercise 5.1's two-query attack: ask `(m,m')`, then `(m,m)`,
and test whether the two ciphertexts are equal. -/
abbrev twoQueryAttackDDS (m m' : CPAScheme.Msg E) :
    PFunDDS.DDD (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  twoQueryEqDDS (Y := CPAScheme.Ciph E) (x₀ := (m, m')) (x₁ := (m, m))

def leftOracle (S : E) (k : CPAScheme.Key E) :
    PFunDDS.DDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  ⟦2⟧ eval[fun q : CPAScheme.Msg E × CPAScheme.Msg E => CPAScheme.enc S k q.1]

def rightOracle (S : E) (k : CPAScheme.Key E) :
    PFunDDS.DDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  ⟦2⟧ eval[fun q : CPAScheme.Msg E × CPAScheme.Msg E => CPAScheme.enc S k q.2]

theorem twoQueryAttack_queriesExactly (m m' : CPAScheme.Msg E) :
    QueriesExactly
      (PFunDDS.ddToDDE (twoQueryAttackDDS (E := E) m m')) 2 := by
  exact twoQueryEq_queriesExactly (Y := CPAScheme.Ciph E) (x₀ := (m, m')) (x₁ := (m, m))

theorem twoQueryAttack_transcript_two_functionEvaluator
    (m m' : CPAScheme.Msg E)
    (f : CPAScheme.Msg E × CPAScheme.Msg E → CPAScheme.Ciph E) :
    PFunDDS.transcript (⟦2⟧ eval[f])
        (PFunDDS.ddToDDE (twoQueryAttackDDS (E := E) m m')) 2 =
      [((m, m'), some (f (m, m'))), ((m, m), some (f (m, m)))] := by
  exact twoQueryEq_transcript_two_functionEvaluator
    (Y := CPAScheme.Ciph E) (x₀ := (m, m')) (x₁ := (m, m)) f

theorem twoQueryAttack_accepts_leftOracle
    (S : E) (k : CPAScheme.Key E) (m m' : CPAScheme.Msg E) :
    twoQueryAttackDDS (E := E) m m' ⊨ leftOracle S k := by
  rw [PFunDDS.verdict_iff_at_exact _ _ 2
    (twoQueryAttack_queriesExactly (E := E) m m')]
  unfold leftOracle
  rw [twoQueryAttack_transcript_two_functionEvaluator]
  simp [twoQueryAttackDDS, twoQueryEqDDS, twoQueryEqStep, PFunDDS.transcriptOutputs]

theorem twoQueryAttack_rejects_rightOracle
    {S : E} (hcorrect : CorrectScheme S) (k : CPAScheme.Key E)
    {m m' : CPAScheme.Msg E} (hne : m ≠ m') :
    ¬ twoQueryAttackDDS (E := E) m m' ⊨ rightOracle S k := by
  intro hv
  rw [PFunDDS.verdict_iff_at_exact _ _ 2
    (twoQueryAttack_queriesExactly (E := E) m m')] at hv
  unfold rightOracle at hv
  rw [twoQueryAttack_transcript_two_functionEvaluator] at hv
  simp [twoQueryAttackDDS, twoQueryEqDDS, twoQueryEqStep, PFunDDS.transcriptOutputs] at hv
  exact (enc_injective_of_correct hcorrect hne) hv.symm

abbrev Hyp (S : E) (m m' : CPAScheme.Msg E) : Prop :=
  CorrectScheme S ∧ m ≠ m'

abbrev Goal (S : E) (_m _m' : CPAScheme.Msg E) : Prop :=
  1 ≤ Δ(CPA.right 2 S, CPA.left 2 S)

theorem deterministicCipher_not_twoQueryCPA
    (S : E) {m m' : CPAScheme.Msg E} (h : Hyp S m m') :
    Goal S m m' := by
  classical
  obtain ⟨hcorrect, hne⟩ := h
  let D : Dist (PFunDDS.DDD (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E)) :=
    Finsupp.single (twoQueryAttackDDS (E := E) m m') 1
  have hD : D.isProbDist := by
    show Dist.weight (Finsupp.single (twoQueryAttackDDS (E := E) m m') (1 : NNReal)) = 1
    rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]
  have hleft : verdictProb D (CPA.left 2 S) = 1 := by
    unfold D verdictProb GamePerf.winProb
    rw [Finsupp.sum_single_index]
    · simp only [one_mul]
      calc
        Finsupp.sum (CPA.left 2 S)
            (fun g gp =>
              gp * if twoQueryAttackDDS (E := E) m m' ⊨ g then 1 else 0)
            = (CPA.left 2 S).mass
                (fun g => twoQueryAttackDDS (E := E) m m' ⊨ g) := by
              unfold Dist.mass
              apply Finsupp.sum_congr
              intro g gp
              by_cases hv : twoQueryAttackDDS (E := E) m m' ⊨ g <;> simp [hv]
        _ = 1 := by
          unfold CPA.left CPA.leftRaw PFunPDS.filterQueries
          rw [Dist.mass_fTransform, Dist.mass_fTransform]
          calc
            (CPAScheme.keyDist S).mass
                (fun a => twoQueryAttackDDS (E := E) m m' ⊨ leftOracle S a)
                = (CPAScheme.keyDist S).mass (fun _ => True) := by
                  apply Dist.mass_congr
                  intro k
                  simp [twoQueryAttack_accepts_leftOracle]
            _ = 1 := by
                  rw [Dist.mass_true, CPAScheme.keyDist_isProbDist]
    · simp
  have hright : verdictProb D (CPA.right 2 S) = 0 := by
    unfold D verdictProb GamePerf.winProb
    rw [Finsupp.sum_single_index]
    · simp only [one_mul]
      calc
        Finsupp.sum (CPA.right 2 S)
            (fun g gp =>
              gp * if twoQueryAttackDDS (E := E) m m' ⊨ g then 1 else 0)
            = (CPA.right 2 S).mass
                (fun g => twoQueryAttackDDS (E := E) m m' ⊨ g) := by
              unfold Dist.mass
              apply Finsupp.sum_congr
              intro g gp
              by_cases hv : twoQueryAttackDDS (E := E) m m' ⊨ g <;> simp [hv]
        _ = 0 := by
          unfold CPA.right CPA.rightRaw PFunPDS.filterQueries
          rw [Dist.mass_fTransform, Dist.mass_fTransform]
          calc
            (CPAScheme.keyDist S).mass
                (fun a => twoQueryAttackDDS (E := E) m m' ⊨ rightOracle S a)
                = (CPAScheme.keyDist S).mass (fun _ => False) := by
                  apply Dist.mass_congr
                  intro k
                  simp [twoQueryAttack_rejects_rightOracle hcorrect k hne]
            _ = 0 := by
                  simp [Dist.mass]
    · simp
  have hAdv : advantage D (CPA.right 2 S) (CPA.left 2 S) = 1 := by
    unfold advantage
    rw [hleft, hright]
    norm_num
  unfold Goal
  calc
    (1 : ℝ) = advantage D (CPA.right 2 S) (CPA.left 2 S) := hAdv.symm
    _ ≤ Δ(CPA.right 2 S, CPA.left 2 S) :=
      advantage_le_maxAdvantage D (CPA.right 2 S) (CPA.left 2 S) hD

end CPAExample51

namespace SemanticFromRRM

variable {E : Type u} [CPAScheme E]

def applySelector
    (select : CPAScheme.Msg E × CPAScheme.Msg E → CPAScheme.Msg E)
    (G : PFunPDS (CPAScheme.Msg E) (CPAScheme.Ciph E)) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  oneCallApplyPDS select (fun _ c => c) G

theorem selector_filter_one_functionEvaluator
    (select : CPAScheme.Msg E × CPAScheme.Msg E → CPAScheme.Msg E)
    (f : CPAScheme.Msg E → CPAScheme.Ciph E) :
    oneCallApplyDDS select (fun _ c => c)
      (PFunDDS.filterQueries 1 (PFunDDS.functionEvaluator f)) =
    PFunDDS.filterQueries 1
      (PFunDDS.functionEvaluator fun q : CPAScheme.Msg E × CPAScheme.Msg E => f (select q)) := by
  apply Subtype.ext
  funext qs
  apply Part.ext
  intro c
  cases qs with
  | nil =>
      simp [oneCallApplyDDS, oneCallApplyRaw, PFunDDS.filterQueries, PFunDDS.functionEvaluator]
  | cons q rest =>
      cases rest with
      | nil =>
          simp [oneCallApplyDDS, oneCallApplyRaw, PFunDDS.filterQueries, PFunDDS.functionEvaluator]
      | cons q₂ rest₂ =>
          constructor
          · intro hc
            exfalso
            simp [oneCallApplyDDS, oneCallApplyRaw, PFunDDS.filterQueries,
              PFunDDS.functionEvaluator] at hc
            cases hlast : (q₂ :: rest₂).getLast? with
            | none =>
                simp [hlast] at hc
            | some qlast =>
                simp [hlast] at hc
          · intro hc
            simp [PFunDDS.filterQueries, PFunDDS.functionEvaluator] at hc

def leftViaRRM (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  applySelector (E := E) Prod.fst (RRM.real 1 S)

def leftRandomViaRRM (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  applySelector (E := E) Prod.fst (RRM.random 1 S)

def rightRandomViaRRM (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  applySelector (E := E) Prod.snd (RRM.random 1 S)

def rightViaRRM (S : E) :
    PFunPDS (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E) :=
  applySelector (E := E) Prod.snd (RRM.real 1 S)

theorem leftViaRRM_eq_left (S : E) :
    leftViaRRM S = CPA.left 1 S := by
  unfold leftViaRRM applySelector RRM.real RRM.realRaw CPA.left CPA.leftRaw
    PFunPDS.filterQueries oneCallApplyPDS
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun f => Dist.fTransform f (CPAScheme.keyDist S))
  funext k
  exact selector_filter_one_functionEvaluator (E := E) Prod.fst
    (fun m => CPAScheme.enc S k m)

theorem rightViaRRM_eq_right (S : E) :
    rightViaRRM S = CPA.right 1 S := by
  unfold rightViaRRM applySelector RRM.real RRM.realRaw CPA.right CPA.rightRaw
    PFunPDS.filterQueries oneCallApplyPDS
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun f => Dist.fTransform f (CPAScheme.keyDist S))
  funext k
  exact selector_filter_one_functionEvaluator (E := E) Prod.snd
    (fun m => CPAScheme.enc S k m)

theorem leftRandomViaRRM_eq_rightRandomViaRRM (S : E) :
    leftRandomViaRRM S = rightRandomViaRRM S := by
  unfold leftRandomViaRRM rightRandomViaRRM applySelector RRM.random RRM.randomRaw
    PFunPDS.filterQueries oneCallApplyPDS
  rw [Dist.fTransform_comp, Dist.fTransform_comp, Dist.fTransform_comp]
  rw [Dist.fTransform_comp]
  apply congrArg (fun f =>
    Dist.fTransform f (Dist.prod (CPAScheme.keyDist S) (CPAScheme.msgDist S)))
  funext km
  calc
    oneCallApplyDDS Prod.fst (fun _ c => c)
        (PFunDDS.filterQueries 1
          (PFunDDS.functionEvaluator fun _ : CPAScheme.Msg E => CPAScheme.enc S km.1 km.2))
        =
        PFunDDS.filterQueries 1
          (PFunDDS.functionEvaluator fun _ : CPAScheme.Msg E × CPAScheme.Msg E =>
            CPAScheme.enc S km.1 km.2) := by
          exact selector_filter_one_functionEvaluator (E := E) Prod.fst
            (fun _ : CPAScheme.Msg E => CPAScheme.enc S km.1 km.2)
    _ =
        oneCallApplyDDS Prod.snd (fun _ c => c)
          (PFunDDS.filterQueries 1
            (PFunDDS.functionEvaluator fun _ : CPAScheme.Msg E => CPAScheme.enc S km.1 km.2)) := by
          exact (selector_filter_one_functionEvaluator (E := E) Prod.snd
            (fun _ : CPAScheme.Msg E => CPAScheme.enc S km.1 km.2)).symm

theorem leftSelectorHop_le_rrm (S : E) :
    Δ(leftViaRRM S, leftRandomViaRRM S) ≤
      Δ(RRM.real 1 S, RRM.random 1 S) := by
  unfold leftViaRRM leftRandomViaRRM applySelector
  exact RandomSystems.CR18.Complexity.maxAdvantage_oneCallApplyPDS_le Prod.fst (fun _ c => c)
    (RRM.real 1 S) (RRM.random 1 S)

theorem rightSelectorHop_le_rrm (S : E) :
    Δ(rightRandomViaRRM S, rightViaRRM S) ≤
      Δ(RRM.random 1 S, RRM.real 1 S) := by
  unfold rightRandomViaRRM rightViaRRM applySelector
  exact RandomSystems.CR18.Complexity.maxAdvantage_oneCallApplyPDS_le Prod.snd (fun _ c => c)
    (RRM.random 1 S) (RRM.real 1 S)

def trace (S : E) :
    SystemTrace (CPAScheme.Msg E × CPAScheme.Msg E) (CPAScheme.Ciph E)
  | 0 => leftViaRRM S
  | 1 => leftRandomViaRRM S
  | 2 => rightRandomViaRRM S
  | _ => rightViaRRM S

def stepBound (leftBound rightBound : ℝ) : Nat → ℝ
  | 0 => leftBound
  | 1 => 0
  | _ => rightBound

abbrev SelectorHopBounds (S : E) (leftBound rightBound : ℝ) : Prop :=
  AdjacentMaxAdvantageBounded (trace S) 3 (stepBound leftBound rightBound)

abbrev RRMBounds (S : E) (leftBound rightBound : ℝ) : Prop :=
  Δ(RRM.real 1 S, RRM.random 1 S) ≤ leftBound ∧
    Δ(RRM.random 1 S, RRM.real 1 S) ≤ rightBound

/-- Named hypothesis for Boneh-Shoup Exercise 3.3, forward direction:
the real/random-message bounds hold in the two signed directions.  The CPA
endpoint realization and the selector-hop reductions are proved internally. -/
abbrev Hyp (S : E) (leftBound rightBound : ℝ) : Prop :=
  RRMBounds S leftBound rightBound

abbrev Goal (S : E) (leftBound rightBound : ℝ) : Prop :=
  Δ(CPA.left 1 S, CPA.right 1 S) ≤ leftBound + rightBound

theorem selectorHopBounds_of_local_bounds {S : E} {leftBound rightBound : ℝ}
    (hleft : Δ(leftViaRRM S, leftRandomViaRRM S) ≤ leftBound)
    (hmiddle : Δ(leftRandomViaRRM S, rightRandomViaRRM S) ≤ 0)
    (hright : Δ(rightRandomViaRRM S, rightViaRRM S) ≤ rightBound) :
    SelectorHopBounds S leftBound rightBound := by
  cr18_hop_cases [trace, stepBound]

theorem selectorHopBounds_of_rrm_bounds {S : E} {leftBound rightBound : ℝ}
    (h : Hyp S leftBound rightBound) :
    SelectorHopBounds S leftBound rightBound := by
  rcases h with ⟨hleft, hright⟩
  apply selectorHopBounds_of_local_bounds
  · exact le_trans (leftSelectorHop_le_rrm S) hleft
  · rw [leftRandomViaRRM_eq_rightRandomViaRRM]
    exact maxAdvantage_self_le_zero (rightRandomViaRRM S)
  · exact le_trans (rightSelectorHop_le_rrm S) hright

theorem bound_from_selector_hops {S : E} {leftBound rightBound : ℝ}
    (h : SelectorHopBounds S leftBound rightBound) :
    Goal S leftBound rightBound := by
  have htrace := AdjacentMaxAdvantageBounded.threeHopBound h
  unfold Goal
  rw [← leftViaRRM_eq_left S, ← rightViaRRM_eq_right S]
  simpa [trace, stepBound] using htrace

theorem bound_from_rrm_bounds {S : E} {leftBound rightBound : ℝ}
    (h : Hyp S leftBound rightBound) :
    Goal S leftBound rightBound :=
  bound_from_selector_hops (selectorHopBounds_of_rrm_bounds h)

end SemanticFromRRM

end

end Complexity
end RandomSystems.CR18
