import RandomSystems.GameOf

/-!
# Common-carrier games

An exact common part of two laws can be fed directly to the pre-winning
behavior machinery.  The common realizations carry the constant `false` MBO;
the residual realizations carry the constant `true` MBO.
-/

noncomputable section

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped RandomSystems.CR18.CondEquiv

universe u v

variable {X : Type u} {Y : Type v}

/-- Event mass is linear in the underlying finite mass function. -/
theorem finiteMass_add {A : Type*} (left right : Dist A)
    (event : A → Prop) :
    (left + right).mass event = left.mass event + right.mass event := by
  unfold Dist.mass
  exact Finsupp.sum_add_index' (fun _ => by simp only [ite_self])
    (fun value leftMass rightMass => by
      by_cases member : event value <;> simp [member])

/-- Total weight is linear in the underlying finite mass function. -/
theorem finiteWeight_add {A : Type*} (left right : Dist A) :
    (left + right).weight = left.weight + right.weight := by
  unfold Dist.weight
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Pushforward is linear in a finite mass function. -/
theorem finiteFTransform_add {A B : Type*} (map : A → B)
    (left right : Dist A) :
    Dist.fTransform map (left + right) =
      Dist.fTransform map left + Dist.fTransform map right := by
  exact Finsupp.mapDomain_add

/-- Pre-winning transcript mass is linear in the game law. -/
theorem massYAfalse_add
    (left right : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse (left + right) i ys xs =
      CondEquiv.massYAfalse left i ys xs +
        CondEquiv.massYAfalse right i ys xs := by
  unfold CondEquiv.massYAfalse
  exact finiteMass_add left right _

/-- A game whose common part is not won and whose residual part is won from
the first answered query. -/
noncomputable def commonCarrierGame
    (common residual : PFunPDS X Y) : PFunPDS X (Y × Bool) :=
  gameOf common (fun _history => false) +
    gameOf residual (fun _history => true)

theorem constant_false_monotoneCond :
    PFunDDS.MonotoneCond (fun _history : List (X × Y) => false) := by
  intro _first _second _prefix
  exact le_rfl

theorem constant_true_monotoneCond :
    PFunDDS.MonotoneCond (fun _history : List (X × Y) => true) := by
  intro _first _second _prefix
  exact le_rfl

/-- The common-carrier construction is a monotone game. -/
theorem commonCarrierGame_monotoneMBO
    (common residual : PFunPDS X Y) :
    MonotoneMBO (commonCarrierGame common residual) := by
  classical
  intro game support
  rcases Finset.mem_union.mp (Finsupp.support_add support) with left | right
  · exact monotoneMBO_gameOf common (fun _history => false)
      constant_false_monotoneCond game left
  · exact monotoneMBO_gameOf residual (fun _history => true)
      constant_true_monotoneCond game right

/-- Stripping commutes with addition of finite system laws. -/
theorem PFunPDS.ignoreMBO_add
    (left right : PFunPDS X (Y × Bool)) :
    PFunPDS.ignoreMBO (left + right) =
      PFunPDS.ignoreMBO left + PFunPDS.ignoreMBO right := by
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO
  exact Finsupp.mapDomain_add

/-- Erasing the bit reconstructs the common part plus the chosen residual. -/
theorem ignoreMBO_commonCarrierGame
    (common residual : PFunPDS X Y) :
    PFunPDS.ignoreMBO (commonCarrierGame common residual) =
      common + residual := by
  rw [commonCarrierGame, PFunPDS.ignoreMBO_add,
    ignoreMBO_gameOf, ignoreMBO_gameOf]

/-- A constant-false enhancement has exactly the plain system's cumulative
transcript mass before winning. -/
theorem massYAfalse_gameOf_const_false
    (system : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse (gameOf system (fun _history => false)) i ys xs =
      CondEquiv.massY system i ys xs := by
  unfold CondEquiv.massYAfalse CondEquiv.massY PFunPDS.cumulativeBehavior
    gameOf
  rw [Dist.mass_fTransform]
  apply Dist.mass_congr
  intro deterministic
  constructor
  · intro before k
    obtain ⟨domain, answer, _bit⟩ := before k
    exact ⟨domain, by
      simpa only [PFunDDS.output_gameOfDDS
        (fun _history : List (X × Y) => false) deterministic
        (xs.toList.take (k.1 + 1)) domain domain] using answer⟩
  · intro transcript k
    obtain ⟨domain, answer⟩ := transcript k
    exact ⟨domain, by
      simpa only [PFunDDS.output_gameOfDDS
        (fun _history : List (X × Y) => false) deterministic
        (xs.toList.take (k.1 + 1)) domain domain] using answer, rfl⟩

/-- A constant-true enhancement has no nonempty pre-winning transcript. -/
theorem massYAfalse_gameOf_const_true
    (system : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse (gameOf system (fun _history => true)) i ys xs = 0 := by
  unfold CondEquiv.massYAfalse gameOf
  rw [Dist.mass_fTransform]
  apply Dist.mass_eq_zero_of_forall_not
  intro deterministic before
  have positive : 0 < ys.toList.length := by simp
  obtain ⟨domain, _answer, bit⟩ := before ⟨0, positive⟩
  have : true = false := by
    simpa only [PFunDDS.output_gameOfDDS
      (fun _history : List (X × Y) => true) deterministic
      (xs.toList.take 1) domain domain] using bit
  contradiction

/-- The pre-winning mass of a common-carrier game is exactly the common
part's transcript mass; the residual never reaches the not-won region. -/
theorem massYAfalse_commonCarrierGame
    (common residual : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse (commonCarrierGame common residual) i ys xs =
      CondEquiv.massY common i ys xs := by
  rw [commonCarrierGame, massYAfalse_add,
    massYAfalse_gameOf_const_false,
    massYAfalse_gameOf_const_true, add_zero]

/-- Two games built from the same common carrier have identical pre-winning
transcript masses, irrespective of their residual laws. -/
theorem commonCarrierGame_massYAfalseEq
    (common leftResidual rightResidual : PFunPDS X Y) :
    MassYAfalseEq
      (commonCarrierGame common leftResidual)
      (commonCarrierGame common rightResidual) := by
  intro i ys xs
  rw [massYAfalse_commonCarrierGame, massYAfalse_commonCarrierGame]

/-- Concrete winning probability is linear in the game law. -/
theorem winProb_add_right (winner : Dist (PFunDDS.Winner X Y))
    (left right : PFunPDS X (Y × Bool)) :
    winProb winner (left + right) =
      winProb winner left + winProb winner right := by
  unfold winProb GamePerf.winProb
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro deterministicWinner _support
  exact Finsupp.sum_add_index' (by simp)
    (by intro game leftMass rightMass; ring)

/-- A constant-false enhancement cannot be won by any winner. -/
theorem winProb_gameOf_const_false
    (winner : Dist (PFunDDS.Winner X Y)) (system : PFunPDS X Y) :
    winProb winner (gameOf system (fun _history => false)) = 0 := by
  unfold winProb gameOf
  rw [winProb_fTransform_game]
  unfold GamePerf.winProb
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro deterministicWinner _winnerSupport
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro deterministicSystem _systemSupport
  have notWin : ¬ winsDDS deterministicWinner
      (PFunDDS.gameOfDDS
        (fun _history : List (X × Y) => false) deterministicSystem) := by
    exact PFunDDS.not_winsDDS_tagFalse deterministicWinner deterministicSystem
  rw [if_neg notWin]
  ring

/-- Every win of a common-carrier game lies in its residual part.  Thus its
winning probability is bounded by the residual weight for every probabilistic
winner, independently of the query strategy. -/
theorem winProb_commonCarrierGame_le_residual_weight
    (winner : Dist (PFunDDS.Winner X Y))
    (common residual : PFunPDS X Y)
    (winnerProbability : winner.isProbDist)
    (residualNonnegative : residual.NonNeg) :
    winProb winner (commonCarrierGame common residual) ≤ residual.weight := by
  rw [commonCarrierGame, winProb_add_right,
    winProb_gameOf_const_false, zero_add]
  have bound := GamePerf.winProb_le_weight winsDDS winner winnerProbability
    (residualNonnegative.fTransform
      (PFunDDS.gameOfDDS (fun _history : List (X × Y) => true)))
  exact bound.trans_eq (Dist.weight_fTransform _ residual)

/-- Nonnegativity of the common and residual parts makes the constructed game
an honest nonnegative system law. -/
theorem commonCarrierGame_nonNeg
    {common residual : PFunPDS X Y}
    (commonNonnegative : common.NonNeg)
    (residualNonnegative : residual.NonNeg) :
    (commonCarrierGame common residual).NonNeg := by
  intro game
  simp only [commonCarrierGame, Finsupp.add_apply]
  exact add_nonneg
    (commonNonnegative.fTransform _ game)
    (residualNonnegative.fTransform _ game)

/-- The game weight is the sum of common and residual weights. -/
theorem commonCarrierGame_weight
    (common residual : PFunPDS X Y) :
    (commonCarrierGame common residual).weight =
      common.weight + residual.weight := by
  rw [commonCarrierGame, finiteWeight_add]
  change
    (Dist.fTransform (PFunDDS.gameOfDDS (fun _history => false)) common).weight +
      (Dist.fTransform (PFunDDS.gameOfDDS (fun _history => true)) residual).weight =
        common.weight + residual.weight
  rw [Dist.weight_fTransform, Dist.weight_fTransform]

/-- A normalized common-plus-residual decomposition yields a probability game. -/
theorem commonCarrierGame_isProbDist
    {common residual : PFunPDS X Y}
    (commonNonnegative : common.NonNeg)
    (residualNonnegative : residual.NonNeg)
    (normalized : common.weight + residual.weight = 1) :
    (commonCarrierGame common residual).isProbDist := by
  exact ⟨commonCarrierGame_nonNeg commonNonnegative residualNonnegative,
    commonCarrierGame_weight common residual |>.trans normalized⟩

end RandomSystems.CR18
