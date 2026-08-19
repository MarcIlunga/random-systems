import SequenceHash.RandomSystems.DeferredSampling

/-!
# Cached deferred sampling for adaptive random-function programs

An adaptive computation may query the same random-function point more than
once.  Repeats return the cached answer and consume no fresh randomness.  This
module proves the exact eager/lazy equivalence for such computations.

The proof routes the `i`-th repeated semantic query to a private padding point
`Sum.inr i`.  Fresh semantic queries use `Sum.inl q`.  Hence the enlarged
schedule is pointwise fresh for every answer tape.  The generic adaptive-fibre
theorem then says that its raw answers are independent uniform coordinates.
The padding answers are ignored by the cached execution.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems

universe u v w z

variable {Q : Type u} {A : Type v} {S : Type w} {P : Type z}

/-- A deterministic oracle program.  Its control state contains every piece
of local computation and interaction history needed to select the next query.
One oracle answer advances the control state by one micro-step. -/
structure CachedOracleProgram (Q : Type u) (A : Type v) (S : Type w) where
  query : S → Q
  step : S → A → S

/-- Control state together with the finite-function cache accumulated so far.
The cache is represented extensionally because all carriers are finite at the
probability boundary. -/
structure CachedExecution (Q : Type u) (A : Type v) (S : Type w) where
  control : S
  cache : Q → Option A

/-- Empty-cache initial execution state. -/
def initialCachedExecution (initial : S) : CachedExecution Q A S where
  control := initial
  cache := fun _ => none

/-- One raw tape coordinate advances a cached program.  On a repeated query
the coordinate is ignored; on a first query it is installed in the cache. -/
def cachedOracleStep [DecidableEq Q]
    (program : CachedOracleProgram Q A S)
    (execution : CachedExecution Q A S) (raw : A) :
    CachedExecution Q A S :=
  let point := program.query execution.control
  match execution.cache point with
  | some answer =>
      { control := program.step execution.control answer
        cache := execution.cache }
  | none =>
      { control := program.step execution.control raw
        cache := Function.update execution.cache point (some raw) }

/-- Replay a finite raw answer vector through the cache. -/
def cachedOracleRun [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) :
    {m : ℕ} → (Fin m → A) → CachedExecution Q A S
  | 0, _values => initialCachedExecution initial
  | m + 1, values =>
      cachedOracleStep program
        (cachedOracleRun program initial (Fin.init values))
        (values (Fin.last m))

/-- Ordinary eager execution against a complete function oracle. -/
def eagerOracleRun (program : CachedOracleProgram Q A S)
    (oracle : Q → A) : S → ℕ → S
  | state, 0 => state
  | state, m + 1 =>
      let previous := eagerOracleRun program oracle state m
      program.step previous (oracle (program.query previous))

/-- Strict prefix of a finite vector. -/
def finStrictPrefix {m : ℕ} (values : Fin m → A) (index : Fin m) :
    Fin index.1 → A :=
  fun earlier => values ⟨earlier.1, Nat.lt_trans earlier.2 index.2⟩

@[simp]
theorem finStrictPrefix_castSucc {m : ℕ} (values : Fin (m + 1) → A)
    (index : Fin m) :
    finStrictPrefix values index.castSucc =
      finStrictPrefix (Fin.init values) index := by
  rfl

/-- Every strict prefix of a completed adaptive run is the adaptive run of
that shorter length.  In particular, later oracle coordinates cannot alter
an answer that has already been generated. -/
theorem finStrictPrefix_adaptiveRun
    (schedule : AdaptiveSchedule Q A) (oracle : Q → A)
    {m : ℕ} (index : Fin m) :
    finStrictPrefix (adaptiveRun schedule oracle m) index =
      adaptiveRun schedule oracle index.1 := by
  induction m with
  | zero => exact Fin.elim0 index
  | succ m inductionHypothesis =>
      rcases Fin.eq_castSucc_or_eq_last index with ⟨earlier, rfl⟩ | rfl
      · rw [adaptiveRun_succ, finStrictPrefix_castSucc, Fin.init_snoc]
        exact inductionHypothesis earlier
      · change
          Fin.init (adaptiveRun schedule oracle (m + 1)) =
            adaptiveRun schedule oracle m
        rw [adaptiveRun_succ, Fin.init_snoc]

/-- The queried point is cached immediately after its step. -/
theorem cachedOracleStep_query_isSome [DecidableEq Q]
    (program : CachedOracleProgram Q A S)
    (execution : CachedExecution Q A S) (raw : A) :
    ∃ answer,
      (cachedOracleStep program execution raw).cache
          (program.query execution.control) = some answer := by
  cases lookup : execution.cache (program.query execution.control) with
  | none =>
      exact ⟨raw, by simp [cachedOracleStep, lookup]⟩
  | some answer =>
      exact ⟨answer, by simpa [cachedOracleStep, lookup] using lookup⟩

/-- Once a cache coordinate is present, later program steps preserve it. -/
theorem cachedOracleStep_cache_some [DecidableEq Q]
    (program : CachedOracleProgram Q A S)
    (execution : CachedExecution Q A S) (raw : A)
    (point : Q) (answer : A)
    (present : execution.cache point = some answer) :
    (cachedOracleStep program execution raw).cache point = some answer := by
  cases missing : execution.cache (program.query execution.control) with
  | some current =>
      simpa [cachedOracleStep, missing] using present
  | none =>
    by_cases equal : program.query execution.control = point
    · subst point
      rw [present] at missing
      cases missing
    · simp only [cachedOracleStep, missing]
      rw [Function.update_of_ne (Ne.symm equal)]
      exact present

/-- Every query made at an earlier micro-step is present in the final cache.
This is the only cache invariant needed for schedule freshness. -/
theorem cachedOracleRun_cache_query_before [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S)
    {m : ℕ} (values : Fin m → A) (index : Fin m) :
    ∃ answer,
      (cachedOracleRun program initial values).cache
          (program.query
            (cachedOracleRun program initial
              (finStrictPrefix values index)).control) = some answer := by
  induction m with
  | zero => exact Fin.elim0 index
  | succ m inductionHypothesis =>
      rcases Fin.eq_castSucc_or_eq_last index with ⟨earlier, rfl⟩ | rfl
      · obtain ⟨answer, present⟩ :=
          inductionHypothesis (Fin.init values) earlier
        exact ⟨answer,
          cachedOracleStep_cache_some program
            (cachedOracleRun program initial (Fin.init values))
            (values (Fin.last m)) _ answer (by simpa using present)⟩
      · simpa using cachedOracleStep_query_isSome program
          (cachedOracleRun program initial (Fin.init values))
          (values (Fin.last m))

/-- The padded schedule associated with a cached program.  At semantic first
occurrences it queries the original point; repeats use the current step index
in a disjoint finite padding space. -/
def cachedAdaptiveSchedule [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ) :
    AdaptiveSchedule (Q ⊕ Fin (budget + 1)) A where
  next := fun {m} values =>
    let execution := cachedOracleRun program initial values
    let point := program.query execution.control
    match execution.cache point with
    | none => Sum.inl point
    | some _answer => Sum.inr (Fin.ofNat (budget + 1) m)

@[simp]
theorem cachedAdaptiveSchedule_point [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ)
    {m : ℕ} (values : Fin m → A) (index : Fin m) :
    adaptivePointAt (cachedAdaptiveSchedule program initial budget) values index =
      let execution := cachedOracleRun program initial
        (finStrictPrefix values index)
      let point := program.query execution.control
      match execution.cache point with
      | none => Sum.inl point
      | some _answer => Sum.inr (Fin.ofNat (budget + 1) index.1) := by
  rfl

/-- Padding makes the schedule fresh on every raw answer vector.  If two
semantic first occurrences selected the same point, the earlier occurrence
would already be present in the later cache.  Repeated occurrences instead
carry their distinct step indices in the disjoint padding summand. -/
theorem cachedAdaptiveSchedule_fresh [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ)
    (values : Fin budget → A) :
    FreshAt (cachedAdaptiveSchedule program initial budget) values := by
  intro left right pointEqual
  by_contra indexDifferent
  have valueDifferent : left.1 ≠ right.1 := by
    intro equal
    exact indexDifferent (Fin.ext equal)
  have noCollision : ∀ {earlier later : Fin budget},
      earlier.1 < later.1 →
      adaptivePointAt (cachedAdaptiveSchedule program initial budget)
          values earlier ≠
        adaptivePointAt (cachedAdaptiveSchedule program initial budget)
          values later := by
    intro earlier later earlierBefore
    let earlierExecution := cachedOracleRun program initial
      (finStrictPrefix values earlier)
    let laterExecution := cachedOracleRun program initial
      (finStrictPrefix values later)
    let earlierPoint := program.query earlierExecution.control
    let laterPoint := program.query laterExecution.control
    have earlierFormula := cachedAdaptiveSchedule_point program initial budget
      values earlier
    have laterFormula := cachedAdaptiveSchedule_point program initial budget
      values later
    change adaptivePointAt
        (cachedAdaptiveSchedule program initial budget) values earlier =
      (match earlierExecution.cache earlierPoint with
        | none => Sum.inl earlierPoint
        | some _answer =>
            Sum.inr (Fin.ofNat (budget + 1) earlier.1)) at earlierFormula
    change adaptivePointAt
        (cachedAdaptiveSchedule program initial budget) values later =
      (match laterExecution.cache laterPoint with
        | none => Sum.inl laterPoint
        | some _answer =>
            Sum.inr (Fin.ofNat (budget + 1) later.1)) at laterFormula
    intro collision
    rw [earlierFormula, laterFormula] at collision
    cases earlierCache : earlierExecution.cache earlierPoint with
    | none =>
        cases laterCache : laterExecution.cache laterPoint with
        | some answer => simp [earlierCache, laterCache] at collision
        | none =>
            have pointsEqual : earlierPoint = laterPoint := by
              simpa [earlierCache, laterCache] using collision
            let earlierInside : Fin later.1 :=
              ⟨earlier.1, earlierBefore⟩
            obtain ⟨answer, present⟩ :=
              cachedOracleRun_cache_query_before program initial
                (finStrictPrefix values later) earlierInside
            have presentEarlier :
                laterExecution.cache earlierPoint = some answer := by
              simpa [laterExecution, earlierExecution, earlierPoint,
                earlierInside, finStrictPrefix] using present
            rw [pointsEqual, laterCache] at presentEarlier
            cases presentEarlier
    | some earlierAnswer =>
        cases laterCache : laterExecution.cache laterPoint with
        | none => simp [earlierCache, laterCache] at collision
        | some laterAnswer =>
            have taggedPaddingEqual :
                (Sum.inr (Fin.ofNat (budget + 1) earlier.1) :
                    Q ⊕ Fin (budget + 1)) =
                  Sum.inr (Fin.ofNat (budget + 1) later.1) := by
              simpa [earlierCache, laterCache] using collision
            have paddingEqual :
                Fin.ofNat (budget + 1) earlier.1 =
                  Fin.ofNat (budget + 1) later.1 := by
              exact Sum.inr.inj taggedPaddingEqual
            have valuesEqual := congrArg Fin.val paddingEqual
            have earlierBound : earlier.1 < budget + 1 :=
              Nat.lt_trans earlier.2 (Nat.lt_succ_self budget)
            have laterBound : later.1 < budget + 1 :=
              Nat.lt_trans later.2 (Nat.lt_succ_self budget)
            simp [Fin.ofNat, Nat.mod_eq_of_lt earlierBound,
              Nat.mod_eq_of_lt laterBound] at valuesEqual
            exact (Nat.ne_of_lt earlierBefore) valuesEqual
  rcases Nat.lt_or_gt_of_ne valueDifferent with earlierBefore | laterBefore
  · exact noCollision earlierBefore pointEqual
  · exact noCollision laterBefore pointEqual.symm

/-! ## Exact eager/lazy law -/

/-- A cache agrees with a complete oracle on every installed coordinate. -/
def CachedExecution.Agrees
    (oracle : Q → A) (execution : CachedExecution Q A S) : Prop :=
  ∀ point answer, execution.cache point = some answer → oracle point = answer

theorem initialCachedExecution_agrees (oracle : Q → A) (initial : S) :
    (initialCachedExecution initial : CachedExecution Q A S).Agrees oracle := by
  intro point answer present
  simp [initialCachedExecution] at present

/-- Cache agreement is preserved when a raw coordinate is correct whenever
the current semantic query is fresh. -/
theorem cachedOracleStep_agrees [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (oracle : Q → A)
    (execution : CachedExecution Q A S) (raw : A)
    (agrees : execution.Agrees oracle)
    (rawCorrect : execution.cache (program.query execution.control) = none →
      raw = oracle (program.query execution.control)) :
    (cachedOracleStep program execution raw).Agrees oracle := by
  intro point answer present
  cases lookup : execution.cache (program.query execution.control) with
  | some current =>
      exact agrees point answer (by
        simpa [cachedOracleStep, lookup] using present)
  | none =>
      by_cases equal : point = program.query execution.control
      · subst point
        have answerRaw : answer = raw := by
          simpa [cachedOracleStep, lookup] using present.symm
        rw [answerRaw, rawCorrect lookup]
      · have old : execution.cache point = some answer := by
          simpa [cachedOracleStep, lookup,
            Function.update_of_ne equal] using present
        exact agrees point answer old

/-- The control component of one cached step is the eager oracle step under
the same freshness premise. -/
theorem cachedOracleStep_control [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (oracle : Q → A)
    (execution : CachedExecution Q A S) (raw : A)
    (agrees : execution.Agrees oracle)
    (rawCorrect : execution.cache (program.query execution.control) = none →
      raw = oracle (program.query execution.control)) :
    (cachedOracleStep program execution raw).control =
      program.step execution.control
        (oracle (program.query execution.control)) := by
  cases lookup : execution.cache (program.query execution.control) with
  | none => simp [cachedOracleStep, lookup, rawCorrect lookup]
  | some answer =>
      have correct := agrees _ answer lookup
      simp [cachedOracleStep, lookup, correct]

/-- Restrict a function on the padded query space to semantic queries. -/
def semanticOracle (oracle : Q ⊕ P → A) : Q → A :=
  fun point => oracle (Sum.inl point)

/-- The raw answer selected at a fresh cached step is the corresponding
semantic-oracle answer. -/
theorem cachedAdaptiveSchedule_raw_correct [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ)
    (oracle : Q ⊕ Fin (budget + 1) → A) {m : ℕ}
    (values : Fin m → A)
    (fresh :
      (cachedOracleRun program initial values).cache
          (program.query
            (cachedOracleRun program initial values).control) = none) :
    oracle ((cachedAdaptiveSchedule program initial budget).next values) =
      semanticOracle oracle
        (program.query (cachedOracleRun program initial values).control) := by
  simp [cachedAdaptiveSchedule, fresh, semanticOracle]

@[simp]
theorem cachedOracleRun_snoc [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S)
    {m : ℕ} (values : Fin m → A) (last : A) :
    cachedOracleRun program initial (Fin.snoc values last) =
      cachedOracleStep program (cachedOracleRun program initial values) last := by
  simp [cachedOracleRun]

/-- Deterministic replay theorem behind cached deferred sampling.  The padded
adaptive schedule and eager complete-function execution reach the same
control state, and the replay cache agrees with the semantic oracle. -/
theorem cachedOracleRun_adaptiveRun [DecidableEq Q]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ)
    (oracle : Q ⊕ Fin (budget + 1) → A) :
    ∀ m : ℕ,
      let values := adaptiveRun
        (cachedAdaptiveSchedule program initial budget) oracle m
      (cachedOracleRun program initial values).control =
          eagerOracleRun program (semanticOracle oracle) initial m ∧
        (cachedOracleRun program initial values).Agrees
          (semanticOracle oracle) := by
  intro m
  induction m with
  | zero =>
      exact ⟨rfl, initialCachedExecution_agrees _ _⟩
  | succ m inductionHypothesis =>
      let previousValues := adaptiveRun
        (cachedAdaptiveSchedule program initial budget) oracle m
      let previous := cachedOracleRun program initial previousValues
      let raw := oracle
        ((cachedAdaptiveSchedule program initial budget).next previousValues)
      have previousControl : previous.control =
          eagerOracleRun program (semanticOracle oracle) initial m := by
        exact inductionHypothesis.1
      have previousAgrees : previous.Agrees (semanticOracle oracle) :=
        inductionHypothesis.2
      have rawCorrect :
          previous.cache (program.query previous.control) = none →
            raw = semanticOracle oracle (program.query previous.control) := by
        intro fresh
        exact cachedAdaptiveSchedule_raw_correct program initial budget oracle
          previousValues fresh
      have controlStep := cachedOracleStep_control program
        (semanticOracle oracle) previous raw previousAgrees rawCorrect
      have cacheStep := cachedOracleStep_agrees program
        (semanticOracle oracle) previous raw previousAgrees rawCorrect
      constructor
      · rw [adaptiveRun_succ, cachedOracleRun_snoc]
        change (cachedOracleStep program previous raw).control = _
        rw [controlStep, previousControl]
        rfl
      · rw [adaptiveRun_succ, cachedOracleRun_snoc]
        exact cacheStep

/-- Split a function on a sum into its two restrictions. -/
def sumFunctionEquiv (Q : Type u) (P : Type v) (A : Type w) :
    (Q ⊕ P → A) ≃ (Q → A) × (P → A) where
  toFun function :=
    (fun point => function (Sum.inl point),
      fun padding => function (Sum.inr padding))
  invFun pair := Sum.elim pair.1 pair.2
  left_inv := by
    intro function
    funext point
    cases point <;> rfl
  right_inv := by
    intro pair
    rfl

/-- The semantic restriction of a uniform function on a disjoint sum is a
uniform function. -/
theorem semanticOracle_uniform
    [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P]
    [Fintype A] [Nonempty A] :
    Dist.fTransform semanticOracle (Dist.uniform (Q ⊕ P → A)) =
      Dist.uniform (Q → A) := by
  classical
  have splitUniform :
      Dist.fTransform (sumFunctionEquiv Q P A)
          (Dist.uniform (Q ⊕ P → A)) =
        Dist.uniform ((Q → A) × (P → A)) :=
    Dist.fTransform_equiv_uniform (sumFunctionEquiv Q P A)
  have semanticAsFirst :
      semanticOracle = Prod.fst ∘ sumFunctionEquiv Q P A := by
    rfl
  rw [semanticAsFirst, ← Dist.fTransform_comp, splitUniform]
  exact Dist.fTransform_fst_uniform (Q → A) (P → A)

/-- **Exact cached deferred sampling.**  The final control state of any
finite adaptive program has the same law whether it is run eagerly against a
uniform random function or lazily from an independent uniform raw tape.
Repeated semantic queries are handled by the cache and cost no fresh sample. -/
theorem eagerOracleRun_uniform_eq_cachedOracleRun_uniform
    [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (program : CachedOracleProgram Q A S) (initial : S) (budget : ℕ) :
    Dist.fTransform
        (fun oracle : Q → A =>
          eagerOracleRun program oracle initial budget)
        (Dist.uniform (Q → A)) =
      Dist.fTransform
        (fun values : Fin budget → A =>
          (cachedOracleRun program initial values).control)
        (Dist.uniform (Fin budget → A)) := by
  classical
  let paddedSchedule := cachedAdaptiveSchedule program initial budget
  let eagerObserve : (Q ⊕ Fin (budget + 1) → A) → S := fun oracle =>
    eagerOracleRun program (semanticOracle oracle) initial budget
  let lazyObserve : (Fin budget → A) → S := fun values =>
    (cachedOracleRun program initial values).control
  have eagerMarginal :
      Dist.fTransform eagerObserve
          (Dist.uniform (Q ⊕ Fin (budget + 1) → A)) =
        Dist.fTransform
          (fun oracle : Q → A =>
            eagerOracleRun program oracle initial budget)
          (Dist.uniform (Q → A)) := by
    unfold eagerObserve
    change Dist.fTransform
        ((fun oracle : Q → A =>
          eagerOracleRun program oracle initial budget) ∘ semanticOracle)
          (Dist.uniform (Q ⊕ Fin (budget + 1) → A)) = _
    rw [← Dist.fTransform_comp,
      semanticOracle_uniform (Q := Q) (P := Fin (budget + 1)) (A := A)]
  have rawUniform :
      Dist.fTransform
          (fun oracle => adaptiveRun paddedSchedule oracle budget)
          (Dist.uniform (Q ⊕ Fin (budget + 1) → A)) =
        Dist.uniform (Fin budget → A) := by
    exact adaptiveRun_uniform_eq_uniform_of_fresh paddedSchedule budget
      (cachedAdaptiveSchedule_fresh program initial budget)
  have replayPointwise : eagerObserve =
      lazyObserve ∘
        (fun oracle => adaptiveRun paddedSchedule oracle budget) := by
    funext oracle
    exact (cachedOracleRun_adaptiveRun program initial budget oracle budget).1.symm
  rw [← eagerMarginal, replayPointwise, ← Dist.fTransform_comp,
    rawUniform]

end MDSimulator
end RandomSystemsModel
end SequenceHash
