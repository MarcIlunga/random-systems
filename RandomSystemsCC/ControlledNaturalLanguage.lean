/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCrypto.ControlledNaturalLanguage
import RandomSystems.TotalityTactics
import RandomSystems.SwitchingLemma
import RandomSystems.HTechnique.Derivation
import RandomSystemsCC.TypedConstruct

/-!
# Controlled natural language for random-systems proofs

The `rs.` vocabulary anticipated by `AbstractCrypto.ControlledNaturalLanguage`
("a downstream `CC` or `RandomSystemsCC` controlled-language module may add
scoped sentences to the same namespace").  The sentences are organized as
**proof styles**, so each paper argument keeps its own shape:

* **Condition C** (`rs.condition_c.*`) — Maurer's two transitions on CR18
  PDF page 62: Theorem 4.17 gives the blind-game inequality, Lemma 4.18
  discharges the remaining blind game.
* **H coefficients** (`rs.h_coefficient.*`) — the Patarin skeleton: a bad
  event, a probability ratio on good transcripts, and an ideal-world
  bad-transcript probability, entering through the existing derivation-layer
  theorems `adv_le_of_fixedQuery_ratio_of_good`, `adv_le_of_fixedQuery_ratio`
  (perfect form, `Bad = ∅`), and `adv_le_of_fixedQuery_eq_on_good`.
* **Construction assembly** (`rs.construction.*`) — MauRen11 §5.1 Definition
  3 on the interface-indexed carrier: entering the leaf of a construction,
  MauRen11's availability clause from its security clause, the honest/
  adversary commutation premise, and Theorem 1(i) serial composition.  Every
  sentence here lowers to one `rs_*` command of
  `RandomSystemsCC.TypedConstruct`, which in turn selects one named theorem.

Two sentence granularities coexist, so the mathematics is displayed rather
than buried:

* **structure sentences** open a skeleton theorem and leave exactly its
  mathematical legs as goals (`?good_ratio`, `?bad_probability`,
  `?pointwise_ratio`, `?good_equality`).  What they discharge silently is
  strictly non-argument bookkeeping: `KStepTotal` side conditions
  (`cr18_total`), `NNReal` cast arithmetic such as `δ + 0 = δ`, and the
  degenerate `defect > 1` branch, where the advantage of total systems is
  at most `1`;
* **summary sentences** cite one finished endpoint theorem when the
  argument's structure is not the point.

## Writing standard

The wording is the working prose of H-coefficient security proofs
(Patarin's technique as written up by Chen–Steinberger-style papers) and of
CR18, following the corpus rule of `AbstractCrypto.ControlledNaturalLanguage`:
sentences are taken from what the papers actually say, not invented.  The
recurring phrases are “the bad event is …”, “good transcripts”, “the ideal
world”, “the ratio of real to ideal probabilities is at least one minus the
defect”, “equally likely in both worlds”, “the birthday bound”, and “since
otherwise the bound is trivial”.  Three grammar rules keep every sentence
plain English:

1. a sentence is a complete clause with articles and a finite verb;
   parameters enter through predicative phrases (“the bad event is ⟨B⟩”,
   “the ratio defect is ⟨ε⟩”), never a bare parameter list;
2. a citation attaches the way papers attach reasons: a trailing
   “…, by ⟨ref⟩”, or “… using ⟨ref⟩” where the verb takes an instrument
   (“we obtain … using”, “… gives the bound using”);
3. a hypothesis is named with the labeling idiom of paper prose:
   “; call this assumption ⟨h⟩”;
4. a sentence never repeats a quantity the statement already fixes — a
   parameter that unification can read off the goal is omitted (the wlog
   guard says “the stated bound”, carrying no term, exactly as a paper
   refers back to a displayed formula).

No sentence performs proof search or theorem selection: every citation is an
explicit `cryptoCnlReference`, optionally annotated with a quoted prose
comment that is retained for the reader and ignored by the elaborator.
`set_option trace.CryptoControlledNaturalLanguage.sentence true` shows each
sentence's stable label as it elaborates.
-/

open Lean Elab Tactic

namespace RandomSystems.CR18.HTechniqueDerivation

/-- Degenerate-branch reduction for an `NNReal`-coerced advantage bound: it
suffices to prove the bound assuming it is at most one, since above one it
holds trivially (total systems have advantage at most `1`).  The bound is
read off the goal, so the controlled sentence needs no term.  (Belongs next
to `adaptiveTranscriptAdvantage_le_one`; parked here to avoid a
`Derivation.lean` rebuild.) -/
theorem adv_le_coe_of_le_one_imp {X Y : Type*} {q : ℕ}
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (eps : NNReal) (h : eps ≤ 1 → Adv[q](S, T) ≤ (eps : ℝ)) :
    Adv[q](S, T) ≤ (eps : ℝ) := by
  by_cases h1 : eps ≤ 1
  · exact h h1
  · exact le_trans (adaptiveTranscriptAdvantage_le_one S T hS hT)
      (by exact_mod_cast (not_le.mp h1).le)

end RandomSystems.CR18.HTechniqueDerivation

namespace CryptoControlledNaturalLanguage

/-! ### Bookkeeping dischargers (deliberately not sentences)

These close the side conditions a paper proof never writes down.  They are
scoped tactic macros, not controlled sentences, and appear only inside
sentence expansions. -/

-- `urp` totality postdates the `Cr18Total` freeze in `TotalityTactics.lean`;
-- register it here so `cr18_total` covers both switching worlds.  (Move next
-- to `urp_KStepTotal` at the next planned `Derivation.lean` rebuild.)
attribute [aesop safe apply (rule_sets := [Cr18Total])]
  RandomSystems.CR18.HTechniqueDerivation.urp_KStepTotal

/-- Discharge a `KStepTotal` totality side condition: a hypothesis or a
standard-constructor fact, via `cr18_total` and the `Cr18Total` rule set. -/
scoped macro "rs_cnl_total" : tactic =>
  `(tactic| first
      | cr18_total
      | fail "cannot discharge this totality side condition; provide it as a hypothesis")

/-- Close the residual bound arithmetic between a skeleton conclusion
`((δ + ε : NNReal) : ℝ)` and the stated bound — cast normalization and
`δ + 0 = δ`, never an estimate. -/
scoped macro "rs_cnl_bound_arith" : tactic =>
  `(tactic| first
      | rfl
      | simp
      | norm_num
      | (push_cast; ring_nf; norm_num)
      | fail "the stated bound does not match `bad probability + defect`")

/-! ### Condition C (CR18 §4.7; Maurer's transitions on PDF page 62) -/

/-- Maurer's “according to Theorem 4.17, we obtain” transition:

`According to the condition C theorem, we obtain the blind game bound using
⟨ref⟩` -/
scoped macro (name := rsCnlTheorem417)
    "According" "to" "the" "condition" "C" "theorem" ","
      "we" "obtain" "the" "blind" "game" "bound" "using"
      proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.condition_c.theorem_417" =>
      exact $proof)

/-- Maurer's “It remains to analyze ...; hence Lemma 4.18 can be applied”
transition:

`It remains to analyze the blind game; the birthday lemma gives the bound
using ⟨ref⟩` -/
scoped macro (name := rsCnlLemma418)
    "It" "remains" "to" "analyze" "the" "blind" "game" ";"
      "the" "birthday" "lemma" "gives" "the" "bound" "using"
      proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.condition_c.lemma_418" =>
      exact $proof)

/-- Summary citation of a finished condition-C switching endpoint:

`The condition C argument gives the switching bound using ⟨ref⟩` -/
scoped macro (name := rsCnlConditionCSwitching)
    "The" "condition" "C" "argument" "gives" "the" "switching" "bound"
      "using" proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.condition_c.switching" =>
      exact $proof)

/-! ### H coefficients: the degenerate-branch guard -/

/-- Dispose of the degenerate branch where the claimed bound exceeds one,
and continue with the named assumption `⟨h⟩ : bound ≤ 1` in scope:

`We may assume the stated bound is at most one, since otherwise it holds
trivially; call this assumption ⟨h⟩`

The bound is read off the goal, so the sentence carries no term — as in a
paper, where the quantity has already been stated.  The branch itself
(total systems have advantage at most `1`), the totality side conditions,
and the `ℝ`/`NNReal` cast are the hidden bookkeeping. -/
scoped macro (name := rsCnlDefectWlog)
    "We" "may" "assume" "the" "stated" "bound" "is" "at" "most" "one" ","
      "since" "otherwise" "it" "holds" "trivially" ";"
      "call" "this" "assumption" h:ident : tactic =>
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.defect_wlog" =>
      refine RandomSystems.CR18.HTechniqueDerivation.adv_le_coe_of_le_one_imp
        _ _ (by rs_cnl_total) (by rs_cnl_total) _ (fun $h => ?_))

/-! ### H coefficients: the technique skeletons

Each skeleton opens one existing derivation-layer theorem and leaves exactly
its mathematical legs as named goals.  The totality side conditions and the
final `δ + ε` cast arithmetic are discharged silently. -/

/-- The Patarin good/bad skeleton (`adv_le_of_fixedQuery_ratio_of_good`):

`We apply the H coefficient technique: the bad event is ⟨B⟩, the ratio
defect is ⟨ε⟩, and the bad probability is at most ⟨δ⟩`

Leaves `?good_ratio` — the fixed-query probability ratio away from the bad
event — and `?bad_probability` — the ideal-world bad-transcript bound,
uniform over environments. -/
scoped macro (name := rsCnlGoodBadSkeleton)
    "We" "apply" "the" "H" "coefficient" "technique" ":"
      "the" "bad" "event" "is" badEvent:cryptoCnlReference ","
      "the" "ratio" "defect" "is" eps:cryptoCnlReference "," "and"
      "the" "bad" "probability" "is" "at" "most"
      delta:cryptoCnlReference : tactic => do
  let badEvent ← referenceTerm badEvent
  let eps ← referenceTerm eps
  let delta ← referenceTerm delta
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.good_bad" =>
      refine le_trans
        (RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_ratio_of_good
          _ _ $badEvent $eps $delta (by rs_cnl_total) (by rs_cnl_total)
          ?good_ratio ?bad_probability)
        (by rs_cnl_bound_arith))

/-- The equality-on-good skeleton (`adv_le_of_fixedQuery_eq_on_good`):

`We apply the H coefficient technique: the bad event is ⟨B⟩, good
transcripts are equally likely in both worlds, and the bad probability is
at most ⟨δ⟩`

Leaves `?good_equality` and `?bad_probability`. -/
scoped macro (name := rsCnlEqOnGoodSkeleton)
    "We" "apply" "the" "H" "coefficient" "technique" ":"
      "the" "bad" "event" "is" badEvent:cryptoCnlReference ","
      "good" "transcripts" "are" "equally" "likely" "in" "both"
      "worlds" "," "and" "the" "bad" "probability" "is" "at" "most"
      delta:cryptoCnlReference : tactic => do
  let badEvent ← referenceTerm badEvent
  let delta ← referenceTerm delta
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.eq_on_good" =>
      refine le_trans
        (RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
          _ _ $badEvent $delta (by rs_cnl_total) (by rs_cnl_total)
          ?good_equality ?bad_probability)
        (by rs_cnl_bound_arith))

/-- The perfect skeleton (`adv_le_of_fixedQuery_ratio`, `Bad = ∅`):

`We apply the perfect H coefficient technique, with no bad transcripts`

The defect is read off the stated bound; leaves `?pointwise_ratio`. -/
scoped macro (name := rsCnlPerfectSkeleton)
    "We" "apply" "the" "perfect" "H" "coefficient" "technique" ","
      "with" "no" "bad" "transcripts" : tactic =>
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.perfect" =>
      refine RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_ratio
        _ _ _ (by rs_cnl_total) (by rs_cnl_total) ?pointwise_ratio)

/-- The perfect skeleton with the defect named explicitly, for statements
whose bound is not literally the coerced defect:

`We apply the perfect H coefficient technique, with no bad transcripts and
ratio defect ⟨ε⟩` -/
scoped macro (name := rsCnlPerfectSkeletonWithDefect)
    "We" "apply" "the" "perfect" "H" "coefficient" "technique" ","
      "with" "no" "bad" "transcripts" "and" "ratio" "defect"
      eps:cryptoCnlReference : tactic => do
  let eps ← referenceTerm eps
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.perfect" =>
      refine le_trans
        (RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_ratio
          _ _ $eps (by rs_cnl_total) (by rs_cnl_total) ?pointwise_ratio)
        (by rs_cnl_bound_arith))

/-! ### H coefficients: the mathematical legs

Each leg closes one skeleton goal from one explicit citation, attached the
way papers attach reasons — a trailing “, by ⟨ref⟩”.  The hidden step is at
most an `intro` and the `simp` normalization of a vacuous defect
(`(1 - 0) · x = x`) — never an estimate. -/

/-- Close `?good_ratio`:

`On good transcripts, the ratio of real to ideal probabilities is at least
one minus the defect, by ⟨ref⟩` -/
scoped macro (name := rsCnlGoodRatioLeg)
    "On" "good" "transcripts" "," "the" "ratio" "of" "real" "to" "ideal"
      "probabilities" "is" "at" "least" "one" "minus" "the" "defect" ","
      "by" proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.good_ratio" =>
      (intro xs t h_good
       first
         | exact $proof xs t h_good
         | simpa using $proof xs t h_good))

/-- Close `?good_equality`:

`On good transcripts, the real and ideal probabilities are equal, by ⟨ref⟩` -/
scoped macro (name := rsCnlGoodEqualityLeg)
    "On" "good" "transcripts" "," "the" "real" "and" "ideal"
      "probabilities" "are" "equal" "," "by"
      proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.good_equality" =>
      (intro xs t h_good
       first
         | exact $proof xs t h_good
         | simpa using $proof xs t h_good))

/-- Close `?bad_probability` when the bad event is a collision bounded by
the adaptive birthday argument (the recurring random-systems case):

`The probability of a bad transcript in the ideal world is at most the
birthday bound, by ⟨ref⟩` -/
scoped macro (name := rsCnlBadBirthdayLeg)
    "The" "probability" "of" "a" "bad" "transcript" "in" "the" "ideal"
      "world" "is" "at" "most" "the" "birthday" "bound" "," "by"
      proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.bad_probability" =>
      (intro E
       first
         | exact $proof E
         | simpa using $proof E))

/-- Close `?bad_probability` from a general per-environment bound:

`The probability of a bad transcript in the ideal world is at most the
stated bound, by ⟨ref⟩` -/
scoped macro (name := rsCnlBadProbabilityLeg)
    "The" "probability" "of" "a" "bad" "transcript" "in" "the" "ideal"
      "world" "is" "at" "most" "the" "stated" "bound" "," "by"
      proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.bad_probability" =>
      (intro E
       first
         | exact $proof E
         | simpa using $proof E))

/-- Close `?pointwise_ratio`:

`The ratio of real to ideal probabilities is at least one minus the defect
on every transcript, by ⟨ref⟩` -/
scoped macro (name := rsCnlPointwiseRatioLeg)
    "The" "ratio" "of" "real" "to" "ideal" "probabilities" "is" "at"
      "least" "one" "minus" "the" "defect" "on" "every" "transcript" ","
      "by" proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.pointwise_ratio" =>
      (first
        | exact $proof
        | (intro xs t
           first
             | exact $proof xs t
             | simpa using $proof xs t)))

/-- Summary citation of a finished perfect H-coefficient endpoint:

`The perfect H coefficient argument gives the switching bound using ⟨ref⟩` -/
scoped macro (name := rsCnlPerfectHCoefficientSwitching)
    "The" "perfect" "H" "coefficient" "argument" "gives" "the"
      "switching" "bound" "using" proof:cryptoCnlReference : tactic => do
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.h_coefficient.switching" =>
      exact $proof)

/-! ### Construction assembly (MauRen11 §5.1 Definition 3, Theorem 1)

Four sentences over `RandomSystemsCC.TypedConstruct`.  Each carries exactly
one inference and lowers to exactly one `rs_*` command; the ideal resource,
the simulator and the admitted simulator class are never inferred — they are
already displayed in the goal or cited as arguments.

**Token discipline.**  These sentences add exactly two parser atoms,
`availability` and `composition`, each verified to have no code occurrence in
either repository.  Every other content word is parsed as an `ident` and
validated by `expectWord`, following
`AbstractCrypto.ControlledNaturalLanguage` — so `construction`, `simulator`,
`protocol`, `honest`, `filter`, `advantage` and `coupling` all remain usable
as Lean identifiers, which they are (`Symmetric/OTP.lean` binds `simulator`
and `security`; `RandomSystems.Complexity.PRG` defines `distinguishing`).
Each sentence is anchored by an **atom** in a position where no other
sentence of this module or of the AC module has one, so alternatives are
separated at parse time rather than by macro-time error. -/

/-- Enter the construction leaf.  The two cited facts are the endpoint's own
normalization of the protocol action and its packing of the ideal resource;
what remains is the paper's advantage inequality:

`It remains to bound the distinguishing advantage, by ⟨normalized⟩ and
⟨target⟩`

Typed converter composition, the converter action, boundary alignment and the
`ℝ`/`ℝ≥0∞` boundary are the hidden bookkeeping — never an estimate. -/
scoped macro (name := rsCnlBoundAdvantage)
    "It" "remains" "to" "bound" "the" distinguishingWord:ident
      advantageWord:ident "," "by" normalized:cryptoCnlReference "and"
      target:cryptoCnlReference : tactic => do
  expectWord distinguishingWord "distinguishing"
  expectWord advantageWord "advantage"
  let normalized ← referenceTerm normalized
  let target ← referenceTerm target
  `(tactic|
    crypto_cnl_sentence "rs.construction.distinguishing_advantage" =>
      rs_construct using $normalized, $target)

/-- Close a construction at every radius from one exact behavioral equality —
the shape a coupling argument produces:

`The perfect construction follows from the coupling ⟨ref⟩` -/
scoped macro (name := rsCnlPerfectConstruction)
    "The" "perfect" constructionWord:ident followsWord:ident "from" "the"
      couplingWord:ident proof:cryptoCnlReference : tactic => do
  expectWord constructionWord "construction"
  expectWord followsWord "follows"
  expectWord couplingWord "coupling"
  let proof ← referenceTerm proof
  `(tactic|
    crypto_cnl_sentence "rs.construction.coupling" =>
      rs_construct using $proof)

/-- MauRen11 Definition 3's availability clause from its security clause:

`The availability condition follows from ⟨security⟩, since the simulator is
idle and the honest protocol commutes with the availability filter`

The two named reasons are left as the two visible goals, in the order the
sentence states them. -/
scoped macro (name := rsCnlAvailability)
    "The" "availability" "condition" followsWord:ident "from"
      security:cryptoCnlReference "," "since" "the" simulatorWord:ident "is"
      idleWord:ident "and" "the" honestWord:ident protocolWord:ident
      commutesWord:ident "with" "the" "availability" filterWord:ident :
      tactic => do
  expectWord followsWord "follows"
  expectWord simulatorWord "simulator"
  expectWord idleWord "idle"
  expectWord honestWord "honest"
  expectWord protocolWord "protocol"
  expectWord commutesWord "commutes"
  expectWord filterWord "filter"
  let security ← referenceTerm security
  `(tactic|
    crypto_cnl_sentence "rs.construction.availability" =>
      rs_availability using $security)

/-- The honest/adversary commutation premise of MauRen11 Theorem 1(i), from
simulator support alone:

`We obtain the commutation of the honest protocol with every admitted
simulator, by ⟨admitted⟩ and ⟨member⟩` -/
scoped macro (name := rsCnlCommutation)
    "We" "obtain" "the" commutationWord:ident "of" "the" honestWord:ident
      protocolWord:ident "with" "every" admittedWord:ident
      simulatorWord:ident "," "by" admitted:cryptoCnlReference "and"
      member:cryptoCnlReference : tactic => do
  expectWord commutationWord "commutation"
  expectWord honestWord "honest"
  expectWord protocolWord "protocol"
  expectWord admittedWord "admitted"
  expectWord simulatorWord "simulator"
  let admitted ← referenceTerm admitted
  let member ← referenceTerm member
  `(tactic|
    crypto_cnl_sentence "rs.construction.commutation" =>
      rs_commute using $admitted, $member)

/-- Name the simulator of a LiuMau20 specification-form leaf.  The wording
follows MaRuTa12's "We use the following simulator … to prove …", narrowed to
MauRen11 Definition 3's own name for the clause it witnesses:

`We use ⟨simulator⟩ to prove the security condition, by ⟨member⟩`

The simulator is an argument, never inferred; its admission is discharged from
the cited membership and the behavioral leg is left as the visible goal. -/
scoped macro (name := rsCnlUseSimulator)
    "We" useWord:ident simulator:cryptoCnlReference "to" proveWord:ident
      "the" securityWord:ident "condition" "," "by"
      member:cryptoCnlReference : tactic => do
  expectWord useWord "use"
  expectWord proveWord "prove"
  expectWord securityWord "security"
  let simulator ← referenceTerm simulator
  let member ← referenceTerm member
  `(tactic|
    crypto_cnl_sentence "rs.construction.simulator" =>
      rs_simulator $simulator using $member)

/-- MauRen11 Theorem 1(i): serial composition of two fixed-`Z` judgments, in
the order the two constructions are written:

`The composition of ⟨first⟩ and ⟨second⟩ is secure, by ⟨admitted⟩` -/
scoped macro (name := rsCnlSerialComposition)
    "The" "composition" "of" first:cryptoCnlReference "and"
      second:cryptoCnlReference "is" secureWord:ident "," "by"
      admitted:cryptoCnlReference : tactic => do
  expectWord secureWord "secure"
  let first ← referenceTerm first
  let second ← referenceTerm second
  let admitted ← referenceTerm admitted
  `(tactic|
    crypto_cnl_sentence "rs.construction.serial" =>
      rs_compose $first, $second using $admitted)

end CryptoControlledNaturalLanguage

/-! ### Elaboration checks

One compiled instance of the skeleton the demo does not exercise
(`eq_on_good`), in the demo's own instance regime.  This is a grammar
elaboration check with trivial witnesses, not mathematics. -/

section ElaborationChecks

open RandomSystems RandomSystems.CR18 RandomSystems.CR18.HTechniqueDerivation
open PFunPDS.Prob (urp)
open scoped RandomSystems.CR18 RandomSystems.CR18.HTechniqueDerivation
  CryptoControlledNaturalLanguage

example (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    Adv[q](urp (X := X), urp (X := X)) ≤ ((0 : NNReal) : ℝ) := by
  We apply the H coefficient technique: the bad event is (fun _ => False),
    good transcripts are equally likely in both worlds, and the bad
    probability is at most 0
  · On good transcripts, the real and ideal probabilities are equal, by
      (fun _ _ _ => rfl)
  · The probability of a bad transcript in the ideal world is at most the
      stated bound, by (fun E => by simp [probBad, Dist.mass_eq_sum])

end ElaborationChecks
