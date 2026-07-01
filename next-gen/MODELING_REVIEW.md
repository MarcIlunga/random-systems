# CR18 NextGen Modeling Review

Date: 2026-06-25

Scope: adversarial modeling review of every file in `next-gen/NextGen/*.lean`, plus the two CR18 review/formalization rubrics and `papers/CR18_LN.txt`. No Lean source edits were made.

Files read: `BlindAbsorption.lean`, `BlindConverter.lean`, `CausalApply.lean`, `CondEquiv.lean`, `Distinguishing.lean`, `GameEquivalence.lean`, `HCTR2.lean`, `Lemma415.lean`, `MaxWinProb.lean`, `PDS.lean`, `PFunConverter.lean`, `PFunDDS.lean`, `PFunFix.lean`, `PreWinFactorization.lean`, `ReductionByConverter.lean`, `ReductionByInstantiation.lean`, `RelateGameDistinguishing.lean`, `SwitchingLemma.lean`, `SystemMBO.lean`, `Theorem417.lean`, `WinProb.lean`.

Paper anchors used:

- `papers/CR18_LN.txt:5595-5605`: Theorem 4.17 starts from a base `(X,Y)`-system `S`; an MBO is defined to obtain `Shat`, and the conclusion is the blind-game bound.
- `papers/CR18_LN.txt:5689-5695`: the proof chain constructs `Shat`, `That`, `bShat`, and the copying converter; these are not arbitrary inputs.
- `papers/CR18_LN.txt:5719-5730`: Lemma 4.19 is the filtered URP-URF switching result `Delta([q]R,[q]P) <= ...`, reducing through `Gamma(b[q]Rhat)`.
- `papers/CR18_LN.txt:5489-5491`: `S^-` is obtained from an MBO system by ignoring the MBO bit.

## Must-Fix Findings

### 1. `Theorem417.theorem_4_17_condEquiv` takes the derived game as an input

Location: `next-gen/NextGen/Theorem417.lean:398`

Offending signature:

```lean
theorem theorem_4_17_condEquiv (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (maxWinProb Shat : ℝ)
```

Why unfaithful: this is the exact enhanced-object-as-input pattern the rubric forbids. The theorem is stated over a free `Shat`, then assumes `hCE` and `hmono`. The paper does not say "for any MBO-carrying system `Shat`"; it says that for a base `(X,Y)`-system `S`, one defines an MBO to obtain the concrete enhanced game `Shat`. The statement also proves only the adaptive `Gamma(Shat)` helper, while the PDF headline is the blind `Gamma(bShat)` bound.

Fix direction: the public Theorem 4.17 should take base systems, e.g. `S : PFunPDS X Y` and `T : PFunPDS X Y`, plus the actual MBO/enhancement data. The statement should construct `Shat := gameOf S ...` internally and prove or require only genuine standing facts about that construction: `PFunPDS.ignoreMBO Shat = S`, `MonotoneMBO Shat`, and `Shat |≡ T`. The conclusion should be either the PDF bound `Delta(S,T) <= Gamma(bShat)` or the per-distinguisher/per-winner absorbed form that immediately implies it.

### 2. Blind Theorem 4.17 variants keep the same free-`Shat` punt

Locations: `next-gen/NextGen/BlindConverter.lean:150`, `next-gen/NextGen/BlindConverter.lean:184`

Offending signatures:

```lean
theorem theorem_4_17_condEquiv_blind (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist)
    (hblind : ∀ d ∈ D.support, IsBlindDDD d) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ)
```

```lean
theorem theorem_4_17_condEquiv_blind_winProb (D : Dist (PFunDDS.DDD X Y))
    (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) Shat : ℝ)
```

Why unfaithful: these are useful helper shapes, but not faithful CR18 theorem endpoints. They still take `Shat` and its core properties as inputs. The first also adds `hblind`, although the paper's all-distinguisher Theorem 4.17 obtains blindness by absorption through the copying converter, not by assuming the original distinguisher is blind.

Fix direction: keep these as internal lemmas with names that state their helper role. The public theorem must construct `Shat` from base `S`, construct the absorbed blind winner from `D` and `T`, and derive blindness rather than assuming it on `D`.

### 3. Absorbed Theorem 4.17 is closest to the paper but still abstracts away the construction

Locations: `next-gen/NextGen/BlindAbsorption.lean:629`, `next-gen/NextGen/BlindAbsorption.lean:667`

Offending signatures:

```lean
theorem theorem_4_17_condEquiv_absorbed_winProb (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (winProb (absorbedWinnerDist D T) Shat : ℝ)
```

```lean
theorem theorem_4_17_condEquiv_absorbed (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ)
```

Why unfaithful: the absorption proof is the right proof ingredient, but the statement still starts after the hard modeling step. It lets a caller supply any `Shat` with `hCE` and `hmono`, so it does not certify that the MBO is the intended one for the base system `S`.

Fix direction: expose a paper-facing theorem whose inputs include the base `S`, `T`, query budget, and an enhancement constructor. Internally set `Shat := gameOf S ...`, prove `ignoreMBO Shat = S`, then apply these absorbed lemmas. If an abstract version is kept, name it as an abstract conditional-equivalence/absorption lemma, not as the CR18 theorem.

### 4. `RelateGameDistinguishing.theorem_4_17` is not CR18 Theorem 4.17

Location: `next-gen/NextGen/RelateGameDistinguishing.lean:410`

Offending signature:

```lean
theorem theorem_4_17 (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hST : S ≡ᵍ T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ) ≤ (maxWinProb S : ℝ)
```

Why unfaithful: this is a Lemma 4.16-style corollary over two already-game-enhanced systems and game equivalence. It is not the conditional-equivalence theorem of CR18 4.17. It also concludes the adaptive `Gamma(S)`, not the blind `Gamma(bShat)`.

Fix direction: rename to something like `lemma_4_16_to_adaptive_maxWinProb` or keep private. Reserve `theorem_4_17` for the base-system conditional-equivalence theorem that constructs `Shat` and `That`.

### 5. Concrete paper lemmas are restated as abstract scaffolds with the content as hypotheses

Locations: `next-gen/NextGen/RelateGameDistinguishing.lean:219`, `next-gen/NextGen/Theorem417.lean:274`, `next-gen/NextGen/Theorem417.lean:298`

Offending signatures:

```lean
theorem lemma_4_16 (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool))
    (hadvS : ...)
    (hadvT : ...)
    (hcancel : ...)
    (hWeq : ...)
    (h415 : winProb ... T = winProb ... S) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ)
```

```lean
theorem lemma_4_16'_mass (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEq S T)
    ...
```

```lean
theorem theorem_4_17_mass (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEq S T)
    ...
```

Why unfaithful: these are algebraic assembly lemmas, not the named CR18 results. They take the central content as assumptions: cancellation, Lemma 4.15 equality, and pointwise not-won mass equality. This is exactly the "abstract scaffold" smell in the rubric.

Fix direction: make these private/internal with helper names. A public `lemma_4_16` should take only game systems, game equivalence/pre-winning equivalence, probability/query/totality assumptions, and discharge the cancellation and Lemma 4.15 bridge inside. A public Theorem 4.17 should not take `MassYAfalseEq`; it should prove it for the constructed `Shat` and `That`.

### 6. Eq. 4.39 bridge takes `Shat`, `hCE`, and `hmono` instead of constructing the game

Location: `next-gen/NextGen/Theorem417.lean:216`

Offending signature:

```lean
theorem massYAfalse_gameEnhance_eq (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (hCE : Shat |≡ T) (hTprob : T.isProbDist) (hTtot : CondEquiv.TotalOnNonempty T)
    (hmono : MonotoneMBO Shat)
    (i : ℕ) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse (gameEnhance T Shat) i ys xs = massYAfalse Shat i ys xs
```

Why unfaithful: as a generic algebra lemma this is fine, but it is documented as CR18 Eq. 4.39. In the paper, Eq. 4.39 applies to `That` constructed from the concrete `T` and the concrete enhanced `Shat`, not to an arbitrary `Shat` provided with the hard hypotheses.

Fix direction: keep this as a generic helper, but make the paper-facing Eq. 4.39 theorem specialize it to a constructed `Shat` and `That`, with `hCE` and `hmono` discharged by the enhancement construction.

### 7. Lemma 4.19 is not the filtered URP-URF switching lemma in the paper

Location: `next-gen/NextGen/SwitchingLemma.lean:183`

Offending signature:

```lean
theorem lemma_4_19 (n q : ℕ) (D : Dist (PFunDDS.DDD (Fin (2 ^ n)) (Fin (2 ^ n))))
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (q + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.Ex35.R n n) (PFunPDS.Ex35.P n) : ℝ) ≤ ((q : ℝ) + 1) ^ 2 / (2 * 2 ^ n) := by
  sorry
```

Why unfaithful: CR18 Lemma 4.19 is a `Delta([q]R,[q]P)` statement with the query limit as the filter `[q]` on the systems. This Lean statement is a per-distinguisher result over unfiltered `R` and `P`, with a `QueriesExactly ... (q + 1)` hypothesis and a shifted bound `((q : ℝ) + 1)^2`. That is not the PDF theorem, and the `sorry` hides all of the concrete MBO construction and switching argument.

Fix direction: restate the public lemma as a filtered advantage theorem:

```lean
(maxAdvantage (PFunPDS.filterQueries q (PFunPDS.Ex35.R n n))
              (PFunPDS.filterQueries q (PFunPDS.Ex35.P n)) : ℝ)
  ≤ (q : ℝ)^2 / (2 * 2^n)
```

or a per-`D` version against the filtered systems with `D.isProbDist` and no exact-query hypothesis beyond what the filter enforces. Construct the collision game `Rhat` from `R` inside the proof/statement, use the filtered game `[q]Rhat`, and align the Lean `q` with the paper's `q`.

### 8. Unfiltered `Gamma`/`Gamma^b` is exposed where the paper uses a query filter

Locations: `next-gen/NextGen/BlindAbsorption.lean:667`, `next-gen/NextGen/HCTR2.lean:247`

Offending signatures/comments:

```lean
theorem theorem_4_17_condEquiv_absorbed ... :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ)
```

```lean
-- 2. `Theorem417.theorem_4_17_condEquiv` (CE ⇒ Δ ≤ Γ(b·Ŝ)) lifts to the filtered
--    `maxAdvantage` via the filter monotonicity of `PFunPDS.filterQueries`.
-- 3. `Γ(b·Ŝ)` = the non-adaptive within-query collision probability ...
```

Why unfaithful: for concrete bounded-query results, CR18 uses the filter before taking the blind-game supremum: `Gamma(b[q]Rhat)`, not `Gamma(bRhat)`. The comments in `BlindAbsorption.lean:661-665` correctly admit that unfiltered `Gamma^b` overshoots for the collision game. HCTR2 nevertheless plans to identify `Gamma(b·Shat)` with a within-query collision probability, which is only true for the filtered or per-winner object.

Fix direction: concrete switching/HCTR2 bounds should use the per-winner absorbed theorem or `Gamma^b (PFunPDS.filterQueries q Shat)`. The paper-facing abstract theorem can expose unfiltered `Gamma^b Shat`, but concrete instantiations must not assume an unfiltered `Gamma^b` is birthday-small.

### 9. Game subtypes are defined, then bypassed by raw `PFunPDS X (Y × Bool)` plus side predicates

Locations: `next-gen/NextGen/PDS.lean:2045`, `next-gen/NextGen/PDS.lean:2051`, `next-gen/NextGen/PDS.lean:2061`, `next-gen/NextGen/WinProb.lean:32`, `next-gen/NextGen/WinProb.lean:38`, `next-gen/NextGen/WinProb.lean:71`, `next-gen/NextGen/CondEquiv.lean:115`

Relevant definitions:

```lean
def DDS.IsGame {X : Type u} {Y : Type v} (g : DDS X (Y × Bool)) : Prop := ...
abbrev DDG (X : Type u) (Y : Type v) : Type (max u v) := { g : DDS X (Y × Bool) // g.IsGame }
abbrev PDG (Ω : Type w) (X : Type u) (Y : Type v) : Type _ :=
  Dist.RV (Ω := Ω) (A := PFunDDS.DDG X Y)
```

```lean
def winsDDS (w : PFunDDS.Winner X Y) (g : PFunDDS.DDS X (Y × Bool)) : Prop := ...
noncomputable def winProb (W : Dist (PFunDDS.Winner X Y)) (G : PFunPDS X (Y × Bool)) : NNReal := ...
noncomputable def maxWinProb (G : PFunPDS X (Y × Bool)) : NNReal := ...
def CondEquiv (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) : Prop := ...
```

Why unfaithful: the file correctly says a game is an exclusion subtype/codomain. Later APIs ignore that and work over arbitrary MBO-shaped systems, using `MonotoneMBO Shat` as a free hypothesis only in selected theorems. This permits non-games in `Gamma`, `Gamma^b`, and conditional-equivalence statements. It is the structural reason free `Shat` parameters are easy to write.

Fix direction: introduce a paper-facing probabilistic game type at the distribution level, e.g. a distribution/RV over `DDG`, or a subtype `{G : PFunPDS X (Y × Bool) // ∀ g ∈ G.support, g.IsGame}`. Define `winProb`, `Gamma`, `Gamma^b`, and `CondEquiv` over that game type, or provide constructors that produce that type from a base system plus MBO. Side predicates like `MonotoneMBO Shat` should disappear from named theorem signatures.

### 10. Global totality hypotheses are stronger than the paper's bounded/filter setting

Locations: `next-gen/NextGen/CondEquiv.lean:93`, `next-gen/NextGen/Theorem417.lean:401`, `next-gen/NextGen/BlindConverter.lean:153`, `next-gen/NextGen/BlindAbsorption.lean:632`

Offending pattern:

```lean
def TotalOnNonempty (T : PFunPDS X Y) : Prop :=
  ∀ t ∈ T.support, ∀ xs : List X, xs ≠ [] → xs ∈ PFunDDS.dom t
```

and theorem hypotheses such as:

```lean
(hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
```

Why unfaithful: Maurer's phrase is "defined on the histories under discussion." For bounded-query theorems, the histories under discussion are bounded by `[q]`. A `[q]`-filtered game is intentionally undefined after the query limit, so global `TotalOnNonempty` is the wrong standing assumption for the filtered statements the paper actually uses.

Fix direction: public bounded-query theorems should use `TotalUpTo G q` or obtain it from `PFunPDS.filterQueries`. Reserve `TotalOnNonempty` only for genuinely total base resources, and do not require it for `[q]`-filtered games.

### 11. HCTR2 constructs `hctr2Hat`, but the theorem plan still relies on the wrong Theorem 4.17 interface

Locations: `next-gen/NextGen/HCTR2.lean:158`, `next-gen/NextGen/HCTR2.lean:184`, `next-gen/NextGen/HCTR2.lean:223`, `next-gen/NextGen/HCTR2.lean:240`

Offending signatures/comments:

```lean
abbrev NoInnerCollisionMBO {L : ℕ}
    (Shat : PFunPDS (WideIn F L) (WideOut F L × Bool)) : Prop :=
  MonotoneMBO Shat
```

```lean
def hctr2Hat ... : PFunPDS (WideIn F L) (WideOut F L × Bool) := ...
```

```lean
theorem hctr2_condEquiv ... :
    CondEquiv.CondEquiv (hctr2Hat H ctr) (tweakablePerm (F := F) (L := L)) := by
  sorry
```

```lean
theorem hctr2_stprp_withinquery_bound ... :
    hctr2Advantage H ctr q ≤ ((q * L : ℕ) : ℝ) ^ 2 / (2 * Fintype.card F) := by
  ...
  -- `Theorem417.theorem_4_17_condEquiv` (CE ⇒ Δ ≤ Γ(b·Ŝ))
  sorry
```

Why unfaithful: HCTR2 is better than the generic theorem files because it constructs `hctr2Hat` from the base real system. But `NoInnerCollisionMBO` is only an alias for monotonicity, not a concrete characterization of the no-inner-collision event; the proof obligations proving `ignoreMBO hctr2Hat = hctr2Real`, monotonicity, and conditional equivalence are not exposed as named lemmas. The final theorem plan then invokes the adaptive `Theorem417.theorem_4_17_condEquiv` as if it produced the blind filtered bound.

Fix direction: add concrete HCTR2 bridge lemmas: `ignoreMBO_hctr2Hat`, `hctr2Hat_isGame`/`hctr2Hat_monotoneMBO`, and a collision-event characterization of `innerCollided`. The final theorem should apply a corrected filtered/per-winner absorbed Theorem 4.17 to `PFunPDS.filterQueries q (hctr2Hat H ctr)`, not to an unfiltered abstract `Shat`.

### 12. Real `sorry`s hide exactly the content that determines model faithfulness

Locations: `next-gen/NextGen/SwitchingLemma.lean:186`, `next-gen/NextGen/HCTR2.lean:233`, `next-gen/NextGen/HCTR2.lean:253`

Offending snippets:

```lean
theorem lemma_4_19 ... := by
  sorry
```

```lean
theorem hctr2_condEquiv ... := by
  sorry
```

```lean
theorem hctr2_stprp_withinquery_bound ... := by
  sorry
```

Why unfaithful: these are not harmless proof gaps. They cover the collision-MBO construction, conditional-equivalence proof, query-filter reduction, and birthday-bound connection. Those are precisely the obligations that distinguish a faithful theorem from a vacuous abstract scaffold.

Fix direction: do not treat these files as validated paper theorems until the statements are corrected and the sorries are discharged. In particular, fix the theorem interfaces before filling the proofs.

## Minor / Structural Findings

### 13. `GameEquivalence.lean` labels a tautological factor-through lemma as CR18 Lemma 4.15

Location: `next-gen/NextGen/GameEquivalence.lean:79`

Offending signature:

```lean
theorem gameEquiv_winFun_eq {winFun : PFunPDS X (Y × Bool) → NNReal}
    (hFactors : FactorsThroughPreWinning winFun) {G H : PFunPDS X (Y × Bool)} (hEquiv : G ≡ᵍ H) :
    winFun G = winFun H
```

Why unfaithful: the theorem is true as a generic abstraction, but it is documented as CR18 Lemma 4.15. The paper lemma is about game-winning probabilities, not an arbitrary `winFun` whose factorization is assumed. There is a stronger concrete bridge in `Lemma415.lean`; this older generic theorem should not be the paper-facing result.

Fix direction: rename/document this as a generic helper. The public Lemma 4.15 should be the concrete `winProb` congruence with the factorization proved, not assumed.

### 14. Converter application has multiple public semantic layers and `rfl` aliases for concrete converters

Locations: `next-gen/NextGen/PFunConverter.lean:131`, `next-gen/NextGen/PFunConverter.lean:828`, `next-gen/NextGen/PFunConverter.lean:1189`, `next-gen/NextGen/CausalApply.lean:48`

Offending snippets:

```lean
noncomputable def driveFrom (α : DDC U V X Y) (S : PFunDDS.DDS X Y) : ...
```

```lean
noncomputable def cascadeViaConverter
    (S : PFunDDS.DDS X Y) (T : PFunDDS.DDS Y Z) : PFunDDS.DDS X Z :=
  PFunDDS.cascade S T
```

```lean
noncomputable def combineViaConverter
    (op : Y → Y → Y) (S T : PFunDDS.DDS X Y) : PFunDDS.DDS X Y :=
  PFunDDS.combine op S T
```

```lean
def causalDrive (step : List Y → X ⊕ V) (s : X → Y) : ℕ → List Y → Option V
```

Why risky: the project now has raw DDC fixed-point application, semantic DDS aliases for cascade/combine, and fuel-based causal application. The cascade/combine equations are `rfl` because the converter side is defined to be the native DDS operation, not because `DDC.apply` of the raw converter was proved equivalent. That is acceptable as a private proof strategy, but dangerous as public paper-facing evidence.

Fix direction: choose one paper-facing converter-application API. If semantic aliases are kept, name them as native semantic constructions and separately prove that raw `cascadeConverter`/`combineConverter` realize them under `DDC.apply`. Keep driver/fuel machinery private or in implementation namespaces.

### 15. Public `[DecidableEq P]` on resource interface attachment is avoidable

Locations: `next-gen/NextGen/PFunConverter.lean:1220`, `next-gen/NextGen/PFunConverter.lean:1470`

Offending snippet:

```lean
variable {P : Type u} [DecidableEq P]
```

Why minor: this is not a DDS/winner-carrier `Fintype` leak, and interface labels may often be finite. Still, CR18 resource interface labels are mathematical labels, and the public attachment theorem should not require decidable equality if classical case splits suffice.

Fix direction: localize decidability with `classical`/`if h : p = i` in proofs and definitions, or make clear that this section formalizes decidable finite interface sets only.

### 16. Sample-space `Fintype` in transcript conditional bridge is stronger than needed

Location: `next-gen/NextGen/PDS.lean:1994`

Offending signature:

```lean
theorem transcriptCond_eq_behaviorOf {Ω₁ : Type w} {Ω₂ : Type z}
    [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    ...
```

Why minor: this is not a DDS/PDS/winner carrier leak. But the surrounding `Dist` model already works with finite support, and CR18 does not restrict ambient sample spaces to `Fintype`. This can become an unnecessary hypothesis on downstream behavior/transcript theorems.

Fix direction: prove the bridge using finite support of `Dist.ProbDist` and `Dist.mass_prod_and`, not `Fintype Ω₁/Ω₂`.

### 17. `stripMBO` and `ignoreMBO` duplicate Definition 4.18

Locations: `next-gen/NextGen/SystemMBO.lean:29`, `next-gen/NextGen/RelateGameDistinguishing.lean:35`, `next-gen/NextGen/RelateGameDistinguishing.lean:185`

Offending pattern:

```lean
def PFunDDS.stripMBO ...
noncomputable def PFunPDS.stripMBO ...
```

and separately:

```lean
def ignoreMBO ...
noncomputable def PFunPDS.ignoreMBO ...
```

Why minor: the definitions appear extensionally identical, but two public names for the same paper object invite theorem drift (`S^-` lemmas can be proved for one and not the other).

Fix direction: keep one canonical Definition 4.18 API and make the other notation an abbrev or deprecated alias with simp lemmas equating them.

## Explicit Non-Findings

- `HCTR2.lean` does construct `hctr2Hat` from base data; it does not itself use the primary free-`Shat` theorem signature pattern. The finding is that the supporting theorem interface it plans to call is wrong, and that the HCTR2-specific bridge lemmas are still sorries/missing.
- `PreWinFactorization.lean` takes `Shat` in generic factorization lemmas, but those are not public concrete CR18 endpoints. I did not count those as primary enhanced-object-as-input defects.
- `PDS.lean` correctly introduces the list-of-random-variables transcript distribution and proves `transcriptDist_eq_mul` by `Dist.mass_prod_and`. I did not flag the deterministic `PFunDDS.transcript` itself because it is used as an execution/winner read, while the behavior/transcript-distribution primitive is modeled separately.
- I found no `admit`, `axiom`, or `unsafe` in `next-gen/NextGen/*.lean`.
