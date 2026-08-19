# Exact, reshape, coupling, winnability, and the metric receipt

## Contents

- Family I — exact (distance is zero)
- Family II — reshape
- Coupling
- Winnability
- Condition-based (legacy)
- Family IV — reductions
- Family V — composition and amplification
- The metric receipt

---

Families I, II, IV, V, the two remaining family-III techniques, and the step people forget
at the end.

## Family I — exact: show the distance is **zero**

**Check this first.** It is cheapest when available and routinely overlooked in favour of a
bound. A `δ = 0` proof beats every `δ ≤ ε` proof.

| technique | where | when |
|---|---|---|
| **behavioural equivalence / quotient** | `RandomSystems/RandomSystemQuotient.lean`, `Legacy.Equiv` (`≡ₚ`) | the two systems are the *same object* in the behavioural quotient |
| **relabelling invariance** | `RandomSystems/StrictRelabel.lean` | bijective renaming of query/answer alphabets is invisible to the metric |
| **query compression** | `compressedQuery_bound` | normalisation — the standard preprocessing before any count |
| **non-adaptive sufficiency** | `lemma_2_18_nonadaptive_environments_suffice` (`RandomSystems/LanzenbergerChain.lean`) | when it applies, **the entire adaptive apparatus disappears** |
| **fundamental theorem** | `delta_eq_advantage` (LM20 Thm 1) | `Δ(S,T) = Adv(S,T)` — an identification, move between the two sides at will |

Non-adaptive sufficiency is worth an explicit check on every new proof. The only creative
content is verifying the hypothesis applies.

## Family II — reshape: rewrite `Δ` into `Δ`s you can attack

Pure algebra, and **the step a model most often omits.** Attacking `Δ(Real, Ideal)` head-on
when a hybrid splits it into two easy halves is the most common self-inflicted difficulty in
this repo.

| move | lemma | you supply |
|---|---|---|
| **hybrid / triangle** | `maxAdvantage_triangle` | **the intermediate system `T`** — the only creative bit. No side conditions; the workhorse |
| **data processing** | `maxAdvantage_apply_le` | the converter `α`, and `Emulable α`. A converter cannot increase advantage |
| **parallel composition** | `maxAdvantage_par_le` | nothing (4 `isProbDist`) |
| **query restriction** | `maxAdvantage_filterQueries_le` | nothing (2 `TotalOnNonempty`) |
| **branch additivity** | `delta_sum_cons_pushforwards_…` (LM20 Lemma 2) | the disjoint cell decomposition. `δ` is additive across disjoint support cells, **no normalisation needed** |
| **descent** | `maxAdvantage_le_of_forall_advantage_le` | nothing — but it fixes `D`, which family III needs. **The doorway** from `Δ` into transcript-level reasoning |

Model application, `RandomSystems/CBCMAC.lean:1099-1118` — a headline theorem with **no new
mathematics at all**: a triangle, a DPI hop through converter monotonicity (CBC makes at
most `L` round-function calls per message), and the switching lemma.

```lean
calc Δ(⌈q⌉ cbcRealP bf, ⌈q⌉ Vn)
    ≤ Δ(⌈q⌉ cbcRealP bf, ⌈q⌉ cbcReal bf) + Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) := maxAdvantage_triangle _ _ _
  _ ≤ Δ(⌈q*L⌉ 𝖯 X, ⌈q*L⌉ 𝖱 X) + Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn)            := … maxAdvantage_filterQueries_applyDDC_le …
  _ ≤ …                                                                := … switching lemma …
```

## Coupling — the bad thing is **disagreement**

`RandomSystems/Coupling.lean:136`

```lean
coupling_bound {X Y : Dist A} (C : DistCoupling X Y) : statDist X Y ≤ C.prDisagree
```

with `DistCoupling` (`:41`) = a joint distribution plus proofs that its marginals are `X`
and `Y`.

**Two library facts that end whole categories of deliberation:**

- `system_coupling_exists` — a coupling **always** exists (LM20 Thm 2). Never argue about
  whether the technique applies. *(Legacy layer: `RandomSystems/Legacy/SystemCoupling.lean`.)*
- `optimal_probability_coupling_exists` (`RandomSystems/RandomSystemCoupling.lean`) — the
  **optimal** coupling's disagreement **equals** `Δ`. So the *technique* has no inherent
  slack: there is always a coupling that is exactly tight.

### But your coupling is lossy until you show it is the optimal one

Do not read the second fact as "coupling is never lossy". It says an optimal coupling
*exists*, not that the one you wrote is it. `coupling_bound` is an inequality, and the gap
between `C.prDisagree` and `Δ` is entirely your construction's.

This distinction is load-bearing, and the tree contains a worked case of both sides.
`RandomSystems/SoP/SoP2.lean` builds **two** couplings of the same pair of systems:

| coupling | result | status |
|---|---|---|
| Proposition 5, *maximal* tape coupling | Theorem 6: `Adv = ½ Σ_y \|C_G(y)/(N)_m² − 1/N^m\|` | **exact** — an equality |
| Proposition 8, *sequential/online* coupling | Corollary 9: `Adv ≤ 2q³/3N²` | a bound, and knowingly loose |

`SoP2.md` says so in as many words: the online construction is *"weaker than the optimal
coupling above, but exposes an actual online disagreement event and gives a clean all-group
bound"*, and *"Proposition 5's global maximal coupling is not a substitute for Proposition
8's sequential joint"*.

The lesson generalises. A tractable coupling is usually **not** the optimal one, and the
trade is deliberate: the maximal coupling is exact but its disagreement is a quantity you
then have to estimate (here, a compatible-count L¹ deviation — the actual research problem);
the online coupling is suboptimal but its failure event is something you can bound step by
step.

So when a coupling gives a bound you think is loose, there are **two** places the loss can
be, and you must say which: the coupling itself, or the estimate of its disagreement.

**Obligations:** the joint distribution (`[CREATIVE]`), its two marginal proofs
(`[ROUTINE]` if the joint was built right), and a bound on `prDisagree` (`[CREATIVE]`).

Choose it when the two systems can be **run on shared randomness**. Plumbing:
`RandomSystems/DistCoupling.lean`, `RandomSystemCoupling.lean`, `MultiSystemCoupling.lean`.

No labelled spine yet — apply `coupling_bound` directly and `sorry` the two creative parts.

## Winnability — the bad thing is **the adversary winning**

`Δ ≤ ν(S^A)`. Thesis-shape statement `theorem_2_37_winnability_theorem`
(`RandomSystems/LanzenbergerChain.lean:281`); the proved workhorse is
`winnability_theorem_of_fixed_domain_and_bounded` (`RandomSystems/GameWinnability.lean`).

**Creative:** the MBO, and the winning-probability bound.

This overlaps conditional equivalence heavily — CE *is* a winnability argument with the game
constructed for you by `gameOf`. **Prefer CE** unless the game is given to you rather than
derived from a condition.

## Condition-based (Maurer EUROCRYPT 2002)

`statDist_le_conditionFailure_single` (`RandomSystems/Legacy/ConditionBased.lean:241`), with
`TranscriptCondition X Y q` (`:60`) and `maxConditionFailure` (`:88`).

**Route with care.** This lives in the `Legacy` struct model (`Fin q → X × Y` transcripts,
`Fintype (DDS …)`), not the PFun next-gen surface the rest of the pipeline speaks. Its
statement is clean and its examples are canonical ("no internal collision" in CBC-MAC, "all
outputs distinct" for the switching lemma) — but a proof starting here must cross the legacy
bridge (`RandomSystems/Legacy/`, `HTechnique/LegacyBoundary.lean`) to compose with anything.

**Default: use conditional equivalence instead** for the same mathematics on the modern
surface. Reach for condition-based only when already inside the legacy layer.

## Family IV — reductions: trade this problem for another

| technique | where | you supply |
|---|---|---|
| **by converter** | `CausalApply.winProb_apply` (CR18 §4.7.2) | the converter and the solver map `ρ`. `winProb W (convert G) = winProb (ρ W) G` |
| **by instantiation** | CR18 §4.7.3, `RandomSystems/ReductionByInstantiation.lean` | `σ^q` maps a solver to its `q`-fold independent instantiation |
| **costed / game hopping** | `RandomSystems/Complexity/`, `GameHop`, `GameSeq` | the hop sequence |

## Family V — composition and amplification

| technique | where |
|---|---|
| **CC composition theorem** | `Legacy.CC.Composition` — the reason modular proofs work |
| **amplification** | `amplification_theorem` (LM20 Thm 3), `RandomSystems/Legacy/Amplification.lean` |
| **threshold combiners** | `threshold_combiner_bound_1_2` (LM20 Defs 14–15), same file |
| **absorption / blinding** | `RandomSystems/AbsorbDPI.lean`, `BlindAbsorption.lean`, `BlindConverter.lean` (Def 4.20) |

**Legacy-layer warning, same as condition-based:** `system_coupling_exists`,
`amplification_theorem`, `threshold_combiner_bound_1_2` and `delta_eq_advantage` live under
`RandomSystems/Legacy/`. They are proved and citable, but composing them with the PFun
next-gen surface means crossing the legacy bridge. Check what layer your statement is in
before building a `calc` through them.

## The metric receipt — do not leave slack here

`Δ` is the advantage; `maxEDist` is the strict-context metric. The relation:

- `maxEDist ≤ ofReal Δ` — **unconditionally**, on the unrestricted carrier.
- `maxEDist = ofReal Δ` — **on the shared-domain subcarrier**, i.e. on every
  Lanzenberger-Def-2.14 object. Kernel-checked as
  `StrictContextSharedDomain.maxEDist_filterDom_eq_ofReal_maxAdvantage`.

Applied at `RandomSystems/CBCMAC.lean:1875` and `:1891`.

**Rule:** state headline results in `Δ`, then attach the equality receipt if the metric form
is wanted. One lemma application. Never re-derive the metric/advantage relationship, and
**never quietly accept the `≤` form when the `=` receipt is available** — that is silent
slack in a headline bound, and it is invisible to anyone reading the statement.

The gap between the two sides is a CR18 deletion rewind on the *advantage* side.
`RandomSystems/AttainmentCounterexample.lean` proves `maxAdv = ½` with class-distance 1 —
note it makes **no `maxEDist` statement**, so do not cite it as one.
