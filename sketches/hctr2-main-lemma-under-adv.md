# HCTR2 §3.4 (Main Lemma) under `Adv` — and what we learned getting there

Stage-1 sketch, second draft. The first draft got the augmentation wrong; §B
records that and the other mistakes, for feeding back into the skill.

---

# A. The design

## A.1 Why H applies directly under `Adv`

`hTechnique_ratio` is carrier-agnostic — two `Dist A`, a predicate, nothing else.
Thesis Def 2.26 is

    Adv S T := sup_e δ( tr(S,e) , tr(T,e) )

so each summand of the supremum is *already* a pair of distributions. H bites
there. No query bound, no verdict distinguisher, no `⊥`-elimination, no
fixed-query→adaptive transfer.

One obstacle, and it is not H's: every packaged H lemma is stated with `[Fintype A]`,
because `statDist` sums over `Finset.univ`. The transcript carrier `List (X × Option Y)` is
infinite. That hypothesis is **removable** rather than essential (B.5) — `Dist` already
carries finite support — so the principled fix is to generalize `statDist` in place. The
`δ`-native lemmas below are the cheaper path taken instead, and additionally drop the weight
equality, which `δ` genuinely does not need. Now in the tree:

* `RandomSystems.CR18.δ_hTechnique_ratio`
* `RandomSystems.CR18.adv_le_of_ratio_of_good`
* `RandomSystems.CR18.adv_le_of_le_on_good`  ← `eps = 0`, which is §3.3 exactly

## A.2 The statement

    Adv^{±rnd}_{HCTR2[Perm(n)]}(q,σ)  ≤  (3σ² + 2qσ + 7σ + 2)/2ⁿ⁺¹

about `rnd` and `hctr2Perm` — **the paper's own two systems**. No augmented world
appears in it. Orientation: `Adv S T` is the excess of `S` over `T`, so the
*ideal* system is first (`rnd`), matching §3.3's two bullets, which are both about
the ideal world `Y`.

## A.3 Augmentation: refine the observation, not the system

**This is the part the first draft got wrong.** Do *not* build a second pair of
systems with a wider alphabet — that forces a simulation obligation relating two
different systems' transcripts.

The paper says the extra information is *"included in the transcript"*. Nothing
about the system changes; what changes is the map the PDS is pushed forward along.

    transcriptDist S e m  =  fTransform (fun s => transcript s e m) S

and `hctr2Perm bf` is itself `fTransform (fun π => DDS_of π) (uniform (Perm n))`,
so by `Dist.fTransform_comp`

    transcriptDist (hctr2Perm bf) e m
      = fTransform (fun π => transcript (DDS_of π) e m) (uniform (Perm n))

Refine that map:

    augView bf e m π := ( transcript (DDS_of π) e m,  π (bin 0),  π (bin 1),  Dˢ… )
    augLaw  bf e m   := fTransform (augView bf e m) (uniform (Perm n))

`h̄`, `L` and every `Dˢ` are functions of `π`, so `augView` is an ordinary function
on the key space. Since `Prod.fst ∘ augView = fun π => transcript (DDS_of π) e m`,

    transcriptDist (hctr2Perm bf) e m = fTransform Prod.fst (augLaw bf e m)

and DPI (`δ_fTransform_le` at `f = Prod.fst`) gives in two lines

    δ( tr(rnd,e) m , tr(hctr2Perm,e) m )  ≤  δ( augLaw rnd e m , augLaw hctr2Perm e m ).

Take `sup` over `(e,m)`. The simulation obligation disappears.

**And it fixes the `h̄`/`L` timing for free.** §3.4.2 needs `h̄, L` independent of
the queries. Handing them out as *answers* would let the environment adapt to
them; modelling them as a reveal *query* forces a spurious "asked last" condition
on the environment. Recorded in the **observation**, they are invisible to the
environment — whose queries are functions of responses only — so "given after all
queries are complete" is structural.

## A.4 The obligations

| # | obligation | status |
|---|---|---|
| 0 | augmentation soundness | `δ_fTransform_le` at `Prod.fst` — **not** a simulation |
| 1 | `Bad` = a repeat in `𝒟` or `ℛ` | defined; needs no casts (see B.10) |
| 2 | support-local good dominance, `eps = 0`: `∏_{i<σₘ}1/(2ⁿ−i) ≥ 2^{−σₘn}` | open; arithmetic **proved**, no side condition (see B.14) |
| 3 | bad mass: union bound + partition + count | **proved** (`bad_probability_le`) |
| 3′ | §3.4.2's case analysis + summation | open; the bulk (`collAt_le_expected_cost`, `costSum_le`) |
| 4 | closing arithmetic | **proved**, and it is an *equality*, not `≤` |

Node 3′ is **Figures 4 and 5 as a cost table** — `cost side deg dir : Origin → Origin → ℕ`,
red `0` / grey `1` / green `dˢ`, gated on `dirOf s = side` because a green cell is green on
only one side (B.18). Two obligations, and they are the paper's own two remaining pieces:

* `collAt_le_expected_cost` — the 22 cases, pp. 12–14. Each is `mass_le_of_fiber_bound`
  (p. 11's "*conditioning on … all values of `L` are equally likely*") with a free coordinate
  and a solution count. The green cells are where `prop1`/`prop2`/`prop3` attach.
* `costSum_le` — the summation, pp. 15–16. `c_b, c_f, c_w, c_a` are the four regions of the
  table; `Σ_s dˢ ≤ σ` and `σₘ ≤ σ+2` close it.

The earlier design made the four `c_•` aggregate group masses with an expected-pair-count
baseline. That was built to dodge a *non-problem* — I had computed that per-pair costs give
`Θ(σ³)`, assuming every pair costs `dˢ`. The expensive pairs are indexed by **query**, not
by block (`(bin 0, MMˢ)` is one per query, summing to `σ/2ⁿ`); the `Θ(σ²)` pairs are
`Sᵢ`-vs-`Sⱼ` at exactly `1/2ⁿ`. Eleven declarations existed only to serve that error. **Check
an impossibility argument's arithmetic before building around it.**

Node 2's direction is **ideal ≤ real**, so `eps = 0` and the endpoint is the
*ratio* form at ratio 1 — `eq_on_good` is **false** here, because the good
probabilities are `∏1/(2ⁿ−i)` and `2^{−σₘn}`, ordered but not equal.

Node 3 is technique-independent: a CE or coupling proof reuses it verbatim
(`papers/notes/HCTR2_CE_PROOF.md`).

Naming trap: the paper's `ε` is the *bad mass*, not the ratio slack.

## A.5 Final assembly shape

The production proof should use the zero-defect two-cell endpoint, not instantiate the
general ratio theorem at `eps = 0`.  For each environment and prefix length, name the two
paper obligations first:

* `good_observation_dominance`: for every observation in the ideal augmented law's support,
  `not Bad` implies ideal point mass at most real point mass;
* `ideal_bad_probability`: the ideal augmented law's `Bad` mass is at most the headline
  bound.

Then the proof is exactly two hops: plain transcript distance is at most augmented distance
by `δ_le_δ_aug`, and augmented distance is at most the headline bound by
`δ_hTechnique_le_on_good_of_bad_le`.  Nonnegativity is structural.  No weight bound,
coverage proof, disjointness proof, or separate augmented-H theorem appears.

The declaration `good_ratio_holds` must itself take ideal-support membership.  Asking it to
compute point masses for unreachable observations would be stronger than H and stronger than
the paper argument require.

---

# B. Lessons — PDS, DPI, transcript laws

Errors are marked ✗ with the correction.

**B.1 ✗ I claimed twice that "no theorem says `Adv` depends only on the
behavior".** It exists: `CR18.behavior_equivalent_iff_transcript_equivalent`
(`RandomSystem.lean:680`), axiom-clean. So does Lemma 2.18
(`transcript_equivalent_of_nonadaptive_transcript_equivalent`).
→ **`RandomSystems/LanzenbergerChain.lean` is a thesis-item → declaration name
table.** Read it before concluding anything is missing. It also records source
errata (Def 2.27's `inf`→`sup`; Thm 2.29's printed `min` form refuted
kernel-checked).

**B.2 The transcript law is a pushforward.** `transcriptDist S e m =
fTransform (tr · e m) S`. Seeing this collapses three separate-looking steps into
one tool:

| push along | gives |
|---|---|
| `tr(·,e)` | `Adv ≤ Δ` — Thm 2.31's easy half is *one* `δ_fTransform_le` |
| `verdict` | `maxAdvantage ≤ Adv` — why the verdict can be dropped from the model |
| a forgetful projection | the extra-information step |

Read downward, each level is a pushforward of the one above and DPI says each step
can only lose distinguishing power. Thm 2.31 says the first inequality is tight.

**B.3 ✗ "Step 5.5 doesn't have a pair of distributions."** Wrong — step 1 does.
H applies at the first level where a `Dist` pair exists, which is inside `Adv`'s
own supremum. What `Adv[q]`'s packaging adds is convenience (Layer B's
fixed-query→adaptive transfer, a tidy `Vector` carrier), not applicability.

**B.4 Layer B is trivial at the `Adv` level.** For *deterministic* `e` the
transcript law factors as `systemFactor · environmentFactor`
(`PDS.lean:2659`) and the environment factor is a 0/1 indicator — *the same on
both sides*. So a ratio hypothesis reduces to the system factors and is
environment-independent for free.

**B.5 ✗ "The `Fintype` barrier is `statDist`, because it symmetrises."** `statDist` does
**not** symmetrise — `∑ a : A, max (X a − Y a) 0` is the same one-sided formula as `δ`
(`StatDist.lean:125`). The only difference is the index set: `statDist` sums over
`Finset.univ`, `δ` over `μ.support`. So they are one metric at two generalities, not two
metrics, and they agree exactly when `ν ≥ 0` (B.7).
→ Consequence I got wrong for the whole file: the `Fintype` on `hTechnique_ratio_fTransform`
is **not load-bearing**. `Dist A = A →₀ ℝ` already carries finite support, and outside
`X.support ∪ Y.support` every summand vanishes, so `statDist` admits a Fintype-free
definition with the same value unconditionally. "It requires `Fintype`, so it cannot apply"
was a claim about the *spelling* dressed as a claim about the mathematics — the same error
class as B.19.

**B.6 Orientation is inherited from `δ`, which is asymmetric at unequal weight**
(Def 2.4's own remark). `Adv S T` = excess of `S` over `T` = `Δ(T,S)`. The naive
`Adv S T = Δ(S,T)` is *refutable* at sub-distribution weight (`S = 0`). Ideal
first.

**B.7 `NonNeg` hypotheses are Def 2.4 content, not bookkeeping.** `δ` sums over
`supp μ`; that equals Def 2.4's sum over all of `𝒜` only when `ν ≥ 0`. Dropping it
falsifies partition-additivity outright — that was the real bug in
`TranscriptBranchDistance.lean`, whose statement was unprovable as written.

**B.8 CR18 numbering in a docstring is not evidence of thesis conformance.**
Definitions are named after CR18; only *some* carry a "Lanzenberger Def 2.x is
this plus…" note. Example: Def 2.11's environment is `𝒴* ⇀ 𝒳` with prefix-closed
domain; the library uses CR18's `List (Option Y) → Option X`, so `⊥` is
observable and compatibility is absorbed instead of assumed. Substantive, and the
library says so at `PDS.lean:62` — but only there.

**B.9 ✗ I stated the main lemma about the augmented worlds.** A statement must
not mention proof devices. Making it honest surfaced an obligation that the wrong
statement had hidden.

**B.10 Dependent-type friction is a modelling smell.** `Bad` needed **zero
casts**, because `Bits.sub` is total (reads zeros past the end) and `Bits.blocks`
accepts any width — a malformed transcript entry infers garbage rather than
failing to typecheck, and that totality is exactly what the H endpoint wants.
Where casts *did* threaten (`hctr2Fun`'s length index stuck behind its direction
match), naming the intermediate (`respOf`) removed them. Compare the Σ-width
lesson: width-varying strings want Σ-valued definitions.

**B.12 ✗ I first stated the four corrections per *pair of origins*.** They are
**aggregates over a group**, and the per-pair form is not merely less convenient — it
cannot reach the paper's bound. `c_a`'s pairs cost up to `dˢ/2ⁿ ≈ σ/2ⁿ` each, so
`Θ(σ²)` pairs give `Θ(σ³)/2ⁿ` where the paper has `Θ(σ²)/2ⁿ`. Nor can the baseline be
split per group in closed form: `#sameQuery = 2Σ_s C(dˢ,2)` and
`#crossQuery = 2Σ_{r<s} dʳdˢ` are shape-dependent, and `sup + sup = 2·σ(σ−1)` against a
budget of `σ(σ−1)` — so taking suprema doubles the leading term.
→ Two consequences worth keeping. (i) **Make the baseline an expectation.** Then no
"the shape is constant on the support" hypothesis is owed. **It is not constant** — a
deterministic environment fixes query 1, but query 2 is `e(response 1)`, so every `dˢ` varies
with the coins, and p. 11 warns about precisely this. The expectation is right for the
*honest* reason: condition on a **prefix**, not on the shape (B.19).

**B.19 ✗ "The shape is constant on the support (Lemma 2.18)" — false, and it survived
three commits inside a docstring.** A deterministic environment fixes query 1; query 2 is
`e(response 1)`, so the queries vary with the coins and so does every `dˢ`, `mˢ`, `σₘ`.
Lemma 2.18 says non-adaptive *environments suffice*, not that a deterministic environment's
queries are constant — I read the name and not the statement.
→ The consequence is not that `collAt_le_expected_cost` is false; it is true. The damage is
that the docstring pointed at the **wrong proof strategy**: condition on the shape, which
would condition on later responses and destroy the independence the fiber lemma needs. p. 11
says condition on a *prefix*. A false justification attached to a true statement is harder to
catch than a false statement, because nothing ever fails to typecheck — it only wastes
whoever picks the obligation up.
→ **Audit docstrings, not just statements.** Stage 4's "quote the source" applies to the
*reason* a statement is true, not only to the statement.

**B.18 A figure's qualifications live in the prose beneath it.** `cost` transcribed
Figures 4/5 faithfully and was still wrong: the sentence under them says a green square is
`1/2ⁿ` after all *if query `s` is a decryption query*, and Figure 5's greens are live only
for decryption queries. So each query pays on exactly one side, and the gate is
`dirOf s = side`. Ungated, `c_f` doubles to `4σ` and `costSum_le` is false.
→ Two cells are now deliberately *over*-approximated (`(L, UUˢ)` is grey but scored `dˢ`).
That is free precisely because the gate makes one side dead per query, and the total is
still the paper's `Σ_s 2(dˢ−1) ≤ 2σ` — its own `max(2(dˢ−1), dˢ−1)`. **An over-approximation
is only safe once you have re-summed with it in place.**

**B.17 The audit that works: quote the source, then sum it.** Four definitions/statements
in this file were false against the paper — `inferEntry`'s length class (read off the
response, not the query), `RndKey`'s leftover width (`n`, not `padLen n j − j`), the four
corrections' generic `law`, and `cost`'s missing direction gate. Three surfaced only when a
proof attempt or a review question forced a re-read; the fourth was caught *before* proving,
by two habits now in the skill as stage 4:

1. **Quote the paper in the docstring.** To write the quote you have to find the sentence,
   and that is the check. Three of the four were content in a *different modality* from where
   I was looking: `mˢ`'s definition is a sentence three paragraphs above the display of `𝒟`;
   Figures 4/5 are complete-looking tables whose direction caveat is in the prose beneath.
2. **Sum it and compare the number.** Un-gated, `cost` summed to `c_f ≤ 4σ` against the
   paper's `2σ`. Thirty seconds, and it tests exactly what types cannot. The same check
   validates `σₘ = 2 + Σmˢ` and the `σₘ·n` bit-width identity behind `good_ratio_holds`.

The reason this is *expensive* rather than merely annoying: a wrong definition typechecks,
composes, and lets the skeleton build green, so it accumulates dependents before anything
fails. Composition is preserved by false leaves — see B.16.

**B.16 ✗ I stated the four corrections over an arbitrary `law : Dist (AugObs …)`.** All
four were then **false**, and `bad_probability_le` was a correct assembly of premises
that could never be discharged. The `1/2ⁿ` in `baseline` is world `Y`'s uniformity, not
a combinatorial fact, so over a generic law it asserts nothing that holds: at the point
mass on `o = ([], (0,0), [])` the `ℛ` side is `[(seed 0, 0), (seed 1, 0)]`, giving
`groupMass = 1` against `baseline − 1/2ⁿ = 1/2ⁿ`.
→ **In a bound's *conclusion*, generality is anti-generality** — quantifying over the
distribution strengthens the claim past truth. The tell was already written down: the
docstrings said "in world `Y`" while the signatures did not. When prose and signature
disagree about *which distribution*, the signature is the one that's wrong.
→ And the deeper habit: **the paper's `Pr` is not a parameter.** Its `Pr[Y ∈ 𝒯_bad]` is
one specific law throughout, and `c_b, c_f, c_w, c_a` are *defined* as
`Σ(2ⁿPr[a=b] − 1)` over their group — actual quantities with proven bounds, not claims
that could be refuted. I hoisted `law` because `groupMass`/`baseline` are defined
generically and let the parameter leak from the definitions into the statements. Copy
the paper unless there is a written reason not to; §B.12's aggregate corrections and
`answeredQueries_transcript` are the only two such reasons here, and both are recorded.

**B.14 ✗ I recorded `σₘ ≤ 2ⁿ` as "a side condition the paper does not state".** It is a
*consequence of the bad event*: `¬ Bad` says the inferred plaintexts are pairwise
distinct, and a `Nodup` list of `Str n` has at most `2ⁿ` entries
(`sigmaM_le_card_of_good`). The paper is right to omit it.
→ **Before calling something an unstated hypothesis, check whether the event you are
conditioning on already implies it.** The same reflex found `hbudget`: `σₘ ≤ σ + 2`
looked like an assumption and was a theorem about `⌈budget q σ⌉ᵈ`. Two for two — on this
paper, "the authors skipped a condition" has so far always meant "we modelled the
condition's source as an input".

**B.15 A Mathlib citation is only a simplification if it does not drag an interface with
it.** `Finset.card_eq_sum_card_fiberwise` and `Finset.sum_range_id_mul_two` do replace
`countP4`'s and `two_mul_length_originPairs`'s inductions — both verified to apply. But
reaching them needs `pairIdx`, `labelAt` and `Origin.group`, and then four `iff` lemmas
to keep the paper-named predicates in the `case_*` statements: **4 declarations become
8**. It only pays if the four predicates are *deleted* in favour of `Origin.group`
(10 → 8, and exhaustiveness/disjointness stop being separate proofs), which re-indexes
`CollideIn`, `groupMass`, `collide_of_bad` and the four corrections. Count the
declarations on both sides of a "cleanup" before starting it.

**B.13 `linarith` sees `_ / 2 ^ n` as an atom, so the atoms must match syntactically.**
`2 ^ n` is not a numeral, so `x / 2 ^ n` is `x * (2 ^ n)⁻¹` and a product like
`(σ+2)(σ+1)/2ⁿ` is nonlinear. It still closes, because each such term appears
*identically* on both sides — until one is written `- 1 / 2 ^ n`, which parses as
`(-1) / 2 ^ n` and is a different atom from the `1 / 2 ^ n` in `baseline - 1 / 2 ^ n`.
Spell the combined target with binary `-`.

**B.11 Check whether the aggregator builds before relying on it.**
`LanzenbergerChain.lean` does not currently compile — `BoundedAttainment`,
`TranscriptHybrid`, `RandomSystemCoupling`, `MultiSystemCoupling`,
`GameWinnability` are red from an unfinished `dist-real` migration (~37 errors,
mostly `NonNeg` threading). Thm 2.31/2.32/2.37 are *written* (zero `sorry`) but
cannot be axiom-audited. `RandomSystem.lean` itself is green, which is where B.1's
declarations live.
