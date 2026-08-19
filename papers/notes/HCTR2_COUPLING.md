# HCTR2 vs T̃ via coupling of random systems (Lanzenberger–Maurer)

**Status (2026-07-05, updated same day): deep-research complete; recommended design
adversarially verified; and the two open items are now CLOSED (§5bis) — Lemma B audited in
full by two independent auditors + a dedicated attacker (no escape; one load-bearing
definitional fix), posterior constancy independently re-derived twice (one outright
`confirmed` with the complete derivation). The route's mathematics is settled; remaining
work is exposition + Lean.**
Companion to `HCTR2_CE_PROOF.md` (the completed CE route). Sources: LanMau20 (TCC 2020,
local `papers/LanMau20.pdf` + digest), Lanzenberger's dissertation (Diss ETH 29554, 2023,
`papers/thesis (1).pdf`; its Ch. 2 *is* the extended LM20 — page map: PDF page = thesis
page + 10; coupling theory pp. 11–26, applications pp. 27–42, open problems p. 85), the
repo's `papers/notes/LM20_ORBIT_PROOF.md` (XoP orbit proof) and the Lean `Legacy/` +
`Coupling.lean` surfaces.

## 0. Headline

The coupling route yields, for the recommended (tape-driven) design:

```
Adv^{±p̃rp}_{HCTR2[E]}(q, σ, t)  ≤  Adv^{±prp}_E(σ+2, t+σt′) + (3σ² + 2qσ + 7σ + 2)/2^{n+1}
```

— the paper's main-lemma budget with **no additive `q²/2^{n+1}`** (beats the paper) **and no
multiplicative `α = 2ⁿ/(2ⁿ−q+1)`** (beats the CE route), no `q ≤ 2^{n−1}` side condition.
It also needs **no augmentation, no reveal query, no terminality convention, no filter
converter, no hidden-key posterior lemma, no domination step** — `h̄`, `L` and the leftover
blocks become *internal coupling randomness*, not observables. The α disappears because the
bad event lives on the **raw iid tape layer**: the without-replacement skew is not an
inflation of every response-pinned pair but a set of correction events *already counted* as
collision pairs. All three CE Step-5 repairs dissolve (no WOR in the probability space, no
straddling truncation, no α bookkeeping). Side conditions: `σ_m ≤ 2ⁿ` (else budget ≥ 1),
`ℓˢ ≥ n`, `mˢ−1 < 2ⁿ`, POLYVAL properties 1–3, finite `(q, σ)` horizon baked into the
system domain (LM20 treats query budgets as *system* properties).

## 1. The theory (what LM20/thesis actually provide)

- **DDS** (Def 2.9): a *partial function* `s : X⁺ ⇀ Y` with prefix-closed domain — state is
  canonically encoded by letting output `i` depend on the whole input prefix, so
  stateful/lazy/tape-driven samplers are legitimate DDS. **PDS**: a finite-support
  distribution over DDS with common domain (sub-probability weights allowed and
  load-bearing). A **random system** is the behavioral-equivalence class `[S]`.
- **Lemma 2.18** (= LM20 Lemma 5): equivalence can be certified against **non-adaptive**
  deterministic environments only — transcript mass depends only on the input sequence. So
  proving a lazy representative is in `[HCTR2]` or `[T̃]` is a fixed-query-sequence
  statement; adaptivity is absorbed by the framework.
- **Theorem 2.31** (LM20 Thm 1): `Δ(S,T) := inf_{S∈[S],T∈[T]} δ(S,T) = Adv(S,T)`, infimum
  attained. **Theorem 2.32** (Thm 2, coupling theorem): representatives + a joint
  distribution exist with `Adv = Pr(S ≠ T)`, `≠` = inequality of the sampled partial
  functions over the *entire* domain — a static, pre-interaction event.
- **The usable direction needs no optimality**: for ANY representatives and ANY coupling,
  `Adv = Δ ≤ δ(S,T) ≤ Pr(S ≠ T)` (Def 2.28 + Lemma 2.8(1)). Attainment is only for
  tightness/lower bounds.
- **The unsoundness pitfall** (thesis p. 32, why Lemma 2.44's blinding machinery exists):
  conditioning one side on agreement conditions the other — couplings must give both sides
  their exact marginals *unconditionally*, with disagreement confined to the bad event.
  (Counterexample: `δ(⊕ᵢBᵢ, U) = 2^{n−1}∏δ(Bᵢ,U)`.)
- **Negative findings**: the thesis's only end-to-end coupling application is the combiner
  amplification (Lemma 2.44 / Thm 2.45); the switching lemma is *not* proven by coupling
  anywhere; no Feistel/XoP/tweakable examples; no conditional-coupling or coupling-with-MBO
  theorems; the author himself lists "not so easy to find many examples" as an open problem.
  So an HCTR2 coupling proof is genuinely new territory, with the repo's XoP orbit proof
  (`LM20_ORBIT_PROOF.md`) as the only local precedent.

## 2. Structural finding: the static coupling is unattainable — and that's fine

The "failure decided before interaction" form (Thm 2.32 with natural representatives) is
**provably out of reach for hash-masked schemes like HCTR2**: derived π-points
`MMˢ = Mˢ ⊕ H_h̄(Tˢ,Nˢ)` depend on the query, so "∃ an input sequence in the domain
producing a raw collision" has probability ≈ 1 (for every fixed `(h,l)` and first query
there is a second query forcing an `MM`-collision deterministically); a support-counting
bound (`(2ⁿ)!` real DDS vs `≫` ideal DDS) kills stateless representatives too. Both design
agents discovered this independently. The licensed chain is instead **per-environment
transcript coupling** — for each fixed deterministic environment `e`:

```
δ(tr([G],e), tr([F],e)) = δ(tr(G̃,e), tr(F̃,e))      (class-invariance + Lemma A)
                        ≤ Pr_ω[tr(G̃(ω),e) ≠ tr(F̃(ω),e)]     (data processing + coupling lemma)
                        ≤ Pr_ω[Bad_e(ω)]                      (Lemma B)
Adv = sup_e δ(...) ≤ sup_e Pr[Bad_e] ≤ budget.
```

Adaptivity is absorbed by `sup_e` + per-prefix conditioning (the paper's own world-Y
discipline); randomized distinguishers by convexity. In Lean this chain is exactly
`coupling_bound` (`RandomSystems/Coupling.lean:136`, `statDist ≤ prDisagree`) applied to
transcript distributions.

## 3. The recommended design (tape-driven; judged primary, verifier-corrected)

Per fixed deterministic environment `e`, with the `(q, σ)` horizon in the system domain:

**Tape.** `Ω = (h*, l*) × W × RG × RF`, all independent: `h*, l*` uniform `{0,1}ⁿ`;
`W = (W_{s,j})`, `s ≤ q`, `0 ≤ j ≤ m_max−1`, iid uniform n-bit cells **hard-wired to query
position `s`** (`m_max` fixed by the horizon, so `Ω` is a finite product); `RG`/`RF`
rejection supplies. `h̃ = h*`; `l̃ = l*` unless `h* = l*` (resample; the event is charged —
it is the paper's `h̄ ≟ L` pair). Cell semantics: `W_{s,0}` = fresh π-*output* `UUˢ` (enc)
or fresh π-*preimage* `MMˢ` (dec); `W_{s,j}` = XCTR output `Y_jˢ`. Position-indexing (not
"i-th fresh value") makes both sides consume the same cells on the same prefix.

**Real representative `G̃(ω)`** — global lazy WOR-π seeded `{bin0 ↦ h̃, bin1 ↦ l̃}`, every
fresh evaluation by **rejection-once**: take the W-cell unless it collides with the used
range (dom for inverse calls), else RG-uniform on the complement — exact WOR
(`1/2ⁿ + u/2ⁿ · 1/(2ⁿ−u) = 1/(2ⁿ−u)`). Runs the HCTR2 equations verbatim.

**Ideal representative `F̃(ω)`** — per-class `(T,ℓ)` lazy WOR permutations, **raw-candidate
driven**: on a fresh enc query compute the candidate `C` *by the same formulas on raw
cells* (`UU := W_{s,0}`, `Y_j := W_{s,j}`, `V = N ⊕ Y`-prefix, `U = UU ⊕ H_h̃(T,V)`);
answer it unless it collides with a prior class ciphertext (then RF-rejection). Dec mirrors
on plaintexts. Repeats/mirrors replay from the class record. Leftover bits of the last cell
are simply never output — **no augmentation**.

**Lemma A (marginals, via Lemma 2.18).** `G̃_* ∈ [HCTR2[Perm(n)]]` (rejection-once = exact
two-sided lazy URP, `Pr[π̂ ⊇ φ] = 1/(2ⁿ)_{|φ|}`; identification with HCTR2-under-π via CE
§5.2.1, reusable verbatim). `F̃_* ∈ [T̃]`: for fixed `h̃` the map
`(W_{s,0}, first ℓ−n bits of W_{s,·}) ↦ C` is a bijection, so the raw candidate is uniform
on `{0,1}^ℓ`, independent across queries and of `(h*,l*)`; rejection-once gives exactly
per-class WOR. Both marginals exact and **unconditional** — the Thm-2.45 pitfall never
arises. Bidirectional access is native (tagged alphabet); no `⟨·⟩` lifting.

**Bad event — in inference form (verifier correction 1, load-bearing).** Define the `D`/`R`
multisets from the `F̃`-run *transcript* via the paper's p. 10 table plus
`(h*, l̃, hidden leftover bits)` — over essentially-fresh queries (not exact class-repeats
or mirrors; a deterministic prefix predicate replacing the CE filter) — with a
**first-failure decomposition**: intersect with, never condition on, the no-prior-collision
event. Raw = inferred up to the first divergence, so Lemma B is unaffected, and the
per-pair probability bounds are clean (under the naive raw-cell reading, hash-pinned pairs
whose earlier entry belongs to an already-corrected query would have a skewed cell
posterior).

**Lemma B (divergence ⊆ Bad).** For every `e, ω`: `tr(G̃(ω),e) ≠ tr(F̃(ω),e) ⟹ Bad_e(ω)`.
Induction with the invariant "off Bad, no correction has fired on either side; `π̂` = the
raw derived pairs; `σ̂` = the recorded class pairs; all responses were the identical raw
formulas" — the invariant must carry **within-query sub-step state** (`MM/UU` assigned
before the XCTR loop; verifier correction 4). Every divergence mode lands in a counted
Fig. 4/5 pair: real reuse `MMˢ ∈ dom(π̂)` ⟹ D-repeat; real output-correction ⟹ R-repeat;
ideal class-correction `Cˢ = Cᵗ ⟹ UUˢ = UUᵗ` (CE §5.1 cancellation, reused verbatim);
within-query degeneracies ⟹ within-query rows; repeats/mirrors replay identically on both
sides and add nothing.

**Budget.** `Pr[Bad_e] ≤ Pr[h*=l*] + Σ_{pairs} Pr[collision ∧ h*≠l*]`; per-pair by pinning
one conditionally-uniform-independent variable, never conditioning on goodness:

| case family | pinned by | bound | vs CE `T̃aug` |
|---|---|---|---|
| algebraic (`bin0≟bin1`, `S_iˢ≟S_jˢ`) | — | 0 | = |
| 8 L-pinned | `l*` | exactly `1/2ⁿ` | = |
| 6 hash cases (hash direction) | `h*` + POLYVAL 1–3 | `≤ d/2ⁿ` | = |
| response-pinned (grey + green grey-directions) | **raw cell `W_{s,j}`** (fresh iid) | **exactly `1/2ⁿ`** | `1/(2ⁿ−k)` → `1/2ⁿ`: **α gone** |

Posterior constancy of `(h*, l*, W_{s,·})` given an adaptive prefix: per step, given the
history and any fixed `(h̃,l̃)`, the `F̃` response is class-WOR with `(h,l)`-independent
likelihood (candidate uniform by the bijection; rejection law depends only on `|ran σ̂|`);
later cells untouched by position-indexing. This one paragraph is the entire residue of CE
§5.2 — the hard half (5.2.2/5.2.4/5.3/6.1) is simply not needed. One extra line (verifier
correction 2): for hash-pinned pairs whose earlier entry is a partially-hidden `Y`-cell,
average the hash-property bound over the hidden leftover bits (uniform, independent, never
read by `F̃`'s responses) — the coupling analogue of CE repair #2, bound-preserving. The
union bound is written pathwise over pair slots indexed by the later query's step, with
`Σdˢ ≤ σ` holding on every path, and the §3.4.3 negative-summand rearrangement applied to
per-pair bounds (correction 3 — CE repair-#3 discipline survives even without α). Result:
`sup_e Pr[Bad_e] ≤ (3σ² + 2qσ + 7σ + 2)/2^{n+1}`.

## 4. The fallback design (static/eager, H-coefficient-flavored)

The second design couples full transcript distributions per environment by a mass-splitting
argument built directly on CE 5.2.2/5.2.3 (agreement mass = `min` of the two good-transcript
laws; residuals of equal weight `P^F_e[¬Good]` matched arbitrarily). Verified sound
(`holds_with_corrections`: residual accounting fixed — each residual contains exactly one
bad mass; run-fiber vs `φ`-containment partition fixed; hash rows "at most"). It is
honestly the min-sum/H-coefficient method with `ε = 0`, keeps augmentation + filter +
α, and reproduces exactly the CE bound `(3σ²+2qσ+7σ+2)/2^{n+1} · 2ⁿ/(2ⁿ−q+1)`. Its one
virtue: its heavy obligations are already discharged (they *are* CE §5.2, now confirmed).
Keep as the fallback appendix; its verifier also closed CE §11's hope (c) **negative** for
this design — augmentation stays load-bearing there. (In the tape design the hope is
realized: no augmentation anywhere.)

**Judge's call:** tape-driven primary (strictly better bound; its heavy lemma is about a
*sampler*, not adaptive transcripts; the 22-case engine ports with iid pinning and no WOR
variant), static as verified fallback with an explicit activation criterion (switch only if
the Lemma B audit or posterior constancy breaks).

## 5. Ranked open problems (items 1–2 CLOSED, see §5bis)

1. ~~Lemma B completeness audit~~ — **CLOSED 2026-07-05** (§5bis).
2. ~~Posterior constancy of `(h*, l*)`~~ — **CLOSED 2026-07-05** (§5bis; `confirmed`).
3. **Bad-in-inference-form** — superseded: the audit sharpened it to the **slot-wise
   first-failure definition** (§5bis.1), which is now the authoritative form; write it
   precisely before any Lean.
4. **Pathwise union-bound bookkeeping** with adaptively chosen lengths — the assembly is
   spelled out in the confirmed posterior derivation (§5bis.2(e)); write at paper rigor.
5. **`F̃` marginal exactness full write-up** (dec direction, mirror inverse-lookup, `ℓ = n`
   edge) — spot-checked only; now the top remaining item.
6. Fallback dependency: moot (1–2 closed).
7. Tightness / matching lower bound — deprioritized as before.

## 5bis. Closure of the two open items (2026-07-05, run wf_f8189405-430)

### 5bis.1 Lemma B: audited and confirmed — with one load-bearing definitional repair

Two independent full auditors (enc-first and dec-first orderings) + one pure attacker; all
three `holds_with_corrections`, **no escape from the intended claim**. The complete
mode → Fig 4/5 map is exhaustive: the per-query π touch-points are exactly
`{MM, S₁..S_{m−1}}` forward (enc) / `{UU inverse, S_j forward}` (dec), `D` is compared only
against `dom(π̂)` and `R` only against `ran(π̂)` (D/R never cross, matching the paper); the
real-side reuse/correction modes land in the four rows of each Fig 4/5 column, within-query
modes (`MM≟S_j`, `UU≟Y_j`, `Y_i≟Y_j`) are reachable exactly because the invariant carries
sub-step state, `S_iˢ≟S_jˢ` is impossible on both sides (`bin(i)⊕bin(j) ≠ 0`) = the red
cell, ideal RF-corrections map to `(UU^r,UU^s)`/`(MM^r,MM^s)` via the §5.1 cancellation
**with both provenances of the colliding class value verified** (prior fresh enc answer and
prior dec query), mirrors replay transparently on both sides (real: `UU = U^t⊕H(T,V^t) ∈
ran(π̂)`, unique preimage `MM^t`, all XCTR hits — no cells/RG/RF consumed, no entries
added), branch agreement is circular-free (both sides branch on the same class-record
predicate of the *visible* prefix, identical up to first failure), cross-class ciphertext
collisions are caught because `R` is a *global* multiset, and RG/RF misalignment is
impossible off Bad (neither supply is read).

**The repair (found independently by all three agents; the attacker produced concrete
countermodels):** the literal reading "Bad = final transcript-inferred D/R multisets have a
repeat" is **false** as a Lemma B target — an ideal RF-rejection *resamples* the answer,
and the resampled answer's inferred entries can erase the repeat (minimal countermodel:
`ℓ = n`, `e = [enc(T,M₁), enc(T,M₂)]`, tape `W_{1,0} = W_{2,0} = w ∉ {h*,l*}`: RF and RG
both fire at query 2, transcripts diverge, final multisets repeat-free). The authoritative
definition is **slot-wise first-failure over RAW values**:

```
Bad_e = {h* = l*} ∪ ⋃_slots { no raw collision at any earlier slot ∧
                              the two raw (cell / query-determined) values at this slot collide }
```

On each such event, inferred = raw at all involved slots (same induction), the budget's
per-pair pinning is exactly of this form, and every divergence mode lands in a counted
pair. Additional fixes recorded: (i) `h* = l*` stays an *explicit disjunct* (after the `l̃`
resample it is never visible as a multiset repeat); (ii) with Bad defined over all step-`s`
raw pairs simultaneously, within-query sub-step *ordering* is needed only inside the
invariant proof, not in the definition; (iii) the essentially-fresh predicate is pinned as
class-record membership on the visible prefix (covers both provenances); (iv) ideal RF
firings and real R-corrections at the same slot are the *same* pair event — counted once;
(v) the `h* = l*` resample keeps the `π̂` seed injective even on Bad (feeds Lemma A).

### 5bis.2 Posterior constancy: independently re-derived and CONFIRMED

Two independent re-derivations (one `confirmed` outright with the full computation, one
`holds_with_corrections` with strengthenings). The confirmed derivation's key content, now
part of the design:

- **(a) The crux, resolved.** Per fresh step `t`, for *every* fixed `(h,l)`: the candidate
  is uniform on `{0,1}^ℓ` (the `(W_{t,0}, Y-prefix bits) ↦ C` bijection), the rejection
  probability is `k_t/2^{ℓ_t}` (`h`-independent), and the response law in *both* branches
  is the same uniform law on the `2^{ℓ_t} − k_t` free values. The consistent preimage
  cells vary with `h`, but the **likelihood mass is constant** — the free-response set is
  prefix-measurable and `h`-independent. Replay steps contribute factor 1. Hence the
  strongest clean form: **each visible step kernel is an autonomous function of the visible
  past, identical for every `(h,l)`; the visible transcript `Y^q` is independent of
  `(h*, l*, RG, all never-read W-bits, unread RF)` as a random vector, for every `e`.**
  Posterior constancy is a corollary.
- **(b) `(h*, l̃)` handling, decided:** the pair `(h*, l̃)` is posterior-uniform on ordered
  *distinct* pairs (no atoms — the resample was designed for this). But do **not** pin `l̃`
  (that gives `1/(2ⁿ−1)`, an α-flavored inflation of the 8 L-cases). The clean budget:
  `Pr[Bad] ≤ Pr[h*=l*] + Σ_slots Pr[slot ∧ h*≠l*]`; charge `2^{−n}` once (= the paper's
  `h̄ ≟ L` pair, the `+2` term); on `{h*≠l*}` **substitute `l̃ = l*` inside each slot event
  and drop the intersection** — intersect-and-substitute, never condition. L-pins are then
  exactly `1/2ⁿ`.
- **(d) Why this survives where the CE first draft died:** no step of the chain ever forms
  a conditional given Bad/goodness — every conditioning event is a visible-prefix event
  with constant `(h,l)`-likelihood; the first-failure decomposition intersects and drops by
  monotonicity, never divides. Verified against the CE `m = 2` counterexample: the
  goodness-conditional still varies with `y₁`, but it is never used — the pair is bounded
  *before* the response and the `y₁`-variance integrates out. Leak hunt (response-determines
  -cells, rejection indicator, mirror replay) all closed: past *read* cells are correlated
  with `h*` but are never pinned (slots pin only `{l*, h*, current fresh cell}`); pairs
  among two past queries were bounded at the *later of the two* when its pin was fresh.
- **(e) The three pinning families, verified:** L-pinned exactly `1/2ⁿ`; hash-pinned
  `≤ d/2ⁿ` with the **hidden-leftover averaging line proven** (leftover bits are never read
  by the response functional, hence jointly posterior-prior with `h*`; genuinely needed —
  e.g. a fresh dec query's `R`-entry `UUˢ` is hash-of-visible data, and `(Y_{r,i}, UUˢ)`
  pairs with the earlier `Y`-cell straddling into hidden `D_r` are exactly this family);
  response-pinned exactly `1/2ⁿ` (fresh raw cell vs a target measurable in everything
  else). Pathwise assembly: every slot bound is a `Y^{s−1}`-measurable constant, sums
  inside the expectation, `Σdˢ ≤ σ` on every path ⟹
  `sup_e Pr[Bad_e] ≤ (3σ² + 2qσ + 7σ + 2)/2^{n+1}`, the `+2` being exactly the charged
  `Pr[h*=l*]` plus the vacuous `bin0 ≟ bin1` row.
- **Strengthenings from the second deriver (folded in):** the product-prior statement must
  *jointly* cover the unread bits of past rows (hidden leftover tails + unused columns) —
  same σ-algebra argument at bit granularity; **RF must be position-indexed per step**
  (a single sequential RF supply makes "unread RF" non-prefix-measurable; per-step indexing
  makes the claim immediate); the raw-=-inferred identification at the current step holds
  on the no-rejection event, with rejection-at-`s` absorbed by Lemma B's slot — cite the
  two lemmas together when assembling.

**Bottom line: the coupling route's bound `(3σ² + 2qσ + 7σ + 2)/2^{n+1}` (no α, no +q²) now
rests on fully audited mathematics.** Remaining: paper-rigor exposition (items 3–5 above,
all mechanical) and the Lean build (§6–7).

## 6. Lean mapping (repo inventory, verified 2026-07-05)

Two PDS surfaces coexist. LM20 Thm 1/2 already exist on the **Legacy** surface —
`delta_eq_advantage` (`Legacy/FundamentalTheorem.lean:216`, nonadaptive Adv),
`system_coupling_exists` (`Legacy/SystemCoupling.lean:77`) — plus the generic coupling
primitives `DistCoupling`/`prDisagree`/`coupling_bound` (`Coupling.lean:41/51/136`) and the
orbit machinery (`classifierBlockUniform`, `labelFirstBlockCoupling`,
`PDS.ofPositionTapeDist`, `equivAdaptive_iff_nonadaptive` at `Legacy/Equiv.lean:893`).
HCTR2 lives on the CR18/HTechnique surface (`hctr_bad_bound` at
`HTechnique/HCTR2.lean:4929`). Gaps (from the inventory, M1–M8): adaptive Thm-1/2 forms on
Legacy (cheap); **M2, the one bridging lemma that matters**:
`statDist(transcriptDist S e, transcriptDist T e) ≤ Pr[coupled runs diverge]` on the
HTechnique surface via pushforward + `coupling_bound`; the two-sided lazy-WOR-π = uniform-π
lemma (new but standard); `G̃/F̃` as tape-indexed DDS; and restating the bad event over the
shared tape — where the existing 22-case engine should apply **with iid pinning and no WOR
variant** (the CE migration plan's §9 step 1 becomes unnecessary). Design constraint M7:
build both representatives as deterministic functions of one common tape and literally
equal outside Bad; only honest nonnegative representatives count.

## 7. Work plan (next session)

1. **Math first**: draft `HCTR2_COUPLING_PROOF.md` = the §3 design with all five verifier
   corrections folded in, Bad in inference form, fallback as appendix; statements/proof
   shapes in chat before Lean.
2. **Adversarial verification** of open problems 1 and 2 (separate passes): the full
   Lemma B case audit; an independent re-derivation of posterior constancy.
3. **Lean skeleton** after 1–2 clear: M2 bridge lemma; tape space; lazy-WOR-π lemma.
4. **Reuse check**: confirm `hctr_bad_bound`'s 22-case engine applies to inference-form
   entries with iid pinning; log automation deltas into STATUS.md §7.
5. **Decision gate**: if 1 or 2 breaks, activate the fallback (bound reverts to CE-equal).

## 8. Comparison table

| | paper (H-coeff + PRP-RND) | CE route (confirmed) | coupling route (designed+verified) |
|---|---|---|---|
| bound | `(3σ²+2qσ+q²+7σ+2)/2^{n+1}` | `(3σ²+2qσ+7σ+2)/2^{n+1} · α`, `α = 2ⁿ/(2ⁿ−q+1)` | `(3σ²+2qσ+7σ+2)/2^{n+1}` |
| ideal object | `±rnd` then switch | `T̃aug` direct | `T̃` direct |
| augmentation / reveal / filter | augmentation, no reveal step | all three, load-bearing | **none** |
| hard lemma | (transcript counting) | hidden-key posterior (§5.2, confirmed) | Lemma B case audit + posterior constancy (open 1–2) |
| adaptivity | H-coeff | Lemma 1(iv)+Lemma 7, adaptive ν | `sup_e` + prefix conditioning |
| 22-case engine | world-Y, iid | `T̃aug`, WOR (α on response rows) | raw tape, iid — **verbatim** |
| status | published | fully verified, §5.2 done | design verified; proof to be written |

## References

- Lanzenberger, Maurer. *Coupling of Random Systems.* TCC 2020.
- Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification.* Diss. ETH
  29554, 2023. (Ch. 2 = extended LM20 + winnability Thm 2.37; Lemma 2.8, 2.18, 2.33, 2.44;
  Thm 2.31/2.32/2.45; open problems p. 85.)
- `papers/notes/HCTR2_CE_PROOF.md` (§5.1, §5.2.1, §7 case table reused here; §5.2.2–§6
  superseded on the primary path, load-bearing on the fallback).
- `papers/notes/LM20_ORBIT_PROOF.md` (XoP orbit coupling — the local precedent; its generic
  partition/coupling layer `Legacy/Applications/SoP/Partition.lean` is reusable).
- Crowley, Huckleberry, Biggers. ePrint 2021/1441 (pp. 10–17: the inference table and the
  22-case budget, inherited without the CE repairs #1–#3).
