# A tighter HCTR2 proof via Maurer's conditional equivalence

**Status (2026-07-05): verified draft.** Every step below survived an adversarial verification
pass (17 independent verifiers over 7 claims, all `holds_with_corrections`, zero refutations;
~1.6M tokens of checking). The corrections are folded in; the residual obligations are listed
in §10. The single architecture-level repair relative to the first draft: the naive
"conditional law is uniform over the good set" argument was **false as written** (the good
set depends on the hidden `(h̄, L)`), and Steps 2–3 are now built on the *hidden-key posterior
lemma* (§5.2), which all three verifiers independently re-derived and confirmed.

## 0. Result

For HCTR2 (Crowley–Huckleberry–Biggers, ePrint 2021/1441), a proof in Maurer's
random-systems framework organized around conditional equivalence (CE), comparing
`HCTR2[Perm(n)]` **directly** against the tweakable-URP ideal `T̃` — no `±rnd` intermediary,
no Halevi–Rogaway PRP-RND lemma — with final bound (side condition `q ≤ 2^{n−1}`):

```
Adv^{±p̃rp}_{HCTR2[E]}(q, σ, t)
    ≤ Adv^{±prp}_E(σ+2, t+σt′) + (3σ² + 2qσ + 7σ + 2)/2^{n+1} · 2ⁿ/(2ⁿ − q + 1)
```

versus the paper's

```
    ≤ Adv^{±prp}_E(σ+2, t+σt′) + (3σ² + 2qσ + q² + 7σ + 2)/2^{n+1}.
```

The additive `q²/2^{n+1}` switching term is traded for a multiplicative inflation
`2ⁿ/(2ⁿ−q+1) ≤ 1 + q/(2ⁿ−q+1)`, whose absolute cost is `≈ 3σ²q/2^{2n+1}` — a **net gain
whenever `3σ² < q·2ⁿ`**, i.e. essentially everywhere the bound is non-vacuous (it can lose
only in a few-very-long-queries corner, `q² ≲ 3σ²q/2ⁿ`). The paper's entire §3.4.2–3.4.3
collision combinatorics is reused; the without-replacement ideal changes *nothing additively*
— its effect is purely the multiplicative factor. In particular (this was the conjecture
going in, now confirmed by the case-by-case audit): the quadratic contributions from
XCTR-block and nonce collisions stay absorbed inside the existing POLYVAL/hash-property and
response-pinned rows of the 22-case budget; no new additive `q²` appears anywhere.

Novelty (verified against the literature through 2026-07): no published work proves HCTR2
directly against the tweakable-URP ideal or removes its PRP-RND term. Closest precedents:
Jha–Nandi's survey (ePrint 2018/1130, Lemma 9) proves a *PRF-simplified* HCTR\* directly vs
a tweakable length-preserving URP; ZCZ (Asiacrypt 2018) uses a without-replacement ideal in
an H-coefficient ratio; Minematsu (SAC 2006) did the single-block XEX/LRW analogue in exactly
this Maurer-CE style — which is the methodological template here, per the Liskov–Minematsu
XTS comment's remark that the approach "can offer a slightly tighter bound than previous
ones", citing Maurer's removal of the `C(q,2)/2^{2n}` term from 3-round Luby–Rackoff.

## 1. Where the loss enters in the paper's proof

The paper (§3.4–3.5) proves, via the H-coefficient technique, a main lemma against world
Y = `±rnd` (every query answered by fresh uniform bits):

```
Adv^{±rnd}_{HCTR2[Perm(n)]}(q, σ, t) ≤ Pr_Y[T_bad] ≤ (3σ² + 2qσ + 7σ + 2)/2^{n+1}
```

then pays `Adv^{±p̃rp}_{±rnd}(q,σ,t) ≤ C(q,2)/2ⁿ ≤ q²/2^{n+1}` [HR03, App. C, Lemma 6] to
reach the tweakable URP. This `±rnd` detour is a design choice inherited from the
Halevi–Rogaway CMC/EME tradition (also Adiantum, TET, HCH, HEH, XCB, FAST). Nothing in the
collision analysis needs it: the bad event already implies all the distinctness that
separates `rnd` from `T̃` (§5.1 below). CE lets us compare against `T̃` in one step and
*still* compute the bad probability in the convenient (ideal) world.

Notation (paper §3.1, §3.4): per query `s`, `mˢ = ⌈|Pˢ|/n⌉` response blocks,
`dˢ = mˢ + ⌈|Tˢ|/n⌉`; `σ ≥ Σ_s dˢ`; `σ_m = 2 + Σ_s mˢ` block-cipher calls; `ℓˢ = |Pˢ| ≥ n`.
Augmented transcript: leftover blocks `Dˢ = XCTR_π(Sˢ)[|Pˢ|−n; nmˢ−|Pˢ|]`, plus `h̄, L`
revealed after all queries. Inferred multisets (direction-agnostic — every query contributes
`MMˢ` to `D` and `UUˢ` to `R` regardless of direction):

```
D = [bin(0), bin(1)] ⊎ ⊎_s [MMˢ, S₁ˢ, …, S_{mˢ−1}ˢ]        (π inputs)
R = [h̄, L]           ⊎ ⊎_s [UUˢ, Y₁ˢ, …, Y_{mˢ−1}ˢ]        (π outputs)
```

Bad ⇔ some entry of `D` or of `R` has multiplicity > 1.

## 2. The Maurer toolkit, with its verified soundness status

All systems are families of conditional distributions `P^F_{Y_i|X^i Y^{i−1}}` (Maurer02
Def 3 — the input alphabet may be a union of query types, which is how we get bidirectional
+ reveal access without any permutation-specific lemma). An MES `A = A₀ ≥ A₁ ≥ …` is a
monotone sequence of (possibly internal) events, `A₀` = the certain event.

What we use, and what the adaptivity literature (Jetchev–Özen–Stam ASIACRYPT'12 = JOS12;
Maurer ISIT'13; Demay–Gazí–Maurer–Tackmann '14) says about each piece:

- **Def 6 / footnote 11 (one-sided CE).** `F|A ≡ G|C` formally means: there is a common
  system `H` with `P^F_{Y_i|X^i Y^{i−1} A_i} = P^H_{Y_i|X^i Y^{i−1}}` and likewise for `G|C`,
  *wherever defined*. Exhibiting `H` and matching the definedness domains is a real proof
  obligation (§5.2, §5.4) — the "wherever defined" convention does work here and cannot be
  left implicit.
- **Lemma 1(iv).** `F|A ≡ G|C` + pointwise domination
  `P^F_{A_i|X^i Y^{i−1} A_{i−1}} ≤ P^G_{C_i|X^i Y^{i−1} C_{i−1}}` ⟹ `F^A ≡ G^{C∧D}` for an
  MES `D` adjoined to `G`. **Proof debt:** the proceedings say "the proof of (iv) is
  omitted"; no published proof exists (verified). We carry our own (§6.1): adjoin `D` by a
  per-step Bernoulli thinning with retention ratio
  `r_i(x^i, y^{i−1}) = P^F_{A_i|·A_{i−1}} / P^G_{C_i|·C_{i−1}} ∈ [0,1]` (well-defined by
  domination; depends only on `(x^i, y^{i−1})`, allowed by Def 7).
- **Lemma 7 / Theorem 1(i),(iii).** `F^A ≡ G^B` ⟹ for every adaptive distinguisher **D**:
  `|P^{DF}(E_k) − P^{DG}(E_k)| ≤ P^{DF}(¬A_k) = P^{DG}(¬B_k)`; packaged, Theorem 1(iii) is
  *verbatim* our Step 4: `F|A ≡ G|C` + domination ⟹ `Δ_k(F,G) ≤ ν(F, ¬A_k)` with `ν` the
  **adaptive** provoking probability on the dominated side. **Soundness: unconditional** for
  adaptive distinguishers — re-proven independently in MPR07 (Lemma 4, per-distinguisher),
  JOS12 (their Lemma 7, under the even weaker hypothesis
  `P^F_{a_j Y^j|X^j} ≤ P^G_{Y^j|X^j}`), and Maurer ISIT'13 (Lemma 2/Theorem 3).
- **Theorem 2 (ν = μ adaptive→non-adaptive collapse): NOT USED.** This is the piece with
  the known gap: stepwise CE alone does *not* imply the collapse (JOS12 Prop. 10
  counterexample: URP with the "no fixed point yet" MES); the sound versions need output-
  independence of the event (JOS12 Thm 12) or joint CE (ISIT'13 Def 13). Our chain
  terminates at the adaptive `ν`, so we owe nothing here — but this transfers an obligation
  to Step 5: **every case bound must hold conditioned on an arbitrary adaptive C-good
  history**, and may not silently fix a non-adaptive transcript (§7).
- **Lemma 10(iii) (bidirectional lifting): DROPPED.** It is stated and proven only for an
  `X`-random permutation `Q` and `⟨Q⟩` on a fixed domain; our augmented systems are
  tweakable, variable-length, and carry auxiliary outputs (leftovers, reveal) — not `⟨Q⟩`
  for any `Q`. It is also unnecessary: we define both systems *natively* as bidirectional
  (Def 3, tagged query alphabet), define the MES on them directly, and apply
  Lemma 1(iv)/Lemma 7 which hold for arbitrary random systems. (Minematsu's `⟨G⟩`/cpa′
  "equivalent representation" from FSE'09 §2.2 is the same move.)
- **Lemma 8(ii)** is the pattern we generalize: `R^C ≡ P^{C∧D}` (URF vs URP under output-
  distinctness), proven exactly via Lemma 1(iv) from `P^R_{C_i|·} ≤ P^P_{C_i|·}`. Our proof
  is this lemma with `R ↦ T̃aug`, `P ↦ HCTR2[Perm(n)]aug`, distinctness ↦ the HCTR2 bad
  event.

## 3. The two systems

Both are single random systems with query alphabet = tagged union
`{enc(T,P)} ∪ {dec(T,C)} ∪ {reveal}` (direction bit native, per Def 3):

- **G := HCTR2[Perm(n)]aug** — the real construction over one uniform `π`; each response
  carries the leftover block `Dˢ`; `reveal` outputs `(h̄, L) = (π(bin 0), π(bin 1))`.
- **F := T̃aug** — per `(T, ℓ)` class an independent uniform permutation of `{0,1}^ℓ`
  (a uniform length-preserving tweakable permutation family); augmented with independent
  uniform leftover coins per distinct query, and **`(h̄, L)` sampled internally at time 0**
  as independent uniform coins, output at `reveal`.

Three definitional decisions, each load-bearing (each was the target of a concrete
verifier attack that succeeds if the decision is dropped):

1. **`h̄, L` exist in `F` from time 0** (not sampled at reveal time) — otherwise the MES
   below is not even defined for `i ≤ q`, and the reveal-step CE fails (the reveal must
   output the *same* internal values the MES has been conditioning on).
2. **`reveal` is terminal**: both systems answer `⊥` to everything after it. Otherwise the
   bound is *vacuous*: a distinguisher that reveals first learns `h̄` and then forces a
   `D`-collision deterministically (query `(T¹, M¹‖N)` then `(T², M²‖N)` with
   `M² = M¹ ⊕ H_h̄(T¹,N) ⊕ H_h̄(T²,N)` gives `MM² = MM¹` with probability 1), so
   `ν(F, ¬C) ≈ 1`. Terminality is WLOG for the target statement: the plain systems are
   obtained by the stripping converter that never reveals (Lemma 5(ii)), and a late reveal
   dominates any early-reveal strategy for the *plain*-induced distinguisher class.
3. **Pointless queries are filtered *before* augmentation.** A repeated `(T,P)`/`(T,C)`
   pair (including pairs formed by an earlier answer — mirror queries) is answered by a
   caching filter converter in front of both *plain* systems; this is advantage-preserving
   because both plain worlds are consistent permutation families (a repeat or mirror query
   has a determined answer in both). Only the filtered (repeat-free) interaction is
   augmented and carries the MES. This ordering is forced: with per-query-index fresh
   leftover coins, `F`aug answers a repeated partial-block query with fresh leftovers while
   `G`aug deterministically replays them (same `S`, same XCTR tail) — advantage ≈ 1 — and a
   passed-through repeat would duplicate multiset entries, setting `¬C` with probability 1
   and making `ν` vacuous. (Alternative, equivalent fix: memoize `F`aug's coins per distinct
   underlying pair; filtering first is cleaner.)

Augmentation only strengthens the distinguisher (plain = converter ∘ augmented), so the
final bound transfers to the plain pair: `Δ_q(plain) ≤ Δ_{q+1}(aug)`.

## 4. The MES

On **both** systems, over the filtered stream, with `h̄, L` internal from time 0:

```
C_i = "the multisets D, R built from the first i queries (plus bin(0), bin(1), h̄, L)
       have no entry of multiplicity > 1"
```

In `G` the entries are genuine π inputs/outputs; in `F` they are the formally identical
expressions computed from (query, response, leftover coins, `h̄`, `L`) via the paper's p. 10
inference table (`MMˢ = Mˢ ⊕ H_h̄(Tˢ,Nˢ)`, `UUˢ = Uˢ ⊕ H_h̄(Tˢ,Vˢ)`, `Sˢ = MMˢ ⊕ UUˢ ⊕ L`,
`Y_jˢ = ((Nˢ⊕Vˢ) ‖ Dˢ)[(j−1)n; n]` for `1 ≤ j ≤ mˢ−1` (0-based substring convention: XCTR
starts at `bin(1)`, so `Y₁` is the stream block at offset 0), `S_jˢ = Sˢ ⊕ bin(j)`).

**Convention fixes** (Maurer §3.2 requires `A₀` = certain): `C₀ :=` certain; the time-0
checks `bin(0) ≠ bin(1)` (trivial) and `h̄ ≠ L` are folded into `C₁`. In `F`, `h̄ = L` has
probability `2^{−n}` and is charged to `ν` — it is exactly the paper's `h̄ ≟ L` case, part of
the existing `+2/2^{n+1}` term. This fold is also what makes §5.2 work: `C` conditioning
forces the `(h̄, L)`-posterior in `F` onto ordered *distinct* pairs, matching `G`'s
`(π(bin0), π(bin1))`. The reveal step adds no multiset entries: `C_{q+1} := C_q`.

Side conditions carried throughout: `σ_m ≤ 2ⁿ` (else both worlds' good sets are empty by
pigeonhole and every conditional below is 0 — trivial case split); `k < 2^ℓ` per class
(automatic: a class-exhausting query would be pointless); `ℓ ≥ n` (HCTR2 spec);
`mˢ − 1 < 2ⁿ` (distinct `bin(j)` counters).

## 5. The conditional equivalence and the domination

### 5.1 Step 1 — `C` forces `T̃`-consistency (two-sided, direction-agnostic)

**Lemma (class distinctness).** In a `C`-good transcript, within each `(T, ℓ)` class and
across *all* queries regardless of direction, the induced pairs `(Pˢ, Cˢ)` have pairwise
distinct plaintexts **and** pairwise distinct ciphertexts.

*Proof.* Same class ⟹ the parse `C = U‖V` at position `n` (and `P = M‖N`) is at the same
offset. `Cʳ = Cˢ` ⟹ `Uʳ = Uˢ ∧ Vʳ = Vˢ` ⟹
`UUʳ = Uʳ ⊕ H_h̄(T,Vʳ) = Uˢ ⊕ H_h̄(T,Vˢ) = UUˢ` — an `R`-multiset repeat. Dually `Pʳ = Pˢ`
forces `MMʳ = MMˢ` in `D`. Purely deterministic cancellation of `H_h̄` at the shared internal
key — no hash properties, no randomness; hence usable identically in both worlds, which is
what §5.2 needs. Covers the degenerate `ℓ = n` case (`V, N` empty; `H` on the empty message
is well-defined by the `n | |M|` branch, since `n` divides 0). Note a full mirror
`(Pʳ,Cʳ) = (Pˢ,Cˢ)` is *also* excluded by `C` (`Pʳ = Pˢ` alone forces the `MM` repeat in
`D`), so class distinctness follows from `C` alone; the pointlessness filter remains a
standing convention for the §3 reasons (leftover replay, definedness of the conditionals),
not for this lemma. ∎

**Lemma (attainability).** A `C`-good filtered transcript has positive probability under
`F`. *Proof:* per class the pairs form a partial injection (above), which extends to a full
permutation of `{0,1}^ℓ` (finite extension); assemble per tweak; the augmentation
coordinates (`h̄`, `L`, leftovers) are free uniform coins in `F`, hence unconstrained. ∎

### 5.2 Step 2 — the hidden-key posterior lemma and `G|C ≡ F|C` (full proof)

**Why the naive argument fails.** The first-draft claim "conditioned on `C_i` the response
law is uniform over the good set" is false: `C_i`-goodness depends on the *hidden* `(h̄, L)`,
so the visible conditional law is proportional to a count of compatible `(h,l)` pairs, which
genuinely varies with the response (concrete counterexample: first encryption query, `m = 2`
— the number of `h` killing `UU = Y₁` varies with the candidate response). The CE is proven
at the *joint* level. Everything below is over the filtered (repeat- and pointless-free)
stream, with the conventions of §3–§4 in force.

#### 5.2.0 Setup and notation

Fix a query sequence `x^i = (x_1, …, x_i)`, each `x_s = (dir_s, T_s, ·)` with message length
`ℓ_s ≥ n`, `m_s = ⌈ℓ_s/n⌉`. A **candidate response** `y_s` is a pair (main response of
length `ℓ_s`, leftover of length `n·m_s − ℓ_s`). For a tuple `τ = (x^i, y^i, h, l)` define
the **derived pairs**, via the paper's p. 10 inference equations applied per query
(direction-agnostically — each query yields a `(T, P, C, D)` record, with `P` the query for
enc and the response for dec, and vice versa for `C`):

```
per query s:  MM_s = M_s ⊕ H_h(T_s, N_s)          (M_s‖N_s = P_s, |M_s| = n)
              UU_s = U_s ⊕ H_h(T_s, V_s)          (U_s‖V_s = C_s, |U_s| = n)
              S_s  = MM_s ⊕ UU_s ⊕ l,   S_{s,j} = S_s ⊕ bin(j)         (1 ≤ j ≤ m_s−1)
              Y_{s,1} ‖ … ‖ Y_{s,m_s−1} = (N_s ⊕ V_s) ‖ D_s
```

and the **derived pair family** — the indexed list (counted with multiplicity)

```
φ_i(τ) = ⟨ bin(0) ↦ h, bin(1) ↦ l ⟩ ⧺ ⧺_s ⟨ MM_s ↦ UU_s, S_{s,j} ↦ Y_{s,j} (1 ≤ j ≤ m_s−1) ⟩,
```

of exactly `u_i = 2 + Σ_{s≤i} m_s` (input, output) pairs, whose input multiset is `D` and
output multiset is `R` (§1). (As an indexed family it is well-formed off `Good` too, where
entries may literally coincide; only under `Good_i` is it a *set* of `u_i` distinct pairs.)
Let

```
Good_i(τ)  ⟺  D and R (as multisets of u_i entries each) are repeat-free,
```

a **deterministic, world-independent predicate** of `τ`. `Good_i(τ)` makes `φ_i(τ)` an
injective partial function `{0,1}ⁿ ⇀ {0,1}ⁿ` of size exactly `u_i`. The MES of §4 is
`C_i = Good_i(x^i, Y^i, h̄, L)` with the *internal* `(h̄, L)`. Write `k_s` for the number of
`t < s` with `(T_t, ℓ_t) = (T_s, ℓ_s)` — deterministic in `x^s` alone. Falling factorial:
`(2ⁿ)_u = 2ⁿ(2ⁿ−1)⋯(2ⁿ−u+1)`. Standing side conditions (§4): `u_i ≤ 2ⁿ` (else see the
degenerate split in 5.2.2), `k_s < 2^{ℓ_s}` (automatic from the filter: after `2^{ℓ}`
distinct same-class pairs the class permutation is fully determined, so any further query
in the class is a repeat or mirror, absorbed by the filter), `m_s − 1 < 2ⁿ`.

Throughout, `P^W[y^i, h, l | x^i]` denotes the **system-functional** quantity: the
probability, in the experiment with the input sequence *fixed* to `x^i`, that the responses
are `y^i` and the internal pair is `(h, l)` — equivalently the product of the automaton's
per-step conditionals. (This, not a conditional of some adaptive interaction, is what
Maurer's Def 6 and Lemma 1(iv) consume; for full-transcript conditionals such as 5.2.4's
posterior the two readings coincide for every environment, since environment factors
cancel.) It is well-defined since `(h̄, L)` is an internal random variable of both systems
(in `G` it is `(π(bin 0), π(bin 1))`; in `F` a time-0 coin). **Joint causality:** in both
automata the internal randomness (`π`; resp. the class permutations, coins, and the time-0
pair) is sampled independently of the inputs, and `(Y^{i−1}, h̄, L)` are functions of
`(x^{i−1}, randomness)`; hence the joint law of `(Y^j, h̄, L)` given `x^i` depends only on
`x^j` for `j ≤ i`. We use this when forming ratios.

**Totality off the intended histories:** both augmented systems answer `⊥` deterministically
on post-reveal and on pointless/repeat queries, and `C` freezes there; so the CE and
domination statements below hold trivially on those histories (both conditionals are the
same Dirac mass), and Maurer's quantification "for all input sequences" — including early
reveals and malformed streams — is satisfied. The reveal-step statements are phrased for a
reveal at any position, applied to the current filtered prefix.

#### 5.2.1 Lemma (inference/execution inversion)

Fix `(h, l)` with `h ≠ l`, a query `x_s`, a candidate `y_s`, and let `φ_s` denote the
derived pairs of query `s` alone. Let `π` be **any** permutation with
`π(bin 0) = h, π(bin 1) = l` and `π ⊇ φ_s`. Then the `G`-execution of `x_s` under `π`
returns exactly `y_s`. Conversely, if the `G`-execution of `x_s` under `π` returns `y_s`,
then `π ⊇ φ_s`.

*Proof.* Forward direction, `x_s = enc(T, P)`, `P = M‖N`: the execution computes
`MM = M ⊕ H_{π(bin0)}(T, N) = M ⊕ H_h(T, N) = MM_s`, then `UU = π(MM_s) = UU_s` (from
`φ_s`), `S = MM_s ⊕ UU_s ⊕ π(bin 1) = S_s`, and XCTR outputs `π(S_{s,j}) = Y_{s,j}`. Its
response is `C′ = U′‖V′` with

```
V′ = N ⊕ (Y_{s,1}‖…‖Y_{s,m_s−1})[0; ℓ_s−n] = N ⊕ ((N ⊕ V_s)‖D_s)[0; ℓ_s−n] = N ⊕ (N ⊕ V_s) = V_s
U′ = UU_s ⊕ H_h(T, V′) = UU_s ⊕ H_h(T, V_s) = U_s          (definition of UU_s inverted)
D′ = (Y_{s,1}‖…‖Y_{s,m_s−1})[ℓ_s−n; n·m_s−ℓ_s] = D_s ,
```

i.e. `y_s`. (The converse below is scoped differently: for **any** permutation `π` with
`π(bin 0) = h, π(bin 1) = l` — not assumed to extend `φ_s` — if the execution returns `y_s`
then `π ⊇ φ_s`.) For `x_s = dec(T, C)`, `C = U‖V`: the execution computes
`UU = U ⊕ H_h(T, V) = UU_s` — determined by the *query* and `h` — then
`MM = π^{-1}(UU_s) = MM_s` (because `π ⊇ φ_s` contains `MM_s ↦ UU_s` and `π` is injective,
so the preimage is unique), `S = S_s`, and forward XCTR calls `π(S_{s,j}) = Y_{s,j}` (XCTR
is forward in both directions — only the single `E^{-1}` call is inverse); then
`N′ = V ⊕ (Y-blocks)[0;ℓ−n] = N_s` and `M′ = MM_s ⊕ H_h(T, N′) = M_s` by the same two-line
cancellations, and `D′ = D_s`. Conversely: if the execution returns `y_s`, then the
executed π-evaluations are, by definition of the procedure, exactly the derived pairs of
`(x_s, y_s, h, l)` — the inference equations are the procedure equations solved for the
π-I/O, which is the paper's p. 10 observation. ∎

The same statement holds jointly for a sequence: `π ⊇ φ_i(τ)` (with the two constants) iff
the `G`-run on `x^i` outputs `y^i` with `(h̄, L) = (h, l)` — by induction on `s`: given
`π ⊇ φ_s` (forward direction), resp. on the event that query `s`'s output is `y_s`
(converse), the execution of query `s` reads `π` only at `{bin0, bin1} ∪ (derived inputs of
query s)`; and since `G` is stateless given `π`, the joint event factors as the conjunction
of the per-query events plus `{π(bin0) = h, π(bin1) = l}`.

#### 5.2.2 Lemma (real-world falling-factorial constancy)

For every tuple `τ = (x^i, y^i, h, l)` with `Good_i(τ)`:

```
P^G[y^i, h, l | x^i] = 1/(2ⁿ)_{u_i} = (2ⁿ(2ⁿ−1))^{-1} · ∏_{s=1}^{i} c_s ,
      c_s = ∏_{j=0}^{m_s−1} (2ⁿ − u_{s−1} − j)^{-1},   u_s = 2 + Σ_{t≤s} m_t, u_0 = 2.
```

In particular the value depends only on `x^i` (through `u_i`), **not on `(h, l)` nor on
which good `y^i`** — and not on the directions of the queries.

*Proof.* By the sequence form of 5.2.1, the event `{Y^i = y^i, (h̄,L) = (h,l)}` given `x^i`
equals `{π ⊇ φ_i(τ)}`. `Good_i(τ)` makes `φ_i(τ)` an injective partial function of size
exactly `u_i`, and for uniform `π`,
`Pr[π ⊇ φ] = (2ⁿ − u_i)!/(2ⁿ)! = 1/(2ⁿ)_{u_i}` — a count of completions, blind to how the
pairs were produced (forward vs inverse calls). The regrouping into `∏ c_s` is arithmetic.
Degenerate split: if `u_i > 2ⁿ`, no injective `φ_i` of size `u_i` exists, so the hypothesis
`Good_i` is unsatisfiable (pigeonhole on n-bit `D`-entries) and the lemma is vacuous;
downstream, `N_i = 0` and the positivity/definedness clauses of 5.2.4–5.2.5 exclude the case
(this is the §4 `σ_m ≤ 2ⁿ` split). Note the lemma says nothing off `Good` (there the
transcript may still be `G`-possible, with a different probability); we never need it. ∎

#### 5.2.3 Lemma (ideal-world product constancy)

Call `(x^i, y^i)` **class-injective** if within each `(T, ℓ)` class the induced plaintexts
are pairwise distinct and the induced ciphertexts are pairwise distinct (across both
directions). For every `τ = (x^i, y^i, h, l)` with `(x^i, y^i)` class-injective (in
particular for every `Good` tuple, by §5.1 — whose proof is a pointwise deterministic
cancellation, valid at the same `(h,l)` as the tuple):

```
P^F[y^i, h, l | x^i] = 2^{−2n} · ∏_{s=1}^{i} c′_s ,
      c′_s = (2^{ℓ_s} − k_s)^{-1} · 2^{−(n m_s − ℓ_s)} .
```

*Proof.* `F`'s components are independent: the class permutations `{π_{T,ℓ}}`, the leftover
coins, and the time-0 pair `(h̄, L)`; the responses never read `(h̄, L)` or other classes.
The `(h̄,L)`-factor is `2^{−2n}`. Per query `s`, the queried point is fresh in its class:
on the lemma's own domain this already follows from class-injectivity of the tuple
(plaintext side for enc, ciphertext side for dec); the pointlessness filter — whose rule
covers answers, so mirror queries too — guarantees it for the realized interaction, which
is what 5.2.5's definedness bookkeeping uses (division of labor: the lemma is self-contained
on class-injective tuples; the filter matters for which prefixes occur). Prior same-class
queries fix `k_s` input/output pairs of `π_{T_s,ℓ_s}` (each prior query fixes exactly one,
either direction), and these pairs are pairwise **distinct** — prefixes of class-injective
tuples are class-injective — so exactly `k_s` output values (resp. input values, for dec)
are excluded and the response to the fresh point is uniform over exactly `2^{ℓ_s} − k_s`
values. The candidate `y_s` is one of them precisely because `(x^i, y^i)` is
class-injective: the excluded values are the `k_s` prior same-class *ciphertexts* for an
enc query (resp. plaintexts for dec), whether those values appeared as queries (prior dec
queries) or as responses (prior enc answers); a candidate hitting any of them has
conditional probability 0 and is outside the claim, and outside `Good`. The leftover factor
is `2^{−(n m_s − ℓ_s)}` (independent coins). Multiply. Constancy in `(h, l)` and across
class-injective `y^i` is manifest. ∎

#### 5.2.4 Corollary (posterior matching)

For `i ≥ 1`, condition either world on `(X^i = x^i, Y^i = y^i, C_i)`, assuming this event
has positive probability. Then the posterior of `(h̄, L)` is uniform on

```
S(x^i, y^i) = {(h, l) : Good_i(x^i, y^i, h, l)}
```

**in both worlds**, and the event has positive probability iff `N_i(y^i) := |S(x^i,y^i)| > 0`
(same condition in both worlds).

*Proof.* `C_i` given `(x^i, y^i)` is exactly `(h̄, L) ∈ S(x^i, y^i)`. So the posterior at
`(h, l)` is `P^W[y^i, h, l | x^i] · 1[(h,l) ∈ S] / Σ_{(h′,l′) ∈ S} P^W[y^i, h′, l′ | x^i]`,
and by 5.2.2 resp. 5.2.3 the numerator is the *same constant* for every `(h,l) ∈ S` — hence
uniform on `S`, in each world separately. (For `G`, tuples with `h = l` are already outside
`Good`; for `F`, `S` excludes `h = l` because `[h̄, L] ⊆ R` — this is the §4 fold of the
`h̄ ≠ L` check into `C₁`, and it is what reconciles `G`'s ordered-distinct pair
`(π(bin0), π(bin1))` with `F`'s iid pair: both conditioned laws are uniform on the same
`h ≠ l`-respecting set.) Positivity: the denominator is `(const_W(x^i)) · N_i(y^i)` with
`const_W > 0` under the standing side conditions, so positivity ⟺ `N_i(y^i) > 0`,
world-independently. ∎

#### 5.2.5 Theorem (conditional equivalence, Def-6 form, including the reveal)

For every `i ≥ 1`, every `x^i, y^{i−1}, y_i`:

```
P^G_{Y_i | X^i Y^{i−1} C_i}(y_i, x^i, y^{i−1})  =  P^F_{Y_i | X^i Y^{i−1} C_i}(y_i, x^i, y^{i−1})
                                                =  N_i(y^{i−1} y_i) / Σ_{y′} N_i(y^{i−1} y′)
```

wherever either side is defined; and both sides are defined on exactly the same arguments,
namely those with `Σ_{y′} N_i(y^{i−1} y′) > 0`. Moreover at the terminal reveal step
(`i = q+1`, `C_{q+1} = C_q`), both worlds output `(h̄, L)` distributed uniformly on
`S(x^q, y^q)` given `(x^q, y^q, C_q)`. Hence `G|C ≡ F|C`, with the common system `H` of
Maurer's footnote 11 exhibited explicitly as: "answer `y_i` with probability
`N_i(y^{i−1}y_i)/Σ_{y′} N_i(y^{i−1}y′)`; at reveal, output a uniform element of `S`"
(extended by a *fixed default response* — a Dirac mass — off histories where the denominator
vanishes; a uniform extension would be ill-defined on the countably infinite response
alphabet, and `H` must be total per Maurer's footnote 5).

*Proof.* Unfold Def 6:

```
P^W_{Y_i|X^i Y^{i−1} C_i}(y_i, ·) = P^W[Y^i = y^{i−1}y_i, C_i | x^i] / P^W[Y^{i−1} = y^{i−1}, C_i | x^i].
```

Numerator: `Σ_{(h,l)} P^W[y^{i−1}y_i, h, l | x^i] · 1[Good_i] = const_W(x^i) · N_i(y^{i−1}y_i)`
by 5.2.2/5.2.3 (only `Good` tuples contribute — the indicator kills the rest, which is why
the off-`Good` values of the joint never matter). Denominator: sum the numerator over `y_i`
(the events `{Y_i = y′}` partition, and `C_i` is `Y^i`-measurable given `(x^i, h, l)`):
`const_W(x^i) · Σ_{y′} N_i(y^{i−1} y′)`. The world constant cancels, leaving the displayed
world-independent ratio. Definedness ⟺ denominator > 0 ⟺ `Σ_{y′} N_i > 0` — the same
predicate in both worlds (this is the **domain-match**: no argument is `F`-defined but
`G`-undefined or vice versa, so Def 6's "wherever defined" and Lemma 1(iv)'s quantification
range over the same set). The reveal step is 5.2.4 verbatim (its output *is* `(h̄, L)`, the
system is terminal afterwards, and `C_{q+1} = C_q` adds no constraint). Within-query
degeneracies (`S_{s,j} = MM_s ⟺ UU_s ⊕ l = bin(j)`, `MM_s ∈ {bin0, bin1, prior D}`, …)
need no case analysis: they are transcript-level predicates that remove `(h,l)` from `S` or
zero out `N_i` *identically in both worlds*. ∎

#### 5.2.6 Corollary (reduction of Step 3 to the per-element inequality)

For every `i ≥ 1` and every argument with `P^W[y^{i−1}, C_{i−1} | x^{i−1}] > 0`: if
`u_{i−1} + m_i > 2ⁿ` then `Good_i` is unsatisfiable and both worlds' conditionals are 0
(domination trivial); otherwise

```
P^W_{C_i | X^i Y^{i−1} C_{i−1}} = ( Σ_{y_i} N_i(y^{i−1} y_i) / N_{i−1}(y^{i−1}) ) × w_i^W ,
      w_i^G = c_i ,   w_i^F = c′_i ,
```

where the bracket is world-independent (a nonnegative combinatorial factor — not itself a
probability; only `bracket × w_i` is; note the bracket can far exceed 1). Hence the
domination `P^F_{C_i|·} ≤ P^G_{C_i|·}` of §5.3 holds **if** `c′_i ≤ c_i` at every step where
the bracket is positive — which is exactly the inequality proven in §5.3 (and conversely,
`c′_i ≤ c_i` is forced wherever the bracket is positive). Reveal step: `C` at the reveal is
`C` of the prefix (no new multiset entries), so `P^W_{C|·}` at that step equals 1 in both
worlds wherever defined — domination is `1 ≤ 1` directly, without the displayed identity
(under 5.2.0's multiset-only `Good`, the literal bracket at the reveal would be `2^{2n}`
against `w = 2^{−2n}`-type constants; the direct one-liner avoids that bookkeeping).

*Proof.* `P^W[C_i, y^{i−1} | x^i] = Σ_{y_i} const_W^{(i)}(x^i) N_i(y^{i−1}y_i)` and
`P^W[C_{i−1}, y^{i−1} | x^i] = P^W[C_{i−1}, y^{i−1} | x^{i−1}] = const_W^{(i−1)}(x^{i−1})
N_{i−1}(y^{i−1})` (joint causality, §5.2.0); divide, and note
`const_W^{(i)}/const_W^{(i−1)} = w_i^W` by the product forms in 5.2.2/5.2.3 (both defined
in the non-degenerate case). Per-extension monotonicity `S(x^i, y^i) ⊆ S(x^{i−1}, y^{i−1})`
holds for each fixed `y_i`, but is summed over `y_i` — hence the bracket is a combinatorial
factor, not a fraction ≤ 1; its world-independence is all that is used. ∎

**What 5.2 delivers downstream.** 5.2.5 is the `F|C ≡ G|C` hypothesis of Lemma 1(iv)
(with domain match); 5.2.6 turns its domination hypothesis into the elementary §5.3
inequality; 5.2.4 at `i = q+1` is the reveal-step CE. No other property of the two worlds
is used anywhere in §6.

### 5.3 Step 3 — pointwise domination `P^F_{C_i|·} ≤ P^G_{C_i|·}`

By Corollary 5.2.6, `P^W_{C_i|·C_{i−1}} = (world-independent survival fraction) × w_i^W`
with `w_i^G = c_i`, `w_i^F = c′_i`, so domination reduces exactly to the per-element
inequality `c′_i ≤ c_i`:

```
∏_{j=0}^{m−1} (2ⁿ − u − j)^{-1}  ≥  ((2^ℓ − k) · 2^{nm − ℓ})^{-1}
⟺  ∏_{j=0}^{m−1} (1 − (u+j)/2ⁿ)  ≤  1 − k/2^ℓ
```

Under `C_{i−1}` all prior `D`-entries are distinct, so `u = 2 + Σ_{t<i} m_t ≥ 2 + km ≥ k+2`
(the `k` same-class predecessors have the *same* `m` — length-preservation fixes `ℓ` for
decryption answers too; `bin(0), bin(1)` and other classes only increase `u`, which only
*helps*). With all factors in `[0,1]` (from `k ≤ u−2 < 2ⁿ` and the `σ_m ≤ 2ⁿ` case split of
§4) and `m ≥ 1`, `ℓ ≥ n`:

```
∏_j (1 − (u+j)/2ⁿ) ≤ (1 − k/2ⁿ)^m ≤ 1 − k/2ⁿ ≤ 1 − k/2^ℓ.        ∎
```

Reveal step: `1 ≤ 1` (no new entries). Degenerate split: if `u + m > 2ⁿ`, `Good` is empty
for every `(h,l)` by pigeonhole and both sides are 0.

This inequality is the mathematical heart of why the switch term can be absorbed: the
paper's own good-transcript comparison (`2^{−σ_m n} ≤ ∏ 1/(2ⁿ−i)`, p. 11) is its `k = 0`
full-transcript shadow; here the per-query `T̃` deficit `1 − k/2^ℓ` is covered by the real
world's accumulated usage `u ≥ k + 2`.

### 5.4 A structural remark

In `G`, `¬C` can only fire through `D`-collisions (a permutation cannot produce an
`R`-collision from distinct fresh inputs); all `R`-side rows of the 22-case analysis are
ideal-world-only phenomena. Nothing downstream needs this, but it is a useful audit
invariant for §7.

## 6. Assembly

### 6.1 Lemma 1(iv), proven

Adjoin `D` to `G` per Def 7 with retention probability
`r_i(x^i, y^{i−1}) = P^F_{C_i|x^i y^{i−1} C_{i−1}} / P^G_{C_i|x^i y^{i−1} C_{i−1}} ∈ [0,1]`
(defined on the common domain by §5.2's domain match; `≤ 1` by §5.3; depends only on
`(x^i, y^{i−1})`, not `y_i`). Monotonicity of `C` makes `D_{i−1}` conditionally independent
of `(Y_i, C_i)` given the history with `C_{i−1}`; the chain rule plus `F|C ≡ G|C` then gives
the two-sided per-step equality `P^F_{Y_i C_i|·C_{i−1}} = P^G_{Y_i (C∧D)_i|·(C∧D)_{i−1}}`,
i.e. `F^C ≡ G^{C∧D}`; support bookkeeping closes by induction from equal factor products,
using `C₀` certain. (Cross-check: the same conclusion follows from JOS12's Lemma 7 under
`P^F_{c_j Y^j|X^j} ≤ P^G_{Y^j|X^j}`, which our per-step hypotheses imply by the chain rule —
so Step 4 is doubly covered, once by our proof, once by the modern literature.)

### 6.2 Step 4 — the bound lands ideal-side

Lemma 7 now gives, for every adaptive distinguisher (the direction of §5.3 is what puts the
bare MES — and hence the `ν` computation — on the **ideal** side; the real side carries the
adjoined `C∧D`, and the right-hand side is `P^{DG}(¬(C∧D)_k)`, not the plain real-world bad
probability):

```
Δ_{q+1}(G, F) ≤ ν(T̃aug, ¬C_q)        (reveal step adds nothing: ¬C_{q+1} = ¬C_q)
```

and with the stripping/filter converters of §3 and the standard substitution step:

```
Adv^{±p̃rp}_{HCTR2[E]}(q, σ, t) ≤ Adv^{±prp}_E(σ+2, t+σt′) + ν(T̃aug, ¬C_q).
```

## 7. `ν(T̃aug, ¬C_q)`: the paper's combinatorics, rebuilt where needed

Because Theorem 2 is unused, `ν` is the **adaptive** provoking probability: every case bound
below is a per-step conditional bound given an arbitrary `C`-good history
(query + all prior queries/responses/leftovers), then union-bounded (JOS12 Prop. 9 shape).
In `T̃aug` this discipline is easy to satisfy: `h̄, L`, leftovers are coins independent of the
entire query–response process (responses never read them — they are dummies until the
terminal reveal), and responses are per-class uniform without replacement given the history.

Per-case port of the paper's §3.4.2 (pp. 11–14), with `k ≤ q−1` prior same-class queries and
`α := 2ⁿ/(2ⁿ − q + 1)`:

| case family | in `±rnd` world | in `T̃aug` world |
|---|---|---|
| impossible (`bin0≟bin1`, `S_iˢ≟S_jˢ`) | 0 | 0 (algebraic identities, world-independent) |
| pinned by `L` (8 cases) | exactly `1/2ⁿ` | exactly `1/2ⁿ` (`L` independent coin) |
| pinned by `h̄` (hash props 1–3; the 6 green cases, hash direction) | `dˢ/2ⁿ`, `max(dʳ,dˢ)/2ⁿ` | unchanged (`h̄` exactly uniform given everything; AXU preconditions from the pointlessness filter when the relevant value is query-side) |
| pinned by a fresh response block (6 grey cases **and the grey directions of the 6 green cases**) | exactly `1/2ⁿ` | `≤ 1/(2ⁿ − k) ≤ α/2ⁿ` |

Three repairs to the paper's arguments were needed (found by the verifiers; all
bound-preserving):

1. **Global bad-set counting replaces sequential block conditioning.** The paper's "given
   `Cˢ[0;jn]`, exactly one value of `Cˢ[jn;n]`" is *unsound verbatim* under
   without-replacement sampling: an adversary can burn `k = 2^a − 1` same-class decryption
   queries exhausting all-but-one completion of a prefix, spiking the conditional block
   probability to `2^{a−n}` (up to 1/2). Fix: count over **full `ℓ`-bit responses** — the
   collision event is a set of exactly `2^{ℓ−n}` responses (one per completion of the pinned
   block; block ↦ (block, rest) is injective even when the pinned block depends on the rest),
   inside a support of size `≥ 2^ℓ − k`, giving
   `Pr ≤ 2^{ℓ−n}/(2^ℓ − k) ≤ 1/(2ⁿ − k)` unconditionally, via
   `2^ℓ − k ≥ 2^{ℓ−n}(2ⁿ − k)` ⟺ `k(2^{ℓ−n} − 1) ≥ 0`.
2. **Straddling blocks.** When the pinned `n`-bit window spans the response/leftover
   boundary (`|Pˢ|` not a multiple of `n`): split into `b` response bits and `n−b`
   independent-uniform leftover bits; `Pr ≤ 2^{ℓ−b}/(2^ℓ−k) · 2^{−(n−b)} = 2^{ℓ−n}/(2^ℓ−k)`
   — same bound, but the formula must be stated (the paper glosses this even in the `±rnd`
   world).
3. **The inflation applies to the whole budget, per pair, before the paper's
   rearrangement.** Two subtleties: (a) each green case's *opposite-direction* sub-case
   (bounded `1/2ⁿ` in the paper via response pinning; contributing 0 to the paper's
   correction `c`) also inflates to `α/2ⁿ` — and since `dˢ` can be 1, `1/(2ⁿ−q)` can exceed
   `dˢ/2ⁿ`, so one cannot inflate only a "subtotal"; (b) the paper's `c`-rearrangement
   contains negative summands (`c_b = −1`, `c_w ≤ 0`), so `α` must multiply the sum of
   nonnegative *per-pair bounds* (`Σ Pr_T̃ ≤ α · Σ bound_paper`), never the already-
   rearranged closed form term-by-term. With that discipline the paper's §3.4.3 algebra
   goes through verbatim and yields:

```
ν(T̃aug, ¬C_q) ≤ (3σ² + 2qσ + 7σ + 2)/2^{n+1} · 2ⁿ/(2ⁿ − q + 1)          (q < 2ⁿ)
```

Optional tightening recorded but not taken (keeps the statement clean): the `h̄ ≟ Y_jˢ` case
can be pinned by `h̄` instead of the response, staying exactly `1/2ⁿ`, so only 5 of the 6
grey response-pinned cases strictly need `α`.

**Where the "expected quadratic loss" went** (the going-in conjecture, confirmed): nonce/
XCTR-collision events are exactly the `Y_iʳ ≟ Y_jˢ`, `UUˢ ≟ Y_jˢ`, `S_iʳ ≟ S_jˢ`-type rows.
Their quadratic mass was already inside the paper's `2·C(σ_m,2)/2ⁿ`-shaped budget (the `3σ²`
term); the without-replacement ideal multiplies those rows by `α` instead of adding anything.
The POLYVAL rows (hash properties) are *exactly unchanged*. No new additive `q²` arises at
any point in the audit.

## 8. Honest positioning and sanity anchors

- **Net comparison with the paper.** Removed: additive `q²/2^{n+1}`. Added: multiplicative
  `α − 1 = (q−1)/(2ⁿ−q+1)`, absolute cost `≈ 3σ²q/2^{2n+1}`. Strictly better iff
  `3σ²(q−1)/2ⁿ ≲ q²`, i.e. `3σ² ≲ q·2ⁿ` — essentially the whole non-vacuous regime; it can
  lose only for few very long queries (`σ/q` of order `√(2ⁿ/q)` blocks). For `q ≤ 2^{n−1}`,
  `α ≤ 2` gives the crude corollary `ν ≤ (3σ² + 2qσ + 7σ + 2)/2ⁿ`. The contribution is
  therefore best framed as *structural* (direct-to-`T̃`, single CE step, no hybrid; and the
  right shape for the Lean build) plus a constant-regime tightening — not an asymptotic one.
  Order-tightness context: Nandi (ePrint 2008/090) gives matching `Θ(σ²/2ⁿ)` attacks for the
  hash-counter-hash class, so the quadratic order is optimal; no attack pins the constant.
- **Degenerate single-block case** (`ℓ = n`: `N, V` empty, `m = 1`, no XCTR calls, no
  leftover; `C = UU ⊕ H_h̄(T, ε)`, `MM = M ⊕ H_h̄(T, ε)` — input and output masks *equal*
  since `|M| = 0` takes the `n | |M|` branch of `H`): HCTR2 collapses to a single-key
  XEX/LRW2-type tweakable block cipher with hash key `h̄ = π(bin 0)` (and `L = π(bin 1)`
  dead in the output but still in `R` via the reveal — the same-key extra collision rows are
  exactly Minematsu's single-key terms). Our bound at `σ = 2q` (n-bit tweaks) evaluates to
  `≈ 8q²/2ⁿ`; with empty tweaks (`σ = q`) to `≈ 2.5q²/2ⁿ`. Reference points: Rogaway's XEX
  `9.5q²/2ⁿ`, Minematsu SAC'06 single-key `4.5q²/2ⁿ` (per the XTS comment). So: **consistent
  in order, constant-factor looser** — expected, since `σ` counts tweak blocks and the
  generic budget is not specialized. No contradiction with known attacks (`≈ q²/2ⁿ`
  MM-collision attack exists).
- **Proof-skeleton match with Minematsu SAC'06** (reconstructed from his slide deck +
  FSE'09 toolkit + the XTS comment): his ideal object is the "perfect tweakable
  permutation" = tweak-indexed independent URPs (never a random function); his Theorem 1
  (LRW, independent hash key, `εq²` — the 3ε→ε improvement over LRW02) is a *direct* CE
  `LRW|A ≡ PTP|B` + Lemma 1(iv) + Theorem 1(i) with the bad event evaluated ideal-side via
  Lemma 6(ii) — structurally identical to ours. His Theorem 4 (single-key XEX) does use one
  hybrid `TW[P,R]` — but only for *mask derivation* (`V = R(N)`), never replacing the
  enciphering permutation, at cost `2^{−(n+1)}q²`. Our proof needs no hybrid at all: the
  posterior lemma (§5.2) handles the mask-derivation reuse (`h̄, L` from the same `π`)
  inside the CE. CCA handling matches his `⟨G⟩`/cpa′ equivalent-representation convention.
- **Luby–Rackoff precedent** (Maurer02 Thm 7 remark): the `k²/|R|²` term of Naor–Reingold
  is removed by the same one-step CE; `q²/2^{n+1}` is the same artifact one level up.

## 9. Relation to the Lean formalization

Inventory (verified 2026-07-05): the repo already contains a full CR18-style CE stack —
`CondEquiv.lean` (Def 4.19 `Ŝ |≡ T`, division-free), `GameOf.lean` (`MonotoneCond`,
`theorem_4_17`: CondEquiv ⟹ `Δ(S,T) ≤ Γᵇ`, with filtered variants), `Theorem417.lean`
(`gameEnhance` = the adjoined-MBO construction ≈ our Lemma 1(iv) surrogate),
`BlindConverter.lean` (`blindMaxWinProb Γᵇ` playing ν), and a worked template
`SwitchingLemma.lean` (`urf_urp_switching` = Lemma 8(ii) mechanized end-to-end). MBO-based
games replace MES; no ν/μ identifiers exist. The HCTR2 endpoints
(`hctr2_securityL` at HCTR2.lean:4918 etc.) live in the H-technique world
(`filteredAdaptiveTranscriptAdvantage` over ProbPDS).

Migration shape for the CE-tightened theorem:

1. **Ideal-side reuse is near-total**: the 22-case reveal/collision library
   (`revealCollapse_le`, the response-pin engine `hctr_respPin_le`, the dispatch/summation)
   computes precisely the per-case conditional bounds §7 needs; the only mathematical change
   is the sampling model of the six-plus-grey response-pinned leaves
   (`lpUrf` → `lpTweakableStrongURP`-side masses: `1/N` → `1/(N−k)`-shaped, the
   `uniform_pi_selfloc_le` engine needs a without-replacement variant) and threading `α`.
2. **Spine**: instantiate `theorem_4_17`/`gameEnhance` with the §4 MES-as-MBO over the
   augmented pair — i.e. the HCTR2 analogue of `urf_urp_switching`, with §5.2's joint
   factorization as the new core lemma (this is where the real formalization work is:
   falling-factorial transcript counting for `hctr2RealL`, product-form for the ideal).
3. **Known gap to budget**: the CondEquiv/Γᵇ world (Δ = `maxAdvantage` over DDD
   distinguishers) and the HCTR2 endpoints' `filteredAdaptiveTranscriptAdvantage` world are
   bridged only partially (`SwitchingBridge.lean`, `AdaptiveLawBridge.lean` exist; no
   verified direct bridge lemma) — this bridge is the first thing to build.
4. **Then delete** the `tweakableStrongURP_rndL` leg and the triangle from the headline.

## 10. Verification log (2026-07-05 workflow, 24 agents) and residual obligations

Round 1 verdicts: V1 domination 3/3, V2 cond-equiv 3/3, V3 support 2/2, V4 framework 3/3,
V5 ideal bad probability 3/3, V6 novelty 1/1, V7 degenerate+WLOG 2/2 — all
`holds_with_corrections`, zero refutations. All corrections are folded into §§3–8 above.

**Round 2 (2026-07-05 later, run wf_ed3c450c-d0f): §5.2 written out in full (5.2.0–5.2.6)
and CONFIRMED.** Four adversarial verifiers, one per failure surface (A: inversion algebra
incl. XCTR block-count accounting; B: real-world event equality, φ-indexing, telescoping;
C: ideal-world filter/WOR subtleties incl. cross-direction exclusions; D: Def-6/conditioning
bookkeeping, H totality, causality, reveal step). All four: **mathematics correct on every
checked point**; corrections were purely textual (a `[jn;n]` → `[(j−1)n;n]` off-by-one in
§4's display, φ as indexed family off-Good, converse scoping in 5.2.1, degenerate-split
wording in 5.2.2, exclusion-count distinctness in 5.2.3, "iff"→"if"+guard and the reveal
one-liner in 5.2.6, H's Dirac extension, joint-causality and totality clauses in 5.2.0) —
all applied. **§5.2 is done.**

What remains before this is publishable:

- Write out Lemma 1(iv)'s thinning proof (§6.1) — no published proof exists to cite.
- The per-case §7 write-up at paper rigor (especially the global-counting replacements and
  the per-pair `α` bookkeeping around the negative corrections).
- Re-sweep ePrint immediately before any priority claim (last swept 2026-07; active area:
  2026/085 multi-user HCTR2, 2026/254 key-committing, 2026/383 HCTR++ (errata pending)).
- Optional strengthening: confine `α` to the response-pinned rows for a slightly tighter
  statement (per-row bookkeeping cost vs. cleanliness — currently not taken).

Operational note: during the web sweep, scraped ePrint-adjacent pages twice contained
injected fake "SYSTEM INSTRUCTION" text (prompt-injection attempts); the research agents
flagged and ignored them. Treat scraped pages as untrusted input in future sweeps.

## 11. Follow-up line: the coupling route — RESEARCHED (2026-07-05), see HCTR2_COUPLING.md

The coupling deep-research (run wf_ed3c450c-d0f) is complete; full writeup in
`papers/notes/HCTR2_COUPLING.md`. Outcome: the tape-driven per-environment coupling design
(adversarially verified) yields `(3σ² + 2qσ + 7σ + 2)/2^{n+1}` — **no α, no +q², and none
of this note's augmentation/reveal/filter apparatus** (hope (c) realized on that path;
closed negative for the static/eager variant, which reproduces exactly this note's bound).
What this note contributes to that route: §5.1 and §5.2.1 are reused verbatim (Lemma A /
the ideal-correction cases of Lemma B); §5.2.2–§6 are superseded on the primary path but
remain the *fallback's* entire proof obligation — so §5.2's confirmation (round 2, §10) is
load-bearing either way. Static full-domain coupling (LM20 Thm 2.32 form) is provably
unattainable for hash-masked schemes; the per-environment transcript chain is the licensed
form. Open before the coupling bound is "done": the Lemma B ~22-mini-case audit and an
independent re-derivation of the `(h*,l*)` posterior-constancy paragraph.

## References

- Crowley, Huckleberry, Biggers. *Length-preserving encryption with HCTR2.* ePrint 2021/1441.
- Maurer. *Indistinguishability of Random Systems.* EUROCRYPT 2002. (Defs 5–7, Lemma 1,
  Lemma 5, Lemma 7, Thm 1, Lemma 8(ii); Thm 2 and Lemma 10 deliberately unused.)
- Maurer. *Conditional equivalence of random systems and indistinguishability proofs.*
  ISIT 2013. (Joint CE Def 13; Lemmas 1–2, Thm 3.)
- Jetchev, Özen, Stam. *Understanding Adaptivity: Random Systems Revisited.* ASIACRYPT 2012.
  (Prop 10 counterexample to stepwise ν=μ; Lemma 7; Thm 12; the audit.)
- Maurer, Pietrzak, Renner. *Indistinguishability Amplification.* CRYPTO 2007. (Lemma 4.)
- Demay, Gazí, Maurer, Tackmann. *Optimality of Non-Adaptive Strategies: The Case of
  Parallel Games.* ISIT 2014 / ePrint 2014/299.
- Minematsu. *Improved Security Analysis of XEX and LRW Modes.* SAC 2006. (Thm 1, Thm 4;
  reconstructed via his slide deck, FSE 2009 App. A toolkit, and:)
- Liskov, Minematsu. *Comments on XTS-AES.* NIST comment, 2008.
- Jha, Nandi. *A Survey on Applications of H-Technique.* ePrint 2018/1130 / Entropy 24(4),
  2022. (Lemma 9: direct-URP proof of simplified HCTR\*.)
- Nandi. *Improving upon HCTR and matching attacks for Hash-Counter-Hash approach.*
  ePrint 2008/090. (Order-tightness of the quadratic bound.)
- Bhaumik, List, Nandi. *ZCZ.* ASIACRYPT 2018. (Without-replacement ideal precedent.)
- Halevi, Rogaway. *A Tweakable Enciphering Mode (CMC).* CRYPTO 2003. (App. C Lemma 6 —
  the PRP-RND lemma this proof removes.)
- Crowley, Biggers. *Adiantum.* ToSC 2018(4). (Same rnd-detour architecture.)
- Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification.* ETH Diss.
  29554, 2023; Lanzenberger, Maurer. *Coupling of Random Systems.* TCC 2020.
