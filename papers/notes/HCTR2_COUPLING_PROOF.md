# A coupling proof of HCTR2 security against the tweakable URP — full details

**Status (2026-07-05): CONFIRMED full write-up.** The design was audited at derivation
level (runs wf_ed3c450c, wf_f8189405: Lemma B by three agents, posterior constancy
confirmed); this assembled paper-rigor document was then refereed section-by-section by
five adversarial verifiers (run wf_75f76b69: tape/representatives, marginals,
Bad+Lemma B, posterior+slots, summation+assembly) — **all mathematics confirmed; the
corrections were text-level and are folded in** (Lemma 5.2's statement normalization,
the §0 vacuity arithmetic at n = 1, the `σ+2 ≤ 2ⁿ` hypothesis form, RF-truncation
semantics, the (L)-family case list, the §11 constant-pair bookkeeping, and several
explicitness upgrades).

## 0. Theorem

Let `HCTR2[Perm(n)]` be HCTR2 (ePrint 2021/1441) with the block cipher replaced by a
uniform permutation `π` of `{0,1}ⁿ`, accessed bidirectionally (tagged `enc(T,P)` /
`dec(T,C)` queries), and let `T̃` be the ideal tweakable length-preserving permutation
family (an independent uniform permutation of `{0,1}^ℓ` for each tweak–length class
`(T,ℓ)`), accessed the same way. Fix the interaction horizon in the systems (LM20
convention): at most `q` queries with `Σ_s dˢ ≤ σ`, where per query `s`:
`ℓˢ = |Pˢ| ≥ n`, `mˢ = ⌈ℓˢ/n⌉`, `dˢ = mˢ + ⌈|Tˢ|/n⌉`. Assume `σ + 2 ≤ 2ⁿ`; this
dominates the per-run call count `σ_m := 2 + Σ_s mˢ` on every horizon path (`mˢ ≤ dˢ`,
`Σ dˢ ≤ σ`), so `σ_m ≤ 2ⁿ` pathwise. (Otherwise the bound below is ≥ 1 and there is
nothing to prove: a path with `σ_m > 2ⁿ` has `σ ≥ σ_m − 2 > 2ⁿ − 2`, i.e. `σ ≥ 2ⁿ − 1`,
whence `(3σ² + 7σ + 2)/2^{n+1} ≥ (3(2ⁿ−1)² + 7(2ⁿ−1) + 2)/2^{n+1} ≥ 1` for every
`n ≥ 1`.) The condition `mˢ − 1 < 2ⁿ` (distinct `bin(j)` counters) is implied:
`mˢ ≤ σ_m − 2 ≤ 2ⁿ − 2`.

**Theorem.** For all adaptive (computationally unbounded) distinguishers within the
horizon:

```
Adv( HCTR2[Perm(n)], T̃ )  ≤  (3σ² + 2qσ + 7σ + 2) / 2^{n+1}.
```

**Corollary (computational).** With the standard substitution step (`σ+2` block-cipher
calls simulate the game):

```
Adv^{±p̃rp}_{HCTR2[E]}(q, σ, t)  ≤  Adv^{±prp}_E(σ+2, t+σt′) + (3σ² + 2qσ + 7σ + 2)/2^{n+1}.
```

No additive `q²/2^{n+1}` (the paper's PRP-RND term) and no multiplicative
`2ⁿ/(2ⁿ−q+1)` (the CE routes' WOR inflation) appear.

## 1. Preliminaries

### 1.1 HCTR2 equations (paper Fig. 2/3, p. 3–4)

`h̄ = π(bin 0)`, `L = π(bin 1)`. Encryption of `(T, P)`, `P = M‖N`, `|M| = n`:

```
MM = M ⊕ H_h̄(T, N);   UU = π(MM);   S = MM ⊕ UU ⊕ L;
Y_j = π(S ⊕ bin(j))  (j = 1..m−1);   stream = Y₁‖…‖Y_{m−1}   (n(m−1) bits);
V = N ⊕ stream[0; ℓ−n];   U = UU ⊕ H_h̄(T, V);   C = U‖V.
```

Decryption of `(T, C)`, `C = U‖V`: `UU = U ⊕ H_h̄(T,V)`, `MM = π^{-1}(UU)`,
`S = MM ⊕ UU ⊕ L`, XCTR **forward** as above, `N = V ⊕ stream[0; ℓ−n]`,
`M = MM ⊕ H_h̄(T,N)`, `P = M‖N`. The *leftover* of query `s` is
`stream[ℓ−n; nm−ℓ]` — the unused tail of the last block `Y_{m−1}`; it is internal (never
output; there is **no augmentation** in this proof). `H` is the POLYVAL hash with the
paper's Properties 1–3: for the formal polynomial `H(T,M)` of degree `≤ d(T,M)`,
`Pr_h̄[H_h̄(T,M) = g] ≤ d/2ⁿ` (P1), `Pr_h̄[H_h̄(T₁,M₁) ⊕ H_h̄(T₂,M₂) = g] ≤ max(d₁,d₂)/2ⁿ`
for `(T₁,M₁) ≠ (T₂,M₂)` (P2), `Pr_h̄[H_h̄(T,M) ⊕ h̄ = g] ≤ d/2ⁿ` (P3).

### 1.2 Framework (LM20 / thesis Ch. 2)

A DDS is a partial function `s : X⁺ ⇀ Y` with prefix-closed domain (stateful by
construction); a PDS is a finite-support distribution over DDS with common domain; a
random system is a behavioral-equivalence class `[S]`, where `S ≡ S′` iff
`tr(S,e) = tr(S′,e)` for every compatible deterministic environment `e` — and by
**Lemma 2.18** it suffices to check *non-adaptive* `e` (fixed input sequences). We use
only the easy direction of the coupling theorem: for any representatives and any joint
distribution, `Adv([S],[T]) = Δ ≤ δ(S,T) ≤ Pr(S ≠ T)`; and, in the per-environment form
used here (data processing under `tr(·,e)` + the classical coupling lemma): if
`S = f(μ)` and `T = g(μ)` are pushforwards of one probability space `μ`, then for every
`e`, `δ(tr(S,e), tr(T,e)) ≤ Pr_{ω∼μ}[tr(f(ω),e) ≠ tr(g(ω),e)]`. Deterministic
environments suffice for `Adv` in the IT setting; randomized distinguishers are convex
combinations.

*Remark (why per-environment).* A static full-domain coupling (LM20 Thm 2.32 form with
natural representatives) is provably unattainable for hash-masked schemes: derived
π-points `MM = M ⊕ H_h̄(T,N)` are query-dependent, so "some input sequence in the domain
produces a raw collision" has probability ≈ 1. The per-environment chain above is the
licensed and sufficient form; adaptivity is absorbed by `sup_e` and per-prefix
conditioning (§9–§11), never by a non-adaptive collapse.

## 2. The tape

All coordinates independent; `m_max ≤ σ` fixed by the horizon, so `Ω` is a finite
product:

```
Ω = (h*, l*) × W × RG × RF
h*, l*        iid uniform {0,1}ⁿ
W = (W_{s,j}) s ∈ [q], 0 ≤ j ≤ m_max−1, iid uniform {0,1}ⁿ, hard-wired to query POSITION s
RG = (RG₀, RG_{s,j})  independent uniform rankings (linear orders) of {0,1}ⁿ
RF = (RF_s)           independent uniform rankings of {0,1}^{ℓ_max}, position-indexed per step
```

("Uniform ranking" makes "uniform on the complement of a set A" constructive: take the
first element of the ranking outside `A`; this is exactly uniform on the complement.
`ℓ_max := n·m_max` is the maximal message width on the horizon; "`RF_s` truncated to
width `ℓ`" means the order `RF_s` induces on the embedded subset
`{x‖0^{ℓ_max−ℓ} : x ∈ {0,1}^ℓ}` — by exchangeability again a uniform ranking of
`{0,1}^ℓ`, which is what Lemma 6.2's rejection-once step consumes. Position-indexing of
`RF` is load-bearing for §9 — a single sequential supply would make "unread RF"
non-prefix-measurable.)

Set `h̃ := h*`, and `l̃ := l*` if `h* ≠ l*`, else `l̃ :=` first element of `RG₀` distinct
from `h*` (uniform on `{0,1}ⁿ∖{h*}`). Thus `h̃ ≠ l̃` always. The event `{h* = l*}` has
probability `2^{−n}` and is charged to the budget (§11); it is the paper's `h̄ ≟ L` pair.

**Cell semantics** (position-indexed, so both representatives consume the same cells on
the same visible prefix — up to the first failure, §8): at a fresh query `s`, `W_{s,0}`
is the fresh π-*output* `UUˢ`
(enc) or the fresh π-*preimage* `MMˢ` (dec); `W_{s,j}` (`1 ≤ j ≤ mˢ−1`) is the XCTR
output `Y_jˢ`. Non-fresh (replayed) queries consume no cells and no rankings.

## 3. The two representatives

Both are deterministic functions of `ω` — stateful DDS over the tagged alphabet, defined
on the horizon's domain.

### 3.1 Real: `G̃(ω)` — global lazy WOR-π

State: a partial injection `π̂`, initialized `π̂ = {bin0 ↦ h̃, bin1 ↦ l̃}` (injective by
construction of `l̃`). π-evaluations:

- *Forward at `x`*: if `x ∈ dom(π̂)`, return `π̂(x)` (no cell consumed). Else, at position
  `(s,j)`: candidate `c := W_{s,j}`; if `c ∉ ran(π̂)`, set `π̂(x) := c` (*no correction*);
  else set `π̂(x) :=` first element of `RG_{s,j}` outside `ran(π̂)` (*RG-correction
  fires*).
- *Inverse at `y`*: if `y ∈ ran(π̂)`, return `π̂^{-1}(y)` (unique by injectivity). Else at
  `(s,0)`: candidate `p := W_{s,0}`; if `p ∉ dom(π̂)`, set `π̂(p) := y`; else take the
  `RG_{s,0}`-first element outside `dom(π̂)`.

*Rejection-once is exact WOR*: for any fixed target `v ∉ ran(π̂)`, with `u = |π̂|`:
`Pr[c = v] + Pr[c ∈ ran(π̂)]·Pr[RG picks v] = 1/2ⁿ + (u/2ⁿ)·1/(2ⁿ−u) = 1/(2ⁿ−u)`.
(Each position is evaluated at most once, so "once" suffices; `u ≤ σ_m − 1 < 2ⁿ` keeps
complements nonempty.)

Responses: run the §1.1 equations verbatim against this lazy π, cells assigned in
execution order: enc — `MM` (position `(s,0)` if the forward call is fresh), then
`S ⊕ bin(j)` at `(s,j)`; dec — inverse call at `(s,0)`, then XCTR forward at `(s,j)`.

### 3.2 Ideal: `F̃(ω)` — per-class lazy WOR, raw-candidate driven

State: per class `(T,ℓ)` a record list `σ̂_{T,ℓ}` of answered pairs `(P, C)`.

- `enc(T,P)`: if `P` is among the recorded plaintexts of class `(T, ℓ)`, **replay** the
  recorded `C` (covers exact repeats *and* mirrors of prior dec queries). Else *fresh*:
  compute the **raw candidate** by the same formulas on raw cells —
  `UU := W_{s,0}`, `Y_j := W_{s,j}`, `stream := Y₁‖…‖Y_{m−1}`,
  `V := N ⊕ stream[0;ℓ−n]`, `U := UU ⊕ H_{h̃}(T,V)`, `C := U‖V`. If `C` is not among the
  recorded ciphertexts of the class, answer `C` (*no correction*); else answer the
  `RF_s`-first element of `{0,1}^ℓ` outside the recorded ciphertexts (*RF-correction
  fires*). Record `(P, answer)`.
- `dec(T,C)`: replay if `C` recorded; else raw candidate `MM := W_{s,0}`,
  `Y_j := W_{s,j}`, `stream := Y₁‖…‖Y_{m−1}` as in enc, `N := V ⊕ stream[0;ℓ−n]`,
  `M := MM ⊕ H_{h̃}(T,N)`, `P := M‖N`, rejection-once against recorded plaintexts via
  `RF_s`. Record `(answer, C)` — i.e. the pair `(P, C)` in the same orientation as enc
  (the enc replay key reads the first component, the dec replay key the second; both
  provenances of each side are thereby covered).

Note: `F̃`'s responses use `h̃` only (never `l̃`, never `RG`); the leftover bits (the
last `nm−ℓ` bits of the stream, and unused columns `W_{s,j}`, `j ≥ mˢ`) are never read.
Uniqueness of the replayed partner rests on the pairwise-distinctness invariant
established in Lemma 6.2's induction.

### 3.3 The freshness predicate

Query `s` is **essentially fresh** iff its class-record key is absent: for `enc(T,P)`,
`P` is not a recorded plaintext of `(T,ℓ)`; for `dec(T,C)`, `C` is not a recorded
ciphertext. This is a deterministic predicate of the *visible prefix*
`(x^s, y^{s−1})` (records = prior same-class queries and answers, both directions), so
it is computed identically by both sides whenever their visible prefixes agree.

## 4. Replay transparency of `G̃`

**Lemma 4.1.** Suppose through step `s` the invariant of §8 holds (in particular
`π̂ = seed ∪ {MM_t ↦ UU_t, S_{t,j} ↦ Y_{t,j} : t ≤ s fresh}` with recorded values, and
`σ̂` matches). If query `s+1` is non-fresh, then `G̃` returns the recorded partner,
consumes no cells or rankings, and adds nothing to `π̂`.

*Proof.* Mirror `dec(T, C_t)` after fresh enc `t` with answer `C_t = U_t‖V_t`: `G̃`
computes `UU = U_t ⊕ H_{h̃}(T, V_t) = UU_t ∈ ran(π̂)`; injectivity gives the unique
preimage `MM_t`; `S = MM_t ⊕ UU_t ⊕ l̃ = S_t`, so every `S ⊕ bin(j) = S_{t,j} ∈ dom(π̂)`
with values `Y_{t,j}`; the stream is `t`'s stream, `N = V_t ⊕ stream[0;ℓ−n] = N_t`,
`M = MM_t ⊕ H(T,N_t) = M_t`; answer `P_t`. Enc-after-dec mirror `enc(T, P_t)` after
fresh dec `t`: dec `t` computed `M_t = MM_t ⊕ H_{h̃}(T,N_t)`, so the later enc
recomputes `MM = M_t ⊕ H_{h̃}(T,N_t) = MM_t ∈ dom(π̂)` (a forward D-side hit on an
entry created by an inverse evaluation — the direction that deserves the explicit
line); the hit returns `UU_t`, `S = S_t`, every XCTR lookup hits, `V = N_t ⊕
stream_t[0;ℓ−n] = V_t`, `U = UU_t ⊕ H_{h̃}(T,V_t) = U_t`; answer `C_t`. Exact repeats
are the originator's own chain of hits. All lookups hit; nothing is consumed or
added. ∎

## 5. Lemma A1: `G̃ ∈ [HCTR2[Perm(n)]]`

**Lemma 5.1 (seed law).** `(h̃, l̃)` is uniform on ordered distinct pairs of `{0,1}ⁿ`.

*Proof.* For `h ≠ l`: `Pr[(h̃,l̃) = (h,l)] = 2^{−n}(2^{−n} + 2^{−n}/(2ⁿ−1)) =
1/(2ⁿ(2ⁿ−1))`. ∎ (This matches `(π(bin0), π(bin1))` for uniform `π`.)

**Lemma 5.2 (lazy WOR = uniform π).** For any sequence of forward/inverse evaluation
requests (adaptively chosen): **each fresh forward value is uniform on the
range-complement of `π̂`, and each fresh inverse preimage uniform on the
domain-complement — exactly the conditionals of a uniform permutation given
`π ⊇ π̂`.** Consequently, for every `h ≠ l` and every injective partial function
`φ ⊇ {bin0 ↦ h, bin1 ↦ l}` with `|φ| = u` that is *realizable* as the end-state of the
request sequence (its non-seed pairs are exactly those the requests would create given
the answers recorded in `φ`):

```
Pr[π̂ = φ] = (2ⁿ−u)!/(2ⁿ)! = Pr_{uniform π}[π ⊇ φ]
```

(equivalently, conditionally on the seed:
`Pr[π̂ = φ | (h̃,l̃) = (h,l)] = (2ⁿ−u)!/(2ⁿ−2)!`).

*Proof.* The kernel form is an induction over evaluations; the step is the
rejection-once computation of §3.1 (forward) and its mirror image (inverse:
`Pr[p = w] + Pr[p ∈ dom]·1/(2ⁿ−u) = 1/(2ⁿ−u)` for any fresh `w`), with the candidate
cell and ranking independent of the past (disjoint tape coordinates). Uniform-π
conditionals are the same by completion counting: given `u` I/O constraints, `π(x)` for
fresh `x` is uniform on the `2ⁿ−u` unused range points; `π^{-1}(y)` for fresh `y`
uniform on the `2ⁿ−u` unused domain points (the two counts agree because `π` is a
bijection). The unconditional identity follows by multiplying the WOR product
`∏_{v=2}^{u−1} (2ⁿ−v)^{-1} = (2ⁿ−u)!/(2ⁿ−2)!` by the seed law `1/(2ⁿ(2ⁿ−1))` of
Lemma 5.1, giving `(2ⁿ−u)!/(2ⁿ)!` — the uniform-π value. ∎

**Corollary 5.3.** `tr(G̃, e) = tr(HCTR2[Perm(n)], e)` for every `e` (by Lemma 2.18 it
suffices for fixed input sequences, but the argument is uniform in `e`): the run of
HCTR2 under uniform `π` touches `π` exactly at the derived points (the
inference/execution inversion, `HCTR2_CE_PROOF.md` §5.2.1, both directions), and Lemma
5.2 says the lazy evaluations have exactly the corresponding conditional laws.
Formally, by the gluing induction: `G̃` and `HCTR2[π]` execute the same deterministic
equations, so — by induction over π-evaluations — given identical evaluation-answer
histories both runs issue the identical next forward/inverse request (in particular the
lazy run touches exactly the derived points of §5.2.1's converse); the seed laws agree
(5.1) and each subsequent answer has the same conditional law given the history (5.2);
hence the joint law of the full π-I/O history — and therefore the transcript, a
deterministic function of `(e, answers)` — coincides. Hence
`G̃ ∈ [HCTR2[Perm(n)]]`. ∎

## 6. Lemma A2: `F̃ ∈ [T̃]`

**Lemma 6.1 (candidate uniformity).** Fix `(h,l)`, a class state, and a fresh
`enc(T,P)` at position `s`. The map
`(W_{s,0}, first ℓ−n bits of W_{s,1..m−1}) ↦ C = U‖V` is a bijection onto `{0,1}^ℓ`:
`V = N ⊕ stream-prefix` is a bijection in the prefix bits; given `V`,
`U = W_{s,0} ⊕ H_h(T,V)` is a bijection in `W_{s,0}`. Hence the candidate is uniform on
`{0,1}^ℓ`, independent of `(h,l)`-values, of other queries' cells, and of the unread
bits. Dually for dec (`P = M‖N`, `M = W_{s,0} ⊕ H_h(T,N)`). ∎

**Lemma 6.2 (response law).** At a fresh query of a class with `k` records, for every
fixed `(h,l)`: the response is uniform on the `2^ℓ − k` non-recorded values of the
appropriate side. *Proof.* The `k` recorded pairs have pairwise-distinct plaintexts and
pairwise-distinct ciphertexts (immediate induction: each fresh answer avoids the
recorded values of its side by rejection-once, and each fresh query key is unrecorded
on its side by essential freshness (§3.3); replays add nothing), so exactly `k` values
are excluded;
candidate uniform (6.1) + rejection-once: `1/2^ℓ + (k/2^ℓ)·1/(2^ℓ−k) = 1/(2^ℓ−k)` for
every free value. `k ≤ q − 1 ≤ σ_m − 3 < 2ⁿ ≤ 2^ℓ` keeps the complement nonempty. ∎

**Corollary 6.3.** `F̃ ∈ [T̃]`. *Proof.* `T̃`'s behavior: fresh enc in a class with `k`
constraints answers uniformly on the `2^ℓ−k` unused range points; fresh dec uniformly on
the `2^ℓ−k` unused domain points; repeats and mirrors are answered consistently
(permutation family). `F̃` matches: Lemma 6.2 for fresh (both directions — the dec case
is the uniform-preimage law), replay for non-fresh; the law is the same for every
`(h,l)` (6.2), hence also after marginalizing the internal coins. Moreover the step-`s`
conditional law given the FULL visible past (all classes) and `h*` is exactly this
uniform-on-free law, because `(W_{s,·}, RF_s)` are fresh position-indexed coordinates
independent of the σ-algebra generated by `(h*, W_{<s}, RF_{<s}) ⊇ σ(visible past)`;
the same holds for `T̃` by independence of the class permutations. Hence the per-step
kernels — and by the chain rule the fixed-sequence transcripts — coincide, which by
Lemma 2.18 suffices. ∎

## 7. Raw entries and the Bad event

For each step `s` of the `F̃(ω)`-run under `e`, with the *visible prefix*
`(x^s, y^{s−1})` of that run (all queries and responses so far; the essential-freshness
classification and the queries `x_t` used below are those of the `F̃`-run — on `¬Bad`
the `G̃`-run coincides with it by Lemma 8.1, so the choice matters only on Bad, and
§§9–11 condition on the `F̃`-run prefix), define — only for essentially fresh `s` — the
**raw entries** of step `s`, as functions of `(x_s, h*, l̃, W_{s,·})` alone:

```
enc:  MMₛ = Mₛ ⊕ H_{h*}(Tₛ, Nₛ)   (query-determined)      UUₛ = W_{s,0}   (cell)
dec:  UUₛ = Uₛ ⊕ H_{h*}(Tₛ, Vₛ)   (query-determined)      MMₛ = W_{s,0}   (cell)
both: Y_{s,j} = W_{s,j}  (cells, full n bits — leftover tail included)
      S_{s,j} = MMₛ ⊕ UUₛ ⊕ l̃ ⊕ bin(j)      (1 ≤ j ≤ mₛ−1)
```

The step-`s` **D-entries** are `{MMₛ, S_{s,1..mₛ−1}}`, the **R-entries**
`{UUₛ, Y_{s,1..mₛ−1}}`; the constants are `bin(0), bin(1)` (D-side) and `h*, l̃`
(R-side). Non-fresh steps contribute no entries.

**Definition (Bad, slot-wise first-failure).** A *slot* is an unordered same-side pair
of entry positions (constant or (fresh step, entry index)), indexed by its later step.
Let

```
FirstFailₛ := (h* ≠ l*) ∧ (all raw entries of essentially fresh (F̃-run) steps < s,
              together with the constants, are pairwise distinct within D and within R) ∧
              (some D-side or R-side pair involving a step-s raw entry — against a
              constant, an earlier entry, or another step-s entry — collides)

Bad_e(ω)  := {h* = l*}  ∨  ∃ s ≤ q : FirstFailₛ .
```

Two remarks, both load-bearing (from the audit): (i) Bad is **not** "the final
transcript-inferred multisets have a repeat" — an RF-correction resamples the answer and
can erase the repeat from the final inferred multisets (countermodel: `ℓ = n`, two enc
queries in one class, `W_{1,0} = W_{2,0} = w ∉ {h*, l*}`); the slot-wise raw form is the
definition. (ii) `{h*=l*}`
must remain an explicit disjunct: after the `l̃` resample it is never visible as a
multiset repeat. Because Bad at step `s` quantifies over *all* step-`s` raw pairs
simultaneously, no within-query sub-step ordering enters the definition (it is needed
only inside the proof of Lemma B).

On `¬Bad`, `l̃ = l*` and — as the next section shows — the executed values coincide
with the raw values at every step, so "raw" = "inferred from the transcript by the
paper's p. 10 table" throughout.

## 8. Lemma B: divergence ⊆ Bad

**Lemma 8.1.** For every deterministic `e` and every `ω`:
`tr(G̃(ω), e) ≠ tr(F̃(ω), e) ⟹ Bad_e(ω)`.

*Proof.* Contrapositive: assume `¬Bad_e(ω)`; we prove by induction the invariant

```
Iₛ:  (a) the two visible transcripts through step s are identical;
     (b) no RG- and no RF-correction has fired, and no real-side π̂ lookup at a
         supposedly-fresh point has hit (no "unexpected reuse");
     (c) π̂ = {bin0 ↦ h*, bin1 ↦ l*} ∪ {MMₜ ↦ UUₜ, S_{t,j} ↦ Y_{t,j} : t ≤ s fresh},
         all at raw values (and, mid-query, the partial version with MM ↦ UU inserted
         before the XCTR loop);
     (d) σ̂ = the fresh records {(Pₜ, Cₜ) : t ≤ s fresh}, at raw-formula values;
     (e) every response so far was the identical raw formula on both sides.
```

`I₀` holds (`l̃ = l*` since `h* ≠ l*`). Step `s+1`:

**Non-fresh.** The predicate (§3.3) is computed from the shared visible prefix (a), so
both sides classify `s+1` identically. `F̃` replays; `G̃` replays by Lemma 4.1; equal
answers, no state growth, no consumption. `I_{s+1}`. ✓

**Fresh `enc(T, P = M‖N)`.** `G̃` computes `MM = M ⊕ H_{h*}(T,N) = MMₛ₊₁` (raw). Every
way the run can deviate from the raw formulas is a firing whose trigger is a raw
collision, hence in `FirstFailₛ₊₁` (all earlier entries are raw by (c)/(d) and
collision-free by `¬Bad`), contradiction. Exhaustively:

1. *Real D-reuse at `MM`*: `MM ∈ dom(π̂) = {bin0, bin1} ∪ {MMₜ} ∪ {S_{t,j}}` — the four
   raw D-pairs `(bin0, MMₛ₊₁)`, `(bin1, MMₛ₊₁)`, `(MMₜ, MMₛ₊₁)`, `(S_{t,i}, MMₛ₊₁)`
   (paper Fig. 4, column `MMˢ`). Excluded. So the forward call is fresh.
2. *Real R-correction at `W_{s+1,0}`*: `W_{s+1,0} ∈ ran(π̂) = {h*, l*} ∪ {UUₜ} ∪
   {Y_{t,j}}` — the raw R-pairs `(h̄, UUₛ₊₁)`, `(L, UUₛ₊₁)`, `(UUₜ, UUₛ₊₁)`,
   `(Y_{t,i}, UUₛ₊₁)` (Fig. 5, column `UUˢ`). Excluded. So `UU = W_{s+1,0} = UUₛ₊₁`, and
   `π̂` gains `MMₛ₊₁ ↦ UUₛ₊₁` (the mid-query state of (c)).
3. `S = MM ⊕ UU ⊕ l̃ = Sₛ₊₁` (raw; `l̃ = l*`). *Real D-reuse at `S ⊕ bin(j)`*:
   membership in `dom(π̂) ∪ {MMₛ₊₁}` — the raw pairs `(bin_b, S_{s+1,j})`,
   `(MMₜ, S_{s+1,j})`, `(S_{t,i}, S_{s+1,j})`, and the within-query
   `(MMₛ₊₁, S_{s+1,j})`. Excluded. (Within-query `(S_{s+1,i}, S_{s+1,j})` is impossible:
   `S_i ⊕ S_j = bin(i) ⊕ bin(j) ≠ 0` since `mₛ₊₁ − 1 < 2ⁿ` — the paper's red cell; this
   holds identically on both sides and needs no exclusion.)
4. *Real R-correction at `W_{s+1,j}`*: membership in `ran(π̂) ∪ {UUₛ₊₁} ∪
   {W_{s+1,i}, i<j}` — the raw pairs of Fig. 5 column `Y_jˢ` plus the within-query
   `(UUₛ₊₁, Y_{s+1,j})` and `(Y_{s+1,i}, Y_{s+1,j})`. Excluded. So all XCTR outputs are
   the raw cells; `G̃`'s response is the raw formula `C`.
5. *Ideal RF-correction*: fires iff the candidate `C` equals a recorded ciphertext
   `Cₜ` of the class (`t` fresh — replays add no records beyond their fresh
   originator's). Same class ⟹ same parse offsets; `C = Cₜ ⟹ V = Vₜ ∧ U = Uₜ ⟹
   UUₛ₊₁ = U ⊕ H_{h*}(T,V) = Uₜ ⊕ H_{h*}(T,Vₜ) = UUₜ` — the deterministic cancellation
   (`HCTR2_CE_PROOF.md` §5.1), valid for **both provenances** of `Cₜ` (answer of a fresh
   enc `t`, where `UUₜ` is `t`'s raw cell; or query of a fresh dec `t`, where `UUₜ` is
   `t`'s query-determined raw entry). Either way a raw R-pair `(UUₜ, UUₛ₊₁)` — excluded.
   So `F̃` answers the same raw `C`. ✓ `I_{s+1}` holds.

**Fresh `dec(T, C = U‖V)`.** Mirror image: `UU = U ⊕ H_{h*}(T,V) = UUₛ₊₁` raw and
query-determined. (1′) `UU ∈ ran(π̂)` at a *non-mirror* dec — the raw R-pairs
`(h̄, UUₛ₊₁)` [P3 row], `(L, UUₛ₊₁)`, `(UUₜ, UUₛ₊₁)` [P2 row], `(Y_{t,i}, UUₛ₊₁)`
[P1 row] of Fig. 5 — excluded, so the inverse call is fresh; (2′) preimage candidate
`W_{s+1,0} ∈ dom(π̂)` — the raw D-pairs of Fig. 4 column `MMˢ` (dec direction) —
excluded, so `MM = W_{s+1,0} = MMₛ₊₁`; (3′)/(4′) XCTR as in (3)/(4); (5′) ideal
RF-correction iff candidate `P = Pₜ ⟹ MMₛ₊₁ = MMₜ` (dual cancellation, both
provenances) — excluded. ✓

Since under `¬Bad` the invariant propagates to the horizon (early stops by `e` truncate
both runs identically), the transcripts are equal. ∎

*Remark (cascade-freeness).* A "cascading correction" — a correction at `t` altering the
run so that a later reuse fires without a raw collision — cannot occur: a cascade needs
a *first deviation* (a correction **or** an unexpected reuse hit, modes 1/1′ — invariant
clause (b) covers both), and at the first deviation all prior state is raw by (c)/(d),
so its trigger is itself a raw collision, i.e. Bad. This is exactly what the
first-failure form of Bad encodes.

*Remark (same-slot double firing).* An ideal RF-firing and a real R-correction can fire
at the same slot with the same trigger pair (e.g. RF at enc `s` and `W_{s,0} = UUₜ` are
the same `(UUₜ, UUₛ)` event); the slot-wise union of §11 counts each pair once.

## 9. Master independence lemma (posterior constancy)

**Lemma 9.1.** Fix a deterministic `e` and a step `s`. Conditioned on the `F̃`-run
visible prefix `{Y^{s−1} = y^{s−1}}` (queries determined by `e`), the joint law of

```
( h*, l*, RG, W_{s,·}, W_{>s}, the never-read bits of W_{<s}   [leftover tails of
  W_{t,mₜ−1} and unused columns W_{t,j}, j ≥ mₜ, and all cells of replayed steps],
  RF_{≥s} )
```

is the prior product. In the strongest form: **each visible step kernel of `F̃` is an
autonomous function of the visible past — uniform on the `2^{ℓₜ}−kₜ` free values at
fresh steps, deterministic at replays — identical for every value of the listed
coordinates; hence the visible transcript `Y^q` is independent of all of them, for every
`e`.**

*Proof.* Condition on any fixed value of the listed coordinates. The remaining
randomness is (read bits of `W_{<s}`, `RF_{<s}`), mutually independent of the
conditioning by tape independence. Per step `t < s`: a replay is a deterministic
function of the visible past (likelihood factor 1). At a fresh step, for the *fixed*
`h*`: the candidate is uniform on `{0,1}^{ℓₜ}` over the read bits (Lemma 6.1 — a
bijection for each `h*`; the bijection *varies* with `h*`, the resulting law does not);
the rejection event has probability `kₜ/2^{ℓₜ}` (`h*`-independent — the recorded set is
visible-past-measurable); on rejection the answer is `RFₜ`-uniform on the free set, on
non-rejection it is the candidate conditioned to the free set — the same uniform law in
both branches. So the likelihood of the observed `yₜ` is `1[yₜ ∈ freeₜ]/(2^{ℓₜ}−kₜ)`,
a function of the visible past alone, constant in every conditioned coordinate. The
product over `t < s` is therefore a fixed function of `y^{s−1}`; by Bayes the posterior
of the conditioned coordinates is the prior. (`l*` and `RG` are never read by `F̃`'s
responses at all; `RG₀` defines `l̃`, which `F̃` never reads either.) ∎

**Corollary 9.2 (`(h*, l̃)`).** Given the prefix, `(h*, l̃)` is distributed uniformly on
ordered *distinct* pairs (Lemma 5.1's computation, now under the posterior = prior), and
is independent of `(W_{s,·}, W_{>s}, unread bits)`.

**Convention 9.3 (intersect-and-substitute).** In the budget we never pin `l̃` (its
marginal is uniform on `2ⁿ−1` values — pinning it would give `1/(2ⁿ−1)`, an α-flavored
loss). Instead: `Pr[Bad] ≤ Pr[h*=l*] + Σ_slots Pr[slot ∧ h*≠l*]`; charge `2^{−n}` once;
inside each slot event substitute `l̃ = l*` (valid on `{h*≠l*}`) and drop the
intersection. All `l̃`-occurrences below are handled this way.

## 10. Per-slot bounds

Fix a slot with later step `s`; bound its probability **conditioned on `Y^{s−1}`**
(before the step-`s` response), on the first-failure event (so earlier raw = executed =
inferred values; in particular every earlier entry is a function of
(visible prefix, `h*`, `l*`, hidden leftover bits) — the *inference form*). By Lemma
9.1/9.2 the pin variable in each family below is uniform and independent of the rest of
the slot data given the prefix. All bounds are uniform over adaptive prefixes; no
adaptive/non-adaptive collapse is used anywhere.

**(L) `l*`-pinned — exactly `1/2ⁿ`.** The 7 slot cases where `l̃` occurs an odd number
of times in the collision equation, plus the separately charged `h* ≟ l̃` (same value
`2^{−n}`): `L≟UUˢ`, `L≟Y_jˢ`, `bin(0)≟S_jˢ`, `bin(1)≟S_jˢ`, `S_iʳ≟MMˢ` (both directions
— for s enc `MMˢ` is (query, `h*`)-determined, for s dec `MMˢ = W_{s,0}`; either way the
event after substitution is `{l* = MMʳ ⊕ UUʳ ⊕ bin(i) ⊕ MMˢ}` with an `l*`-free right
side), `MMʳ≟S_jˢ`, `MMˢ≟S_jˢ` (s dec: `UUˢ` query-determined, pin `l*` in
`UU ⊕ l* = bin(j)`). After substitution the event is `{l* = v}` with `v` a function of
(prefix, `h*`, cells, leftovers) — all independent of `l*`. `Pr = 2^{−n}` exactly.
(For `h̄ ≟ L` the slot event is vacuous after 9.3 — on `{h*≠l*}` we have
`l̃ = l* ≠ h*` — so it contributes 0 as a slot; its `2^{−n}` is exactly the
once-charged disjunct `Pr[h*=l*]`, cf. §11's accounting.)

**(H) `h*`-pinned via POLYVAL — `≤ dˢ/2ⁿ` resp. `≤ max(dʳ,dˢ)/2ⁿ`.** The 6 green cases
in their hash direction: `bin_b ≟ MMˢ` (s enc; P1), `MMʳ ≟ MMˢ` (later query enc; P2 on
the `(T,N)` hash inputs), `h̄ ≟ UUˢ` (s dec; P3), `UUʳ ≟ UUˢ` (later dec; P2 on
`(T,V)`), `Y_iʳ ≟ UUˢ` (s dec; P1). The event is `{p(h*) = c}` for a formal-polynomial
difference `p` of degree `≤ d` with coefficients functions of (visible data, `l*`,
hidden leftovers) — independent of `h*` given the prefix. Degenerate coefficients are
excluded structurally: equal hash inputs with equal masked parts would make the two
queries share a class record, contradicting essential freshness (this is the paper's
pointless-query argument, delivered here by the record predicate); equal hash inputs
with different masked parts give a nonzero constant equation — probability 0. (Why the
same-class premise holds: equal hash inputs force equal `(T, N)` — resp. `(T, V)` —
hence equal `ℓ = n + |N|` and the same class `(T, ℓ)`; the record exists because
entries are contributed only by essentially fresh steps, and records cover both
directions. So "different classes with the same tweak" is impossible for equal hash
inputs — `N`/`V` determines `ℓ`.) Hence `Pr = E[#roots/2ⁿ] ≤ d/2ⁿ`.

**Lemma 10.1 (hidden-leftover averaging).** In family (H), the earlier entry may be a
`Y`-cell whose inference-form value straddles into hidden leftover bits (e.g. the pair
`(Y_{r,i}, UUˢ)` with `s` dec: the constant is `c = Uₛ ⊕ [(N_r⊕V_r)‖D_r]-block`, and
`D_r` is hidden). By Lemma 9.1 the hidden bits are uniform and jointly independent of
`h*` given the prefix, so
`Pr[p(h*) = c(visible, D_r)] = E_{D_r}[Pr_{h*}[p = c]] ≤ max_c d/2ⁿ = d/2ⁿ`. ∎

**(R) cell-pinned — exactly `1/2ⁿ`.** All remaining cases: the 6 grey response-pinned
cells, the grey directions of the 6 green cells (later query in the non-hash direction:
`MMˢ = W_{s,0}` for dec, `UUˢ = W_{s,0}` for enc), all `Y_jˢ` columns, the
within-query pairs `(MMˢ, S_jˢ)` (enc direction: pin `UUˢ = W_{s,0}` in
`UU ⊕ l* = bin(j)`), `(UUˢ, Y_jˢ)`, `(Y_iˢ, Y_jˢ)`; and the cross-query
`(S_iʳ, S_jˢ)`, `r < s` (the `l*` cancels: pin the later query's cell `W_{s,0}`).
The event is `{W_{s,j} = target}` with the target
measurable in (prefix, `h*`, `l*`, hidden leftovers, cells at positions `≠ (s,j)`) —
never self-referential. Since `W_{s,j}` is a fresh iid cell independent of all of that
given the prefix: `Pr = 2^{−n}` exactly. **This is where the WOR inflation α of the CE
routes vanishes**: the pinned object is a raw tape cell, not a without-replacement
response. Entries are full n-bit cells (leftover bits included in the entry by
definition), so no truncation/straddling correction is ever needed in this family.

**(0) impossible — `0`.** `bin(0) ≟ bin(1)` and `(S_iˢ, S_jˢ)` within-query.

Every bound equals the paper's world-Y value for the same cell (Figs. 4/5: fourteen
exact `1/2ⁿ` cells, six green cells `≤ d/2ⁿ` in the hash direction and `1/2ⁿ` in the
other, two impossible cells), with `h* ≟ l̃` replaced by the once-charged `Pr[h*=l*] =
2^{−n}` — the same value.

## 11. Union bound and summation

By the disjoint decomposition of Bad over its first-failure step, followed by the
per-slot union bound at each step (intersect, never condition — the
no-earlier-collision conjunct of `FirstFailₛ` is used to rewrite earlier raw entries
into inference form, then dropped by monotonicity):

```
Pr[Bad_e] ≤ Pr[h*=l*] + Σ_s E_{Y^{s−1}}[ Σ_{slots at s(Y^{s−1})} Pr[slot ∧ h*≠l* | Y^{s−1}] ]
```

with the conventions that the inner inventory is empty when step `s` is non-fresh, and
"slot" denotes the inference-form event of §10. Each inner bound (§10) is a
`Y^{s−1}`-measurable constant in `{0, 2^{−n}, d/2ⁿ, max(dʳ,dˢ)/2ⁿ}`; the slot inventory
at step `s` (which pairs, which degrees) is prefix-measurable, and on every path the
horizon gives `Σ_s dˢ ≤ σ`, `Σ_s mˢ ≤ σ`, `≤ q` queries. Therefore the pathwise total
(the charged `Pr[h*=l*]` plus the slot-sum) is bounded by the paper's §3.4.3
accounting, verbatim, with `σ_m = 2 + Σ mˢ ≤ σ + 2`:

```
Pr[h*=l*] + Σ_slots bound  ≤  ( 2·C(σ_m, 2) + c ) / 2ⁿ ,     c = c_b + c_f + c_w + c_a
c_b = −1                        (bin0 ≟ bin1 contributes 0, not 1/2ⁿ)
c_f ≤ Σ_s 2(dˢ−1) ≤ 2σ          (bin_b ≟ MMˢ enc / h̄ ≟ UUˢ dec corrections)
c_w ≤ 0                         (within-query: S_i ≟ S_j impossible)
c_a ≤ Σ_{r<s} max(dʳ,dˢ)−1 + (mʳ−1)(dˢ−1) ≤ (q−1)σ + C(σ,2)
```

Bookkeeping of the constant–constant pairs (this is where the `Pr[h*=l*]` charge
lands): the pair inventory is the paper's — per side the slots total
`2M + C(M,2) = C(M+2,2) − 1` pairs, `M = Σ_{fresh} mˢ`, i.e. all pairs except the two
constant–constant ones. The `(h*, l̃)` pair is never a slot (every slot contains a
step-`s` entry); it contributes its baseline `1/2ⁿ` through the separately charged
`Pr[h*=l*]`, and `(bin0, bin1)` contributes the `−1`. Read as a bound on the slot-sum
alone, `c_b` would be `−2` with the `2^{−n}` added on top — the same total; no pair is
double-counted.

and hence, exactly as in the paper (p. 17):

```
Pr[Bad_e] ≤ ( 2·C(σ+2, 2) − 1 + 2σ + (q−1)σ + C(σ,2) ) / 2ⁿ
          = ( 3σ(σ−1)/2 + qσ + 5σ + 1 ) / 2ⁿ
          = ( 3σ² + 2qσ + 7σ + 2 ) / 2^{n+1} ,
```

uniformly in `e`. (The negative summands `c_b, c_w` are rearrangement artifacts of the
per-pair sum; since every per-pair bound here equals its world-Y counterpart, the
identity applies as-is — no α is ever threaded, so the CE routes' "multiply per-pair
before rearranging" discipline is moot.)

## 12. Assembly

For every deterministic environment `e` within the horizon:

```
δ( tr(HCTR2[Perm(n)], e), tr(T̃, e) )
   = δ( tr(G̃, e), tr(F̃, e) )                (Corollaries 5.3, 6.3; class-invariance)
   ≤ Pr_ω[ tr(G̃(ω), e) ≠ tr(F̃(ω), e) ]      (both are pushforwards of the same tape
                                              law; data processing + coupling lemma)
   ≤ Pr_ω[ Bad_e(ω) ]                        (Lemma 8.1)
   ≤ (3σ² + 2qσ + 7σ + 2)/2^{n+1}            (§9–§11).
```

Taking `sup_e` (deterministic environments suffice; randomized distinguishers are convex
combinations) gives the Theorem; the Corollary follows by the standard substitution
argument (the simulator makes `σ_m ≤ σ+2` block-cipher calls). ∎

## 13. Remarks

1. **Degenerate cases.** `ℓ = n`: `N, V` empty, `m = 1`, no XCTR cells, no leftover; the
   candidate bijection is `W_{s,0} ↦ U` alone; all lemmas specialize (`H` on the empty
   message is well-defined via the `n | |M|` branch). `σ_m > 2ⁿ`: bound ≥ 1, vacuous
   (stated in §0). Class exhaustion (`k = 2^ℓ`) cannot occur before a repeat/mirror,
   which replays.
2. **What is *not* here.** No augmentation, no reveal query, no terminality convention,
   no filter converter, no hidden-key posterior lemma, no domination step, no Maurer-02
   MES machinery. `h*, l̃`, leftovers are internal coupling randomness; repeats and
   mirrors are handled by the record predicate *inside* the representatives.
3. **Where each audited correction lives.** Slot-wise first-failure Bad: §7 (with the
   countermodel). `h*=l*` explicit disjunct: §7. Within-query sub-step state: §8
   invariant (c). Both provenances of RF collisions: §8 case 5/5′. Position-indexed RF:
   §2 + §9. Intersect-and-substitute for `l̃`: 9.3. Hidden-leftover averaging: 10.1.
   Same-slot double firing counted once: §8 remark + §11.
4. **Tightness.** Upper bound only; order-optimal for the hash-counter-hash class
   (Nandi, ePrint 2008/090: matching `Θ(σ²/2ⁿ)` attacks); no attack matches the
   constant.
