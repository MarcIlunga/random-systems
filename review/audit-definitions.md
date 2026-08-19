# Definitional audit — `RandomSystems.CR18.SoPTight.sop_randomness_expander_tight`

Slice: **definitions**. Read-only on the proof; every claim below is either read off the
source, machine-checked in a scratch Lean file, or read visually off the paper.

**Bottom line: no load-bearing definitional defect found.** The objects denote what the
theorem's prose says they denote. Every framework definition in the cone was checked against
CR18_LN.pdf visually (Def 4.1/4.17/4.18/4.19/4.20, Thm 4.17, §4.10 preamble) and matches.
The findings below are five MINOR statement-shape / scope observations, none of which makes
the theorem false or vacuous.

---

## 0. Method and evidence

Machine-checked probes (compiled clean against the repo; scratch kept at
`/tmp/audit-defs-evidence/AuditDefs{1..5}.lean`, removed from the project tree):

| probe | what it establishes |
|---|---|
| `AuditDefs1` | `sopIdeal = PFunPDS.URF` by `rfl`; `uniform (Perm G × Perm G) = prod (uniform (Perm G)) (uniform (Perm G))`; each pair carries mass `1/(N!)²`; `functionEvaluator` injective; `sopIdeal` puts mass `N^{-N}` on each function evaluator and nothing elsewhere; `sopReal` unfolds to the stated pushforward |
| `AuditDefs2` | **Δ is not vacuously 0**: an explicit one-query distinguisher gives `1 ≤ Δ(pure(const false), pure(const true))` |
| `AuditDefs3` | both filtered systems are prob. dists; `Δ(⌈q⌉real, ⌈q⌉ideal) = Δ(⌈q⌉ideal, ⌈q⌉real)`; `0 ≤ Δ`; `sopEps N 1 = 0` and hence `Δ(⌈1⌉real, ⌈1⌉ideal) = 0` (replaying the theorem's own chain); `sopEps N 2 = 1/(N−1)²`; every support atom of `⌈q⌉S` is undefined past `q` queries; the `∀ H` class is inhabited (instantiated at `ZMod 5`); the second conjunct past birthday is discharged by `min_le_left` alone |
| `AuditDefs4` | `#print axioms` → `[propext, Classical.choice, Quot.sound]`; dependency-cone probe: the theorem reaches `sopEps`, `maxAdvantage_filterQueries_seededConditionCGame_le`, `blindMaxWinProb`, `DeltaFilteredFiniteQueryNormalization`, and the **proved** `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty` |
| `AuditDefs5` | **the `⌈q⌉` filter really cuts the interaction**: running a 2-query environment against `⌈1⌉ (const-c evaluator)` gives transcript `[(true, some c), (false, none)]` |

Paper pages read visually: `papers/CR18_LN.pdf` pp. iii–viii (ToC), 105–110.

---

## 1. Framework definitions

### `Dist A := A →₀ NNReal` (`Dist.lean:50`)

**Denotes.** A finitely supported function `A → ℝ≥0`. **No normalisation.** `weight X = Σ_a X a`;
`isProbDist X ↔ weight X = 1`.

**Intended.** LM20 Def 1 / CR18 sub-distribution of arbitrary weight.

**Agree.** Yes. I checked every normalisation-sensitive lemma reached by the proof: each takes
`isProbDist` as an explicit hypothesis and the caller supplies it —
`Dist.mass_le_one` (needs `hX`), `Dist.mass_add_compl` (returns `weight`, called with
`Dist.uniform_isProbDist`), `CondEquiv.massDom_eq_one_of_totalOnNonempty` (needs `hT`),
`GamePerf.winProb_le_weight` (needs `hW`), and both suprema (`maxAdvantage`, `blindMaxWinProb`)
range only over `{· | isProbDist}`. `CondEquiv` itself is stated cross-multiplied, so it needs
no normalisation at all. **Nothing silently assumes weight 1.**

### `Dist.uniform A` (`Dist.lean:431`)

**Denotes.** `Finsupp.equivFunOnFinite.invFun (fun _ => 1/|A|)`, i.e. every `a : A` gets mass
`1/|A|` (`uniform_apply`), total weight 1 (`weight_uniform`).

**Intended.** The uniform measure on `A`.

**Agree.** Yes. Specifically for the theorem's seed law I *verified* (not assumed):

```lean
Dist.uniform (Equiv.Perm G × Equiv.Perm G)
    = Dist.prod (Dist.uniform (Equiv.Perm G)) (Dist.uniform (Equiv.Perm G))   -- compiles
Dist.uniform (Equiv.Perm G × Equiv.Perm G) p = 1 / (N! * N!)                  -- compiles
```

So "two **independent** uniform permutations" is literally what the seed distribution is; the
independence is not merely asserted in a docstring.

### `Dist.mass X P` (`Dist.lean:150`)

**Denotes.** `X.sum (fun a w => if P a then w else 0)` = `Σ_{a ∈ supp X, P a} X a`, with the
classical instance for the `Prop`. **Intended.** `X(P)`. **Agree.** Yes.

### `Dist.fTransform f X` (`Dist.lean:523`)

**Denotes.** `Finsupp.mapDomain f X`; `fTransform f X b = X.mass (fun a => f a = b)`
(`fTransform_apply_eq_mass`). **Intended.** CR18 Def 4 pushforward. **Agree.** Yes — fibres are
*summed*, so two seeds inducing the same system correctly share one atom.

### `Dist.prod X Y` (`Dist.lean:1107`)

**Denotes.** `prod X Y (a,b) = X a * Y b` (`prod_apply`), `weight = |X|·|Y|`.
**Intended.** Independent product. **Agree.** Yes.

**Load-bearing?** Only indirectly — `sopReal` is built from `Dist.uniform` on the *product type*,
not from `Dist.prod`. The two coincide (checked above), so nothing turns on it. `Dist.prod` is
reachable in the theorem's cone at depth 10 (via generic framework lemmas), not via the
construction.

### `PFunPDS X Y := Dist (PFunDDS.DDS X Y)` (`PDS.lean:68`)

**Denotes.** A finite-support distribution over *deterministic* systems, where
`DDS X Y = {S : List X →. Y // [] ∉ dom S ∧ dom S closed under nonempty prefixes}`.

**Intended.** CR18 Def 3.14 = a random variable over DDSs, given by its law.

**Agree.** Yes. Note this is the *representative-level* object: it is a distribution over
representatives, not a behaviour class. That is CR18's own convention (the file `Distinguishing.lean`
flags the thesis reconciliation). Not a defect for this theorem.

### `PFunDDS.functionEvaluator f` (`PFunDDS.lean:112`)

**Denotes.** The DDS with `dom = {l | l ≠ []}` and `output l = f (l.getLast)`. Stateless,
total on nonempty histories.

**Intended.** "the system that answers query `x` with `f x`". **Agree.** Yes; and it is
**injective** in `f` when the query type is nonempty (machine-checked), so pushing a function
law through it does not collapse mass.

### `maxAdvantage S T` — the `Δ` of the statement (`Distinguishing.lean:136`)

**Denotes.**
```
advantage D S T   = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)                (signed, ℝ)
Δ(S,T) = maxAdvantage S T = sSup { advantage D S T | D : Dist (DDD X Y), D.isProbDist }
```
where `DDD X Y = {d : List (Option Y) → X ⊕ Bool // StopFinal d}` — a distinguisher reads the
**full output history** and picks its next query from it, so the class is genuinely **adaptive**;
`verdict d s = ∃ n, d (tr(s, ddToDDE d) n ↓ᵧ) = inr true` is read off Maurer's Def-3.7
interaction transcript; `verdictProb = GamePerf.winProb` is `Σ_{d,s} D(d)·S(s)·⟦verdict d s⟧`
(independent product of distinguisher and system randomness).

**Intended.** CR18 §4.10.2 Def 4.1: `Δ^D(S,T) = ⟨S|T⟩(D) = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`,
`Δ(S,T) := sup_D Δ^D(S,T)`.

**Agree — verified against the paper.** CR18_LN.pdf p. 107 states exactly this formula,
including the orientation (T minus S) and the signedness (no absolute value).

**Non-vacuity, established not assumed:**
- the defining set is **non-empty** (`advantage_image_nonempty`, the reject distinguisher) and
  bounded above (`bddAbove_advantage_image`), so `Δ` is a real supremum, not junk `sSup`;
- `0 ≤ Δ(S,T)` always (machine-checked: the reject distinguisher has advantage 0);
- `Δ` genuinely **sees** systems: I built an explicit one-query distinguisher and proved
  `1 ≤ Δ(pure (functionEvaluator (fun _ => false)), pure (functionEvaluator (fun _ => true)))`.
  If `verdict`/`transcript`/`winProb` were degenerate this would be unprovable.

**Class width vs. the paper.** CR18 §4.10 (p. 105) explicitly restricts to environments "that
stop after a finite number of queries" and then pads to exactly `q`. Lean's `DDD` does **not**
require halting, so the Lean supremum is over a **strictly larger** class than CR18's — the safe
direction for an upper bound. The paper's WLOG padding is not swept under the rug: it is the
explicit predicate `DeltaFilteredFiniteQueryNormalization`, and the theorem routes through
`deltaFilteredFiniteQueryNormalization_of_totalOnNonempty`, which **proves** it from totality of
`sopReal`/`sopIdeal` rather than assuming it (dependency-cone probe, `AuditDefs4`).

### `PFunPDS.filterQueries q` = `⌈q⌉` (`PDS.lean:120`, notation `PDS.lean:279`)

**Denotes.** `Dist.fTransform (PFunDDS.filterQueries q)`, where at the DDS level
`dom (filterQueries q s) = dom s ∩ {l | l.length ≤ q}` and outputs are unchanged where defined.

**Intended.** CR18 §3.4.3 `[q]s` — "`s` restricted to `q` queries, undefined as of the `(q+1)`-st".

**Agree — and the *interaction* really stops.** Domain-level containment is not by itself enough:
the distinguisher talks to `s⊥` (`fullyDefined`, via `keptPrefix`), so one must check the
refused query is dropped rather than, say, silently re-answered. Machine-checked concretely:
against `⌈1⌉ (const-c evaluator)`, a two-query environment produces the transcript
`[(true, some c), (false, none)]` — first query answered, second refused. Also checked
generically: every support atom of `⌈q⌉ S` is undefined on every history longer than `q`.

### `CondEquiv` / `|≡` (`CondEquiv.lean:118`)

**Denotes.** For all `i`, `xs : Vector X (i+1)`, `ys : Vector Y (i+1)`:
```
massAfalse Ŝ xs ≠ 0 → massDom T xs ≠ 0 →
  massYAfalse Ŝ i ys xs · massDom T xs = massY T i ys xs · massAfalse Ŝ xs
```
with `massYAfalse` = mass of "the visible outputs match `ys` on every prefix **and** every prefix
MBO bit is false", `massAfalse` = mass of "defined at `xs` and the bit is false", `massY` = the
`T`-side cumulative behaviour, `massDom` = `T`'s definedness mass.

**Intended.** CR18 Def 4.19 / eq. (4.38):
`p^Ŝ_{Y^i|X^i,A_i=0} = p^T_{Y^i|X^i}`, equivalently
`p^Ŝ_{Y^i,A_i=0|X^i} = p^Ŝ_{A_i=0|X^i} · p^T_{Y^i|X^i}`.

**Agree — verified against the paper (p. 108).** The cross-multiplication is the division-free
reading of (4.38); the `≠ 0` guards are exactly CR18 footnote 29 ("equal for all arguments for
which they are both defined … only `x^i` for which `A_i` has non-zero probability").

**Vacuity check.** The guard *does* fire in this proof — once `2k ≥ N` distinct queries have been
made, `freshKeep` is empty and `massAfalse = 0`, so eq. (4.38) holds there as `0 = 0`. That is
harmless because in that regime `mass_sopTightBad_le` already forces `ε ≥ 1` and the first
conjunct is free. Below `N/2` the guard does not fire and the identity carries real content —
it is proved from the unconditional counting identity `mass_agree_and_good`, which is not
guarded at all.

### `seededConditionCGame D F bad` (`SwitchingLemma.lean:1824`)

**Denotes.** `fTransform (fun a => historyEvaluator (fun l h => (F a (l.getLast h), decide (bad a l)))) D`
— sample seed `a ~ D`; answer the last query with `F a`; emit `bad a (full history)` as the MBO bit.

**Intended.** "the real system, watched by a monitor". **Agree.** Yes. `seededConditionCGame_ignoreMBO`
(and the instance `sopTightGame_ignoreMBO`) proves that stripping the bit returns exactly `sopReal`,
so the game is the real system *plus a bit*, not a different system.

### `IsBlind w` (`BlindConverter.lean:51`)

**Denotes.** `∀ l₁ l₂, l₁.length = l₂.length → w l₁ = w l₂` — the winner's query depends only on
the *round number*.

**Intended.** CR18 Def 4.20 `bS`: "to win game `bS` means to win game `S` blindly, without seeing
the outputs … equivalently, non-adaptively, since the inputs `x₁,…,x_q` can be interpreted as
being chosen in advance". **Agree — verified against the paper (p. 109).**

### `blindMaxWinProb Ŝ` = `Γᵇ` (`BlindConverter.lean:67`)

**Denotes.** `sSup {winProb W Ŝ | IsBlindDist W ∧ W.isProbDist}`, at the same concrete winning
predicate `winsDDS` (CR18 Def 3.23). **Intended.** `Γ(bŜ)` (Def 4.17 + 4.20). **Agree.**

No vacuity risk here even if the blind class were empty: `Γᵇ` is used only on the **upper** side
(`Δ ≤ Γᵇ ≤ ε`), so a spuriously small `Γᵇ` could only make the theorem *stronger*, and it is
proved.

### `blindQueryList w q` (`SwitchingLemma.lean:811`)

**Denotes.** `((List.finRange q).map (fun k => w (List.replicate k none))).reduceOption` — the
`some`-entries, in round order, of the schedule a blind winner announces when fed `q` rounds of
"no reply". Length `≤ q`.

**Intended.** "the fixed query schedule of a non-adaptive winner". **Agree.** For a blind `w` the
reply placeholder is irrelevant by definition of `IsBlind`, so `replicate k none` is a faithful
probe. The `reduceOption` compaction can shift a schedule that stops and then restarts, but this
is not load-bearing: the leaf `mass_sopTightBad_le` is proved for **every** list of length `≤ q`,
so the reduction only needs `blindQueryList_length_le`.

---

## 2. The proof's own definitions

### `sopFunction p x = p.1 x + p.2 x` — as advertised. `p.1`, `p.2 : Equiv.Perm G`.

### `sopReal` (`SumOfPermutationsTight.lean:82`)

**Denotes.** `fTransform (fun p => functionEvaluator (sopFunction p)) (uniform (Perm G × Perm G))`.
Sample `(π₁,π₂)` uniformly and independently from `Perm G × Perm G` (verified = product of two
uniform perm laws), answer `x ↦ π₁x + π₂x`.

**Intended.** XoP / the sum-of-permutations system. **Agree.**

### `sopIdeal` (`SumOfPermutationsTight.lean:88`)

**Denotes.** `fTransform functionEvaluator (uniform (G → G))`.

**Intended.** A uniform random function `G → G`.

**Agree — established, not assumed.** Machine-checked:
- `sopIdeal = PFunPDS.URF` **by `rfl`** — it is literally the framework's URF, not a lookalike;
- `sopIdeal (functionEvaluator f) = 1 / N^N` for every `f` — every one of the `N^N` functions gets
  exactly its uniform share (uses injectivity of `functionEvaluator`, so no collapsing);
- `sopIdeal s ≠ 0 → ∃ f, s = functionEvaluator f` — no mass anywhere else. It is a random
  function in the sense of CR18 Def 3.15.

### `freshFiber U V y = (univ \ U).filter (fun u => y − u ∉ V)`

**Denotes.** `{u : u ∉ U ∧ y − u ∉ V}` — the `π₁x` values that produce answer `y` with neither
permutation repeating a used value. Cardinality `N − |U| − |V| + r(y)` with
`r(y) = #(U ∩ (y − V))`; `card_freshFiber_ge` proves the `≥ N − |U| − |V|` half.

**Intended.** Exactly that (module docstring). **Agree.** Independent re-derivation matches.

### `freshKeep U V y = canonSubset (freshFiber U V y) (N − 2|U|)` and `canonSubset`

**Denotes.** `canonSubset s m = if m ≤ s.card then (Finset.exists_subset_card_eq h).choose else s`
— a **deterministic** (choice-fixed) `m`-element subset of `s`, a function of `(s,m)` only.
So `freshKeep U V y` is an unspecified-but-fixed `(N − 2|U|)`-element subset of `freshFiber U V y`.

**Intended.** "cut the fiber down to exactly `N − 2k`, the same number for every `y`, so the
conditioned answer law is uniform". **Agree.** The argument needs only the *cardinality*, never
the identity of the elements, and the choice is a genuine function (same `U,V,y` ⇒ same set), so
`sopFresh` is well defined. When `2|U| ≥ N` the target is `0` (ℕ truncation) and `freshKeep = ∅`,
so the monitor fires with certainty — consistent with the docstring and with `card_avail_fresh_answer`
returning `0`. The `m > s.card` fallback branch is never reached (`card_freshFiber_ge` covers it).

### `sopFresh U V u v := u ∈ freshKeep U V (u + v)`

**Denotes.** "the fresh pair `(u,v)` lies in the balanced subset of the pairs realizing answer
`u+v`". Note pairs realizing a given `y` are parameterised by their first coordinate, so
membership of `u` *is* membership of the pair. Availability (`u ∉ U`, `v ∉ V`) is implied via
`freshKeep ⊆ freshFiber`. **Agree.**

### `sopTightBad p l` (`SumOfPermutationsTight.lean:218`)

**Denotes.** `∃ pre, ∃ x, pre ++ [x] <+: l ∧ x ∉ pre ∧ ¬ sopFresh (pre.toFinset.image p.1) (pre.toFinset.image p.2) (p.1 x) (p.2 x)`
— at some **first occurrence** of a query `x` in `l`, with `U,V` the `π₁`- and `π₂`-images of the
*distinct* earlier queries, the fresh pair fell outside the balanced set.

**Intended.** The monitored condition described in the header. **Agree.** `x ∉ pre` is exactly
"first occurrence"; `|U| = |V| = |pre.toFinset|` because permutations are injective, which is what
`card_freshKeep`'s `U.card = V.card` hypothesis needs and what the proof supplies (`himgcard`).
Prefix-stated, so monotonicity is `IsPrefix.trans`.

### `sopEps N q = min 1 (Σ_{k<q} k²/(N−k)²)`

**Denotes.** Exactly that, in `ℝ`. **Intended.** `≈ q³/3N²`, "the discarded excess `k²` out of the
`(N−k)²` available fresh pairs at step `k`".

**Agree — independently re-derived.** At `k` distinct queries the available pairs number `(N−k)²`
and the kept pairs number `N·(N−2k)` (`card_avail_fresh`); the difference is
`(N−k)² − N(N−2k) = k²`. So the per-step charge really is `k²/(N−k)²`. Sanity checks:
`sopEps N 1 = 0` (checked in Lean), `sopEps N 2 = 1/(N−1)²` (checked in Lean).

---

## 3. Independent numeric cross-check of the whole statement

For any finite abelian `G` of order `N` and `q = 2` on two distinct queries, the real system's
answer difference is `y₂ − y₁ = d + e` with `d, e` independent uniform on `G∖{0}`, so
`Pr[y₂−y₁ = 0] = 1/(N−1)` and `Pr[y₂−y₁ = c ≠ 0] = (N−2)/(N−1)²`. Against the URF's uniform
`1/N`, the statistical distance is `1/(N(N−1))`.

The theorem's exhibited bound at `q = 2` is `1/(N−1)²`. So:

- bound holds: `1/(N(N−1)) ≤ 1/(N−1)²` ✓
- ratio is exactly `N/(N−1)` — **precisely** what the module docstring claims ("tight up to `N/(N−1)`")
- for `N = 3` this is true-value `1/6` vs bound `1/4`, which I computed independently by
  enumerating the 36 permutation pairs on `ℤ/3`.

At `q = 1` the theorem asserts `Δ = 0` and that is true (`π₁x + π₂x` is uniform for a single `x`);
I verified the Lean statement really does assert it (`AuditDefs3.delta_one_query_is_zero`).

This is the strongest available evidence that the definitions denote the intended objects: an
externally computed distinguishing distance lands under the formalised bound at exactly the
predicted ratio.

---

## 4. Findings

### F1 (MINOR) — `Δ` is a *signed* one-directional supremum; two-sidedness is off-statement

`Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ ε` literally bounds only
`sup_D (Pr^{D,ideal}(1) − Pr^{D,real}(1))`. A reader of the statement alone cannot tell whether
the other direction is covered. It **is**: `maxAdvantage_comm` (verdict-flip + truncation
argument, `CompatibleMetric.lean:1405`) gives `Δ(S,T) = Δ(T,S)` for probability systems, and both
filtered systems are probability distributions. I machine-checked the instance:

```lean
theorem delta_symm (q : ℕ) :
    Δ(⌈q⌉ (sopReal (G := G)), ⌈q⌉ (sopIdeal (G := G)))
      = Δ(⌈q⌉ (sopIdeal (G := G)), ⌈q⌉ (sopReal (G := G))) :=
  maxAdvantage_comm (filt_real_prob q) (filt_ideal_prob q)
```

The orientation itself is **faithful to CR18** (p. 107 defines `Δ^D(S,T) = Pr^{DT} − Pr^{DS}`), so
this is a readability finding, not a soundness one. Suggest a one-line corollary or docstring note
in `SumOfPermutationsTight.lean` recording the symmetry.

### F2 (MINOR) — the "beats birthday" conjunct is discharged by the `min 1` cap wherever `q² > N`

Second conjunct: `∀ N q, 1 < q → q < N → ε N q < q²/N`. In the branch `N < q²` the proof is
`lt_of_le_of_lt (min_le_left _ _) …`, i.e. it uses only `ε ≤ 1 < q²/N`. **Any** capped `ε` passes
there. So the conjunct has content only for `1 < q ≤ √N` — precisely *before* the birthday point,
not past it. I machine-checked that the cap alone suffices:

```lean
theorem second_conjunct_is_the_cap_past_birthday (N q : ℕ) (hq : 1 < q) (hqN : q < N)
    (hcase : N < q ^ 2) : sopEps N q < (q : ℝ) ^ 2 / (N : ℝ)
```

The file's own docstring is honest about this ("a floor, not the target"), but the theorem
*statement* reads as a quality gate that it is not. The real content is the first conjunct.

### F3 (MINOR) — junk values in `sopEps` for `k ≥ N` (benign, but fragile)

`sopEps` uses real subtraction, so the `k = N` term is `N²/0 = 0` in Lean (not `+∞`), and terms
with `k > N` use `(N−k)² > 0`. This makes the sum *smaller* than the mathematically intended
formula in exactly one place, so it strengthens the claim. It never binds:
`sopEps_ge_one_of_large` fires first via a `k < N` with `2k ≥ N`, which exists whenever `N ≥ 2`
and `q > N` (take `k = ⌈N/2⌉`). Consequence worth knowing: for the trivial group `N = 1`,
`ε(1,2) = 0`, so the theorem claims *exact* indistinguishability at `q = 2` there — which is true
(both systems are the unique one-point system), but is an accident of `1/0 = 0` rather than a
consequence of the intended formula. If the leaf bound were ever restated, this convention should
be pinned down explicitly.

### F4 (MINOR) — the exhibited `ε` is informative only up to `q = Θ(N^{2/3})`

`Σ_{k<q} k²/(N−k)² ≥ (q−1)q(2q−1)/(6N²)`, so `ε < 1` requires `q ≲ (3N²)^{1/3} ≈ 1.44·N^{2/3}`.
Past that the first conjunct degenerates to `Δ ≤ 1`, and (by F2) the second conjunct is also
content-free. So the formalised security claim is: **XoP is indistinguishable up to about
`1.44·N^{2/3}` queries.** That is genuinely beyond the birthday barrier `√N` — the file's stated
goal — but well short of the literature: Dai–Hoang–Tessaro (ePrint 2017/537, present in
`RandomSystems/SoP/`) prove the **optimal** `√q/2^n`, i.e. security essentially to `q ≈ N`. The
header's "the construction is believed to be secure well beyond the birthday barrier … the
interesting regime is `q` far past `√N`" could be read as claiming more coverage than `N^{2/3}`.
Not a defect — a scope statement worth making explicit next to the theorem.

### F5 (MINOR, pedantic) — `ε` is chosen per universe level

`theorem sop_randomness_expander_tight.{u} : ∃ ε : ℕ → ℕ → ℝ, (∀ H : Type u, …)`. The `∃` sits
inside the universe-parametrised theorem, so formally each universe level gets its own `ε`. The
docstring's "one formula that works for every group of that order" is literally true only within
one universe. Harmless (the witness `sopEps` is universe-free), and the `∀ H : Type u` class is
inhabited at every level; I checked instantiation at `ZMod 5` in `Type 0`.

### Not a finding, recorded because I looked for it

- **`Δ` vacuity.** Ruled out constructively (`1 ≤ Δ` between two distinct deterministic systems).
- **Empty distinguisher class.** Ruled out (`advantage_image_nonempty`).
- **The filter not really filtering.** Ruled out concretely (transcript ends in `none`).
- **`sopIdeal` merely resembling a URF.** Ruled out (`= PFunPDS.URF` by `rfl`, mass `N^{-N}`
  per function, support exactly the function evaluators).
- **Normalisation assumed without hypothesis.** Not found; every such lemma takes `isProbDist`.
- **CR18 §4.10.1 WLOG smuggled in as an axiom/assumption.** Not smuggled: the theorem routes
  through `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty`, which *proves* the
  normalisation from support-totality of `sopReal`/`sopIdeal`.
- **Axiom footprint.** `[propext, Classical.choice, Quot.sound]`.

---

## 5. Coverage

**Checked (42 nodes).** All 22 nodes named in the task, plus the supporting definitions they
depend on: `PFunDDS.Valid`/`DDS`, `PFunDDS.DDD`/`StopFinal`, `ddToDDE`, `verdict`,
`PFunDDS.transcript`, `fullyDefined`/`keptPrefix`, `transcriptInputs/Outputs`, `advantage`,
`verdictProb`, `GamePerf.winProb`, `GamePerf.maxWinProb`, `PFunDDS.filterDom`/`filterQueries`,
`PFunPDS.stripMBO`/`ignoreMBO`, `PFunPDS.ofFunDist`/`URF`/`IsRandomFunction`, `historyEvaluator`,
`massY`/`massYAfalse`/`massAfalse`/`massDom`, `TotalOnNonempty`, `TotalUpTo`, `QueriesExactly`,
`DeltaFilteredFiniteQueryNormalization`, `IsBlindDist`, `Counting.availPairs`, `goodCount`,
`sopEps`, `sopTightGame`.

**Not checked (statements read, proofs not audited; and material not read):**

1. The *proofs* of the framework Thm-4.17 chain: `advantage_le_blindMaxWinProb_of_condEquiv_of_totalUpTo`
   (`BlindAbsorption.lean:728`), the Lemma-4.15/4.16 transcript algebra (`Lemma415.lean`,
   `RelateGameDistinguishing.lean`). I read the statements and confirmed they match CR18 Lemma 4.16 /
   Theorem 4.17 as printed on pp. 107 and 110, and that the whole cone is axiom-clean — but I did
   not verify the Lean proofs line by line against Maurer's argument. **This is the largest
   residual: if the framework's Thm 4.17 were unsound, the SoP theorem would inherit it.** The
   `q = 2` numeric cross-check in §3 is evidence against that, not proof.
2. `PFunDDS.padDDD` / `padDDDDist` and `advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty`
   — the §4.10.1 padding construction. Statement only.
3. `Counting.chain_product_lower_bound` (Weierstrass) and `Counting.three_sum_sq_le_cube`.
   Statements only; both are pure real analysis and kernel-checked.
4. `Dist.cond`, `Dist.condPMF`, `Dist.marginal`, `Dist.iidPow` — present in `Dist.lean`, not in
   this theorem's cone.
5. Papers: `papers/CR18_LN.pdf` pp. 105–110 read visually (Def 4.1, 4.15–4.21, Lemma 4.15/4.16,
   Thm 4.17, §4.10 preamble). **`papers/MaPiRe07.pdf`, `papers/Maurer13b.pdf`, and
   `papers/thesis (1).pdf` were NOT read.** `RandomSystems/SoP/2017-537.pdf` — abstract only.
