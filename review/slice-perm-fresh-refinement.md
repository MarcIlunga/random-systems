# Slice review — `perm-fresh-refinement` (19 nodes)

Reviewer: adversarial pass, read-only. Target file `RandomSystems/PermFreshCounting.lean`
(385 lines, read in full) plus the LIB dependency `RandomSystems/Counting.lean:539–656`
(read in full).

**Verdict: 19 / 19 nodes CLEAN. No defect found. Four MINOR observations, all
"reader-hazard / scope hand-off", none of which threaten the truth of any statement
in the slice.**

## 0. How the file was exercised

* Typechecked: `lake -KverificationBuildDir=.lake/verify-rs-prover-d0 env lean
  RandomSystems/PermFreshCounting.lean` → clean, no diagnostics.
* Axiom check re-run independently: `card_fresh_pair_refine`, `card_fresh_pair_fiber`,
  `card_permPair_restrict`, `mem_availPairs`, `card_perm_fiber_finset`, `card_perm_fiber`
  → `[propext, Classical.choice, Quot.sound]`; `restrict_perm_injective` → `[propext,
  Quot.sound]`. (Necessary, not sufficient — recorded for completeness only.)
* Source scan: no `sorry`, no `axiom`, no `admit`, no `native_decide`, no `set_option`,
  no `@[simp]` attribute anywhere in the file.
* **Independent numeric evaluation** on `X = Fin 4` (24² = 576 permutation pairs), by
  `#eval` over the actual definitions in the file, not over a paraphrase. Scratch files
  `/tmp/pfc_probe{1,2,3,4}.lean`, deleted after the run. Results below.

## 1. Numeric confirmations and mutation tests

Setting: `X = Fin 4`, `Q = {0,1}` (so `k = 2`, `n = 4`, `(n−k)² = 4`), fresh `x = 2`.
`R` chosen so that `hm` is *actually satisfiable*: `Rmin U V u v := min(univ\U) = u ∧
min(univ\V) = v`, which has exactly one available witness for every `(U,V)` with
`|U|,|V| < 4`, so `m = 1`.

| experiment | result | reading |
|---|---|---|
| `hm` holds for **every** `p` with `m = 1` | `true` (decided over all 576 pairs) | `hm`'s `∀ p` form is satisfiable, non-vacuously |
| `card_fresh_pair_refine` LHS vs RHS, `P = True` | `(576, 576)` | identity holds, both sides non-zero |
| same with a non-trivial restriction-invariant `P` (`π₁ 0 = 0 ∧ π₂ 1 ≠ 3`) | `(108, 108)` | not an artifact of `P = True` |
| same, fresh point `x = 3` instead of `2` | `(108, 108)` | not an artifact of the chosen `x` |
| `card_fresh_pair_fiber` at `p₀ = (id, id)`: `(m, LHS, RHS, |Fib|)` | `(1, 4, 4, 4)` | fiber lemma holds; `|Fib| = ((n−k)!)² = 4` ✓ |
| `card_permPair_restrict` count vs `((n−k)!)²` | `(4, 4)` | product split correct |
| `card_perm_fiber_finset` count vs `(n−k)!` | `(2, 2)` | LIB node correct |
| `availPairs` card vs `(n−|U|)(n−|V|)`; `mem_availPairs` iff | `(4,4)`; `true` | both correct |
| `restrict_perm_injective` decided over all `π` | `true` | correct |

**Mutation tests (each removes one hypothesis and exhibits a concrete counterexample):**

| mutation | result | conclusion |
|---|---|---|
| **drop `hx`** — take `x = 0 ∈ Q` | LHS `0` vs RHS `576` | `hx` is load-bearing, not decoration |
| **drop `hP`** — `P p := (p.1 2 = 0)` reads the fresh point | LHS `288` vs RHS `144` | `hP` is load-bearing; without it the lemma is false by a factor 2 |
| **drop `hm`** — `R U V u v := (u = v)`, whose available count is `\|univ \ (U ∪ V)\|` | counts range over `{0,1,2}`; LHS `112`, `#{P} = 108` | no `m` satisfies `hm` for that `R`, and `112` is not a multiple of `108`, so the conclusion genuinely fails |
| **read `R` at the wrong state** — at `(insert x Q).image` instead of `Q.image` | LHS `0` vs RHS `108` | the "used sets" must be the *pre-query* ones, exactly as the statement has them |
| **drop injectivity in `card_permPair_restrict`** — `f ≡ 0` | count `0`, lemma would claim `4` | `hf`/`hg` are load-bearing |
| **drop injectivity in `card_perm_fiber_finset`** (`g` non-injective) | count `0`, lemma would claim `2` | the `↪` in the LIB statement is load-bearing |

## 2. Node-by-node

### NEW nodes

**`availPairs` (:93) — CLEAN.**
(a) `availPairs U V = (univ \ U) ×ˢ (univ \ V)`. Docstring "the product of the two unused
sets" is exactly the definition. `DecidableEq X` present for `\`. No hidden coercion.
(b) Trivially the intended object.

**`mem_availPairs` (:96) — CLEAN.**
(a) `uv ∈ availPairs U V ↔ uv.1 ∉ U ∧ uv.2 ∉ V`. Implicit `{U V uv}` — coherent. The
`∈ univ` conjunct of `mem_sdiff` is correctly discharged, not silently dropped from the
intended meaning.
(b) True. Confirmed by decision procedure over `Fin 4`.

**`restrict_perm_injective` (:64) — CLEAN.**
(a) `Function.Injective (fun z : ↥Q => π z.1)` — codomain `X`, i.e. the restriction *as a
map into `X`*, which is exactly the shape `card_permPair_restrict` wants (it builds
`⟨f, hf⟩ : ↥Q ↪ X`). `omit [Fintype X] [DecidableEq X]` is correct: the statement needs
neither. Proof `Subtype.ext (π.injective hab)` is the honest one-liner.
(b) True.

**`card_permPair_restrict` (:70) — CLEAN.**
(a) Statement: `#{p : Perm X × Perm X | p.1|_Q = f ∧ p.2|_Q = g} = ((n − |Q|)!)²` given
`f g : ↥Q → X` injective. Both hypotheses are used (numerically load-bearing, see §1).
The `Fintype.card X - Q.card` is truncated `ℕ` subtraction but no guard is needed: if
`|Q| > n` then no injective `f : ↥Q → X` exists, so the hypotheses are unsatisfiable and
the lemma is vacuous there rather than wrong; when `f` exists, `|Q| ≤ n` automatically.
(b) True: the number of permutations extending a prescribed injective partial map on a
`k`-set is `(n−k)!`, and the pair-constraint set is literally a Cartesian product.
**This is the node the DAG names as "where permutation independence enters".** That is
accurate as far as it goes, and worth stating precisely (see MINOR-4): the lemma does not
*prove* independence — it observes that the constraint set on `Perm X × Perm X` factors
(`hsplit`, then `Finset.card_product`), so its cardinality factors. Independence is a
property of the ambient uniform counting measure on the *product type*; whether `sopReal`
samples that way is a `sop-statement-and-semantics` question, not one this slice answers.

**`card_fresh_pair_fiber` (:104) — CLEAN.**
(a) Hypotheses `Q, x, hx : x ∉ Q, hkn : |Q| < n, p₀, R : X → X → Prop, m, hm`. Conclusion
`(n−k)² · #{p ∈ Fib | R (p.1 x) (p.2 x)} = m · #Fib` with `Fib` the pair of restrictions
prescribed by `p₀`. All hypotheses satisfiable simultaneously (probe: `p₀ = (id,id)`,
`Q = {0,1}`, `x = 2`, `m = 1`). Nothing weakened: `m` is pinned by `hm` to the *available*
`R`-witness count against `U = Q.image p₀.1`, `V = Q.image p₀.2` — the sets read off `p₀`,
which is the right state. The two auto-generated arithmetic side conditions were inspected
directly:
`_proof_1_3 : |Q| < n → (insert x Q).card = |Q| + 1 → ¬(n − k = n − k − 1 + 1) → False`
— i.e. `hkn` is exactly and only used to defeat `Nat` truncation at `n − k = 0`; and
`_proof_1_4 : n − (k+1) = n − k − 1`, unconditionally true.
(b) True. The count of `p ∈ Fib` with a prescribed fresh pair `(u,v)`, `u ∉ U`, `v ∉ V`,
is `((n−k−1)!)²` (`hextend`, whose injectivity proofs genuinely use `u ∉ U`/`v ∉ V`); the
fresh pair of any `p ∈ Fib` is always available (`hfresh`, from injectivity plus `x ∉ Q`);
so `#{p ∈ Fib | R} = m·((n−k−1)!)²` and `#Fib = ((n−k)!)²`, and `(n−k)²((n−k−1)!)² =
((n−k)!)²` for `n−k ≥ 1`. Consistency cross-check `(n−k)² · ((n−k−1)!)² = ((n−k)!)²`
holds numerically (`4 · 1 = 4`). The `hterm` case split is exhaustive and each of the three
branches is the right count.

**`card_fresh_pair_refine` (:295) — CLEAN.**
(a) The docstring's `(N − |Q|)² · #{p : P p ∧ R (fresh values of p)} = m · #{p : P p}` is
literally the conclusion; `N` is `Fintype.card X`, the fresh values are `(p.1 x, p.2 x)`,
and `R` is read at `(Q.image p.1, Q.image p.2)` — the used sets *before* the fresh query
(note `x ∉ Q`, so `x`'s own value is not in the image). Mutation test 4 above shows that
reading `R` at the post-query state would make it false, so this detail is not cosmetic.
`hP` is exactly "restriction to `Q` determines `P`" — stated as a one-way implication but
quantified over both `p` and `p'`, hence symmetric; both directions are used in the proof.
`hkn` is **not** a caller obligation: it is derived internally at :311–316 from `hx` via
`Finset.ssubset_univ_iff` + `Finset.card_lt_card` + `Finset.card_univ`. I re-proved that
derivation standalone; it is correct, and it is the only thing standing between the lemma
and the `n − k = 0` degenerate case. No `Nonempty X` needed — `x : X` supplies it.
Decidability instances (`[DecidablePred P]`, `[∀ U V u v, Decidable (R U V u v)]`) are
quantified in the statement, so the theorem holds for *every* instance; the `classical`
inside the proof cannot silently narrow it.
(b) True. Partition `Perm X × Perm X` by the restriction pair `ρ p = (p.1|_Q, p.2|_Q)`.
On each fibre: `P` is constant (`hP`), the used sets are constant (`himage`, via
`Finset.image_congr` on both coordinates — I checked both are covered), so the fibre goal
is exactly `card_fresh_pair_fiber` with `hm p₀`. Empty fibres and `¬P p₀` fibres give
`0 = 0`. Summing is `Finset.card_eq_sum_card_fiberwise` over the full (finite) function
space, including the `σ` not realised by any permutation pair — those are the empty fibres.
Nothing is dropped.

**`card_fresh_pair_fiber._proof_1_3`, `._proof_1_4` (NEW, auto) — CLEAN.** Types printed
and checked by hand; see above.

**`card_fresh_pair_fiber._simp_1_1/._simp_1_2`, `card_fresh_pair_refine._simp_1_1/._simp_1_2`
(NEW, auto) — CLEAN.** Printed: they are the cached Mathlib simp facts
`(a ∈ Finset.filter p s) = (a ∈ s ∧ p a)` and `(x ∈ Finset.univ) = True`. No content of
their own; they are `simp`-normalisation artefacts of `ext; simp` steps.

### LIB nodes

**`card_perm_fiber` (`Counting.lean:539`) — CLEAN.**
(a) `#{π | ∀ i, π (inputs i) = ys i} = (n − q)!` given `inputs`, `ys : Fin q → X` both
injective and `q ≤ n`. All three hypotheses are used: `h_ys_inj` to form `ys_emb : Fin q ↪ X`,
`h_inj` for `hS_card`/`Φ` well-definedness, `h_q_le` for `Nat.descFactorial_pos` and
`Nat.factorial_mul_descFactorial`.
(b) True, and the proof is the standard one: `Φ : π ↦ π ∘ inputs` has all fibres of equal
size because `Perm X` acts `q`-transitively on injective `q`-tuples
(`Equiv.Perm.isMultiplyPretransitive`), so `n! = fibre · descFactorial n q` and
`n! = (n−q)! · descFactorial n q`, cancel by `descFactorial_pos`. I verified the shape of
`Nat.factorial_mul_descFactorial` matches the use.

**`card_perm_fiber_finset` (`Counting.lean:623`) — CLEAN.**
(a) `S : Finset X`, `g : ↥S ↪ X`, conclusion `#{π | ∀ x : ↥S, π x.1 = g x} = (n − |S|)!`.
This is *exactly* the shape `card_permPair_restrict` consumes, and exactly the shape
`restrict_perm_injective` produces the embedding for. The `Fintype.card ↥S → S.card`
conversion is via `Fintype.card_coe`, correct.
(b) True; it is `card_perm_fiber` transported along `Fintype.equivFin ↥S`. Confirmed
numerically (`2 = 2!`), and the embedding hypothesis is load-bearing (non-injective `g`
gives count `0`).

**`card_perm_fiber._simp_1_1/._simp_1_2/._simp_1_3`,
`card_perm_fiber_finset._simp_1_1/._simp_1_2` (LIB, auto) — CLEAN.** Printed: `Finset.mem_filter`,
`Finset.mem_univ`, `Function.Embedding.ext_iff` in `simp`-normal form. No content.

## 3. MINOR observations (no node fails on these)

**MINOR-1 — `hkn` in `card_fresh_pair_fiber` is a redundant hypothesis.**
`card_fresh_pair_fiber` assumes *both* `hx : x ∉ Q` and `hkn : Q.card < Fintype.card X`,
but `hkn` follows from `hx` by the same three lines the caller uses at :311–316 (I
compiled that derivation standalone). So the fiber lemma's hypothesis set is not minimal.
This is not a soundness problem — a redundant hypothesis only weakens the lemma — but it
is a reader hazard: it invites the reading "`card_fresh_pair_fiber` needs a non-degeneracy
side condition that some caller must supply", when in fact no caller can fail to supply it.
`hkn` *is* used by the proof (see `_proof_1_3`), so it is not dead code; it is derivable
input. No action required; recorded so nobody later "hardens" the lemma by propagating
`hkn` upward as a real obligation.

**MINOR-2 — the DAG's own review prompt mis-states the strength of `hm`. Correct it.**
`review/sop-dag.md` §5 says of `card_fresh_pair_refine`: *"the proof uses only `hm p₀`, so
`hm` is stronger than needed here"*. That is wrong in a way that could license a bad future
edit. `p₀` is an *arbitrary* representative of each non-empty `ρ`-fibre, obtained from
`Finset.eq_empty_or_nonempty` inside a `Finset.sum_congr` over **all** `σ : (↥Q → X) × (↥Q → X)`;
the fibres exhaust `Perm X × Perm X`, and which representative is picked is not under the
caller's control. So `hm` cannot be weakened to "at one `p`". The *only* genuine weakening
available is `∀ p, P p → (…) = m` (fibres with `¬ P p₀` never reach `hm`). Both call sites
(`card_goodAgree` :354, `card_good` :440) do discharge it for arbitrary `p` — `intro p`,
then `card_avail_fresh_answer`/`card_avail_fresh` with `himgcard p` and
`Finset.card_image_of_injective` — so the `∀` costs nothing there.

**MINOR-3 — file-header prose slightly overstates `hm`.** The header says `R` must admit
exactly `m` witnesses *"whatever the already-used sets are"*. The Lean hypothesis quantifies
over `p`, hence only over used-set pairs of the form `(Q.image p.1, Q.image p.2)` — i.e.
pairs of subsets **each of cardinality exactly `|Q|`**. The Lean is therefore *weaker* than
the prose, which makes the theorem *stronger*; the direction of the imprecision is the safe
one. Recorded only so the prose is not later "corrected" into the stronger hypothesis.

**MINOR-4 — two scope hand-offs this slice cannot discharge.** Neither is a defect here;
both are places a reader could mistake this slice's guarantee for more than it is.
1. *Independence.* `card_permPair_restrict` gets its product only because the counting is
   over the type `Equiv.Perm X × Equiv.Perm X` with the uniform (counting) measure. That the
   *system under review* actually draws `(π₁, π₂)` that way is a fact about `sopReal`, owned
   by `sop-statement-and-semantics`.
2. *Adaptivity.* Everything in this slice is a fixed-`(Q, x)` cardinality identity. The root
   theorem claims `q` **adaptive** queries. Nothing in `PermFreshCounting.lean` speaks to
   adaptivity; that must be earned in the game / conditional-equivalence layers
   (`condequiv-instantiation`, `blind-game-endpoint`).
3. *Degenerate `m = 0`.* If a caller instantiates `m = 0` (which the call sites do once
   `2|Q| ≥ N`, by `Nat` truncation of `N − 2|Q|`), `card_fresh_pair_refine` remains true and
   forces `#{P ∧ R} = 0`. That is correct behaviour for *this* lemma; whether the overall
   bound is then non-vacuous is the `sop-counting-core` / `mass-layer-and-epsilon` question,
   already flagged in the DAG.

## 4. Coverage

**19 of 19 slice nodes checked, both (a) LEAN and (b) MATH.** Nothing in the slice was
skipped or sampled. The full list, with what was done:

| node | (a) statement | (b) math | evidence |
|---|---|---|---|
| `availPairs` | read | trivial | definition read |
| `mem_availPairs` | read | proved by hand | `decide` over `Fin 4` |
| `restrict_perm_injective` | read (incl. `omit`) | proved by hand | `decide` over `Fin 4` |
| `card_permPair_restrict` | read | proved by hand | `#eval` `(4,4)`; non-inj mutation |
| `card_fresh_pair_fiber` | read, all hyps | proved by hand | `#eval` `(1,4,4,4)`; `_proof_1_*` printed |
| `card_fresh_pair_refine` | read, all hyps, `hkn` derivation re-proved | proved by hand | `#eval` `(576,576)`, `(108,108)`×2; 4 mutations |
| `card_fresh_pair_fiber._proof_1_3` | type printed | checked | `#check` |
| `card_fresh_pair_fiber._proof_1_4` | type printed | checked | `#check` |
| `card_fresh_pair_fiber._simp_1_1/_2` | types printed | Mathlib simp facts | `#check` |
| `card_fresh_pair_refine._simp_1_1/_2` | types printed | Mathlib simp facts | `#check` |
| `card_perm_fiber` (LIB) | read | proof read in full | `Counting.lean:539–618` |
| `card_perm_fiber_finset` (LIB) | read | proof read in full | `#eval` `(2,2)`; non-inj mutation |
| `card_perm_fiber._simp_1_1/_2/_3` (LIB) | types printed | Mathlib simp facts | `#check` |
| `card_perm_fiber_finset._simp_1_1/_2` (LIB) | types printed | Mathlib simp facts | `#check` |

**Not checked (deliberately out of slice, named for the record):**
`canonSubset`, `canonSubset_subset`, `canonSubset_card` — they live in
`PermFreshCounting.lean` but the DAG assigns them to `sop-counting-core`, and I did not
review them. The `Exists.choose` in `canonSubset` is that slice's problem.
The call sites `card_goodAgree` / `card_good` were *read* only far enough to confirm that
`hm` is discharged for arbitrary `p` (MINOR-2); I did not review their inductions.

**Papers:** no node in this slice cites or depends on a claim from MPR07 / Maurer13b /
CR18_LN. The content is self-contained finite combinatorics, and I verified it independently
rather than against a source. I did not open the PDFs for this slice.
