# Theorem 2.31 attainment — execution design (banked 2026-07-18)

## SOURCE-AUDIT CORRECTION (2026-07-20; supersedes the arbitrary-domain plan)

The unconditional CR18-partial-system generalization sketched below is
**false**.  The theorem proved in the thesis and LanMau20 assumes a common DDS
domain and proceeds by induction on a finite bound on answered queries.  The
PDF proof contains no unbounded stabilization argument, and the per-fuel
finiteness of `valueSet n` does not supply one.

A concrete obstruction uses two inputs `a,b` and one ordinary output.  Let
`ab` answer either first query and then self-destruct, let `a` answer only
`a`, let `b` answer only `b`, and let `none` answer neither.  Put

```text
S = 1/2 ab + 1/2 none
T = 1/2 a  + 1/2 b.
```

Under CR18's observable-bottom/skip semantics, `Adv(S,T) = 1/2`: either first
query matches one half of the laws, and asking the other query after an
observed bottom attains the remaining separation.  But transcript equivalence
determines the complete distribution of the four root-domain patterns
`{a,b}`, `{a}`, `{b}`, and `{}`.  Hence every representative equivalent to
`S` has pattern law `1/2 {a,b} + 1/2 {}`, every representative equivalent to
`T` has pattern law `1/2 {a} + 1/2 {b}`, and these laws are disjoint.  Data
processing under the root-pattern map forces every representative distance to
be `1`.  Thus `Delta(S,T) = 1`, not `Adv(S,T)`.

Consequences for the implementation:

- the current unrestricted `Delta_eq_adv` statement must not be completed;
- pattern stratification faithfully preserves the CR18 behavior, but in this
  example it stabilizes at distance `1`, so it cannot be followed by a proof
  that stabilization equals advantage;
- the first attainment theorem must expose the source's finite-alphabet,
  common-domain, bounded-answered-query hypotheses and follow the source
  induction; and
- any later arbitrary-carrier or unbounded theorem needs a genuinely new,
  separately named statement and proof.  It cannot be attributed to Theorem
  2.31.

Everything below is retained as a chronological engineering record.  Claims
about arbitrary domains, infinite ambient input types, or global
stabilization are historical sketches unless re-established under the
corrected theorem boundary above.

## STATUS UPDATE (2026-07-18, later)

§1 is DONE, landed in RandomSystem.lean, all first-pass green:
- `transcript_eq_of_transcript_succ` (recoverability, via the private stall lemma)
- `δ_transcriptDist_mono` (fTransform_comp + δ_fTransform_le)
- `exists_adv_eq_δ_transcriptDist` (= the planned `adv_attained`; renamed
  Mathlib-style, flag to user) — proved WITHOUT cells/attach: private
  `δ_transcriptDist_le_of_transcript_eq_imp` (choice-relabeling γ via
  Exists.choose + `Finsupp.mapDomain_congr` on support + DPI) applied both
  ways gives partition-well-definedness; factor through
  `relOf : DDE × ℕ → (↥F → ↥F → Prop)` (finite via `Prop.fintype`,
  `FinsetCoe.fintype`); `Set.finite_range` + `Set.Nonempty.csSup_mem`.
  Also landed: private `fTransform_congr_of_support` (upstream to Dist.lean
  when free).

§2 rebuild refinements discovered while proving §1:
- fTransform of S alone CANNOT realize the maximal coupling in general: an
  atom cannot split its mass. Equivalence permits atom-splitting (same
  transcripts), so rebuild = (refine S, T into mass-commensurate split PDS)
  ∘ (deterministic per-refined-atom alignment map). Formalize a `split`/
  refinement step or fold it into the alignment construction.
- No single environment induces the common refinement of two partitions
  (statefulness — self-destruct example), so the alignment really must
  recurse down the answer tree; per-node overlap = common part of the two
  first-answer distributions (min, diagonal) — no quantile order needed for
  the diagonal; only the excess mass needs arbitrary (choice) matching.
- Depth stabilization: per-e advantage is monotone (δ_transcriptDist_mono)
  and the global value set is finite, so diverged mass stabilizes at the
  attaining depth; use this for the limit-free δ(S',T') ≤ Adv argument.

## §2 rebuild — carrier decision (2026-07-18, second design pass)

Two shortcuts are PROVABLY dead, one carrier is forced:

1. **`fTransform` of S alone is insufficient.** A single S-atom answering y
   must in general send part of its mass to the coupled continuation and
   part to the S-only excess continuation (whenever S's y-mass exceeds the
   overlap min(p_y, q_y) and the two continuations differ as trees). A
   deterministic per-atom map cannot split mass. (Footnote-11-style joint
   over first queries does not rescue this — the split is per ANSWER mass,
   within one atom.)
2. **Behavior-canonicalization (mergeS(s,t) := behavior tree of s) is
   wrong**: it yields δ = behavior-distribution distance, which the worked
   example (s₂/s₃ vs s₀: 1 vs Adv = ½) shows exceeds Adv. The rebuilt atom
   MUST mix branch-conditional slices of different original atoms
   (s₂₃ = s₂'s a-branch + s₃'s b-branch), which is exactly what
   PDS-equivalence's unobservable cross-branch correlation permits.
3. **Forced carrier: a finite-support coupling `Dist (DDS × DDS)`** (=
   Coupling.lean's `DistCoupling` shape, Finsupp-native) over PAIRS of
   rebuilt trees, built by the flow recursion: at node (Sᵤ, Tᵤ), per query
   x and answer y, coupled flow min(p_y, q_y) into the aligned pair node,
   excesses into solo nodes. S' and T' are the fTransform-marginals of the
   coupling; equivalence of S' with S = per-branch marginal preservation
   (uses transcriptDist_successor); δ(S', T') ≤ P[uncoupled] ≤ Adv via the
   stabilization argument.
   Also note the Finsupp-collapse point: identical-forever rebuilt trees
   coincide as Finsupp atoms — harmless (mass adds on both sides equally).

## Thesis §2.4.2 proof read VERBATIM (2026-07-18, PDF pp. 28–33; book pp. 18–23)

Statement (Thm 2.31, book p. 20): Δ(S,T) = Adv(S,T), AND attainment: ∃ PDS
S ∈ [S], T ∈ [T] with δ(S,T) = Δ(S,T). Thm 2.32 (coupling) = 2.31 + classical
coupling lemma (their Lemma 2.8). NOTE: Def 2.26/2.27/2.28 all say "with the
same domain"; footnote 8 has FINITE first-input set {x₁,…,x_q}; Lemma 2.33
(= LanMau20 Lemma 6) is indexed over finite [n]. The thesis general case is
finite-first-alphabet; our arbitrary-X statement is a genuine generalization
(see finiteness argument below for why it should still hold).

Proof structure (induction over max answered queries q):
1. Adv unfold: sup_e δ = max_{x∈X'} Σ_y sup_{e'} δ(tr(S↑x↓y,e'), tr(T↑x↓y,e'))
   — steps: condition on first query (adaptive e), Lemma 2.5 = our
   δ_sum_of_disjoint_support (first-answer partition), per-y adaptivity.
   [We have all pieces: transcriptDist_successor + δ_sum_of_disjoint_support.]
2. IH per (x,y): rebuilt pair S_xy ∈ [S↑x↓y], T_xy with δ(S_xy,T_xy) = sup.
3. PREPEND: S'_xy := prepend (first query x ↦ answer y) to every atom of
   S_xy; undefined at other first queries; (S'_xy)↑x↓y = S_xy; δ preserved
   (prepend is an injective atom map ⇒ pushforward preserves δ pointwise).
   [Lean: needs δ_fTransform_eq_of_injective — small, provable now via
   Finsupp.mapDomain_apply / sum_image; or both-ways DPI with invFun.]
4. Per-x sum: S'_x := Σ_y S'_xy; δ(S'_x,T'_x) = Σ_y δ(S'_xy,T'_xy) by
   disjoint first-answer supports (δ_sum_of_disjoint_support again).
5. Cross-x JOINT (Lemma 2.33): all S'_x have EQUAL weight p_S (thesis: same
   domain; for US automatic — s⊥/Option-Y totalization makes every atom
   answer every x, weight_successorTransform sums to S.weight ✓). Common
   part TRIMMED to uniform weight τ := min_x overlap(S'_x,T'_x):
   S'_x = E_x + X'_x, T'_x = E_x + Y'_x with |E_x| = τ; take joints E, X', Y'
   of the three equal-weight families (their Lemma 2.3, n-ary); S' := E+X',
   T' := E+Y'. δ(S',T') ≤ p−τ = max_x δ(S'_x,T'_x); ≥ by marginal DPI.
   Footnote 8: joint atoms = TUPLES of per-x atoms reassembled into one DDS.
6. S' ∈ [S]: transcripts only probe one first query per interaction, and
   every x-marginal of S' is S'_x ≡ (x-restriction of S).

KEY RESOLUTIONS for our formalization:
- **Mass-splitting is NOT atom-copying**: E_x and X'_x are summand
  sub-distributions that may share atoms; recombination is Finsupp `+`
  (masses add). The Finsupp-collapse worry from the second design pass
  dissolves — no distinct copies ever needed. The carrier stays
  PFunPDS-native: rebuilt distribution = E + X' as Finsupp sums.
- **Equal-weight hypothesis of Lemma 2.33 is automatic in CR18-s⊥**: every
  atom answers every x in Option Y. Our repair (#28) pays off here.
- **Attainment + δ_transcriptDist_mono replace the q-induction shell for
  unbounded systems**: finite support ⇒ any two distinct rebuilt atoms
  differ at finite depth ⇒ δ(S',T') equals the depth-D divergence for some
  finite D ≤ (max pairwise separation depth) — no limit needed; the depth-D
  divergence = the construction's per-depth optimum ≤ Adv, and ≥ via
  adv_le_Δ. So the rebuild recursion runs on histories (no fuel), and the
  δ computation closes at a finite depth.
- **Infinite-X: RESOLVED by user ruling (2026-07-18) — case distinction on
  query CLASSES, not on x.** Statement stays arbitrary-X as posed. Proof
  shape for `rebuild_support_finite` (now a plan, not a conjecture):
  (i) at any node, x acts on the finite atom sets only through its induced
  answer-pattern (⊥ included) + mass profile; finitely many atoms ⇒
  finitely many classes; τ-values range in a finite set (cell masses
  through ≤ |supp S|+|supp T| separation events; between separations τ
  passes through unchanged or hits 0 on matched-end mismatch; trimming
  factors τ/τ_x stay in the finite ring).
  (ii) cross-x joint constraints live ONLY at each node's top level —
  below (x,y) the alignment is local to the branch — so one finite common
  refinement of the class profiles gives a finite-support joint uniformly
  in x; rebuilt support size = top piece count, and deeper atom choices
  are functions of the top piece.
  (iii) the trivial class: queries where all atoms answer ⊥ pass through
  via the skip-aware successor (successor s x = s); genuinely mismatched
  domains are OBSERVABLE differences (⊥ is an answer) counted in Adv —
  "non-compatible ones are trivially not equiv". Same move that removed
  the same-domain hypothesis removes the finite-alphabet one.
  (iv) the thesis's max over X′ becomes a sup attained because the value
  set is finite (and globally we already have exists_adv_eq_δ_transcriptDist).

OPEN (must settle before coding): finiteness of the coupling's support.
Conjecture: rebuilt threads are labeled by reachable (cell of F_S) ×
(cell of F_T ∪ {solo}) refinement trees; the cell-pair lattice is finite
and only refines down each branch, so distinct threads ≤ O(2^|F| · 2^|F|);
prove as `rebuild_support_finite` before anything else — if it fails, the
whole Finsupp carrier fails and we need the thesis's own Lemma-6 object
re-examined. Second open point: whether the thesis 2.31 proof (re-read it
verbatim before coding!) already gives the flow construction in a form
closer to Lean — the attainment theorem removes its q-induction shell, so
only its joint/alignment core is needed.

Everything below goes into `RandomSystems/RandomSystem.lean` once the successor-agent
lands. Prereqs already proven: `δ_fTransform_le`, `δ_sum_of_disjoint_support`,
`adv_le_Δ`; in flight: `transcript_successor`, `transcriptDist_successor`.

## 1. Stabilization (replaces the paper's q-induction)

```lean
-- fuel-monotonicity: splitting transcript cells can only grow δ
theorem δ_transcriptDist_mono (S T : PFunPDS X Y) (e) :
    Monotone fun n => δ (transcriptDist S e n) (transcriptDist T e n)
```
Proof: transcript at fuel n is a deterministic function of the fuel-(n+1)
transcript (`if t.length = n+1 then t.dropLast else t`, stall is absorbing);
so trDist at n = fTransform of trDist at n+1; apply `δ_fTransform_le`.
(Needs the recoverability lemma `transcript_eq_of_transcript_succ` — prove via
`transcript_length_le` + the stall lemmas already in the AcceptSet section.)

```lean
-- the δ value is determined by the induced partition of the finite support set,
-- hence ranges in a finite set; monotone ⇒ sup attained
theorem adv_attained (S T : PFunPDS X Y) :
    ∃ e n, Adv S T = (δ (transcriptDist S e n) (transcriptDist T e n) : ℝ)
```
Route: let F := S.support ∪ T.support (Finset). Map (e,n) to the partition
setoid on F induced by `transcript · e n`-equality. δ(trD S e n, trD T e n)
= Σ over cells C of (S(C) − T(C))⁺ — prove as lemma
`δ_transcriptDist_eq_partition_sum`. The set of partitions of F is finite
(functions F → Finset F …); so the Adv-sup set is a finite set of reals; csSup
of a nonempty finite set is a member (`Set.Nonempty.csSup_mem` + finiteness via
image of a finite type). NB: do NOT go through per-e stabilization — directly:
the value set is finite because each value is determined by a partition.

## 2. Rebuild (the attainment construction)

State: pairs of sub-distributions (node states). Define by recursion on
history length (corecursion is unnecessary — every history is finite):

```lean
noncomputable def rebuild (S T : PFunPDS X Y) : PFunDDS.DDS X Y → PFunDDS.DDS X Y
```
`rebuild S T s` answers history (x₁,…,xₖ) by walking node states:
node₀ = (S,T); nodeᵢ₊₁ = (successorTransform Sᵢ xᵢ₊₁ yᵢ₊₁, successorTransform Tᵢ xᵢ₊₁ yᵢ₊₁)
where yᵢ₊₁ = s's own answer along its own successor chain. The REBUILT atom's
answer at each node = the answer of the aligned representative: at node u with
state (Sᵤ, Tᵤ), fix a common-part alignment of the answer distributions
(quantile alignment on an ordering of first answers; only the OVERLAP mass must
map S-atoms and T-atoms to the SAME rebuilt continuation). Invariant to prove:
per-depth diverged mass of (fTransform (rebuild S T) S, fTransform (rebuild S T′?) …)
equals the max fuel-n advantage — by `transcriptDist_successor` +
`δ_sum_of_disjoint_support` + induction on depth.
Note: S′ := fTransform (rebuild …) S is a transform of S itself, so the
"joint over all first queries" (paper Lemma 6, footnote 11) exists even for
infinite X — never build a literal product coupling.

Validation example (must survive as a sanity check): self-destruct systems,
S = ½(s₂+s₃), T = s₀: rebuild must output S′ = ½ s₂₃ + ½ s₀, T′ = s₀, δ = ½ = Adv.

## 3. Assembly

- `Δ_eq_adv`: `le_antisymm (csInf_le (bddBelow_Δ_set S T) ⟨S', T', hS', hT', rfl⟩ …) (adv_le_Δ S T)`
  after rewriting attainment δ(S',T') = Adv.
- `coupling_theorem`: **statement correction needed** — as posed (no hypotheses)
  it is FALSE for |S| ≠ |T| (no joint has marginals of different weights;
  equivalence preserves weight via fuel-0 transcripts). Add
  `(hS : S.isProbDist) (hT : T.isProbDist)` (thesis 2.32 is about random
  systems = weight 1). Then: attainment pair + equal-weight optimal coupling.
  Coupling.lean's `optimal_coupling_exists` is Fintype-bound: generalize by
  transporting along the finite support union (Finsupp.subtypeDomain /
  embedding pushforward), or reprove `optimalJoint` Finsupp-natively — flag as
  its own work item.

## 4. Execution status (2026-07-19) and the reshaped Lemma-2.33 statement

Landed in RandomSystem.lean, all green (milestone reports in session logs):
- M1 prepend: `prepend x y`, inversion laws, injectivity (some-only — the
  ⊥-prepend is NECESSARILY non-injective: prefix closure forces carving the
  whole x-headed cone), `prependTransform` round-trip + δ-preservation.
- M2 per-x reassembly: `prepend_ne_of_ne`, pairwise-disjoint supports,
  `δ_sum_prependTransform`, `successorTransform_sum_prependTransform`,
  weight bookkeeping, per-answer transcript decomposition (per-fuel).
- M3a overlap calculus (`commonPart` = zipWith min, unconditional
  `δ_eq_weight_sub_weight_commonPart`, `weight_smul`/`δ_smul`) + `glue`
  constructor (structural match; `output_fullyDefined_glue` by rfl;
  skip-case `successor_glue_of_not_mem = glue g` — pass-through) +
  glue/prepend profile realization.

M3b statement RESHAPED (three approved deviations from §2's sketch):
1. Finite classes live on PRE-PREPEND branch data (`cls : X → I`, Finset C
  of realized classes) — x ↦ reassembled S'_x is essentially injective, so
  the naive finite-image hypothesis is unsatisfiable.
2. NO ⊥-branch representatives: `successorTransform · x none` is a FILTER
  (skip-aware successor = identity there), so the joint's ⊥-branch is the
  joint itself filtered — self-similar, consumed directly by the M4
  recursion. (i-none) is weight bookkeeping only. Data per class: answered
  values `vs i` + branch reps `Bs Bt : I → Y → PFunPDS`.
3. δ-law in OVERLAP form with separate weights:
  `(δ J_S J_T : ℝ) = max_{i ∈ C} (w_S − overlap_i)`,
  `overlap_i := Σ_{v ∈ vs i} |commonPart (Bs i v) (Bt i v)| + min(βS_i, βT_i)`,
  β = residual ⊥-mass — ⊥-⊥ pairs couple maximally AT the node, divergence
  deferred to depth (stabilization). Fallback license: single-w if separate
  weights break the cross-class refinement (then assembly pre-splits).
Construction: glue-profile atoms (per class: (v, continuation) or the empty
x-slice via a local `DDS.empty`), masses from a finite common refinement
over C by binary trims (smul calculus). M4 then: depth recursion on the
filtered joint + separation-lattice finiteness discharge + assembly (§3).

## 5. M4 stage-0 obstruction and the stratified design (2026-07-19, acked)

**OBSTRUCTION (model fact, counterexample-verified)**: independent
cross-class profile coupling breaks EQUIVALENCE. With skip semantics a
⊥-answer does not leave the node, so one environment can probe several
first queries in one interaction — cross-class correlations INVOLVING
⊥-choices are observable. Counterexample: X = {x₁,x₂}, S = T = ½s₁ + ½s₂,
s_i answers only x_i: the 3b joint gives P(⊥x₁ ∧ ⊥x₂) = ¼, the original 0;
e = (x₁ then x₂) sees it. The thesis's arbitrary-joint freedom (fn. 8)
covers only answered-choice correlations — it silently relies on totalized
systems. (Same ⊥-observability theme as the successor ruling, eq. 6.1's
properness conjunct, and StopsReplying.)

**FIX — ⊥-pattern stratification (δ-lossless)**: stratify each node by the
atoms' ⊥-pattern σ (which classes an atom answers): ≤ |supp S| + |supp T|
realized patterns, finiteness free. Within a cell the pattern is
deterministic, so arbitrary coupling is safe (thesis situation restored per
cell); 3b is already pattern-correct per cell (C := σ's classes; the
profile default-none outside C IS the pattern). Node rebuild = Σ_σ J^σ;
cells are support-disjoint ⇒ δ adds (δ_sum_of_disjoint_support).
Stratification loses no overlap: different patterns ⇒ different trees ⇒
cross-pattern coupling could never share atoms anyway.

**Within cells — interval-piece indexing** (replaces literal data-classes,
which are infinite for arbitrary X — the injective-f atom): pieces of the
common refinement of [0,w]; a piece fixes the full deterministic profile
(finite sum of point masses replaces jointProfileList); shared region
[0,τ) has literally equal glue atoms on both sides. All other 3b machinery
transfers verbatim.

**Finiteness — CORRECTED (stage-B stop-clause, 2026-07-19)**: the stage-0
"node-local, no global closure" claim was too strong — at fuel n+1 the
per-x layout masses are the REBUILT branches' piece-masses, not subsums of
the top node's atoms. Repair (acked): a fuel-indexed value Finset `V_n`
(V_0 = subsums of the node pair; V_{n+1} = one closure round: the
nodeCuts shape a + c + (e − f), a tsub round, a bounded subsums round),
with the invariant `subsums(rebuild n) ⊆ V_n` carried INSIDE the rebuild
induction next to equivalence and the δ-invariant. Sound because
successorTransform is filter+shift — deeper pairs keep original atom
masses on smaller supports, so one V_n from the top pair bounds all per-x
deeper rebuilds uniformly (subsums monotone under support-subsets, an
explicit B0 lemma). This restores §2/§22's original bottom-up phrasing
(finite value set along ≤ n separation levels); stage A's containment
lemma is consumed at the V_n-bounded instances. Stage B gains sub-stage
B0 (~150–250 lines); nothing else in the design moves.

**Recursion**: fuel-indexed; rebuild 0 = id; answered branches recurse at
lower fuel on successor pairs; ⊥-branches recurse on the FILTERED node at
lower fuel (self-similarity holds at the cell-sum level). Stage C needs
the Adv-unfold WITH the ⊥-recursion term:
sup_e δ_{n+1} = sup_x [Σ_v (answered sups at fuel n) + (⊥-filtered sup at
fuel n)]. Stages: (A) nodeCuts + containment, (B) interval-joint +
stratification + fuel-induction equivalence, (C) Adv-unfold + δ-induction,
(D) le_antisymm assembly.
