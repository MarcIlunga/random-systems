# Stable-v1 SequenceHash MD simulator — formalization sketch

This formalization targets the short-customization ideal-compression theorem of
`papers/notes/SEQUENCEHASH_MD_SMART_SIMULATOR.md`.  The real construction and
the ideal simulator are represented by one executable machine whose two tapes
are correlated in the real world and independent in the ideal world.  The
correctness proof unfolds that executor and splits its actual lookup, parser,
and equality observations.  Consequently Lean, rather than a separately
maintained case enumeration, generates the complete list of simulator cases.

## 1. Objects and scope

- `C` is the finite chaining-value type, with `N = |C| > 0`.
- `B` is the compression-block type.
- `X` is the accepted SequenceHash input-sequence type.
- `I : X -> List B` is the complete strengthened inner block word.
- `O : Tag -> C -> List B` is the complete strengthened outer block word.
- `f : C × B -> C` is the ideal compression function.
- `R : X -> C` is the ideal random oracle.
- `T : C × B ⇀ C` is the simulator's lazy compression table.

The initial theorem assumes the stable-v1 short-customization grammar:

1. `I` is injective;
2. complete outer words decode their tag and embedded chaining value uniquely;
3. inner and outer words have distinct first blocks;
4. complete outer words are not proper prefixes of construction words; and
5. the MD block codec and strengthening are injective.

The byte-level stable-v1 realization is a separate layer.  Long customization,
where `S'` itself is obtained through a hidden MD path, is not in this theorem.

## 2. Claim

For every adaptive distinguisher making `a` distinct construction queries and
`q` distinct direct compression queries, with total compression workload
`sigma`,

$$
\Delta\bigl((\operatorname{Seq}_f,f),(R,\Sigma^R)\bigr)
\le
\min\!\left\{
1,
\frac{\binom{\sigma-a+1}{2}+q(\sigma-a)}{N}
+\frac{qa(N-1)}{N^2}
\right\}.
$$

The first compiled milestone is the exact one-step simulator theorem and its
conditional-equivalence lift.  The finite workload theorem follows after the
join and link counts are attached.

## 3. Native transition tree

The first prototype flattened the execution into a hand-written
`PrimitiveCase` enum.  That checks that every *listed* constructor is handled,
but it cannot check that the list itself omitted no semantic distinction.  The
compiled model therefore uses no flattened transition enum.

Lean eliminates the source observations directly, in this order:

1. the public interface tag (`eval` or `prim`);
2. construction-query membership (`seen` or fresh);
3. primitive table lookup (`some answer` or `none`);
4. root-path lookup (`some path` or `none`);
5. every constructor of `WordClass`;
6. on an outer completion, inner-endpoint lookup (`some input` or `none`);
7. when an input is present, tag equality (true or false); and
8. after a live sample, equality with `IV`, lookup in the live-word table,
   membership in the loose-root set, or freshness.

This exposes eleven top-level leaves: repeated/fresh construction queries and
nine primitive leaves.  In particular, an unknown inner endpoint and a known
endpoint carrying the wrong tag are different proof obligations even though
both execute the same pending-terminal action.  Destination propagation adds
four independent obligations: `IV`, existing live state, loose root, and fresh
state.

`evalStep_cases`, `primitiveStep_cases`, and `propagate_cases` are reusable
eliminators for these native observations.  Their proofs contain no
wildcard/default branch.  More importantly, the representative-correctness
theorem `primitive_step_correlated_answer_eq` does not trust even that premise
list: it unfolds `primitiveStep` and uses nested `split` calls.  Each proof goal
therefore comes from a live `match` or `if` in the executor itself.

## 4. Argument

The simulator keeps the compression table, unique live words, completed inner
endpoints, pending outer terminals, and ghost paths for construction calls not
visible at the compression interface.

On a good history, repeated points return their table value.  A fresh
nonterminal point receives a uniform chaining value.  A linked outer terminal
receives `R(x)`.  An unlinked terminal is stored as pending.  Queries made out
of order create loose roots; any later meeting with a hidden construction path
is a join.

The pending-link proof is sequential.  It maintains the posterior law of the
hidden inner endpoint after every interleaving of construction answers and
outer-site queries.  At an occupied site the real and ideal transition kernels
have a maximal common part; its missing mass is `(N-1)/N^2` times the current
posterior mass of that site.  Summing before absolute values gives the static
`c(N-1)/N^2` law and remains valid when the construction answer was revealed
before the outer queries.

The deferred-path lemma gives the real system a lazy representative in which
unobserved internal compression assignments are ghost entries.  Revealing a
ghost entry, or using it in a construction computation, has the same marginal
as eagerly sampling the random-function table.  This is the formal reason the
simulator need not be notified of construction queries.

The generated case theorem then proves that every good next-answer kernel has
an exact common carrier, with loss only in `Join` or the pending-link residual.
The common carrier is packaged as two monotone games with equal pre-winning
transcript mass.  This is the exact game-equivalence premise consumed by the
Theorem 4.17 chain; unlike literal conditional equivalence, it does not require
the retained carrier by itself to be proportional to the complete ideal law.
The existing blind reduction removes adaptivity from the remaining bad-mass
calculation.

## 5. Technique and rejected route

Technique: the pre-winning/game-equivalence core of the conditional-equivalence
method, using a common-carrier representative.  When the retained carrier is
proportional to the ideal law this specializes to literal conditional
equivalence.  The occupied-link carrier is pointwise maximal but generally not
proportional, so the exact coefficient uses the strictly more direct
`MassYAfalseEq` endpoint already present in the random-systems framework.

Rejected: a transcript-only H-coefficient proof.  It can establish a bound,
but it does not expose the simulator state or force the proof to enumerate
every adaptive query order.  Exhaustive transition coverage is a goal of this
formalization, not merely a route to the numerical estimate.

## 6. Adaptation from DRST

| DRST component | Effect here | Reason |
|---|---|---|
| allowed-key parser | kills | SequenceHash uses the fixed empty key |
| colored inner/outer oracle | kills | stable v1 begins with distinct `0x55` and `0xaa` blocks |
| inner/outer role ambiguity | kills | the first block determines the role |
| generic graph collisions | leaves | random chaining states may still merge or hit `IV` |
| out-of-order primitive guesses | leaves | these are the loose-root join cases |
| preimage-awareness loss | shrinks/replaces | exact occupied-link common carrier charges only actual occupied sites |
| long-customization MD path | excluded | it introduces a third path and second hidden link |

## 7. Obligation DAG

### `grammar_cases`

- Statement: every complete or extendable block word has a unique role and
  decode; complete outer words cannot extend a construction word.
- Class: `[CREATIVE]` at the abstract grammar layer; byte realization follows.
- Depends: none.

### `request_classification`

- Statement: `classify` is total, its constructors are disjoint, and its data
  reconstruct the queried table point.
- Class: `[ROUTINE]` once parsers are decidable.
- Depends: `grammar_cases`.

### `sample_classification`

- Statement: every sampled chaining value is either fresh, `IV`, a live state,
  or a loose root; the cases are exhaustive and disjoint under `Good`.
- Class: `[ROUTINE]` finite-set decision procedure.
- Depends: none.

### `lazy_table_marginal`

- Statement: lookup-or-uniform insertion is exactly a random-function
  transition and repeated lookup is deterministic.
- Class: `[LIB]` or general framework lemma.
- Depends: none.

### `deferred_construction_paths`

- Statement: eager hidden construction evaluation and the ghost/deferred table
  representative have identical observable transcript laws.
- Class: `[CREATIVE]`.
- Depends: `lazy_table_marginal`.

### `occupied_link_common_part`

- Statement: for `c` occupied sites, the real link law and independent ideal
  law have exact distance `c(N-1)/N^2`, with exact marginals.
- Class: `[CREATIVE]` finite-distribution calculation.
- Depends: none.

### `causal_pending_invariant`

- Statement: the hidden-endpoint posterior and common-carrier invariant are
  preserved for construction-first, outer-first, and arbitrarily interleaved
  query orders; cumulative loss is the occupied-link deficit.
- Class: `[CREATIVE]`.
- Depends: `occupied_link_common_part`, `lazy_table_marginal`.

### `graph_invariant_by_case`

- Statement: each constructor generated by `classify` either preserves unique
  typed paths or produces a named `Join` constructor.
- Class: `[CREATIVE]`, with one Lean-generated goal per classifier constructor.
- Depends: `grammar_cases`, `request_classification`, `sample_classification`.

### `terminal_programming_legal`

- Statement: before bad, a linked terminal has one obligation and assigning
  `R(x)` preserves both primitive and random-oracle marginals.
- Class: `[CREATIVE]`.
- Depends: `graph_invariant_by_case`, `causal_pending_invariant`.

### `one_step_common_carrier`

- Statement: for every good state and external request, the real and ideal
  next-transition laws have exact marginals and agree on the retained branch.
- Class: `[CREATIVE]`; proof is exhaustive elimination of `classify`.
- Depends: `deferred_construction_paths`, `causal_pending_invariant`,
  `graph_invariant_by_case`, `terminal_programming_legal`.

### `prewinning_equivalence`

- Statement: induction of `one_step_common_carrier` over arbitrary adaptive
  transcripts yields equal not-won transcript masses for monitored real and
  ideal games; stripping their MBOs gives the two target systems.
- Class: `[LIB]` endpoint plus `[CREATIVE]` step invariant.
- Depends: `one_step_common_carrier`.

### `bad_monotone`

- Statement: once a join or link failure occurs it remains true.
- Class: `[ROUTINE]`.
- Depends: none.
- Verdict: **REUSE** `seededHistoryConditionCGame_monotoneMBO`; the only
  construction-specific premise is the compiled
  `simulatorJoinAudit_prefix`.  There is no scheme-specific game wrapper or
  stripping theorem.

### `join_mass`

- Statement: with `s` critical states and `q` loose roots, join mass is at most
  `(choose (s+1) 2 + q*s)/N`.
- Class: `[CREATIVE]` cover plus standard union-bound leaves.
- Depends: `sample_classification`.

### `link_mass`

- Statement: the cumulative pending-link loss is at most
  `q*a*(N-1)/N^2`.
- Class: `[CREATIVE]` counting after the blind reduction.
- Depends: `causal_pending_invariant`.

### `indifferentiability_bound`

- Statement: the exact finite bound above, followed by the `2*sigma^2/N`
  corollary.
- Class: `[LIB]` pre-winning-equivalence endpoint plus `[ROUTINE]` arithmetic.
- Depends: `prewinning_equivalence`, `bad_monotone`, `join_mass`, `link_mass`.

## 8. Required receipts

1. The skeleton compiles with a visible goal for every native observation
   leaf, without relying on a curated transition enum.
2. The finished files contain no `sorry` or `admit`.
3. `#print axioms` for every public endpoint contains only accepted foundational
   axioms.
4. Mutation receipt (2026-08-05): temporarily adding `WordClass.auditOnly`
   makes Lean reject the executor with `Missing cases: WordClass.auditOnly`
   and reject the proof eliminator with
   `Alternative auditOnly has not been provided`.  Removing the mutation
   restores a clean single-file check.
5. The stable-v1 byte realization is kept separate from the abstract simulator
   theorem, so the theorem cannot silently reuse the old v0.1 schedule.
6. `real_machine_to_dds_eq_correlated_simulator` and
   `real_p_eq_correlated` compile: the ordinary real construction is exactly
   the common simulator driven by correlated tapes.
7. `commonCarrierGame_massYAfalseEq` compiles: any two residual laws placed
   above one common carrier give identical pre-winning transcript masses, and
   `ignoreMBO_commonCarrierGame` reconstructs the corresponding untagged law.

Current receipt: the generic history-condition framework, the exact
history-evaluator presentations, and the complete audit-prefix theorem compile
without admissions.  The next creative node is the causal occupied-link and
deferred-path common-carrier invariant.

## 9. Reuse-search verdicts

The search order was `CHEATSHEET.md`, repository grep, then Lean local search.

| DAG node | Verdict |
|---|---|
| tagged external interface | **REUSE** `RandomSystems.HTechnique.IdealCompression.TaggedQuery` and `TaggedReply`; only the datatypes are reused, not the H-technique proof route |
| stateful simulator denotation | **REUSE** `RandomSystems.CR18.TypedResource.Machine`, `Machine.toDDS`, `Machine.lawOf`, and `DependentPDS.Prob.flatten` |
| request/sample classification | **NEW**, after searches for `StateMachine`, lazy-table, simulator-table, and transition-classifier infrastructure returned no applicable declaration |
| lazy random-function evaluation | **ADAPT** `Dist.uniform`, `uniform_mass_eval`, and the uniform-function fiber lemmas into a public lookup/reveal lemma; no lazy table theorem exists |
| overlap/common carrier | **ADAPT** the private `commonPart`/`excess` development currently quarantined in `RandomSystem.lean`; upstream the scheme-independent definitions and lemmas publicly to `Dist` rather than copying them locally |
| occupied-link calculation | **NEW**, using `Dist.ofFiniteMassFunction`, `statDist_eq_mass_sub_mass_pos`, and the public common-part API |
| causal pending invariant | **NEW**; searches for occupied-link, pending-link, posterior, and causal-common-carrier lemmas found no implementation |
| hidden-path deferral | **NEW**, based on the uniform-function evaluator and `Machine` replay semantics |
| generated graph cases | **NEW**, implemented by exhaustive elimination of the classifier inductives |
| conditional-equivalence relation | **REUSE** `CondEquiv`, `massYAfalse`, `massY`, `massAfalse`, `massDom`, and `massDom_eq_one_of_totalOnNonempty` |
| adaptive-to-blind endpoint | **REUSE** `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`; the last-query-only wrapper is too narrow for the stateful simulator target |
| monitored real game | **REUSE/ADAPT** `seededConditionCGame` for the real last-query evaluator; if the common-carrier seed requires a genuinely history-dependent retained representative, generalize the existing history-evaluator monitor publicly rather than adding a scheme-local copy |
| join/link union bounds | **REUSE** `mass_biUnion_le`, `mass_le_pairCollisionUnionBound_of_cover`, and `pairCollisionUnionBound_le_birthday`; only the SequenceHash event cover and leaf probabilities are new |
| MD execution | **REUSE** `SequenceHash.MDCodec`, `mdIterate`, `mdIterate_append`, and `mdHash` |
| stable-v1 grammar realization | **NEW**; the current Lean schedule is v0.1 and cannot discharge this node |
