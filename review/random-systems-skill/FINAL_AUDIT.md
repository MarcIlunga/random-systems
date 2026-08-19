# Final audit receipt: `random-systems-proofs`

Date: 2026-08-06

> **Historical snapshot.** The hashes in this receipt were superseded later
> on 2026-08-06 by the audited distance-first architecture correction. The
> current release and hashes are recorded in
> `DISTANCE_FIRST_DELTA_AUDIT.md`. The findings and validation below remain the
> historical basis of that corrected release.

## Outcome

The concern that triggered this audit was justified. The frozen original skill
was materially unsafe as a factual guide. It contained false universal claims,
mixed distinct proof notions, omitted theorem hypotheses, presented finite
tactic bundles as semantic diagnostics, generalized query compression beyond
its proved scope, and described admitted or non-building routes as completed.

The installed skill has been rewritten and independently release-audited. At
the hashes below:

- both full post-rewrite audits report **PASS**;
- there are zero open blocking findings;
- there are zero open nonblocking findings;
- all 1,182 release lines have two full coverage receipts;
- every quoted Lean signature and namespace has a focused check;
- primary-source interpretations were checked on rendered pages; and
- three blind behavioral tests pass.

This is a release verdict for the skill package. It is not a claim that every
referenced Lean module currently builds.

## Audit structure

### Frozen-original reviews

| Partition | First review | Second review | Resolution |
| --- | --- | --- | --- |
| Strict CE and related terminology | `ce-audit-a.md` | `ce-audit-b.md` | claim-level reconciled |
| Core skill, UI metadata, planning | `core-and-plan-audit.md` | `core-and-plan-audit-b.md` | claim-level reconciled |
| H, counting, reshaping, creative search | `families-audit.md` | `original-families-audit-b2.md` | claim-level reconciled |

`RECONCILIATION.md` records every substantive verdict difference and resolves
it from a primary paper, current declaration, focused build, or direct
counterexample. No resolution was selected by majority vote.

The review protocol was not described as more independent than it was:

- CE review B saw the neutral claim index but not review A's verdicts.
- Original-family review B2 was forced by the governing skill rule to read the
  current core `SKILL.md`, but it did not read the current references or any
  other verdict report. It also disclosed accidental exposure to three
  declaration names from a probe.
- The contaminated H selector claim received a separate clean third source
  check in `POST_REWRITE_AUDIT_B.md`.
- `families-audit-b.md` audited rewritten family files and is therefore treated
  only as extra release evidence, not as the second frozen-original review.

All three frozen-original partitions are coverage-mapped and reconciled; no
substantive mathematical disagreement remains open.

### Corrected-release reviews

- `POST_REWRITE_AUDIT_A.md` audited the full package, identified eight release
  corrections, and appended a post-correction delta receipt.
- `POST_REWRITE_AUDIT_B.md` independently audited the final target without
  reading the review directory. It found two additional intermediate defects,
  both corrected before its final freeze, then reread the changed files.

Both reports independently approve the same final hashes and record full line
coverage.

## Major defects removed

The rewrite removes or corrects these high-risk claims:

1. **Method conflation.** Strict one-sided CE, MPR symmetric monitored games,
   H predicates, honest couplings, representative attainment, winnability, and
   signed expansions now have separate definitions and proof obligations.
2. **Automatic CE refinement.** A smaller monitor no longer purports to inherit
   monotonicity, CE, or a better bound. Every changed monitor requires fresh
   proofs.
3. **False completeness.** The skill no longer advertises a closed family
   taxonomy, complete tactic procedures, or a theorem route for every security
   statement.
4. **Tactic diagnosis.** Failure of `cr18_total`, `cr18_prob`, or an H tactic is
   no longer treated as proof that the model is wrong.
5. **Query compression.** `compressedQuery_bound` is correctly described as a
   numerical lemma. Exact evaluator-law compression is separated from generic
   stateful/adaptive querying.
6. **Coupling scope.** `optimal_probability_coupling_exists` is correctly
   limited to two displayed normalized laws and raw `δ`. Representative-level
   adaptive attainment requires its separate finite/common-domain/bounded
   theorem.
7. **Winnability.** Thesis Theorem 2.37 is stated as
   `ν(S^A) = ω(S^A)` plus attainment, not as a generic `Delta <= ν(S^A)`
   inequality or an MBO theorem.
8. **Schedules.** The fixed `blindQueryList` quantifier is restricted to the
   packaged blind CE wrapper. Ordinary H still quantifies over every adaptive
   `QQueryEnvironment`.
9. **Metrics and orientation.** Nonnegativity, normalization, and common-domain
   premises are explicit; the false deletion/rewind explanation is gone.
10. **Build and admission status.** Broken, admitted, or migration-blocked
    modules are quarantined with dated, snapshot-sensitive instructions rather
    than presented as completed evidence.
11. **Workflow rhetoric.** Unsupported measurements, superlatives, absolute
    API rules, and multi-agent causal claims have been deleted or clearly
    labelled as policy.
12. **Scope.** The skill now routes Random Systems obligations and RS leaves
    inside CC work. It explicitly does not claim to route complete CC
    composition, AC lifting, or multi-interface indifferentiability assembly.

## Final package hashes

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `SKILL.md` | 213 | `13e8c3e354c53224acaf078ff3d6cfb1d49d28ef86cfb94ca0005e6548c652f4` |
| `agents/openai.yaml` | 4 | `bad0bebb58f9cbe877b09bf9689dc87d247fca2d66de6f51e2436417f2687db2` |
| `references/conditional-equivalence.md` | 195 | `726ff1ac7c72da67162b0b5e0e2c90d8afb23c305f4a44b4c058f20fab66aea9` |
| `references/counting.md` | 138 | `32cb22ad7b078ac886105670f91202603463e0d6b1660c7a5dd4cf9e624d76db` |
| `references/creative-search.md` | 117 | `6d71c6aa3ef1797d054b2dced348630e4e3c6fd35778f6e8da0991e45eb2341e` |
| `references/h-technique.md` | 162 | `6cf1b96c9d42ae60d3e55ea564d52f416d1431fd1b79e771d747ae434d6bdb6d` |
| `references/reshape-and-exact.md` | 192 | `a334bb31f3855892f74d1a0eb4da402328b8c828c1b419d1605767a754e93f10` |
| `references/sketch-and-plan.md` | 161 | `c833cf687a05ae9e2b05065d6e2ce9578d8907b615fbe21530983f533a70a019` |

## Validation receipts

- Skill schema/frontmatter validation: **PASS**.
- Internal Markdown files and table-of-contents anchors: **PASS**.
- UI metadata and `$random-systems-proofs` invocation token: **PASS**.
- `review/random-systems-skill/audit-probes/RewrittenSurfaceProbe.lean`:
  **PASS**; it checks the quoted CE, H, counting, compression, coupling,
  orientation, and strict-metric surfaces and compiles the displayed H
  application shape.
- `review/random-systems-skill/audit-probes/CBCReceiptProbe.lean`: **PASS**;
  the completed CBC CE lemma has no `sorryAx`.
- Final headline axiom checks recorded by both release audits contain only the
  expected standard axioms (`propext`, `Classical.choice`, `Quot.sound`) for
  the checked completed endpoints.
- No broad iterative build was used; checks followed the repository's focused
  development policy.

## Behavioral forward tests

`FORWARD_TESTS.md` records three fresh-agent tests performed without audit
access. All passed:

1. smaller CE monitor: rejected automatic refinement and recovered every exact
   obligation and schedule quantifier;
2. maximal coupling plus compression: separated raw-law, representative, and
   adaptive layers and rejected generic compression; and
3. tactic failure: treated it as an import/registration/goal-shape diagnostic,
   not evidence that the model is invalid.

## Remaining repository quarantines

The corrected skill accurately reports, but does not repair, the current
problems in these proof surfaces:

- H-technique SoP migration and aggregate tactic import;
- `CBCStructureGraph.lean` and its admitted central count;
- `GameWinnability` / `LanzenbergerChain` build migration;
- legacy amplification and related legacy import failures; and
- other files identified in `STATUS.md`.

These are not hidden by the release verdict. Any future use must consult the
current `STATUS.md`, run the named focused check, and obtain an axiom receipt
after elaboration.

## Audit artifacts

- `AUDIT_PLAN.md` — policy, frozen hashes, and release gate.
- `CE_CLAIM_INDEX.md` — neutral CE coverage index.
- `ce-audit-a.md`, `ce-audit-b.md` — frozen CE reviews.
- `core-and-plan-audit.md`, `core-and-plan-audit-b.md` — frozen core reviews.
- `families-audit.md`, `original-families-audit-b2.md` — frozen family reviews.
- `families-audit-b.md` — extra partial audit of the rewritten family files.
- `RECONCILIATION.md` — source-resolved original-snapshot reconciliation.
- `POST_REWRITE_AUDIT_A.md`, `POST_REWRITE_AUDIT_B.md` — final release audits.
- `FORWARD_TESTS.md` — blind behavioral checks.
- `audit-probes/` — focused Lean receipts and deliberate tactic-failure probes.

## Final disposition

The frozen original skill must not be reused. This historical rewritten
snapshot was release-approved and has since been superseded by the
distance-first revision in `DISTANCE_FIRST_DELTA_AUDIT.md`. The governing
principle is unchanged: primary papers and current Lean declarations, builds,
and axiom receipts outrank the skill prose.
