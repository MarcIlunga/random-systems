# Random Systems proof skill: independent claim audit

## Purpose

The skill is frozen for evidentiary review after its conditional-equivalence
guidance was found to conflate three distinct notions:

1. strict one-sided conditional equivalence;
2. symmetric equivalence of two systems with monotone-bit outputs; and
3. selection of equivalent PDS representatives.

The audit does not treat the skill, repository prose, or another reviewer's
report as evidence.  Mathematical claims must be checked against the cited
primary paper.  Claims about the formal library must be checked against the
current declaration and, where practical, by `#check` or a focused Lean file.

## Unit of review

A review unit is one independently checkable assertion, including:

- a definition or theorem attributed to a paper;
- a claimed implication of a theorem;
- a declaration name, signature, file, or line number;
- a claim that a tactic discharges a class of goals;
- a claim that a proof route applies to a named construction;
- a claim that a reduction removes adaptivity or fixes a schedule;
- a quantitative or asymptotic statement;
- a statement that two proof notions are equivalent, complete, optimal, or
  interchangeable.

Pure instructions and preferences are labeled `NORMATIVE`, not silently
treated as facts.

## Verdicts

| Verdict | Meaning |
| --- | --- |
| `VERIFIED` | The wording follows from the cited primary source or current declaration. |
| `OVERSTATED` | A narrower statement is supported, but the written statement is not. |
| `FALSE` | A counterexample or the cited source contradicts the statement. |
| `STALE` | It described an earlier library surface but not the current one. |
| `UNVERIFIED` | No adequate primary evidence was found. It must not remain as factual guidance. |
| `NORMATIVE` | Workflow advice rather than a mathematical or library fact. |

## Evidence standard

Every non-normative verdict records:

1. the skill file and exact line span;
2. the smallest standalone claim being reviewed;
3. the verdict;
4. a primary PDF page or current Lean declaration;
5. the logical step from the evidence to the verdict;
6. conservative replacement wording, or `DELETE`.

Secondary notes may locate a source but cannot verify a claim.  Search output
alone cannot verify theorem content.  A declaration name alone cannot verify
the prose interpretation placed on it.

## Independence rule

Reviewers receive the source files and primary evidence locations, but not
another reviewer's conclusions.  Every factual review unit is independently
reviewed twice.  The second reviewer writes a verdict before reading the first
report.  Disagreements are resolved by a third direct inspection, not by
majority vote.

## Coverage map

### Wave 1: conditional equivalence and terminology

- `references/conditional-equivalence.md`: every factual claim.
- `references/creative-search.md`, section “The proof object controls the
  bound”: every factual claim.
- CE routing and CE-specific claims in `SKILL.md`.
- Related claims in `references/reshape-and-exact.md`.

Required primary sources: CR18 Definitions 4.16 and 4.19 and Theorem 4.17;
Maurer--Pietrzak--Renner Lemma 5; Lanzenberger Definitions 2.17 and the cited
attainment theorems; current `CondEquiv`, `GameOf`, and `SwitchingLemma` Lean
declarations.

### Wave 2: core routing and automation

- `SKILL.md` frontmatter and `agents/openai.yaml`.
- `SKILL.md`: all remaining factual claims, tactic capability claims, theorem
  names, file status claims, and “always/never” assertions with factual
  premises.
- `references/sketch-and-plan.md`.

### Wave 3: proof-family references

- `references/h-technique.md`.
- `references/counting.md`.
- `references/reshape-and-exact.md` outside the CE overlap.
- `references/creative-search.md` outside the CE overlap, including any
  empirical claim about multi-agent research.

### Wave 4: blind cross-review

The three partitions above are reassigned so that a different reviewer repeats
each audit without reading the first report.  Only after both reports are
sealed are their verdicts joined by claim identifier.

## Release gate

The skill is not considered audited until:

- every line range is covered by a report;
- every factual review unit has two independent verdicts;
- every factual review unit has a verdict and evidence;
- all `FALSE`, `OVERSTATED`, `STALE`, and `UNVERIFIED` text has been removed,
  corrected, or explicitly marked as a conjecture/heuristic;
- exact theorem signatures in the rewritten guidance have been checked again;
- a final diff-to-ledger pass confirms that no unaudited factual claim was
  introduced during rewriting.

## Closure

**Status: CLOSED — PASS (2026-08-06).**

All release-gate conditions above are discharged. The frozen-original reviews
are reconciled in `RECONCILIATION.md`; the corrected package received two full
post-rewrite approvals at identical hashes in `POST_REWRITE_AUDIT_A.md` and
`POST_REWRITE_AUDIT_B.md`; and the blind behavioral checks are recorded in
`FORWARD_TESTS.md`. The final hashes, validation receipts, disclosed review
limitations, and remaining repository quarantines are collected in
`FINAL_AUDIT.md`.

This closure approves the corrected skill as a conservative workflow and
navigation aid. It does not certify quarantined Lean modules or replace
primary papers, current declarations, focused builds, and axiom receipts.

The original closure hashes were superseded later on 2026-08-06 by a
distance-first architecture correction requested after release. That delta
received two independent reviews, two correction receipts, behavioral
testing, and focused validation. Its current hashes and disposition are in
`DISTANCE_FIRST_DELTA_AUDIT.md`.

## Reviewed snapshot identifiers

These SHA-256 values identify the text sent to the first audit wave.  Any
later edit requires a diff-to-ledger review.

| File | SHA-256 |
| --- | --- |
| `SKILL.md` | `d2ed1ec00b459ce342cc738b40848bc718f2522cba79ee0ca3b8d64c15e0f962` |
| `references/conditional-equivalence.md` | `d7dac55ed3bc0dfba7797236ea425196e5f156a6dc15232fbd507b399e0cd323` |
| `references/counting.md` | `84b19b1fc887311a6573428515e474d01d5d95c6b0128b296a307a79edc13e9e` |
| `references/creative-search.md` | `9765e11bf2c384b23f386378a6e8fdc8d9cdd54c566d18e1198c582ffbf71f11` |
| `references/h-technique.md` | `dc920db8e6d41443d7e69a39a53834a38bf48981c31c72f267429a023b183405` |
| `references/reshape-and-exact.md` | `2be7d137096ff5058d78317c593377763e31d8bc32506154b00d5eecbcceb6be` |
| `references/sketch-and-plan.md` | `a94ef630b3ea43b9c41a14f624171927e9eae206db0c16789505b9d429afe072` |
