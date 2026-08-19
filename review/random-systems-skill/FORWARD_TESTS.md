# Forward tests of the corrected `random-systems-proofs` skill

Date: 2026-08-06

## Protocol

Three fresh agents received the installed skill and a user-style question. They
were forbidden to read `review/random-systems-skill` or any audit report and
were not told an expected answer. They performed read-only current-source
checks and made no edits.

These tests assess whether the skill changes behavior on the failure modes that
motivated the audit. They do not replace the line-by-line source audits.

## Test 1: smaller conditional-equivalence monitor

Prompt summary: a user has `badSmall ⊆ seededHashCollision` and asks whether it
can be substituted into the packaged seeded CE endpoint to obtain an immediate
smaller bound, including questions about the schedule quantifier, simulator,
and representatives.

Result: **PASS**.

The response:

- rejected automatic monitor refinement;
- listed decidability, prefix monotonicity, strict CE, probability, totality,
  and the uniform blind-winner leaf;
- explained that containment transfers at most the old mass bound and enlarges
  the proposed good region, so CE must be reproved;
- distinguished each blind winner's fixed `blindQueryList` from the adaptive H
  environment quantifier; and
- kept simulator redesign separate from replacement by an `Equivalent` PDS
  representative.

It checked
`RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le`,
`blindQueryList_length_le`, and the relevant strip/equivalence declarations.

## Test 2: raw maximal coupling, representatives, and compression

Prompt summary: a user asks whether
`optimal_probability_coupling_exists` gives an optimal adaptive random-system
coupling, licenses convenient representatives, and combines with
`compressedQuery_bound` to assume distinct adaptive queries.

Result: **PASS**.

The response separated:

- maximal coupling of two displayed normalized PDS laws, whose disagreement is
  their raw `δ`;
- representative-level attainment, which needs the finite-input,
  common-domain, bounded-depth hypotheses of the dedicated theorem;
- preservation of operational advantage under `Equivalent` representatives,
  which does not preserve raw `δ` or an attained equality automatically;
- exact fixed-query compression for a sampled static function evaluator; and
- the merely numerical role of `compressedQuery_bound`.

It explicitly rejected generic compression for adaptive or stateful PDSs and
kept the adaptive H quantifier visible.

## Test 3: tactic failure in CBC-MAC

Prompt summary: `cr18_total` is initially unavailable and then both
`cr18_total` and `cr18_prob` fail after importing their tactic modules. The user
asks whether this proves the CBC model is wrong and what a final receipt needs.

Result: **PASS**.

The response:

- rejected tactic failure as semantic evidence;
- identified the owning modules and described both tactics as finite registered
  surfaces;
- prescribed import, goal-state, instance, signature, and explicit-lemma
  checks before changing the model;
- pointed to the explicit CBC probability/totality lemmas and registration
  pattern in the current source;
- followed the focused Lean-LSP / `lake env lean <file>` development loop; and
- required focused gates, `#print axioms`, no admissions, and an exact theorem
  and restriction report for completion.

## Conclusion

All three tests passed without access to the intended corrections or audit
reports. The corrected skill produced the distinctions that the frozen version
had obscured:

```text
strict CE monitor ≠ automatic event refinement
raw maximal coupling ≠ representative-level adaptive attainment
numeric compression side condition ≠ semantic query compression
tactic failure ≠ model invalidity
```
