# Distance-first architecture delta audit

Date: 2026-08-06

## Outcome

**PASS.** The installed skill now starts every mathematical security proof
from one specified distance or advantage between two observable systems. It
treats exact reshaping, H-technique, strict conditional equivalence, honest
coupling, representative selection, winnability, signed expansion, and
counting as distinct but composable certificates for that same comparison.

The previous release hashes in `FINAL_AUDIT.md` are historical. This receipt
supersedes them for the installed package.

## Reason for the correction

The earlier warning to keep proof notions distinct was mathematically useful
but organizationally misleading: it could be read as if the techniques studied
different security objects. The correction makes the common object primary:

```text
two observable systems S and T
          |
          v
specified distance or advantage Adv(S,T)
          |
          v
one or more checked certificates and bridge theorems
          |
          v
finite numerical bound
```

The notions remain distinct only at the certificate layer. An H predicate is
not an MBO, an honest coupling is not a signed law, and representative
equivalence is not conditional equivalence. They may nevertheless be
alternative steps or consecutive steps in a proof of the same original
distance.

## Correct comparison spine

The skill now requires every paper sketch and Lean plan to fix:

1. the two systems `S` and `T` at their observable interfaces;
2. the allowed environments or distinguishers and the query restriction;
3. the exact distance or advantage expression and orientation; and
4. the finite theorem to prove.

Every auxiliary representative, monitor, game, joint law, transcript
predicate, or signed expression must enter through a named equality or
inequality. The representative/coupling example deliberately separates all
layers:

```text
Adv(S, T)
  = Adv(S', T')
  <= rawDelta(S', T')
  <= disagreementMass(joint(S', T'))
  <= epsilon.
```

The first equality needs representative equivalence, the next inequality
needs an operational-to-law bridge, the disagreement inequality needs an
honest coupling with the stated marginals, and the final inequality needs a
numerical estimate. Equality at the raw-law step requires a separate
attainment theorem; it is not inherited from representative equivalence.

## Files changed

- `SKILL.md`: added the common comparison spine, certificate table, explicit
  composition chain, and distance-first endpoint-selection workflow.
- `references/conditional-equivalence.md`: recast nearby notions as other
  certificates for the same comparison while retaining strict CE's own type
  and obligations.
- `references/h-technique.md`: requires the systems, observation model,
  horizon, and orientation before defining `Bad`.
- `references/reshape-and-exact.md`: organizes representatives, couplings,
  winnability, and signed expansions around one comparison spine.
- `references/creative-search.md`: gives every independent route the same
  frozen distance and requires an explicit bridge back to it.
- `references/sketch-and-plan.md`: requires the first displayed quantity to be
  the original system distance.
- `agents/openai.yaml`: makes the distance-first workflow visible in the
  default invocation.

The obligation ledger was also normalized. `REUSE`, `ADAPT`, and `NEW` now
record origin; `OPEN` and `CLOSED` record proof status; automation is a
separate optional field.

## Independent review

Two reviewers independently read the frozen revised package without reading
the audit directory or each other's output. Both checked the wording against
current declarations and rendered primary sources.

### First frozen revision

Both reviewers returned **PASS** with no blocker. They independently found the
same nonblocking ambiguity in the schematic representative/coupling chain:
the prose needed to expose raw law distance between operational advantage and
coupling disagreement. Reviewer B also found the unrelated ledger-label drift.

The chain and ledger were corrected. Reviewer B then requested one final
editorial generalization from “real and ideal systems” to “the two systems
`S` and `T`, often real and ideal.”

### Final delta

Both reviewers inspected the corrected lines and returned **PASS** with no
remaining finding. Their final checks confirm:

- operational `Adv`, raw `delta`, coupling disagreement, and counting are
  separate hops;
- representative equivalence is not said to preserve arbitrary raw `delta`;
- unequal-weight and one-sided orientations remain guarded;
- fixed-query H and adaptive lifting are not collapsed;
- blind CE schedules and adaptive H environments remain distinct;
- honest couplings and signed carriers are not conflated; and
- every cross-technique composition requires an explicit bridge.

Reviewer B was asked to conclude from checks already completed after an
extended audit run; no source conclusion was supplied to it. Neither reviewer
edited the package.

## Behavioral checks

A fresh agent used the revised skill on a multi-route Sum-of-Permutations
planning prompt without seeing this audit. It began with one filtered distance
`D_q` and organized CE, H/signed, and representative/coupling routes as
alternative certificates feeding that same quantity. It kept their schedule,
marginal, adaptivity, and signed-carrier obligations separate. This is a
workflow behavior receipt, not approval of every construction-specific claim
in that generated plan.

A second fresh test forced a chain involving equivalent representatives, an
honest joint, and a signed expansion. It began with the original operational
advantage, pushed the honest joint to each transcript law before applying the
coupling lemma, and treated the signed identity and its half-`L1` estimate as a
separate alternative bound. It explicitly warned that a fixed-transcript
signed calculation does not control adaptive advantage without an additional
reduction. **PASS.**

## Validation

- Skill schema/frontmatter validation: **PASS**.
- `RewrittenSurfaceProbe.lean`: **PASS**.
- `CBCReceiptProbe.lean`: **PASS**; the checked CBC CE theorem reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- No broad iterative build was run.

## Current package hashes

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `SKILL.md` | 258 | `671e7cd1715098863bb1612a89bd0cab3534c7ae78c18b5e6ab96ca65364b745` |
| `agents/openai.yaml` | 4 | `6b9593047aba020e4d1b9a6daa79096618044315a0eb9e6137bdc643405ec8a6` |
| `references/conditional-equivalence.md` | 205 | `329dfd3bc223400459e58b50e72812a8ebb54cc6ee81f6eba199789ba4475c51` |
| `references/counting.md` | 138 | `32cb22ad7b078ac886105670f91202603463e0d6b1660c7a5dd4cf9e624d76db` |
| `references/creative-search.md` | 123 | `1d7d5407c31437c4d08632d53e020c0de66ecf78458f70b3b0fa5ab4d63bc02c` |
| `references/h-technique.md` | 167 | `44de259fadae9588c5c2573891e57c9e6a5911745f0bca89040607f144dc2f30` |
| `references/reshape-and-exact.md` | 212 | `5c1c388f8ca5f6185c6602b73d09b6c7f27df2f823ce6d92c0111c00b12f0360` |
| `references/sketch-and-plan.md` | 176 | `6f338c70faabfe851dc8dffd27c5c46cf97047ac514ee186074b0f0f55352661` |

Total: 1,283 lines.

## Disposition

The distance-first revision is release-approved. The skill remains a
workflow/navigation aid: the original system distance is the proof's common
object, while every route-specific certificate and every bridge must still be
verified from primary mathematics and current Lean declarations.
