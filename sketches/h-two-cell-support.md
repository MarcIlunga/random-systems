# Carrier-independent two-cell H -- pen-and-paper sketch

The H coefficient argument partitions the ideal law's support into a good cell and a bad
cell.  A bad predicate determines both cells: the bad cell contains supported points where
the predicate holds, and the good cell contains the remaining supported points.  The
partition is automatic, so callers should supply neither a coverage proof nor a disjointness
proof.  The useful endpoints should instead force exactly the good-cell density inequality
and the ideal bad-cell mass bound.

## Objects

- An arbitrary value carrier.
- An ideal finite-support law and a real finite-support law on that carrier.
- A predicate selecting the bad cell.
- For the general form, a nonnegative ratio defect and an upper bound on the ideal law's
  total weight.
- A claimed upper bound on the ideal bad-cell mass.
- Optionally, an arbitrary deterministic observation map applied after H.

## Claims

### Zero-defect two-cell H

Assume both laws are nonnegative.  On every point in the ideal support's good cell, assume
that the ideal mass is at most the real mass.  If the ideal bad-cell mass is at most beta,
then the one-sided distance from ideal to real is at most beta.

No normalization or weight-at-most-one assumption is needed in this zero-defect form.

### General two-cell H

Assume both laws are nonnegative and the ideal law has weight at most one.  On every point
in the ideal support's good cell, assume that one minus the defect times the ideal mass is at
most the real mass.  If the ideal bad-cell mass is at most beta, then the one-sided distance
is at most beta plus the defect.

### Post-processing

Both conclusions remain true after pushing the two laws along any common deterministic map,
by data processing.  The map is arbitrary; transcripts and product carriers do not enter the
H layer.

## Argument

The distance is the sum, over the ideal support, of the positive excess of ideal mass over
real mass.  Split each supported point by the bad predicate.

On the bad cell, nonnegativity of the real law bounds the positive excess by the ideal mass.
On the good cell in the zero-defect case, ideal mass is at most real mass, so the positive
excess is zero.  Summing leaves only the ideal bad-cell mass.

In the general case, the good-cell ratio bounds the positive excess by the defect times the
ideal mass.  The good-cell contribution is therefore at most the defect times the ideal
law's total weight, hence at most the defect.  Adding the bad-cell mass proves the claim.

Only points in the ideal support occur in the distance sum.  Requiring a good-cell inequality
outside that support is mathematically unnecessary.

## Technique and rejected alternatives

Technique: the carrier-independent H coefficient method with the two-cell ratio-on-good
analysis, followed optionally by data processing.

Rejected: a finer cell partition.  It adds obligations not present in the two-cell argument.
Also rejected: taking good and bad as independent predicates, because that would force
redundant coverage and disjointness proofs and permit accidental gaps.

## Obligation DAG

`support_partition`

- Statement: every ideal-supported point belongs to exactly one of the good and bad cells.
- Class: routine logic internal to H; callers do not prove it.
- Depends on: the bad predicate.

`good_cell_excess`

- Statement: the positive excess is zero in the zero-defect form, or bounded by defect times
  ideal mass in the general form.
- Class: routine algebra inside H.
- Depends on: the caller's support-local good ratio and law nonnegativity.

`bad_cell_excess`

- Statement: positive excess on the bad cell is bounded by ideal mass.
- Class: routine algebra inside H.
- Depends on: real-law nonnegativity.

`good_ratio`

- Statement: the appropriate density inequality holds at every good point of the ideal
  support.
- Class: creative caller obligation.

`ideal_bad_probability`

- Statement: the ideal mass of the bad cell is at most the advertised beta.
- Class: creative caller obligation.

`two_cell_bound`

- Statement: distance is at most beta in the zero-defect form and beta plus defect in the
  general form.
- Class: library assembly.
- Depends on: all preceding nodes.

`postprocessed_two_cell_bound`

- Statement: the same bound holds after any common deterministic observation.
- Class: library assembly.
- Depends on: `two_cell_bound` and data processing.

## Reuse verdicts

- `RandomSystems.CR18.δ_hTechnique_ratio`: ADAPT.  Its proof already sums only over
  `ideal.support`; generalize its ratio hypothesis in place from the whole carrier to that
  support.
- `RandomSystems.CR18.δ_fTransform_le`: REUSE for arbitrary common deterministic
  post-processing.
- `RandomSystems.CR18.δ_hTechnique_le_on_good`: NEW.  Local declaration search found no
  carrier-free zero-defect endpoint, and specializing the existing ratio theorem would retain
  the mathematically unnecessary weight-at-most-one hypothesis.
- `RandomSystems.CR18.δ_hTechnique_{le_on_good,ratio}_of_bad_le`: NEW thin assembly
  endpoints.  Local declaration search found no equivalent theorem that accepts the bad-mass
  estimate and therefore exposes the two creative obligations directly.

## Lean placement and proof shape

The implementation stays beside the existing carrier-free `δ` theorem in
`RandomSystems/RandomSystem.lean`; module relocation is deliberately outside this layer review.
The zero-defect theorem repeats the short support sum rather than passing through the general
ratio theorem, because the latter genuinely needs a weight bound when the defect is nonzero.
The post-processing corollary is only data processing followed by the corresponding law-level
H theorem.
