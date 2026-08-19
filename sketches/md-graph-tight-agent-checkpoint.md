# SequenceHash MD graph tightening: agent checkpoint

Status: **INCOMPLETE / PAUSED**. This file preserves the analysis that was in
progress when the task was replaced by an independent skill audit. Nothing in
this checkpoint is a proved theorem unless explicitly marked.

## Terminology correction

Conditional equivalence is formulated with enhanced systems/games, retained
subkernels, and monotone bad events. Choosing an equivalent PDS representative
is a separate Maurer--Lanzenberger operation and is not part of CE. The current
SequenceHash draft mixes these vocabularies in several section and lemma names.

## Strongest closed local refinement

For an activation with a fixed occupied-terminal profile

\[
r(y)=|\{z:w_z=y\}|,\qquad c=\sum_y r(y),
\]

the visible real answer law is

\[
P(y)=\frac1N+\frac1N\left(r(y)-\frac cN\right).
\]

Its exact distance from uniform is

\[
\delta(r)=\frac1{2N}\sum_y\left|r(y)-\frac cN\right|
\le \frac{c(N-1)}{N^2}.
\]

This can be realized positively by retaining the pointwise common part of the
two answer kernels. It sharpens the occupied-link charge for a fixed safely
selected profile. It does not, by itself, improve the worst-case polynomial:
the old coefficient is attained when all occupied sites have the same answer,
and for one occupied site the two expressions are equal.

## Existing global theorem that remains defensible

The current draft proves, subject to its stated graph-game obligations,

\[
\operatorname{Adv}
\le
\min\left\{1,
\frac{\binom{s+1}{2}+ps}{N}
+\frac{ca(N-1)}{N^2}\right\},
\]

where `a` is the number of construction queries, `p` the number of direct
compression queries, `s` the number of critical samples, and `c` the number of
pending sites (the draft uses nearby letters differently in different notes).
The only immediately justified global tightening is to bundle compatible
occupied sites per activation and replace the final coarse link summand by the
expected sum of the exact profile deficiencies. The Join/Select charge is not
removed by this local calculation.

## Candidate graph improvement, not proved

A multi-label, pin-aware simulator should be able to keep many ordinary state
joins: an unpinned tree merge is harmless, equal pins are compatible, and a
cycle is harmful only when it forces incompatible visible obligations. This
suggests replacing the quadratic construction-work term by a suffix-sensitive
term. A plausible sparse envelope is

\[
O\left(\frac{p^2+p\Lambda+a\Lambda}{N}\right),
\]

where \(\Lambda\) is aggregate construction path length. With maximum path
length \(\ell\), this is

\[
O\left(\frac{p^2+pa\ell+a^2\ell}{N}\right).
\]

This is **CONJECTURAL** for the full stable-v1 ideal-compression graph. A proof
needs an online pin-aware graph invariant, an adaptive selection lemma, and a
multiple-collision remainder. Gażi's cascade graph count and the 2025 tight
HMAC analysis warn that a finite theorem may also need lower-order terms such
as a multiple-collision contribution, rather than only the displayed leading
order.

## Important obstruction: a primitive-only quadratic search term can matter

The earlier thought that every \(p^2\) term is removable was wrong once one
later construction query is allowed. An adversary can:

1. prequery many unlinked outer terminal targets;
2. expose many candidate complete inner endpoints;
3. select a construction input only after finding an endpoint/target match.

With about \(p/2\) targets and \(p/2\) candidates, the search succeeds with
probability of order \(p^2/N\); the eventual construction query exposes an
inconsistent pending answer with probability close to one. Thus a theorem
uniform over adaptive query order cannot simply delete the Select term or
replace it by \(pa\ell/N\). When `a = 0` the two systems restricted to the
primitive interface are identical, but a single later construction query can
activate the quadratic search.

## Construction-only lower-bound mechanism

For two construction inputs with a common tag and long common suffix, an inner
state meeting before that suffix forces equal inner endpoints and hence the
same outer computation. The ideal random-oracle answers remain independent.
This gives the familiar order \(a^2\ell/N\) in suitable sparse workloads and
shows why a length-linear pair term is expected. The exact stable-v1 message
family and finite constants were not completed here.

## Benign and harmful graph events

Likely benign:

- repeated queries and ordinary table hits;
- merges of two unpinned components;
- attaching an unpinned component to one pin;
- merging equal pins;
- balanced cycles that impose no inconsistent visible value.

Potentially harmful:

- one compression coordinate required to carry two unequal construction
  answers;
- a construction terminal required to disagree with a prior primitive answer;
- an adaptively selected endpoint/target match;
- a cycle that forces an already fixed coordinate to a different value.

A join that is harmless when created may become harmful after a second pin is
attached. Consequently a valid MBO cannot forget latent obligations, and the
claim that all tree joins may simply be ignored is false without a pin-aware
state invariant.

## Literature checks completed

- Gażi--Pietrzak--Rybár (2014), Proposition 1 and its graph counting were
  inspected locally. Their equal-length single-collision graph count is linear
  in path length, while the finite bound retains a multiple-collision tail.
- Shen--Zhang--Wang--Gu (2025), Theorem 1 and matching-attack section were
  inspected locally. Their HMAC PRF bound has leading terms of order
  \(pq\ell/N\) and \(q^2\ell/N\), plus explicit lower-order terms. This is
  supporting evidence for the candidate graph order, not a proof of the
  SequenceHash indifferentiability theorem.
- Backendal--Bellare--Günther--Scarlata (2023) concerns standard-model dual-PRF
  and multi-user PRF security of HMAC/NMAC. It is not directly an
  ideal-compression indifferentiability theorem.

## Exact next obligation when resumed

State and prove a pin-aware online graph lemma: after aggregating hidden
states, the two monitored games have the same retained visible transition
kernel; every residual atom has a unique first witness among (i) a selected
endpoint/target match, (ii) an incompatible terminal pin, or (iii) a
suffix-synchronizing multiple-collision witness. Only after that lemma is
closed is it sound to replace the present all-Join bound by a length-linear
construction term.
