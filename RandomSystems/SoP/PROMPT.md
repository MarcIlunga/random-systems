# PROMPT USED FOR A TIGHT COUPLING PROOF OF THE SUM OF PERMUTATIONS

## Research objective

Work in:

`/Users/marcilunga/Documents/tob/research/random-systems`

Produce exactly one final proof file:

`RandomSystems/SoP/SoP.lean`.

The goal is to discover and prove the strongest correct information-theoretic
security theorem for the sum of two independent uniform random permutations
against a uniform random function, using the coupling theory of random systems.

This is a mathematical research task followed by formalization. Do not assume
that the repository's current proof decomposition, intermediate objects, or
preferred estimate is the right route. Search freely for a deeper and tighter
coupling argument.

The final file must contain:

1. a complete publication-quality pen-and-paper proof in its opening module
   document; and
2. a complete Lean 4 formalization of that proof below the document.

Do not create SoP helper modules or modify existing repository files.

Once the Phase I paper proof is complete and frozen, you are fully authorized
to develop whatever Lean infrastructure is genuinely needed to formalize it.
The restriction is on file placement, not on mathematical or formal depth:
every permanent SoP-specific definition, construction, instance, equivalence,
auxiliary lemma, tactic, test, and final theorem must remain in the single
`RandomSystems/SoP/SoP.lean` file.

## Binding repository and source rules

Read `DESIGN.md` and `STATUS.md` completely before modeling or proving
anything. Follow their rules on the CR18 partial-function model, law-level
public statements, theorem names, decidability, simp normal forms, automation,
and proof development.

The primary source for the proof method is David Lanzenberger's thesis:

`papers/thesis (1).pdf`.

Read the original rendered PDF, including all definitions and conventions
needed by:

- Definitions 2.26-2.28;
- Theorems 2.31 and 2.32;
- Lemma 2.33 and Notation 2.34;
- the proof of Theorem 2.31 in Section 2.4.2.

These occur around PDF pages 28-33, printed pages 18-23.

Also read the original `papers/LanMau20.pdf`, especially its distance and
coupling results. Repository notes, extracted text, and existing Lean files may
be used for navigation, comparison, counterexample discovery, and API
discovery, but source claims must be checked in the PDFs.

## Fixed problem, open proof architecture

The real oracle samples two independent uniform permutations over the relevant
finite group and returns their pointwise sum. The ideal oracle is a uniform
random function on the same domain and codomain. The adversary is
information-theoretic and adaptive, with query budget `q`; repeated queries
must be answered consistently.

The agent must determine during the mathematical phase:

- the most natural algebraic generality of the theorem;
- the right bounded random-system presentation;
- the right coupling and representatives;
- the sharp finite-parameter theorem statement;
- whether the strongest result is an exact characterization, a closed upper
  bound with a matching lower bound, or both;
- the precise range of `q` and group sizes for which each statement is true.

Do not presuppose that the best proof uses visible-output counts, affine
orbits, gain graphs, position tapes, successor systems, density expansions, or
any other current repository decomposition. These are possibilities to test,
not requirements.

Likewise, do not presuppose that the familiar `q^3 / N^2` estimate is the final
answer. Treat it as a benchmark. A proposed theorem must be compared
rigorously with the existing bound on their common parameter range.

The agent is free to reformulate the problem through any mathematically
equivalent coupling-friendly representation, provided the final theorem is
transported back to the repository's law-level random-system statement.

## Coupling-only requirement

The proof must be a coupling proof in substance, not only in terminology.
The main security statement must arise from a joint construction or from the
thesis coupling theorem applied with all hypotheses and representatives
proved for the concrete SoP systems.

The final quantitative estimate must be obtained by analyzing the
disagreement probability of that coupling. Auxiliary combinatorics,
probability, algebra, transport, symmetry, or representation theory may be
used freely when they analyze or construct the coupling.

The H-technique is forbidden. In particular:

- do not prove the result through transcript-density ratios;
- do not use H-coefficient or ratio-on-good arguments;
- do not use an H-technique good/bad-transcript lemma and add a coupling only
  afterward;
- do not invoke existing SoP H-technique endpoints;
- do not import any `RandomSystems.HTechnique.*` module;
- do not rename an H-technique estimate as a coupling failure bound.

A failure event is allowed and often natural, but it must be the actual
disagreement event, or a proved superset of the disagreement event, of the
constructed coupling.

## Two strictly sequential phases

### Phase I: mathematical discovery and paper proof

Do not begin substantive Lean formalization in this phase.

Explore the mathematics broadly before selecting a theorem or proof route.
Use scratch calculations and finite experiments to falsify conjectures, not to
replace proof.

Start with several independent coupling programs. Examples of broad families
worth considering include, but are not limited to:

- direct online couplings of the two permutation tables with a random
  function table;
- couplings of equivalent random-system representatives obtained through the
  thesis successor induction;
- transport or matching formulations of the finite joint law;
- exchangeability and group-action couplings;
- exposure martingales or sequential conditional couplings;
- random graph, random matching, occupancy, or collision-process couplings;
- algebraic, Fourier, representation-theoretic, or additive-combinatorial
  descriptions of the disagreement obstruction;
- Stein, Poisson, dependency, entropy, or optimal-transport viewpoints;
- exact small-query analysis suggesting the correct general invariant.

This list is deliberately non-binding. Create new approach families whenever
the evidence suggests them.

Do not choose the final route merely because it resembles existing code or
produces a familiar bound. Compare candidate couplings by:

- the exactness of their disagreement probability;
- their finite constants;
- their valid query range;
- their algebraic generality;
- whether they preserve adaptivity without a loss;
- whether they expose a matching lower bound or an optimality certificate;
- whether their proof can be stated cleanly and formalized without hiding a
  theorem-strength assumption.

Once a strongest surviving theorem and coupling have emerged, write a
self-contained paper proof in a top-level `/-! ... -/` document in
`RandomSystems/SoP/SoP.lean`. At this point the file must contain the paper
proof only.

The paper proof must:

- define the real and ideal systems and the security quantity precisely;
- state all finiteness, algebraic, domain, and query assumptions;
- define the coupling completely;
- prove that it is a probability law;
- prove both marginals;
- prove any representative-equivalence claims;
- identify and analyze its disagreement event;
- prove the adaptive security conclusion;
- derive the final finite bound or exact expression with no residual
  hypothesis;
- treat degenerate and boundary parameter cases;
- distinguish proved optimality from merely being the strongest bound found.

If the theorem is claimed to be tight or optimal, prove an exact equality or a
matching lower bound. Do not infer optimality from the failure of other
approaches.

Number every mathematical definition, lemma, proposition, and theorem. The
proof must be understandable independently of Lean and must not defer
mathematical content to future code.

#### Phase I adversarial gate

Before formalization, use independent adversarial agents to audit:

- the coupling's normalization and both marginals;
- adaptivity, stopping, repeated queries, and fresh-query accounting;
- all boundary cases and denominator side conditions;
- every symmetry or without-loss-of-generality step;
- any claimed equivalence of system presentations;
- the orientation and normalization of statistical distance;
- every union, collision, transport, or concentration estimate;
- any tightness or optimality claim;
- circular use of the coupling theorem or desired conclusion.

Require concrete counterexamples, equations, or derivations. Reject vague
approval.

Revise until no mathematical gap survives. Then freeze:

- the final theorem statements;
- the coupling;
- the numbered proof;
- a map from every numbered result to its intended Lean declaration.

Only then begin Phase II.

### Phase II: Lean formalization

Keep the complete Phase I proof as the opening module document. Append the
formalization below it and prove the frozen results in the same logical order.
Every substantial Lean declaration must cite the corresponding paper result.

Phase II has broad implementation authority inside this file. Add any
SoP-specific formal material required by the frozen mathematics, including:

- new finite representations of permutations, functions, transcripts,
  histories, representatives, joint laws, or coupling states;
- equivalences and transport theorems connecting those representations to the
  repository's law-level random systems;
- auxiliary probability, counting, algebra, combinatorics, graph, matching,
  transport, or asymptotic lemmas;
- custom structures, predicates, subtypes, finite classifiers, recursors, and
  induction principles;
- local or global instances whose scope is this module;
- private implementation lemmas and named public semantic lemmas;
- local tactics, simp lemmas, and narrowly scoped automation with demonstrated
  consumers;
- executable finite sanity checks used as regression tests in addition to,
  never instead of, symbolic proofs.

Do not avoid necessary formal infrastructure merely because it is not already
present in the repository. If a generic library fact is missing, prove the
needed version locally in `SoP.lean` rather than editing a foundation module.
If an existing representation is unsuitable, introduce a better local
presentation and prove the exact bridge back to the public law-level objects.

You may add every required import at the top of `SoP.lean`, provided the import
is compatible with the coupling-only and no-H-technique requirements. You may
reuse generic proved infrastructure freely. There is no line-count limit and
no requirement that the formalization be a thin wrapper around current APIs.

The Lean development may reuse Mathlib and generic, non-H-technique
`RandomSystems` infrastructure. Existing SoP/XoP application files may be
inspected, but the final result may not be a thin alias, export, or wrapper of
an existing application endpoint. The novel coupling and its sharp analysis
must be present in this file.

Representation changes forced by the library must be connected to the paper
objects by explicit equivalence theorems. Do not silently formalize a different
proof because it is easier in Lean.

This authority does not extend to permanent changes outside `SoP.lean`.
Do not edit `DESIGN.md`, `STATUS.md`, the lake configuration, generic
foundation modules, current SoP/XoP modules, or root import files. Temporary
scratch files may be used outside the repository during development and must
be removed before returning.

If Lean reveals a genuine mathematical gap:

1. stop formalization;
2. repair the paper proof;
3. rerun the relevant Phase I adversarial audit;
4. update the frozen paper-to-Lean map;
5. resume only after the repaired mathematics passes.

A complete paper proof without compiling Lean is incomplete. Compiling Lean
whose paper proof is incomplete or materially different is also incomplete.

## What a complete result must establish

The final theorem surface must include:

- concrete real and ideal law-level random systems;
- their required normalization, domain, and boundedness facts;
- a coupling of honest representatives with explicit marginal theorems;
- a theorem relating coupling disagreement to adaptive distinguishing
  advantage;
- the strongest residual-free finite security theorem selected and proved in
  Phase I;
- precise comparison with the existing `q^3 / N^2` benchmark wherever both
  apply;
- exact or independently checked small-parameter theorems sufficient to audit
  normalization and claimed sharpness;
- an honest statement of any necessary restriction on the algebraic carrier
  or query range.

An exact finite characterization is preferable to a looser closed estimate,
but the prompt does not prescribe its form. If an exact characterization is
proved, derive the strongest useful closed corollaries justified by it.

The following do not count as completion:

- the generic coupling theorem instantiated without a new SoP analysis;
- a fixed-input or nonadaptive result presented as adaptive security;
- an upper bound with a residual term, named unproved condition, or
  theorem-strength hypothesis;
- a computational result for fixed sizes;
- a reduction to orbit enumeration, graph counting, transport feasibility, or
  another unsolved global lemma;
- a claimed improvement without a formal comparison theorem;
- a claimed tight result without equality or a matching lower bound;
- a coupling appended to a proof actually obtained by the H-technique.

Do not freeze theorem names in advance. Choose lowercase ASCII `snake_case`
names after the Phase I statements are stable, following `DESIGN.md`.

## Dynamic multiagent protocol

Use multiagent v2 aggressively and dynamically, with up to 64 concurrent
agents. Do not allocate a fixed number of agents to predetermined strategies.

- Begin with a genuinely diverse portfolio of mathematically incompatible
  coupling ideas.
- Preserve independence in early rounds; do not tell most agents the favored
  approach.
- Maintain an explicit registry of approach families classified by their
  mathematical mechanism.
- Redirect agents when one family becomes overrepresented.
- Require concrete lemmas, constructions, equations, tested finite examples,
  counterexamples, or Lean goal states. Reject status reports and vague
  optimism.
- Mark a route blocked when its missing lemma is equivalent in strength to the
  target. Reopen it only for a materially new mechanism.
- Keep multiple serious routes alive until their actual bounds and gaps can be
  compared.
- Use adversarial agents in every round, not only at the end.
- After Phase I freezes, reorganize agents around independent Lean components,
  integration, proof minimization, import auditing, and axiom auditing.
- Do not stop after the first plausible coupling or the first compiling bound.

The root agent must synthesize, challenge, redirect, and launch new rounds
until a complete proof survives both mathematical and formal audit.

## Lean development loop

Do not iterate with `lake build`.

Use the `lean-lsp` MCP to inspect the exact goal state. Search locally before
guessing declaration names. If the LSP is unavailable, run:

`lake env lean RandomSystems/SoP/SoP.lean`

from the repository root.

Use temporary scratch files outside the repository for doubtful API probes,
and remove them before returning. The only repository file created or edited
for the proof task is `RandomSystems/SoP/SoP.lean`.

After the second failed local proof repair, stop patching. Search for existing
generic infrastructure and reconsider the statement or model.

No `sorry`, `admit`, declared axiom, unsafe proof escape, imported admission,
or hypothesis equivalent to the desired result is allowed.

## Final adversarial and build gates

Before returning:

1. `lake env lean RandomSystems/SoP/SoP.lean` passes;
2. every numbered paper result has a corresponding proved Lean declaration;
3. every final Lean theorem matches its frozen paper statement;
4. the coupling is audited for normalization, both marginals,
   representative equivalence, and disagreement probability;
5. adaptive, repeated-query, stopping, and boundary cases are audited;
6. the final quantitative theorem is residual-free;
7. every improvement or tightness claim has a proved comparison or lower
   bound;
8. the import closure contains no `RandomSystems.HTechnique.*` module;
9. source scans find no `sorry`, `admit`, axiom, unsafe escape, or forbidden
   proof dependency;
10. `#print axioms` for every final endpoint contains only the repository's
    accepted foundational footprint, such as `propext`, `Classical.choice`,
    and `Quot.sound`;
11. `git diff --check` passes;
12. no repository file other than `RandomSystems/SoP/SoP.lean` changed during
    the proof task.

Do not use full `lake build` as an iterative diagnostic. Reserve it for a final
stale-olean check if the focused command is insufficient.

Return only after both phases are complete and the result survives adversarial
audit. Do not return a reduction, residual theorem, isolated missing lemma,
best-effort summary, or explanation that the problem is difficult.

Continue launching new rounds when approaches fail. Spend at least eight hours
on the mathematical search before considering giving up.

Public search may be used for standard mathematical background and named
theorems, not to copy a ready-made solution to this exact task. The local
original PDFs and kernel-checked foundation are authoritative.
