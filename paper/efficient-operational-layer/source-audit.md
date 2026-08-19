# Primary-source audit for the efficient operational layer

## 1. Method

This audit records what the cited literature actually establishes and separates
it from the model proposed in this project.  It uses four labels.

- **Quotation** means that the manuscript reproduces source language.  The
  manuscript currently uses no substantive verbatim quotation.
- **Paraphrase** means that the source states essentially the same
  mathematical or methodological claim.
- **Inference** means that the claim follows from combining source statements
  or from reading a definition against the questions addressed here, but is
  not itself a theorem of the source.
- **New proposal/result** means that the claim belongs to the present lower
  layer.  A source may motivate it, but it must be justified independently.

Page references below use the printed page number when one is printed and add
the PDF page number when the two differ materially.  The source files checked
are the author, institutional, publisher, or archival versions listed in the
bibliography.  The audit was conducted against the actual paper text, not
against abstracts or secondary summaries.

## 2. The top-down hierarchy and the place of computation

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA1 | Maurer--Renner, *Abstract Cryptography*, Sections 1.4--1.5, printed pp. 4--5 (PDF pp. 4--5) | Contrasts a bottom-up path through machines, communication, complexity, efficiency, and games with a top-down path that introduces only the lower structure needed at each stage. | Paraphrase | This does not itself define any machine layer. |
| SA2 | Ibid., Section 1.5, printed p. 4 | Lists Level 1 (general systems and algebra), Level 2 (discrete systems/random-system extension), Level 3 (implementation and abstract efficiency), then lower computational, cost, timing, and physical levels. | Paraphrase | The levels are a research program, not a completed instantiation. |
| SA3 | Ibid., Section 1.5, printed pp. 4--5 | States that higher definitions and theorems are inherited by lower levels provided the lower levels satisfy the postulated properties or axioms. | Paraphrase | “Inherited” is conditional.  It is not enough to exhibit machines; the operational operations and quotient must satisfy the higher laws. |
| SA4 | Ibid., Section 1.8, printed p. 6 | Explicitly leaves formalization of lower abstraction levels and technical comparison with prior frameworks to future work. | Paraphrase | It would be incorrect to attribute the concrete layer of the present project to MR11. |
| SA5 | Maurer, *Constructive Cryptography*, Section 4.1, printed pp. 43--44 (PDF pp. 11--12) | Argues that machine, tape, asymptotic, efficiency, and adversarial details should be left to lower abstraction levels when irrelevant to the theorem. | Paraphrase | The paper deliberately does not discharge those lower-level obligations. |
| SA6 | Ibid., Section 4.2, printed pp. 43--44 | Repeats the top-down discipline and the conditional inheritance of theorems by lower models satisfying the higher axioms. | Paraphrase | This supports the direction of the project, not any chosen scheduler, meter, or cost vector. |
| SA7 | Ibid., Sections 4.3--4.5, printed pp. 44--46 | Defines resources, converters, their algebra, compatible pseudometrics, and closure of distinguishers under converter/resource emulation. | Paraphrase | The cryptographic algebra there is intentionally abstract; exact cost reindexing is new here. |
| SA46 | Maurer--Renner, *Abstract Cryptography*, Section 6.2, Definitions 14 and 16, and Section 6.3, Definition 17, printed pp. 12--14 | Requires commuting converter actions at distinct interfaces, a neutral converter, congruence under converters and parallel resources, distinguisher closure under emulation of every converter and every parallel resource in the restricted algebra, and a closed feasible algebra. It separately requires `Sigma^e subset Sigma^f` and `Sigma^e circ Sigma^e subset Sigma^e` for a compatible honest-efficiency notion. | Paraphrase | The efficient-algebra theorem must verify both converter absorption and arbitrary feasible-parallel-resource absorption, not just absorption of a named ideal oracle. Dependency-relative closure must retain the same occurrence state and randomness; merely granting a test an undeclared oracle would not satisfy the clause. |
| SA47 | Maurer--Renner, *From Indifferentiability to Constructive Cryptography (and Back)*, Sections 3.5 and 4.3, printed pp. 9--13 | Lists four modeling choices for computation, memory, and randomness. Under choice 3, a computational system `beta` in an equation can be represented by a parallel behavioral resource `beta_bar` and a trivial connecting converter. | Paraphrase | This supports reifying simulator behavior under a declared modeling choice. It neither mandates reification for every concrete-security statement nor proves that `beta_bar` decomposes into the selected processor/store/coin API; that is a new refinement obligation. |
| SA48 | Jost, *On Generalizations of Composable Security*, Theorem 2.2.11, printed pp. 22--23, and Definitions 2.2.14--2.2.15, printed pp. 25--26 | Protocol relaxation replaces `epsilon(D)` by `epsilon(D pi)`. Parallel composition with a specification `S` replaces it by `epsilon^S(D)=sup_{S in S} epsilon(D[. || S])`. Asymptotic negligibility quantifies over efficient distinguisher families. | Paraphrase | Exact pointwise absorption proves feasibility of each absorbed test, but does not by itself show that a supremum over an arbitrary set of individually efficient resource families is negligible. A uniform specification witness or fixed finiteness is an additional lower obligation. |

**Conclusion forced by SA1--SA7.**  The absence of a fixed computation model
at the current CC layer is intentional and nonproblematic.  The unresolved
research task is a conditional instantiation theorem: define a lower
operational algebra, prove its laws, and give a homomorphism or refinement into
the discrete/random-system algebra.  This conclusion is an **inference** from
the hierarchy, whereas the particular model in the dossier is a **new
proposal**.

## 3. Which costs are hidden and which are resources

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA8 | Maurer--Renner, *From Indifferentiability to Constructive Cryptography (and Back)*, Section 3.5, printed pp. 9--10 (PDF pp. 9--10) | Gives four modeling regimes: unrestricted converters; explicit memory with converters unable to retain state; explicit computing resources with routing-only converters; and an efficiently implementable converter class. | Paraphrase | These are alternatives.  The present work must say which regime each theorem inhabits instead of combining them silently. |
| SA9 | Ibid., Section 3.5, printed p. 10 | Says polynomial time is attractive when properly defined because the converter class should be closed under composition; also notes that other efficiency/feasibility choices are possible. | Paraphrase | MR16 does not supply the required reactive polynomial-time definition. |
| SA10 | Ibid., Section 3.5, printed p. 10 | Explains that if memory is relevant, it is a resource and converters retain no state between invocations; cites the Ristenpart--Shacham--Shrimpton issue as an artifact of importing Turing machines with hidden tapes into a memory-sensitive setting. | Paraphrase | It would overstate the source to say that every multi-stage composition issue is “solved.”  The exact claim is about the inadequacy of hidden arbitrary memory for that modeling question. |
| SA11 | Ibid., Section 4.3, printed pp. 12--13 | Explains that concrete simulator complexity matters even if converters at the chosen abstract resource level are treated as free, and reifies a computational simulator as an explicit parallel resource. | Paraphrase | This is a modeling transformation, not an exact machine-cost theorem. |
| SA12 | Ristenpart--Shacham--Shrimpton, *Careful with Composition*, extended version, Introduction, pp. 1--4; especially pp. 2--3 | Exhibits a multi-stage storage-auditing failure and explains that a stage boundary can delete the original message while preserving compact state derived from a concrete hash construction. | Paraphrase | RSS11 diagnoses limitations of an indifferentiability/UC use pattern.  It does not define the explicit-memory CC resource used here. |

**Present contribution suggested, not proved, by SA8--SA12.**  Exact hidden
machine cost and explicitly supplied computation resources are two
refinements of the same behavioral system and require different converter
disciplines.  The selected transition-token `PROC`, native-configuration
`STORE`, named `COIN`, two-phase reservation protocol, sequential `SLINK`, and
administrative-erasure theorem are **new results of this project**.  They
must not be attributed to MR16 or RSS11.  RAM, shared processors, visible
clocks, reset, leakage, and concurrent communication remain different API
choices.

## 4. The discrete and random-system target

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA13 | Maurer, *Indistinguishability of Random Systems*, Section 3.1, printed pp. 5--6 (PDF pp. 5--6), Definitions 1--3 | Separates an explicit random automaton with state and randomness from its observable random-system behavior, represented by conditional input/output distributions. | Paraphrase | The 2002 definition is total at every round on its advertised alphabet; strict nonresponse and random domains are extensions in this project. |
| SA14 | Ibid., Section 3.3, printed pp. 8--9, Definition 8 and the invocation discussion | Defines cascades and the invocation of an internal random system. | Paraphrase | This is not a general proof of arbitrary network feedback for partial systems. |
| SA15 | Ibid., Section 4.1, printed pp. 10--11, Definitions 9--10 | Defines interactive distinguishers and maximum advantage over a bounded number of queries. | Paraphrase | No computation cost is attached to distinguishers at this information-theoretic level. |
| SA16 | Lanzenberger--Maurer, *Coupling of Random Systems*, Section 3.1, printed pp. 11--12 (PDF pp. 11--12), Definitions 5--7 | Defines a DDS as a prefix-closed partial history function, deterministic environments, and transcripts. | Paraphrase | Their paper then restricts to finite systems.  The measure-level lifetime carrier here is not already in that definition. |
| SA17 | Ibid., Section 3.2, printed pp. 13--14, Definitions 8--10 and Example 5 | Defines a finite common-domain PDS, identifies observationally equivalent PDSs by all transcript laws, and calls the equivalence class a random system. Their finiteness convention also requires a finite input alphabet and one finite maximum history length. | Paraphrase | Finite support plus a common domain alone does not recover this source definition. Its common-domain condition also excludes the random nonresponse domains that the proposed operational layer must handle or normalize explicitly. |
| SA18 | Ibid., Section 4.1, printed pp. 14--15, Definitions 11--12 and Theorems 1--2 | Equates optimal information-theoretic transcript advantage with a distance between suitable PDS representatives and gives a coupling theorem. | Paraphrase | The present metered/unmetered coupling bound is elementary but distinct; it should not be attributed to their theorem. |

**Present lower realization.**  Fixing all named random tapes, applying the
least first-visible-output evaluator, and folding successful macrosteps into a
DDS is a **new result** of the dossier.  Pushing the tape law forward is
source-aligned.  The standard-Borel partial-DDS carrier, maximal strict
transcripts, and feedback congruence are the **new results** proved in
`partial-random-system-bridge.md`; they are not attributed to the finite
common-domain source.

## 5. System algebra, connection, and feedback

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA19 | Matt--Maurer--Portmann--Renner--Tackmann, *Toward an Algebraic Theory of Systems*, Section 3.1, printed pp. 13--14 (PDF pp. 13--14), Definition 3.1 | Defines a system algebra with finite interfaces, partial parallel composition, allowed connections, and an interface-connection operation. | Paraphrase | This is a signature and law package, not an operational semantics. |
| SA20 | Ibid., Section 3.1, printed p. 14, Definition 3.2 | Defines connection-order and composition-order invariance and notes that the property is substantive. | Paraphrase | A graph presentation proves only the structural part.  Agreement of operational evaluation under reordered feedback remains semantic. |
| SA21 | Ibid., Section 4.1, printed pp. 16--19, Definitions 4.1--4.2, Lemmas 4.3--4.5, Theorem 4.6 | Models functional connection by fixed points and proves composition-order invariance under unique fixed points and reorderable connections. | Paraphrase | The theorem does not select the strict partial first-visible-output fixed point proposed here. |
| SA22 | Ibid., Sections 5.1--5.3, printed pp. 20--24 | Builds monotone and continuous system algebras using least fixed points and proves closure/order results under stated domain-theoretic hypotheses. | Paraphrase | Metered operational feedback must either instantiate these hypotheses or prove its laws directly. |
| SA23 | Ibid., Section 5.4, printed pp. 24--25 | Shows that the “finite sequences of arbitrary finite length” domain is not an omega-CPO because the increasing sequence of finite prefixes has an infinite supremum outside the domain. | Paraphrase | This motivates, but does not itself provide, the projective/cut semantics discussed as future work. |
| SA24 | Portmann--Matt--Maurer--Renner--Tackmann, *Causal Boxes*, Sections 4.1--4.4, printed pp. 17--21 (PDF pp. 17--21), especially Definitions 4.2--4.5 | Defines systems by mutually consistent maps on bounded cuts and imposes a causality function with finite causal descent. | Paraphrase | The model is quantum and partially ordered; the dossier borrows only the projective design lesson. |
| SA25 | Ibid., Section 6, printed pp. 27--35, especially Definition 6.6 and Theorem 6.11 | Defines parallel composition and loops and proves closure and composition-order independence. | Paraphrase | No claim is made that the selected single-token classical model is a causal-box instance. |
| SA26 | Ibid., Appendix C, printed pp. 48--49 (PDF pp. 48--49), Definitions C.1--C.2 | Explains why a single map on an unbounded message space need not be composition closed and defines a finite causal-box subclass with a stronger finite-descent condition. | Paraphrase | The projective extension in the dossier remains deferred. |

The finite normalized graph carrier, alpha quotient, costed contextual
equivalence, erasure homomorphism, and explicit proofs of its algebraic laws
are **new results**.  The route-safe embedding into the selected
standard-Borel partial-random-system algebra is also a **new result**:
canonical routing has a derived dominating envelope, and environment lifting
proves strict-connection congruence.  Identification with a *different*
independently mandated carrier remains a conditional comparison, exactly
because SA19--SA26 show that connection laws are not automatic.

## 6. Uniformity and reactive runtime

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA27 | Jost, *On Generalizations of Composable Security*, Section 2.2.2, printed pp. 17--18 (PDF pp. 33--34), Definition 2.2.2 | Defines discrete converters with a finite upper bound on consecutive inner queries. | Paraphrase | The definition supplies no Turing-step, persistent-space, oracle-tariff, generated-network, or scheduler accounting. |
| SA28 | Ibid., Section 2.2.4, printed pp. 22--23 (PDF pp. 38--39), Theorem 2.2.11 | Shows that converter application and parallel resources reindex a reduction relaxation by absorption into the distinguisher. | Paraphrase | The project's exact profile transformer is a refinement, not a restatement. |
| SA29 | Ibid., Section 2.2.5, printed pp. 25--26 (PDF pp. 41--42), Definitions 2.2.14--2.2.15 and Corollary 2.2.16 | Defines efficient families by one uniform PPT implementation receiving unary security parameter and derives asymptotic composition from closure of efficiency and negligibility. | Paraphrase | It is an asymptotic wrapper around the discrete systems; it does not settle the underlying interactive machine semantics. |
| SA30 | Hofheinz--Mueller-Quade--Unruh, *Polynomial Runtime in Simulatability Definitions*, Sections 3--4, printed pp. 5--7, Definitions 3.1 and 4.1 | Relates runtime to accumulated external communication/view prefixes and defines polynomial shape, including output length and activation count. | Paraphrase | Their model and security roles are not imported here. |
| SA31 | Ibid., printed p. 7 following Definition 4.1 | Gives the internal forwarding-loop obstruction and makes polynomial shape of the composed protocol an additional responsibility. | Paraphrase | This supports a negative requirement: local flow bounds alone are not an unconditional wiring rule. |
| SA32 | Hofheinz--Unruh--Mueller-Quade, *Polynomial Runtime and Composability*, Section 4, printed pp. 27--30, Definitions 8--10 | Distinguishes a priori PPT, polynomial time with overwhelming probability, and reactive polynomial time quantified over a priori-PPT contexts. | Paraphrase | Reactive PPT is a semantic admissibility notion, not the syntactic meter chosen here. |
| SA33 | Ibid., printed pp. 28--29, “Closure properties of reactive polynomial time” | Gives two individually reactive forwarders whose composition loops forever and therefore requires a runtime premise on composed networks. | Paraphrase | This does not prove that every possible compositional efficiency discipline must use meters. |
| SA34 | Ibid., Section 9.2, Definition 33, printed p. 59 (PDF p. 59) | Defines uniform reactive polynomial time using one polynomial transformer independent of the context. | Paraphrase | The ambient-workload transformer is analogous only in quantifier shape and is not a UC runtime notion. |
| SA35 | Küsters--Tuengerthal--Rausch, *The IITM Model*, Section 4.2, printed p. 17 (PDF p. 17), Definition 7 | Distinguishes almost bounded from strictly bounded systems. | Paraphrase | Their transition accounting and machine roles remain IITM-specific. |
| SA36 | Ibid., Sections 4.3--4.4, printed pp. 18--19, Definitions 8--10 and Remark 4 | Defines universally bounded environments and environmentally almost/strictly bounded systems, with the explicit quantifier order “for every environment, there exists a polynomial.” | Paraphrase | The present predicates must state their own auxiliary-input and completion-event quantifiers. |
| SA37 | Ibid., Section 8.2, printed pp. 47--49, Definition 21 and Lemma 19 | Conditional on time-lock puzzles, constructs environmentally almost-bounded protocols whose composition is not environmentally bounded, and a system whose replication is not environmentally bounded. | Paraphrase, assumption-sensitive | The counterexample is conditional.  It cannot be cited as an unconditional impossibility theorem. |

The project's fixed unary-parameter template, explicit nonuniform variant,
self-delimiting generated-network compiler, ambient workload, exact meter, and
separate no-exhaustion/productivity judgments are **new proposals or results**.
The sources establish design hazards and useful quantifier patterns; they do
not establish the selected architecture.

## 7. Reductions and exact cost accounting

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA38 | Maurer, *Cryptography Foundations* (Spring 2018 notes), Section 4.4, especially Definitions 4.2--4.3 | Treats a computational problem as a solver set, ordered performance space, and performance map; defines reductions as solver and performance transformations before choosing a concrete machine cost. | Paraphrase | The course notes motivate the separation but do not give an interactive costed system algebra. |
| SA39 | Ibid., Sections 4.4.3--4.4.5 | Discusses solver complexity and the complexity transformation induced by reductions. | Paraphrase | The seven-coordinate ledger and polynomial profile transformer are selected here. |
| SA40 | Jost, Theorem 2.2.11, as in SA28 | Absorbing a protocol or parallel resource changes the reduction functional applied to the distinguisher. | Paraphrase | Jost's theorem does not provide pathwise equality of exact machine ledgers. |
| SA41 | Maurer--Renner 2016, Section 4.3, as in SA11 | Concrete simulator efficiency matters and can be made explicit as a resource. | Paraphrase | The exact simulator tariff, query profile, and budget reindexing remain new. |

The pathwise absorption equality for a graded converter, the polynomial
profile transformer, budget-reindexed nonexpansion, and the complete
random-function/random-permutation wrapper calculation are **new results**.
They must retain exact wrapper cost and query translation; citing abstract
nonexpansion alone would not justify those numbers.

## 8. Bottom-up frameworks used only as design evidence

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA42 | Canetti, *Universally Composable Security*, Sections 3--4 of the 2001/ePrint version | Gives a bottom-up interactive-machine execution model with parties, adversary, environment, scheduling conventions, security parameter, and polynomial-time restrictions. | Paraphrase | The present project is not a UC instantiation or translation and imports none of UC's roles, corruption, session, or simulator quantifiers. |
| SA43 | Backes--Pfitzmann--Waidner, *The Reactive Simulatability Framework for Asynchronous Systems*, Sections 2--4 | Builds a detailed asynchronous reactive-machine model with ports, buffers, scheduling, and complexity restrictions. | Paraphrase | RSIM is evidence for questions a bottom layer must answer, not the target semantics. |

UC and RSIM are therefore comparison points for what a bottom-up computation
model makes explicit.  The claim that the selected single-token layer is the
right lower boundary for current random systems is a **new design judgment**,
not a consequence of either framework.

## 9. Categorical comparison

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA44 | Broadbent--Karvonen, *Categorical Composable Cryptography*, Introduction and Section 3, especially Definition 1 and Theorems 1 and 3 | Models cryptographic transformations in symmetric monoidal categories, axiomatizes attack models, and proves composability/functorial preservation results. | Paraphrase | The paper supplies neither the concrete operational category nor the metered functor proposed here. |

The analogy between a lower-realization homomorphism and a monoidal functor is
an **inference**.  No theorem in the present paper depends on categorical
security syntax.

## 10. Probability-kernel randomization

| ID | Source and exact locator | Source-supported content | Classification in this project | Boundary that must not be crossed |
|---|---|---|---|---|
| SA45 | Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 3.22 (“kernels and randomization”) | A probability kernel from a measurable source to a Borel target admits a jointly measurable realization as a function of the source point and one independent uniform variable. | Paraphrase | The lemma supplies a pathwise seed realization, not an efficient sampler. The selected reservation, tariff, seed-index, and no-selection rules remain new operational structure. |

This result justifies replacing the informal phrase “fix every
state-dependent oracle sample” by a named uniform seed sequence and a selected
measurable sampler.  It does not make a noncomputable specification kernel
machine implementable.

## 11. Claim-to-source corrections required in the manuscript

1. The phrase “all admitted converters” in the unbounded discussion must not
   be used to identify mathematical information-theoretic resources with
   Turing-computable implementations.  MR16 discusses unrestricted converter
   classes; the operational image remains only the finite-code
   machine-generated fragment.
2. “Almost sure” and “strong” no-exhaustion coincide for finite exhaustion
   traces under full-support product Bernoulli tapes, because every finite trace
   fixes a positive-probability cylinder.  A separation needs accessible null
   branches of a non-full-support kernel or a different, infinite event.  This
   is a new elementary observation, not a literature claim.
3. The IITM nonclosure example must always retain its time-lock-puzzle
   assumption.
4. Causal boxes justify a cut-indexed design pattern, not a classical
   implementation theorem for the present machines.
5. Jost's uniform-PPT definition is evidence that the security parameter is
   unary and the family uniform; it does not settle scheduling, persistence,
   dynamic process generation, exact tariffs, or feedback.
6. MR16's discussion of RSS11 supports explicit memory and stateless
   converters in a memory-sensitive refinement.  It does not erase the
   multi-stage distinction or license hidden state in that refinement.
7. The source-supported algebraic laws are requirements on a lower
   instantiation.  The paper proves operational connection preservation and
   measure-level quotient congruence only for its explicitly selected
   route-safe/maximal-transcript carrier; comparison with another carrier and
   its nonresponse/feedback convention remains conditional.  The separate
   explicit-resource macro theorem is now proved only for the selected private
   sequential processor/store/coin/link APIs.
8. Equality of pointwise terminal outcome laws may be tested by arbitrary
   measurable predicates, but no cited computational framework licenses such
   a predicate as free efficient postprocessing.  The computational class
   therefore uses a fixed graded terminal-scorer code and charges its input
   and report processing.  This observer split is a new modeling obligation,
   not a literature theorem.
9. MR16's phrase “a computer resource” does not justify any atomicity,
   reservation, failure-owner, memory-cell, or routing convention.  Every such
   detail in the selected explicit-resource theorem is a new definition and
   must be justified by its stuttering proof and adversarial audit.

## 12. Stable primary links

- Maurer--Renner 2011:
  <https://crypto.ethz.ch/publications/files/MauRen11.pdf>
- Maurer 2011/2012: <https://doi.org/10.1007/978-3-642-27375-9_3>
- Maurer--Renner 2016:
  <https://doi.org/10.1007/978-3-662-53641-4_1>
- Maurer 2002: <https://doi.org/10.1007/3-540-46035-7_8>
- Lanzenberger--Maurer 2020:
  <https://doi.org/10.1007/978-3-030-64381-2_8>
- Matt--Maurer--Portmann--Renner--Tackmann 2018:
  <https://doi.org/10.1016/j.tcs.2018.06.001>
- Portmann--Matt--Maurer--Renner--Tackmann 2017:
  <https://doi.org/10.1109/TIT.2017.2676805>
- Jost 2020: <https://doi.org/10.3929/ethz-b-000417544>
- Ristenpart--Shacham--Shrimpton 2011:
  <https://eprint.iacr.org/2011/339>
- Hofheinz--Mueller-Quade--Unruh 2009:
  <https://doi.org/10.3233/JCS-2009-0354>
- Hofheinz--Unruh--Mueller-Quade 2013:
  <https://doi.org/10.1007/s00145-012-9127-4>
- Küsters--Tuengerthal--Rausch 2020:
  <https://doi.org/10.1007/s00145-020-09352-1>
- Canetti 2001: <https://eprint.iacr.org/2000/067>
- Backes--Pfitzmann--Waidner 2007:
  <https://eprint.iacr.org/2004/082>
- Broadbent--Karvonen 2022:
  <https://doi.org/10.1007/978-3-030-99253-8_9>
- Kallenberg 2002:
  <https://doi.org/10.1007/978-1-4757-4015-8>
