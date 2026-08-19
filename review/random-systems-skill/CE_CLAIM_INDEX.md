# Conditional-equivalence claim index

This is a coverage index, not a verdict report.  Line numbers refer to the
SHA-256 snapshots in `AUDIT_PLAN.md`.  Reviewers may split an entry further;
they may not merge entries in a way that hides a claim.

| ID | File lines | Review unit |
| --- | --- | --- |
| CE-001 | `conditional-equivalence.md:15-17` | Characterization of when CE should be used and what kind of event an MBO is. |
| CE-002 | `:19` | Displayed blind-winning endpoint and its omitted/implicit hypotheses. |
| CE-003 | `:25-29` | Definition and consequence of strict CR18 conditional equivalence. |
| CE-004 | `:30-34` | Statement and interpretation of MPR07 Lemma 5. |
| CE-005 | `:35-39` | Attribution and separation of representative/coupling attainment. |
| CE-006 | `:41-49` | Five-step design sequence, including the condition for calling an object a coupling. |
| CE-007 | `:51-54` | Simulator redesign versus representative selection. |
| CE-008 | `:58-62` | Claim that the MBO is free and refinement refines the bound. |
| CE-009 | `:64-67` | Diagnosis of looseness via MBO or simulator. |
| CE-010 | `:69-75` | Exact four-part statement of MPR07 Lemma 5. |
| CE-011 | `:77-81` | Erasure/pre-winning interpretation, construction mechanism, and non-implication for strict CE. |
| CE-012 | `:83-92` | Four proposed proof-design moves and their terminology. |
| CE-013 | `:94-98` | Source of an asymptotic rate in a CE proof. |
| CE-014 | `:100-102` | Requirements for a replacement condition to improve a theorem. |
| CE-015 | `:104-107` | Claim that choosing a ready-made predicate decides a constant and that MBO search requires fan-out. |
| CE-016 | `:109-113` | “Two doors,” “almost always right,” and packaged-theorem source location. |
| CE-017 | `:115-126` | Exact signature of `maxAdvantage_filterQueries_seededConditionCGame_le`. |
| CE-018 | `:128-131` | Applicability criterion and coverage of CBC-MAC, NMAC, switching, and “most keyed constructions.” |
| CE-019 | `:135-141` | Classification and proposed discharge of every packaged-theorem hypothesis. |
| CE-020 | `:143-147` | Meaning of `blindQueryList`, removal of adaptivity, and what survives in counting. |
| CE-021 | `:149-151` | Supporting declaration names, role in wrapper, and source ranges. |
| CE-022 | `:153-164` | Raw-theorem locations and exact signature. |
| CE-023 | `:166-171` | Hypothesis count, “adaptive blind winners,” relation between the two doors, and usage restriction. |
| CE-024 | `:173-189` | Whether the skeleton typechecks and whether each placeholder/classification is sound. |
| CE-025 | `:193-201` | CBC-MAC exemplar, proof shape, arithmetic characterization, and number of scheme-specific inputs. |
| CE-026 | `:203-211` | Claimed general proof shape, keyed-cascade fiber argument, and fixed-schedule combinatorics. |
| CE-027 | `:215-217` | Representation of `CondEquiv`, normalizer guards, absence of division/`DecidableEq`, and line location. |
| CE-028 | `:218-219` | Filter-preservation declaration names, locations, and “never re-prove” guidance. |
| CE-029 | `:220` | Claimed contents of `GameOf.lean`. |
| CE-030 | `:221-222` | CBC structure-graph route, equality of bound, tolerant CE, and counting-engine status. |
| CE-031 | `:223-224` | `seededHashCollision` location, monotonicity, applicability, and reuse directive. |
| CE-032 | `:228-229` | Claim that users should never prove a blind-winning bound directly. |
| CE-033 | `:231-233` | Equality character of `hCE` and allocation of all differences to `Γᵇ`/`hleaf`. |
| CE-034 | `:235-237` | MBO monotonicity and validity of replacing a nonmonotone event by its monotone closure. |
| CE-035 | `:239-241` | `ignoreMBO` identity, library availability, and universality across constructions. |
| CS-001 | `creative-search.md:15-23` | Conditions asserted to justify multi-agent exploration. |
| CS-002 | `:25-29` | 90.2% empirical result, causal interpretation, breadth-first prescription, and five-agent claim. |
| CS-003 | `:35-38` | Freedom to choose an MBO among CE-establishing conditions and interpretation of its winning probability. |
| CS-004 | `:40-45` | Claim that CE imposes no rate and that rates enter through winning-probability analysis. |
| CS-005 | `:47-53` | Consequences of changing MBO/simulator and separation from other proof objects. |
| CS-006 | `:55-57` | Status of a ready-made predicate as candidate rather than evidence. |
| CS-007 | `:61-78` | Claimed fan-out failure mode and whether the listed angles are independent. |
| CS-008 | `:80-94` | Attribution of briefing requirements to Anthropic and prohibition on scouts writing Lean. |
| CS-009 | `:98-107` | Claims about agent sizing, recommended fleet sizes, and parallel wall-clock benefit. |
| CS-010 | `:111-126` | Synthesis rules and inference from unanimous scout outcomes. |

