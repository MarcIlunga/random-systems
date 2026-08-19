# Coupling gadgets for the `Machine` pseudocode surface

Stage-1 sketch (mathematics only) for the reasoning principles that turn
`RandomSystems/ResourceMachine.lean` from a *notation* for resources into a
*proof surface* for them.  Written before any Lean was opened for this task;
the reuse search is stage 3 at the bottom.

## What the surface already has, and what it is missing

`Machine`/`InterfaceMachine` gives an author a resource for the price of a
state type, an initial state, and one total `step` into `Option (State ×
AnswerAt query)`; `Machine.toDDS` discharges `empty_not_mem` and
`prefix_closed` generically, and `Machine.toDDS_eq_of_bisim` makes the state
representation refactorable.  `Machine.lawOf` turns a seed-indexed family into
a `DependentPDS.Prob`.

What is missing is the *reasoning* half.  Every construction proof in this tree
eventually owes a leaf of the form "the real composed system and the simulated
ideal system have the same behaviour".  Jost's Prop. 2.2.17 discharges such a
leaf in two moves:

1. **couple the two systems on the key** — pick a joint law on the two seed
   spaces;
2. **induct on the transcript, comparing answers** — check the two machines
   answer identically at each step.

Neither move is expressible today, so the leaf is instead proved by computing
the attachment driver by hand: `RandomSystemsCC/Symmetric/OTP.lean` spends
~2 800 lines and reaches its leaf through a bespoke `securityReindex`.

## The central modelling fact (and why one gadget is not enough)

The obvious gadget is

> a coupling `γ` of `seed₁, seed₂` with `Bisim (m₁ ω₁) (m₂ ω₂)` for every
> `(ω₁, ω₂) ∈ supp γ` gives `lawOf m₁ seed₁ = lawOf m₂ seed₂`.

It is true and it is worth having — but **it does not discharge the OTP leaf,
and it cannot**, because the OTP leaf is false at that strength.  Concretely:
`realSecurityDDS k` answers Eve `some (m + k)` where `m` is read off the
history, and `simulatedSecurityDDS c` answers `some c`.  As *functions of the
history* these differ for every pair `(k, c)` once `|G| > 1`, so no coupling on
`G × G` can make them bisimilar, and the two pushforward laws on
`DependentDDS` are genuinely unequal.  What is equal is the **behaviour**: for
each fixed transcript `t`, the bijection `k ↦ msg(t) + k` preserves the uniform
law and carries the real system's `t`-consistency to the simulated system's.

So the coupling is allowed to depend on the transcript, and the conclusion is
behavioural rather than pointwise.  That is not a weakening of Jost's move —
it *is* his move: "couple on the key" is a choice made after the transcript is
fixed, because the reduction to a fixed query schedule has already happened.

Hence **two** principles, plus the approximate variant of each:

| # | coupling | agreement hypothesis | conclusion |
|---|---|---|---|
| A | one `γ` for the whole system | `Bisim (m₁ ω₁) (m₂ ω₂)` on `supp γ` | `lawOf m₁ seed₁ = lawOf m₂ seed₂` |
| A′ | one `γ` | `(m₁ ω₁).toDDS = (m₂ ω₂).toDDS` off `Bad` | `contextualEDist ≤ ofReal (γ.mass Bad)` |
| B | one `γ_h` per query history | the two machines produce the same `s⊥` answer trace along `h` | `ObservableBehaviorEq`, hence equality in the contextual quotient |
| B′ | one `γ_h` per history | same trace off `Bad_h` | `|observableBehavior₁ t − observableBehavior₂ t| ≤ γ.mass Bad` |

A is the state-refactor / reparameterisation door (same randomness, different
bookkeeping).  B is the simulator door.  A construction proof that reaches for
A where B is needed will find the statement false, not merely unprovable —
which is the useful failure mode.

## The primitives underneath

Everything above factors through **one** elementary fact about finite-support
laws, which is where all of the probability lives:

> Let `γ` be a non-negative joint law on `Ω₁ × Ω₂` with marginals `X` and `Y`.
> Let `P₁ : Ω₁ → Prop`, `P₂ : Ω₂ → Prop`.
>   * if `P₁ p.1 ↔ P₂ p.2` for every `p ∈ supp γ`, then `X.mass P₁ = Y.mass P₂`;
>   * if that holds only off a set `Bad`, then
>     `|X.mass P₁ − Y.mass P₂| ≤ γ.mass Bad`.

Proof of the second (the first is the case `Bad = ∅`): write
`X.mass P₁ = γ.mass (P₁ ∘ fst)` (pushforward of mass along the marginal), split
`γ.mass (P₁ ∘ fst)` as good-part + bad-part, observe the good parts of the two
sides are literally the same event on `supp γ`, and bound each bad part by
`γ.mass Bad` using non-negativity.  No `Fintype` on the sample spaces is needed
— which matters, because the carrier `DependentDDS U σ` is not one.

Note the coupling must be **heterogeneous** (`Dist Ω₁` against `Dist Ω₂`); the
existing `DistCoupling` in `Coupling.lean` is the homogeneous `X Y : Dist A`
case used for the Lanzenberger–Maurer coupling lemma and does not type here.

Law equality (A) is then not even a mass statement: with
`lawOf m seed = fTransform (toDDS ∘ m) seed`, functoriality turns both sides
into pushforwards of `γ` and `Dist.fTransform_congr` (agreement on the support)
closes it.

## The missing bridge: what `s⊥` does to a package

Principle B talks about "the answer trace along `h`", and the definition it
must match is CR18 Def. 3.3's completion `s⊥`, which is *not* "run the machine
on `h`": `fullyDefined` evaluates at `keptPrefix S l.dropLast ++ [l.getLast]`,
i.e. it **deletes** the queries that would leave the domain and continues from
the surviving state.  Any statement of B phrased as "agree on prefixes of `h`"
is therefore wrong for partial resources.

The fix is a gadget worth having on its own:

> **the completion of a package is the skip-fold of its step function.**
> `botRunFrom m s [] = s`, and `botRunFrom m s (q :: r) = botRunFrom m s' r`
> where `s' = s` if `m.step s q = none` and `s' = fst` of the step otherwise.
> Then `keptPrefix` of the flattened package reaches exactly `botRunFrom`, and
> `(fullyDefined (m.toDDS.flatten)) h` is `Option.map` of the single step
> `m.step (botRunFrom m m.init h.dropLast) (h.getLast _)`.

With that, `keptPrefix` never appears again in an application file, and the
`observableBehavior` atom of a package becomes a statement purely about `step`.
This is the piece that replaces OTP.lean's `security_completion_apply_eq`
(≈ 100 lines, construction-specific) with one generic theorem.

The agreement hypothesis of B then has a clean sufficient condition: a relation
on states **indexed by the remaining history**, holding at initialisation and
preserved by the skip-step with equal answers.  Indexing by the remaining
history is exactly what lets the OTP relation say "`c = m + k` where `m` is the
message this history is going to send" — a relation that is *not* preserved by
arbitrary steps and so is not a bisimulation in the sense of A.

## Ladder

1. heterogeneous couplings + the two mass gadgets (pure `Dist`);
2. the `s⊥`/skip-fold computation for packages;
3. A, A′, B, B′ over 1–2;
4. the tape combinator for per-query randomness (eager sampling of a whole
   answer table) with a lazy↔eager receipt;
5. the integration test: the OTP security leaf, restated over machines and
   discharged by B.

## Reuse search (stage 3)

| needed | verdict | name |
|---|---|---|
| pushforward functoriality / support congruence | **LIB** | `Dist.fTransform_comp`, `Dist.fTransform_congr` |
| mass under pushforward | **LIB** | `Dist.mass_fTransform` |
| mass split, monotonicity, `≤ weight` | **LIB** | `Dist.mass_add_compl`, `Dist.mass_mono`, `Dist.mass_le_weight` |
| homogeneous coupling | **LIB, wrong type** | `RandomSystems.DistCoupling` — heterogeneous version is new |
| gluing two laws along a projection | **LIB** | `Dist.exists_coupling_of_fTransform_eq` (homogeneous) |
| bisimulation ⇒ equal denotation | **LIB** | `Machine.toDDS_eq_of_bisim` |
| typed metric = strict metric after flattening | **LIB** | `DependentPDS.contextual_edist_eq_max_edist_flatten` |
| accept mass is a `Dist.mass` | **LIB** | `StrictContext.acceptMass` is definitionally one |
| behaviour ⇒ transcript equivalence | **LIB** | `behavior_equivalent_iff_transcript_equivalent` |
| transcript ⇒ strict contextual equivalence | **LIB** | `StrictContextAdvantage.strict_equivalent_of_equivalent` (public; OTP.lean carries a private duplicate) |
| strict equivalence ⇒ quotient equality | **LIB** | `DependentRandomSystem.ofProb_eq_of_flatten_equivalent` |
| `s⊥` of a package | **NEW** | the skip-fold theorem above |
| heterogeneous coupling + mass gadgets | **NEW** | |
| A, A′, B, B′ | **NEW** | |

## Honesty caveats kept visible

* `Machine.toDDS` domains are order-sensitive, so a package is not
  `ScheduleAgnostic` in general (the constructor is expressive enough to encode
  a scheduling constraint).  Rushing-adversary statements keep owing their own
  receipts; see `STATUS.md` §11.31.  None of the gadgets above weaken that.
* B concludes behavioural equality, i.e. equality in the contextual quotient.
  It does **not** conclude equality of the laws, and for the OTP leaf the laws
  are unequal.  Any downstream statement that needs the law itself is not
  entitled to B.
* Attaching a converter to a package and getting a package back
  (`Machine.attach` with `(m.attach …).toDDS = DependentDDS.attach … m.toDDS`)
  is **not** in this ladder.  It is the other half of the port — the half that
  OTP.lean spends `decrypt_attach_eq`/`encrypt_attach_eq` (~1 400 lines) on —
  and it is a drive simulation against `PFun.fix`, not a coupling argument.
