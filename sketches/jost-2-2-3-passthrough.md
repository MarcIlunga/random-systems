# Jost Prop. 2.2.3, second clause — the one-sided pass-through

Stage-1 sketch for task #33.  Mathematics only; the Lean plan is at the end.

## 1. What the source actually says

`papers/ThesisJost.pdf`, printed p. 18 (PDF p. 34).  Proposition 2.2.3 has **two**
clauses, and the library formalized only the first:

> Let `P` and `Q` be two different parties, let `π_P` and `π_Q` be two converters, and
> let `R` be a resource.  Then for any suitable `γ_P` and `γ_Q` we have
> `π_P^{γ_P} π_Q^{γ_Q} R = π_Q^{γ_Q} π_P^{γ_P} R`.
> *Moreover, if `S` is another resource such that the interface sets of `R` and `S`
> are disjoint, then* `π_P^{γ_P} [R,S] = [π_P^{γ_P} R, S]`.

Clause 1 is `Converter.attachAt_comm` (`Jost/SurfaceCarrier.lean:172`).
Clause 2 is missing, and is exactly this task.  Its payoff is Theorem 2.2.5 (2)
(printed p. 19) — parallel composability — which Jost proves *from* it:
`π[R,T] = [πR,T] ⊆ [S,T]`.

## 2. Dictionary: why our `∥` is Jost's `[·,·]`

Jost's parallel (printed p. 17) is the **union of disjoint interface sets**:
resources `R_i` with `I_{P,i} ∩ I_{P,j} = ∅` compose into a resource whose party-`P`
interface set is `⋃_i I_{P,i}`.

Our `I` in `ResourceSystem S I` is Jost's set of **parties**; our *service* at
`i : I` is the alphabet of that party's whole interface set.  Under that dictionary
"union of disjoint interface sets" **is** the tagged sum of alphabets, i.e.
`Services.free`'s `.sum`.  Two consequences:

* `SurfacePar.lean:14`'s hedge ("TypedParallel's own reading of AC's `∥`") is
  stronger than it needs to be: the sum-coding is Jost-faithful, and the tagging
  performs the *renaming* Jost's disjointness precondition demands.  `R ∥ R` is
  legal here and denotes Jost's `[R, R']` for a renamed copy — that is the
  encoding doing the work, not a divergence.  (This answers task #38.)
* Jost's connection function `γ_P : I_in ↪ I_P` — which selects *which* of the
  party's interfaces the converter plugs into — becomes **tag dispatch inside the
  converter**.  Clause 2's side condition "`γ_P`'s image lies in `R`'s interfaces"
  becomes "the converter is `inLeft` of a converter for `R`".

## 3. The statement

For `α : Converter S.free s t` and a pass-through service `u`:

    inLeft α u : Converter S.free (.sum s u) (.sum t u)

    attachAt_inLeft :  (inLeft α u) •[i] (R ∥ T)  =  (α •[i] R) ∥ T      -- plain `=`

on the bundled carrier `ResourceSystem S.free I`, with `u = T.layoutAt i`.
`inRight` is the mirror.  Corollary (Thm 2.2.5 (2)), with `close_par` at `ε` and `0`:

    α •[i] R ≈[ε] Q   ⟹   (inLeft α u) •[i] (R ∥ T) ≈[ε] Q ∥ T

## 4. Two findings that reshape the task

### F1 — there is no `Converter.par`

`PFunConverter.par α β` (MauRen11 §6.2, `EmulateRealization.lean:3048`) routes by
`filterMap` on tags.  At a pair where every recorded answer is mis-tagged, the left
component sees an *empty* answer list and queries again — forever.  So its query
streaks are unbounded on its own trace tree and it fails `AnswersWithin`, hence
`IsDDC`.  `StrictParallel.lean`'s header records precisely this, and says it is why
that module built `parFixedLeftFn`/`parFixedRightFn`, which "attribute answers by
*count*" and are honest `IsDDC` objects with streak bound 2.

Status: a **documented assessment, not a theorem** — no `not_isDDC_par` exists in the
tree.  Either way the design conclusion holds: the composite object must attribute by
count, so the deliverable is the count-attributed one-sided lift, not a symmetric
`Converter.par`.  (Task #33's original title is unachievable as stated.)

### F2 — count attribution forces silence

With positional attribution the open round's answer segment is located by
`roundOffset` (`StepRealization.lean:1156`), so the converter must produce a move from
a segment that may be mis-tagged.  There is no total
`Out s ⊕ Out u → Out t ⊕ Out u` — it would need `Out s → Out t` — so on a mis-tagged
segment the converter must be **undefined**.  `Converter.ofRounds` cannot express
that: its `step` returns `X ⊕ V`, total.

CR18 §3.4.3 permits silence and `ProtocolFn` already carries it (`→. `), so the fix is
to generalize the constructor rather than to invent a junk element (`Inhabited (Out t)`
would work and is the alternative, rejected: it puts scaffolding in the surface).

    def ofHistoryStepPartial
        (step : (us : List U) → us ≠ [] → List Y → Option (X ⊕ V))
        (cnt  : List U → ℕ) : ProtocolFn U V X Y

    theorem isDDC_ofHistoryStepPartial
        (hcnt : ∀ us hne ys mv, step us hne ys = some mv →
                  (mv.isLeft ↔ ys.length < cnt us))
        (hL   : ∃ L, ∀ us, cnt us ≤ L) :
        IsDDC (ofHistoryStepPartial step cnt)

`hcnt` reads: *whenever it moves at all, it queries exactly while its budget lasts.*
It is what the two `IsDDC` clauses need — `AnswersWithin` needs only the ⟹ half
(no query past budget); `AnswersInY` needs the ⟸ half so that a round never closes
early and `roundOffset` stays aligned with the answers actually consumed.  Silence
stalls a round forever, which keeps both.  Receipt that the class was extended and not
forked (mirroring `ofStep_eq_ofHistoryStep`):

    ofHistoryStep step cnt = ofHistoryStepPartial (fun us h ys => some (step us h ys)) cnt

## 5. The construction

`Converter.Rounds S source target` — the authoring data `(step, calls, discipline,
bound)` that `ofRounds` currently consumes anonymously — becomes a named surface
object, because `∥`-lifting is a *syntactic* operation on a converter's pseudocode,
exactly as it is in Jost.  With `leftHist us' := us'.filterMap Sum.getLeft?`:

    calls' us' = match us'.getLast? with
                 | some (.inl _) => calls (leftHist us')
                 | some (.inr _) => 1
                 | none          => 0

    step' us' h ys' = match us'.getLast h with
      | .inl _ => (ys'.mapM Sum.getLeft?).map fun as =>
                    Sum.map Sum.inl Sum.inl (step (leftHist us') _ as)
      | .inr y => match ys' with
                  | []        => some (.inl (.inr y))     -- forward to the right component
                  | [.inr b]  => some (.inr (.inr b))     -- and answer with what it said
                  | _         => none                     -- mis-tagged: silent

`hcnt` for `step'`: the `.inl` branch inherits `α`'s own discipline through
`mapM`-length preservation; the `.inr` branch is `0 < 1` / `¬(1 < 1)` / vacuous.
`inRight` is the mirror.

### F3 — the §6.2 law cannot evaluate *any* Def-3.8 converter on a partial system

*Found while building, not in the original sketch.*  `PFunConverter.par α β` feeds
`α` the tag-**filtered** answer history

    p.2.filterMap fun oy => (oy.bind Sum.getLeft?).map some

which drops a `⊥` (and a mis-tagged answer) outright.  So `par α β` *moves past a
`⊥`* — exactly what `AnswersInY` forbids, and `AnswersInY` is half of `IsDDC`.
Every legal converter is silent there; `par α β` is not.  Consequently, at a
drive-reachable pair whose answer history carries a `⊥`, `inLeftFn` (silent, as
Def 3.8 requires) and `par αFn idFn` (moving) **disagree**, and
`apply_congr_of_driveReach` does not apply.

This is not a defect of the lift; it is why `PFunConverter.par` is not a Def-3.8
citizen in the first place (F1), showing up a second time on the evaluation side.

Two ways out:

1. **Totality.**  `(PFunDDS.par s t)⊥` returns `none` only off `dom (par s t)`.
   If `s` and `t` are total on nonempty histories then it never does, no `⊥`
   ever reaches the drive, and the only remaining disagreement is a mis-tagged
   answer — which `par s t`'s own routing rules out.  Totality is true of every
   resource (Jost Def. 2.2.1 is a *sequence of conditional distributions*) and is
   this library's standard hypothesis class (`KStepTotal`, `TotalOnNonempty`,
   discharged by `cr18_total`).  **This is the route to take.**
2. A direct realization proof in the shape of `apply_parFixedRightFn`
   (~700 lines), which needs no totality.

## 6. Proof route

Both sides leave the typed carrier by the two existing seams:

* `DependentDDS.flatten_attach_eq_apply_framed` (`TypedFraming.lean:6103`) —
  typed attachment **is** flat `apply` of the all-interface frame;
* `DependentPDS.flatten_parallel` (`TypedParallel.lean:405`) —
  flattening the typed `∥` **is** the relabelled flat `par`.

so the goal becomes a flat identity whose engine already exists:

    apply (par α β) (PFunDDS.par s t) = PFunDDS.par (apply α s) (apply β t)
      -- MauRen11 §6.2, `CompatibleMetric.lean:930`, under `AnswersInY α`, `AnswersInY β`

at `β = identity`, giving `apply (par α id) (par s t) = par (apply α s) t`.

**The one gap.**  `inLeftFn α` (count-attributed, `IsDDC`) is *not* `TraceEquiv` to
`par α idFn`: their trace trees differ exactly at the junk pairs where `par` keeps
querying and `inLeftFn` goes silent.  So `apply_toDDC_congr` (`ProtocolFn.lean:670`)
does **not** apply, and the recorded risk ("is `PFunConverter.apply` a trace
invariant?") resolves **no**.

What is needed instead is a **drive-level congruence**: two protocol functions that
agree on every pair the drive against a *given* system visits have the same `apply` at
that system.  Against `PFunDDS.par s t` every answer is correctly tagged (that is the
routing in `EmulateRealization.lean:3074`), so `inLeftFn α` and `par α idFn` agree
there.  This lemma does not exist; it is an induction over `driveOuter`'s fuel.

Fallback if that turns awkward: re-run `StrictParallel`'s realization pattern for
`inLeftFn` directly — `apply_parFixedRightFn` is ~700 lines of exactly this shape.
Same theorem, roughly 3× the cost.

## 6a. The governing frame: clause 2 is functoriality, not a theorem

*Added 2026-08-08, after the first landing.  This reframes everything above.*

Read the CC axioms as a signature.  Clause 1 (commutation at distinct interfaces)
and serial composition + identity say: the converters at an interface form a
monoid, the monoids commute pairwise, and they act on `Φ` — an action of a
**trace monoid** (independence = "different interface").  We have that:
`Gamma` + `gamma_commute` + `MulAction`.

Clause 2, `α^i[R,S] = [α^i R, S]`, is different in kind.  It says `α^i` acting on
a composite **is** `α^i ⊗ id`, i.e. that `∥` is a **bifunctor** and the action is
by whiskering.  A bifunctor needs an action on *morphisms*.

**Our `∥` is defined on resources only.  There is no `∥` on converters.**  That is
why clause 2 cannot be functoriality here and has to be proved by hand — and it
is the whole explanation of §4's F1/F2: `inLeftFn` *is* the missing morphism-level
`∥`, and F1/F2 are the proof that constructing it is genuinely expensive.

It also explains why the memoryless case was easy.  There the converter *is* a
pair of alphabet maps, `∥` on morphisms *is* `Sum.map`, and clause 2 is
`Sum.map f id` distributing over the coproduct — functoriality of the coproduct,
free.  Composition is not what does the work; the bifunctor is.

### Two hypotheses, only one of them written down

Jost states disjointness, and has already baked it into `[R,S]`'s own definition
(p. 17: *"A finite set of resources with **disjoint interface sets** can be viewed
as a single one"*); the restatement in Prop. 2.2.3 just re-invokes the
precondition.  The second hypothesis is implicit in the typing: for `π_P^{γ_P}R`
on the right-hand side to mean anything, **`γ_P` must land in `R`'s interfaces**.

Both can be baked in at the *type* level rather than as side conditions:
disjointness by putting the composite at `I ⊕ J` (a non-disjoint composite becomes
unwritable), and `γ ⊆ R` by typing converters at `i : I`, so they attach to
`R ⊗ T` at `inl i`.

### The catch: our attachment is unary, Jost's is n-ary

Jost's `γ : I_in ↪ I_P` is an injection from a **set** of inner interfaces, and
`π^γ R` has `I'_P = I_P \ img(γ) ∪ I_out` (p. 18) — attachment *changes* the
interface set.  Fig. 2.3's π_ε^A has two inner interfaces (A of the key resource,
A of the authenticated channel) and one outer, so **clause 2 does not apply to the
flagship converter** — it is for protocols touching one component only.

`Converter S source target` is unary.  The merged-service coding
(`Services.free`, `In (.sum a b) = In a ⊕ In b` definitionally) is exactly how we
simulate Jost's n-ary γ inside a unary attachment, and it is why `encA`/`decB` are
expressible at all.  So the two encodings are **dual**, not better/worse:

| | `∥` on converters (the bifunctor) | multi-interface converters (γ) |
|---|---|---|
| merged services (current) | expensive — `inLeft`, count attribution, silence | free |
| disjoint `I ⊕ J` | free | not expressible — `attach` is unary |

We need both: the flagship needs γ over two components, the composition theorem
needs the bifunctor.

### The proposed resolution, and the one claim that must be checked

    n-ary attach at {i, j}  =  (merge i and j into one interface) ; (unary attach)

with `merge` a pure **re-indexing of the boundary** — no behaviour, hence a
relabelling, in the same sense that `flatten_attach_ofMaps_eq_relabel` shows a
memoryless bijection converter attached at an interface *is* `DDS.relabel`.  Under
that reading the current design is *merge applied globally and permanently, at
every interface, once and for all* — which is precisely what `Services.free` and
`.sum` are, and which explains both cells of the table: pre-merging makes γ free
and leaves no `T` factor for `id` to act on.

So: take disjointness by construction, and take the merge **locally and
explicitly** where a converter actually needs it.

Load-bearing and unverified: that `merge` really is a relabelling on this kernel
and not something with content.  That is checkable rather than arguable, and is
under test in the `TypedTensor.lean` spike.

### DECIDED (2026-08-08)

Bake it in.  Parallel composition is `⊗` at the disjoint interface set `I ⊕ J`;
a non-disjoint composite becomes unwritable, and clause 2 becomes functoriality
rather than a conditional theorem.  The `apply_inLeftFn` route is superseded;
`OneSidedConverter.lean` becomes dead once `⊗` lands.  `ofHistoryStepPartial` and
`DriveReach`/`apply_congr_of_driveReach` are general-purpose and stay.

Consequences, in order of dependency:

1. `RandomSystems/TypedTensor.lean` — `⊗` through all three levels, clause 2, the
   eq.-(3) metric, the cancellation analogue of `parallel_inj`.
2. `merge` as a first-class re-indexing, with the isomorphism and the isometry,
   and `n-ary attach = merge ; attach`.  Expected: `HasSumCode`/`Services.free`/
   `SumService` survive but stop being the coding for *parallel composition* and
   become the coding for *merge* — which is where they belong.
3. Surface migration.  The bundled carrier becomes **index-varying**: `Φ` is a
   family indexed by interface sets — a symmetric monoidal category rather than a
   set with operations.  Maurer11 fn. 9 ("again a resource with the same interface
   set") constrains *attachment*, not parallel composition, so there is no
   conflict with Def. 1; the module header must say so rather than leave it to the
   reader.  Jost Thm 2.2.5 (2) then follows from functoriality + `close_par`.
4. Renderer: `∥` no longer keeps one port per party.  Each party gets one port per
   component — which is what the paper figures actually draw — and a `merge`
   becomes a *visible* element, the bracket gathering two ports before a converter
   attaches, exactly as Jost Fig. 2.3 draws it.

The one thing that could still overturn (2) is the merge result.  It does not
overturn the decision — disjointness is baked in either way — it changes only how
n-ary converters are recovered on top of it.

## 7. Staging and status

| # | where | content | status |
|---|---|---|---|
| 1 | `StepRealization.lean` | `ofHistoryStepPartial`, `isDDC_ofHistoryStepPartial`, `ofHistoryStep_eq_ofHistoryStepPartial` + the membership receipt | **done** |
| 2a | `ProtocolRealization.lean` | `sysAnswer(s)`, `DriveReach`, `drive_congr_of_driveReach`, `driveOuter_congr_of_driveReach`, `apply_congr_of_driveReach` | **done** |
| 2b | `OneSidedConverter.lean` | `leftOuter`, `inLeftCount`, `inLeftStep`, `inLeftFn`, `isDDC_inLeftFn` | **done** |
| 2c | `OneSidedConverter.lean` | tag faithfulness of `(par s t)⊥`; the drive invariant (a left round issues only left-tagged queries, `roundOffset` tracks the answers consumed); the alignment equation `untag (ys.drop offⱼ) = (leftAnswers ys).drop offα`; then `apply_inLeftFn` under totality, via `apply_parallel_eq_parallel_apply` + `apply_idFn` | **open** (~450 lines) |
| 2d | `OneSidedConverter.lean` | `inRightFn`, mirror of 2b/2c | **open** (~250 lines) |
| 3 | typed | transport through `flatten_attach_eq_apply_framed` / `flatten_parallel`; `ResourceAt.attach_par` (HEq, demoted), then bundled `attachAt_inLeft` (plain `=`) | **open** (~300 lines) |
| 4 | surface | `Converter.Rounds`, `inLeft`/`inRight`, Thm 2.2.5 (2) as a `close` corollary, `#cc_moves` pin, a `lift_par` rewrite in `SurfaceMoves` | **open** (~250 lines) |

Landed so far: ~430 lines, all axiom-clean and building.  Remaining ≈ 1250.

Two name collisions found and settled while landing 2a: `PFunConverter.drive_congr`
and `driveOuter_congr` already exist in `CompatibleMetric.lean` with the weaker
outer-history-only hypothesis, so the drive-reachability versions carry the
`_of_driveReach` suffix.  `mapM_length` was promoted out of `TypedAttachment`'s
`private` section into `ProtocolFn.lean` (the lowest module both users see).
