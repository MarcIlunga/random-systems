# Conditional equivalence (CR18 Thm 4.17)

## Contents

- The MBO sets the bound
- There are two doors — pick the packaged one
- Skeleton, statement-first
- A finished instance to read (after routing)
- Related surface
- Traps

---

**The bad thing is a condition the distinguisher triggers.** Use it when transcripts are not
enough: adaptive, stateful systems where the bad event is something the adversary *causes*
rather than a property of the transcript.

`Δ(S,T) ≤ Γᵇ(gameOf S cond)` — the maximal *blind* winning probability of the monitored game.

## The MBO sets the bound

`cond` is a **free parameter**, and it is the only thing standing between you and a tighter
result. The endpoint is an inequality against `Γᵇ` of *your* monitored game: refine the
condition and the bound refines with it, on the same endpoint, with the same plumbing.

So the single most important habit in this family:

> **A loose bound is a loose MBO — not a limit of the technique.**

**This is a theorem.** Maurer–Pietrzak–Renner, *Indistinguishability Amplification*
(CRYPTO 2007), **Lemma 5** (`papers/MaPiRe07.pdf`, p. 140):

> For any two `(X,Y)`-systems `S` and `T` there exist `(X, Y×{0,1})`-systems `Ŝ`, `T̂` with
> MBOs such that (i) `Ŝ⁻ ≡ S`, (ii) `T̂⁻ ≡ T`, (iii) `Ŝ⊣ ≡ T̂⊣`, and
> (iv) `δ_k^D(S,T) = ν_k^D(Ŝ) = ν_k^D(T̂)` **for all `D`**.

Here `Ŝ⁻` ignores the MBO and `Ŝ⊣` masks the output once the MBO fires, so (iii) *is*
conditional equivalence and (iv) says the distance **equals** the winning probability —
per distinguisher, not just in the supremum. MPR07 §1.4: this settles a main open problem
from [MP04], whose Lemma 9 was loose by a logarithmic factor. **Lemma 5 is tight.**

So **conditional equivalence is complete: it has no inherent ceiling.** Whatever bound your
MBO gave, a monotone condition exists that would have given the exact answer. Never conclude
"this is the best CE can do" — that conclusion is unavailable.

### The caveat that decides how you use it

The MBO in Lemma 5 lives on **`Ŝ`, a system equivalent to `S`** — not necessarily as a
deletion on the representative you happen to be holding. The construction is the
`min(P,Q)` split (MPR07 illustrates it for distributions: `P̂(x,0) = Q̂(x,0) = min(P,Q)`,
with the surpluses pushed onto the MBO-fired branch). That **redistributes** mass; it does
not merely delete it.

That matters, because a monitored condition on a *fixed* representative can only delete —
it cannot move surplus on one transcript to cover a deficit on another, while `Δ` averages
surplus and deficit. So a floor you hit while deleting on your given system is a fact about
that representative, **not** about the technique.

Two live moves when a bound disappoints, in order:

1. **Refine the condition** — what is it charging for that it does not need to? This is the
   usual answer and where improvements come from.
2. **Change the representative** — Lemma 5 says a tight one exists. Exhibiting an explicit,
   checkable `Ŝ` is the hard creative work, since the lemma is an existence result and hands
   you no describable combinatorial event.

**Do not confuse this with coupling attainment.** Lanzenberger Thm 2.31/2.32 give
*equivalent representatives whose statistical distance or coupling disagreement realizes
`Adv`* — that is the coupling side, and it does **not** by itself yield a tight MBO. The
thesis is explicit (printed p. 32) that reading "`F` is ideal with probability `1 − Adv`" as
a *conditioning* is unsound, because conditioning also conditions the ideal system; it uses
a coupling there instead. Cite Lemma 5 for CE completeness, Thm 2.31/2.32 for coupling.

Picking `seededHashCollision` because it is sitting there gives you a birthday bound. That is
a fact about *collisions*, not about conditional equivalence. If you believe the construction
is better than birthday, the question is never "should I switch technique" first — it is
**"what is my MBO charging for that it does not need to?"**

Concretely, an MBO that fires on *any* collision charges for collisions that do not actually
break the conditional equivalence. Narrowing it to the events that genuinely break `|≡` is
what buys the beyond-birthday regime.

This is also why the sketch must precede the library search. The tree offers ready-made bad
predicates; taking one is a decision about your constant, made before you noticed you were
making it. When the bound matters, see
[creative-search.md](creative-search.md) — searching for the MBO is a fan-out task.

## There are two doors. Pick the packaged one.

### Door 1 — packaged (almost always right)

`RandomSystems/SwitchingLemma.lean:1864`

```lean
maxAdvantage_filterQueries_seededConditionCGame_le
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    (hmono : ∀ a, ∀ {l₁ l₂}, l₁ <+: l₂ → bad a l₁ → bad a l₂)
    (q : ℕ) (T : PFunPDS I O) (ε : NNReal)
    (hCE  : seededConditionCGame D F bad |≡ T)
    (hD   : D.isProbDist) (hT : T.isProbDist)
    (hTtot : CondEquiv.TotalOnNonempty T)
    (hleaf : ∀ w : PFunDDS.Winner I O, IsBlind w →
      D.mass (fun a => bad a (blindQueryList w q)) ≤ ε) :
  Δ(⌈q⌉ PFunPDS.ignoreMBO (seededConditionCGame D F bad), ⌈q⌉ T) ≤ (ε : ℝ)
```

**Applicability test:** is the real system a *seed-indexed last-query evaluator* — sample
`f ← D`, answer query `x` with `F f x`, and carry a monotone bad bit? If yes, this is your
endpoint. That covers CBC-MAC, NMAC, the switching-lemma family, and most keyed
constructions.

**Obligations:**

| hypothesis | class | how |
|---|---|---|
| `hmono` | `[ROUTINE]` | `bad` is prefix-monotone. Usually a few lines; a genuine check, not a formality |
| `hD`, `hT` | `[ROUTINE]` | `Dist.uniform_isProbDist`, the ideal world's own lemma, or `cr18_prob` |
| `hTtot` | `[ROUTINE]` | the ideal world's `TotalOnNonempty` lemma, or `cr18_total` |
| **`hCE`** | **`[CREATIVE 1]`** | the conditional equivalence: conditioned on not-yet-bad, the game's output law **equals** the ideal system's |
| **`hleaf`** | **`[CREATIVE 2]`** | the seed mass of `bad` on a blind winner's **fixed** query schedule |

**The one structural fact worth internalising:** `hleaf` is stated over
`blindQueryList w q` — a *fixed list*. **The blind reduction has already converted the
adaptive bad-event bound into a non-adaptive one.** Nothing adaptive survives to the
counting layer. If you find yourself reasoning about what an adaptive adversary might query,
you are re-deriving something this endpoint already gave you.

Supporting facts, all `[LIB]`, all supplied inside the wrapper — do not prove them:
`seededConditionCGame_monotoneMBO`, `seededConditionCGame_isProbDist`,
`seededConditionCGame_totalOnNonempty` (`SwitchingLemma.lean:1833-1858`).

### Door 2 — raw Theorem 4.17

`RandomSystems/GameOf.lean:1343` (unfiltered), `:1359` (filtered `q+1`), `:1383` (all `q`).

```lean
maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization
    (S T) (cond : List (X × Y) → Bool)
    (hcond : PFunDDS.MonotoneCond cond) (hS : S.isProbDist) (hT : T.isProbDist)
    (hStot hTtot : CondEquiv.TotalOnNonempty _)
    (hNorm : DeltaFiniteQueryNormalization S T) :
  (gameOf S cond |≡ T) → (Δ(S, T) : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ)
```

Seven hypotheses plus the conditional equivalence, and **you now own `Γᵇ` yourself** — the
blind maximal winning probability, over adaptive blind winners. That is a substantial extra
proof obligation, and it is exactly what Door 1 discharges for you.

Use Door 2 only when the real system is genuinely not a seeded evaluator. If you are here,
say why in a comment.

## Skeleton, statement-first

```lean
theorem my_ce_bound … : Δ(⌈q⌉ Real, ⌈q⌉ Ideal) ≤ ε := by
  calc Δ(⌈q⌉ Real, ⌈q⌉ Ideal)
      = Δ(⌈q⌉ PFunPDS.ignoreMBO (seededConditionCGame D F bad), ⌈q⌉ Ideal) := by
        rw [my_game_ignoreMBO]                      -- [LIB] the game forgets its MBO
    _ ≤ (ε : ℝ) := by
        exact maxAdvantage_filterQueries_seededConditionCGame_le
          D F bad (by sorry)                        -- hmono      [ROUTINE]
          q Ideal ε
          (by sorry)                                -- hCE        [CREATIVE 1]
          (by sorry) (by sorry) (by sorry)          -- isProbDist ×2, TotalOnNonempty
          (by sorry)                                -- hleaf      [CREATIVE 2]
```

Compile this, *then* fill.

## A finished instance to read — AFTER you have routed

`RandomSystems/CBCMAC.lean` proves the CBC-MAC randomness-expander bound through this
endpoint. **Do not open it before you have done stages 1–3 yourself.** It is a worked
instance, not a template: reading it first collapses routing into a lookup and you learn
nothing transferable — which is exactly what happened when this skill was first tested.

What it looks like once you have routed there yourself: a three-hop `calc` — strip the MBO,
apply the packaged endpoint, close the birthday arithmetic — with exactly two
scheme-specific inputs, the conditional equivalence and the fixed-schedule bad-mass count.
Everything else is a citation.

The shape generalises; the lemma names do not. Your scheme needs *its own* answers to the
same two obligations:

- **the conditional equivalence** — conditioned on not-yet-bad, the game's output law is
  *exactly* the ideal system's. For a keyed cascade this is typically a re-randomisation /
  fiber-balance argument: some group action on the seed moves every answer while fixing the
  internal call-site inputs, so the answer fibers are balanced.
- **the fixed-schedule bad-mass bound** — pure combinatorics over a *fixed* query list,
  reached only because the blind reduction removed adaptivity.

## Related surface

- `RandomSystems/CondEquiv.lean` — the definition of `|≡` (CR18 Def 4.19 / eq. 4.38), stated
  in **cross-multiplied, division-free** form guarded by two normalisers, so conditioning
  never introduces a division or a `DecidableEq`. `TotalOnNonempty` is at `:96`.
- `condEquiv_filterDom` (`:203`), `condEquiv_filterQueries` (`:237`) — `|≡` survives domain
  restriction and query filtering. `[LIB]`; never re-prove a filtered variant.
- `RandomSystems/GameOf.lean` — `gameOf`, `Γᵇ`, the blind machinery.
- `RandomSystems/CBCStructureGraph.lean` — the Jha–Nandi structure-graph route to the same
  CBC bound, with a tolerant CE and a full counting engine.
- `seededHashCollision` (`SwitchingLemma.lean:1889`) + its monotonicity — the ready-made
  `bad` predicate for hash-collision arguments. Reuse it rather than defining your own.

## Traps

**Do not prove `Γᵇ` bounds by hand.** If `Γᵇ` is in your goal you are on Door 2. Check
whether Door 1 applies first.

**`hCE` is an equality, not a bound.** `|≡` says the conditioned law *equals* the ideal law.
If you are bounding a difference there, you have the wrong obligation — that difference is
what `Γᵇ`/`hleaf` accounts for.

**The MBO must be monotone.** `bad` is prefix-monotone: once triggered, it stays triggered.
If your event can un-fire, it is not an MBO and this technique does not apply as stated —
strengthen the event to its monotone closure.

**Watch the `ignoreMBO` step.** The real system is the game with its bit forgotten. That
rewrite is `[LIB]` and every construction in the tree has one; find it rather than proving
it.
