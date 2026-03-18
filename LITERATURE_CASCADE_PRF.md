# Cascade / Composition / (P)RF Notes (offline)

This note is a local, implementation-oriented map from key literature to what we
need to formalize in `random-systems/`.

Scope of this note:
- Start from the simplest "composition of random functions" example (Maurer–Pietrzak 2004).
- Use it as a stepping stone toward cascade-style constructions (and later NMAC/HMAC).

Primary reference already in-repo:
- `random-systems/papers/MauPie04.md` (Maurer–Pietrzak, 2004).

## Terminology alignment (paper -> this codebase)

Paper (MauPie04) uses "random systems" as interactive objects. This repo models:
- A `DDS X Y q`: deterministic system answering `q` queries.
- A `PDS X Y q`: a distribution over `DDS X Y q`.
- `advantage S T`: supremum over *non-adaptive* input sequences of the transcript statistical distance.

Important: The paper distinguishes adaptive/non-adaptive distinguishers. In this repo:
- `advantage` is defined via non-adaptive input sequences (see `RandomSystems/Advantage.lean`).
  This is deliberate and matches the "optimize over non-adaptive inputs" approach used throughout.

## MauPie04: what matters for us

### Composition operators (Definition 10 in `MauPie04.md`)

Two operators are introduced:

1) `⋆` ("star"): for random functions E, F, query x, return `E(x) ⋆ F(x)` where `⋆`
   is a group operation on outputs.
   - This is the simplest PRF-style composition to implement first.
   - In game-based terms: if outputs live in an abelian group, `F(x) + G(x)` is again a PRF
     if F and G are independent PRFs (hybrid / replacement argument).

2) `∘` ("circle"): cascade / composition: for random permutations E, F, query x, return `F(E(x))`.
   - This is closer to CBC-like reasoning, but is more involved in RS formalization because it
     links the *output* of one component to the *input* of the other.

Our "simplest example" target:
- Implement the `⋆` operator at the level of *uniform random function oracles* (`Instances.URFfun`)
  and prove it preserves the ideal distribution.

### "Maximum condition" technique (Definitions 3,4,7,8 and Lemmas 3,5,6)

MauPie04's main technical gadget is the maximum condition (relative to G):
- It yields an upper bound of the form `Adv_adapt(F,G) <= mu_k(F, A) * (1 + ln(1/mu_k))` (paper
  narrative; see Lemma 3 / Lemma 5 region in `MauPie04.md`).

We already have a *Maurer 2002 condition-based framework* in:
- `random-systems/RandomSystems/ConditionBased.lean`

What we do *not* yet have (and will likely need for the full MauPie04 story):
- A formalization of the maximum condition itself.
- The submartingale bound used to relate its failure probability to advantage.

For now, the plan is:
1) Start with the `⋆` composition as a purely distributional fact about URFfun (no max-condition).
2) Use this as a testbed to decide the shape of "composition operators" in this repo.
3) Only then tackle MauPie04 maximum-condition lemmas, if/when needed for cascade (`∘`).

## Where the proof should live (planned)

- A first, self-contained Lean file that implements `⋆` on URFfun and proves:
  `URFfun ⋆ URFfun = URFfun` (perfect equivalence).

Suggested location:
- `random-systems/RandomSystems/Applications/CascadePRF.lean`

This keeps the development parallel to:
- `random-systems/RandomSystems/Applications/CTRMode.lean` (similar "pushforward + bijection" style)
- `random-systems/RandomSystems/Applications/CBCMAC.lean` (uses URFfun vs URF bridging, and injective-input reasoning)

## Next after the simplest example

Once `⋆` is in place and well-behaved:
1) Implement the `∘` (cascade) operator for permutations/functions as a construction.
2) Decide whether we need a general `Dist.prod` (product distribution) to model independence
   of sampled components.
3) For HMAC/NMAC, reuse the same "construction + hybrid" scaffolding, but we will likely rely on:
   - iterated constructions (`Construction.lean`), and
   - condition-based bounds (already in `ConditionBased.lean`) for collision-style events.

