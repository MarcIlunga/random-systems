# Stage 1 for hard targets: parallel exploration

## Contents

- When to escalate from a solo sketch to a fleet
- Why the bound is a *choice*, not a property of the technique
- The fan-out protocol, and how to brief a scout
- Effort scaling
- Synthesis, and what to do with the losers

---

## When to escalate

A solo sketch is right when the technique is obvious and the bound is standard. Escalate to
parallel exploration when **the quality of the answer depends on a choice nobody has made
yet**:

- the target bound is unknown, or a known bound must be *beaten*;
- more than one technique family plausibly applies;
- the construction is beyond-birthday, or the obvious route gives a birthday bound and you
  suspect better;
- the argument in the source paper does not transfer and you need a different idea.

Anthropic's research system found multi-agent orchestration outperformed the single-agent
baseline by **90.2%** on internal evals, and specifically that the gain comes from
**breadth-first tasks that pursue several independent directions at once**. Finding the
right bad event is exactly that shape. A single agent commits early and then rationalizes;
five agents disagree, and the disagreement is the information.

## The bound is a choice

The thing worth internalising before any fan-out:

> **For conditional equivalence, the MBO is a free parameter, and it determines the bound.
> A loose bound is a loose MBO — not a limit of the technique.**

Conditional equivalence with a collision MBO gives a birthday bound. That is a fact about
*collisions*, not about CE. A finer monitored condition — one that fires only on the events
that genuinely break the conditional equivalence — gives a finer bound, on the same
endpoint, with the same plumbing.

So when a route delivers `q²/N` and you believe the construction is better, **do not
conclude the technique was wrong.** Ask what the MBO is charging for that it does not need
to. The same applies to the H-technique's bad set and to a coupling's disagreement event:
in each family, the creative object is the one that sets the constant.

This is why stage 1 must be Lean-free and high-freedom. The library will happily hand you a
ready-made collision predicate. Taking it is a decision about the bound.

## The fan-out protocol

**1. Frame the question sharply**, then spawn scouts on *different* angles — not the same
question repeated. Overlap is the main failure mode; Anthropic's writeup records one
subagent researching a 2021 topic while two others duplicated each other on 2025 supply
chains, because the briefs were vague.

Angles that genuinely differ for a bound like this:

| angle | brief |
|---|---|
| **MBO refinement** | keep the technique, find a finer monitored condition; what is the current one over-charging for? |
| **Different family** | would H-technique / coupling / winnability give a better constant? Route it and estimate. |
| **Literature** | what is the best published bound for this construction, by what method, and does that method transfer to this carrier? |
| **Adjacent construction** | which formalized proof in this tree has the same shape? Is this an instance of something more general? |
| **Cross-field** | is the counting core a known object elsewhere — a mixing/coupling argument, a hypergraph count, a rank bound, a Fourier estimate? |
| **Lower bound** | how good *can* any bound be? An attack caps the ambition and tells you when to stop. |

The last two are where non-obvious answers come from, and they are the ones a solo sketch
skips.

**2. Brief each scout properly.** Every subagent needs, per Anthropic's guidance:

- **an objective** — one question, not a topic;
- **an output format** — for a sketch scout: the candidate object (MBO / bad set / coupling),
  the bound it yields, why it beats the incumbent, and what would have to be proved;
- **tools and sources** — papers to read visually, which library subtrees, whether to search
  mathlib;
- **clear boundaries** — say explicitly what the *other* scouts are covering so it does not
  duplicate them.

Tell each scout to report an **honest negative**: "this angle gives nothing better, because
X" is a real result and stops the orchestrator re-exploring it.

**3. Scouts do not write Lean.** They return mathematics. Formalization is stages 4–6, after
synthesis picks a winner.

## Effort scaling

Embed the scale in the brief rather than leaving the agent to judge it — agents are poor at
sizing their own effort:

| situation | fan-out |
|---|---|
| technique obvious, bound standard | **no fan-out** — solo sketch |
| one comparison (two candidate routes) | **2–4 scouts** |
| unknown bound, or beat a published one | **5+ scouts**, distinct angles, run in parallel |

Run scouts **in parallel, not serially** — that is where the wall-clock saving is.

## Synthesis

Collect the candidates and pick on evidence:

1. **Best provable bound**, not best conjectured bound. A scout that returns `q/N` with no
   route is worth less than one returning `q³/N²` with a named argument.
2. **Cost to formalize** — a slightly worse bound with every input already in the tree can
   beat a better one needing new machinery. Say which you chose and why.
3. **Keep the runners-up in the sketch.** Record rejected angles and the reason. That is the
   "technique, and the ones rejected" section, and it is what stops the next agent
   re-exploring dead ground.

Then the winner becomes the stage-1 sketch and the workflow continues normally: DAG, reuse
verdicts, skeleton, fill.

**If every scout lands on the same bound as the incumbent, that is a finding** — report it.
It means either the bound is tight on this carrier, or the whole fleet shared a blind spot,
and saying which you believe is more useful than another round.
