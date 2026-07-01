/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.
-/
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option verso.code.warnLineLength 100

/-! The informalization presentation, hosted by Verso's reveal.js slide genre.
Lean code blocks are elaborated, highlighted, and CLICKABLE (click a token to see
its proof state / info); our informalized prose sits beside the formal proof. -/

#doc (Slides) "To formalized mathematics — and back" =>

# To formalized mathematics — and back

%%%
backgroundColor := "#181717"
%%%

*Informalization*: turning a checked Lean proof into a readable, interactive
document.

A companion to the *verbose layer* and *cnl-rs*.

![Trail of Bits](tob-wordmark.svg)

:::notes
Formalization goes English → Lean. Informalization is the missing arrow: Lean → English.
:::

# The missing arrow

Formalization takes English to Lean. We add the arrow back:

:::table +colHeaders
*
  * Direction
  * Who
*
  * English $`\longrightarrow` Lean (*formalization*)
  * a human, by hand
*
  * Lean $`\longrightarrow` English (*informalization*)
  * this tool, mechanically
:::

The output is *not wrong* by construction: it is symbolic, not an LLM. Every
displayed claim traces to a kernel-checked term.

# A theorem, formalized

Composition of injective functions is injective — the Lean proof. *Click a token*
to see the proof state.

```lean
theorem inj_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro a b h
-- ^ !click
  exact hf (hg h)
```

:::notes
The Lean is exact but terse: `exact hf (hg h)` is written to be understood by the
computer, not the reader.
:::

# The same theorem, informalized

Let $`\alpha`, $`\beta` and $`\gamma` be types. Let $`f : \alpha \to \beta` and
$`g : \beta \to \gamma` be injective functions. Then $`g \circ f` is injective.

*Proof.* The composite $`g \circ f` is injective. {class "inf-toggle"}[⊕]

:::class "inf-hidden"
Let $`a` and $`b` be elements of $`\alpha`. Assume {class "inf-hover"}[$`(g \circ f)\, a = (g \circ f)\, b`].
Since {class "inf-hover"}[$`g` is injective], $`f\, a = f\, b`. Since $`f` is injective, $`a = b`. $`\blacksquare`
:::

:::class "inf-goal"
$`a, b : \alpha,\quad h : g\,(f\,a) = g\,(f\,b) \ \vdash\ a = b`
:::

:::class "inf-goal"
$`g\,(f\,a) = g\,(f\,b) \ \vdash\ f\,a = f\,b`
:::

Hover a dashed phrase for its proof state; click *⊕* to unfold. Generated from the
theorem's *type* and *proof term*.

# Reductions compose — CR18 Lemma 4.5

Informalized close to Maurer's own words (*Cryptography Foundations*, §4.4.8).

Let $`p`, $`q` and $`r` be problems, $`\rho` and $`\rho'` solver-transformations,
and $`\tau` and $`\tau'` $`\le`-respecting functions. Then
$`\tau p \le q \rho \,\wedge\, \tau' q \le r \rho' \Rightarrow \tau' \tau p \le r \rho' \rho`.

*Proof.* The two reduction inequalities compose. {class "inf-toggle"}[⊕]

:::class "inf-hidden"
Composing both sides of $`\tau p \le q \rho` with the $`\le`-respecting function
$`\tau'` on the left side results in {class "inf-hover"}[$`\tau' \tau p \le \tau' q \rho`], since
$`\tau'` is $`\le`-respecting. Composing both sides of $`\tau' q \le r \rho'` with $`\rho` on
the right side results in $`\tau' q \rho \le r \rho' \rho`. We conclude
$`\tau' \tau p \le r \rho' \rho` by combining the two inequalities. $`\blacksquare`
:::

:::class "inf-goal"
$`\tau p \le q \rho \ \vdash\ \tau' \tau p \le \tau' q \rho` — by left-composition with the $`\le`-respecting $`\tau'`.
:::

# How it reads at depth

A proof step carries its *proof state*, summoned on demand — context on the side,
the sentence stays clean.

```lean
example : a = b → b = c → c = d → d = e → a = e := by
  intro h1 h2 h3 h4
  rw [h1, h2, h3, ←h4]
```

:::notes
Click the individual rw steps to cycle through intermediate proof states — the
"show the hidden details" affordance.
:::

# The pipeline

* The Lean proof is read as data (type, proof term, info trees).
* A grammar engine grounded in *GF / Resource Grammar Library* and *Reiter–Dale*
  microplanning realizes it as English — articles, agreement, and aggregation
  are computed, not guessed.
* Output is a structured document: show-hidden-detail, hover proof-states.
* Verso hosts it — so the prose and the *clickable* Lean live in one deck.

:::fragment
Formal and informal, side by side, in one checked document.
:::

# Thank you

:::fragment
Questions?
:::

:::notes
The slides themselves are a Verso document; the Lean is real and checked.
:::
