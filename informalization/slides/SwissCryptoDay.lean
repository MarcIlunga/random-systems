/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.

SwissCryptoDay 2026 — a 10-minute talk.  The non-adaptive PRF-security proof of
CBC, in CR18's notation, on a single proof slide (as CR18 presents it).  Every
glossed step sits behind a ⊕ expander (informalization's show-hidden-detail).
-/
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

#doc (Slides) "CBC is a PRF" =>

# CBC is a PRF

%%%
backgroundColor := "#181717"
%%%

Marc Ilunga · Trail of Bits · Swiss Crypto Day 2026

![Trail of Bits](tob-wordmark.svg)

:::notes
Hi — I have ten minutes, so I'll go straight into a proof. Everything I gloss
over is a ⊕ you can ask me to expand.
:::

# CBC, and the claim

* $`\mathsf{R}_{n,n}` — a uniform random function: each new input gets a fresh, uniform $`n`-bit answer.
* $`\mathsf{P}_n` — a uniform random permutation: the block cipher.
* $`\mathsf{V}_n` — the ideal: a uniform random function on messages.

$`\mathsf{CBC}` digests a fixed-length message $`m = (m_1, \dots, m_b)` block by block:

$$`y_0 = 0, \qquad y_i = \mathsf{F}(y_{i-1} \oplus m_i), \qquad \mathsf{CBC}\,\mathsf{F}\,(m) = y_b.`

**Theorem.** For a distinguisher issuing $`r` blocks in total,
$$`\mathsf{CBC}\,\mathsf{P}_n \;\xrightarrow{\;\epsilon\;}\; \mathsf{V}_n, \qquad \epsilon = r^2\,2^{-n}.`

# Proof

A block cipher is a $`\mathsf{P}_n`; by the triangle inequality it suffices to bound

::::fragment
$$`\Delta(\mathsf{CBC}\,\mathsf{P}_n,\, \mathsf{V}_n) \;\le\; \underbrace{\Delta(\mathsf{CBC}\,\mathsf{P}_n,\, \mathsf{CBC}\,\mathsf{R}_{n,n})}_{\text{PRP/PRF switch}} \;+\; \underbrace{\Delta(\mathsf{CBC}\,\mathsf{R}_{n,n},\, \mathsf{V}_n)}_{\text{CBC over a URF (Thm.\ 6.1)}}.`
::::

::::fragment
**(1)**  $`\Delta(\mathsf{CBC}\,\mathsf{P}_n,\, \mathsf{CBC}\,\mathsf{R}_{n,n}) \le \Delta(\mathsf{P}_n,\, \mathsf{R}_{n,n}) \le \tfrac{1}{2}\,r^2\,2^{-n}`. {class "inf-toggle"}[⊕]

:::class "inf-hidden"
Converter monotonicity (CR18 §4.7.2): a distinguisher for $`\mathsf{CBC}\,\mathsf{P}_n` and $`\mathsf{CBC}\,\mathsf{R}_{n,n}` simulates $`\mathsf{CBC}` to distinguish $`\mathsf{P}_n` from $`\mathsf{R}_{n,n}`. And $`\widehat{\mathsf{R}}_{n,n} \mathrel{|\!\equiv} \mathsf{P}_n` (Ex. 4.15): a $`\mathsf{R}_{n,n}` is a $`\mathsf{P}_n` until two outputs collide.
:::
::::

::::fragment
**(2)**  MBO $`A_i = 1` iff a *non-trivial* collision has occurred at the input to $`\mathsf{R}_{n,n}` by message $`i`. Then $`\widehat{\mathsf{CBC}\,\mathsf{R}_{n,n}} \mathrel{|\!\equiv} \mathsf{V}_n`. {class "inf-toggle"}[⊕]

:::class "inf-hidden"
Conditioned on $`A_i = 0` the inputs to $`\mathsf{R}_{n,n}` are distinct, so every output is uniform: $`p^{\mathsf{CBC}\,\mathsf{R}_{n,n}}_{Y^i \mid X^i,\, A_i=0} = p^{\mathsf{V}_n}_{Y^i \mid X^i}` (CR18 (6.2)).
:::
::::

::::fragment
By Theorem 4.17, $`\Delta(\mathsf{CBC}\,\mathsf{R}_{n,n},\, \mathsf{V}_n) \le \Gamma\!\left(\flat\,\widehat{\mathsf{CBC}\,\mathsf{R}_{n,n}}\right) \le \tfrac{1}{2}\,r^2\,2^{-n}`. {class "inf-toggle"}[⊕]

:::class "inf-hidden"
$`\flat` blocks the replies, so winning is non-adaptive: a collision among $`\le r` independent uniform $`n`-bit values.
:::
::::

::::fragment
Hence $`\Delta(\mathsf{CBC}\,\mathsf{P}_n,\, \mathsf{V}_n) \le r^2\,2^{-n}`.  $`\blacksquare`
::::
