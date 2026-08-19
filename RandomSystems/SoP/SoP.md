# Sum-of-permutations proof index

The two constructions are different and their proofs are kept separate.

| File | Real oracle |
|---|---|
| [`SoP1.md`](SoP1.md) | One uniform permutation $\pi$ on $X\times\{0,1\}$, with output $\pi(x,0)+\pi(x,1)$ |
| [`SoP2.md`](SoP2.md) | Two independent uniform permutations $\pi_1,\pi_2$ on $G$, with output $\pi_1(x)+\pi_2(x)$ |

The corresponding Lean files are `SoP1.lean` and `SoP2.lean`.
`Common.lean` contains only generic lemmas used by both formalizations; it
defines neither oracle and proves no construction-specific bound.
