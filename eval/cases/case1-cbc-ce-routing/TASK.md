# Task

`RandomSystems/CBCMAC.lean` contains the CBC-MAC model: the converter, the real
system `cbcReal`, the game `cbcGame` with its monotone bad predicate `cbcBad`,
the ideal VIL-URF `Vn`, and the supporting lemmas.

The headline theorem `cbc_mac_randomness_expander` is stated but unproved:

```lean
theorem cbc_mac_randomness_expander [Nontrivial M] (bf : M → List X) (q L : ℕ)
    (hbf_pf : PrefixFree bf) (hL : ∀ m, (bf m).length ≤ L) :
    Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) ≤
      (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ)
```

**Produce a compiling proof skeleton for it.** Every genuinely creative
obligation may be left as `sorry`; every routine side condition and every step
that an existing library theorem supplies must be discharged or cited.

The file must compile.

## What is being measured

Not whether you close the mathematics — the creative leaves are allowed to stay
open. What is measured is:

- which endpoint the skeleton routes through;
- how much new surface you mint versus reuse;
- whether a sketch and an obligation plan preceded the Lean.
