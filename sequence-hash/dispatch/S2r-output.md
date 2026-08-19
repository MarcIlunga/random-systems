Revised and overwrote [A2-sequencemac-prf.md](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/sketches/A2-sequencemac-prf.md).

- Fix 1: Replaced the HMAC/RKA bridge with an ordinary compression-PRF hybrid over the distinct `HeaderI`/`HeaderO` run-ups. Redefined $\varepsilon_{\rm KS}$ as that domain-separated run-up cost and included long-key `Derive(K)` hashing.
- Fix 2: Removed all H-technique routing. Hops now use classical equal-until-bad games, advantage triangles, explicit adaptive-to-nonadaptive replay, Gaži’s two hybrid families, and neutral birthday infrastructure. R4 is explicitly reserved for H-technique.

The five-term theorem and short/long customization split remain unchanged. Math delimiters and H-technique-exclusion checks passed; no Lean build was needed for this Markdown-only task.