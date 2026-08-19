Created [A4-indiff-prf.md](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/sketches/A4-indiff-prf.md).

The proposed R3 guardrail is:

$$
\Delta(\lceil q\rceil\mathsf{SM}_H,\lceil q\rceil\mathsf{URF})
\le \varepsilon_{\mathrm{ind}}(4q)+\varepsilon_{\mathrm{enc}}(q),
$$

where $\varepsilon_{\mathrm{enc}}$ combines long-derivation schedule overlap with `pairCollisionUnionBound`. For short keys/customization, the bound sharpens to $\varepsilon_{\mathrm{ind}}(2q)$ plus the collision term.

The sketch:

- Uses the actual `ProtocolIndifferentiable` API and its `.constructs`/relaxed-composition route.
- Explains the missing full-`PFunPDC` RandomSystemsCC bridge explicitly.
- Uses a finite active-call domain because `PFunPDS.URF` cannot be instantiated on infinite `List Byte`.
- Reuses R1 parsing, header/F separation, existing converter realization, uniform restriction, collision bounds, and metric-to-$\Delta$ results.
- Flags only the active-domain wrapper, probabilistic-converter bridge/DPI, keyed collision generalization, and adaptive RO scheduling lemma as genuinely new.