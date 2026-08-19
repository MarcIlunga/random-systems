Wrote the full sketch to [A3-sequencehash-realization.md](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/sketches/A3-sequencehash-realization.md).

Key conclusions:

- The keyed $F=1$ theorem is concretely SequenceMAC, not literal SequenceHash, which fixes $K=""$ and $F=2$. The faithful guardrail is therefore `sequenceMAC_prf_bound_concrete`.
- Its bound is
  $$
  \Delta(\lceil q\rceil\mathsf{ConcreteReal},
         \lceil q\rceil\mathsf{URF}_{\rm InputSequence})
  \le \varepsilon_{\rm C2SP}
  +\Delta(\lceil q\rceil f_K,\lceil q\rceil r)
  +(\ell+1)q\,\varepsilon_{\rm na}
  +q^2/|C|.
  $$
- `encodeItems_injective` does not imply prefix-freeness: one encoded empty item prefixes two encoded empty items. The actual prefix-free obligation is already discharged inside the frozen theorem by `exists_prefixFree_appendDelimiter`.
- Reused: `sequenceMAC_prf_bound`, `nmac_prf_bound`, `encodeItems_injective`, `encodeMSBF_injective`, `sequenceHashSystem_realization`, `mdIterate_append`, and uniform restriction.
- New: keyed $F=1$ realization, codec boundary/injectivity laws, the bounded injective `InputSequence → BlockString` map, and the concrete run-up plus multi-block outer-envelope bridge.
- The sketch explicitly records that C2SP’s outer hash is not definitionally NMAC’s single outer compression call; that normalization must remain inside the concrete bridge term or require a new framed-NMAC theorem.

No Lean build was run, as requested.