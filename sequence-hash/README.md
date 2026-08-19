# SequenceHash formalization

This directory contains the existing Lean formalization of the C2SP
SequenceHash v0.1.0 draft. C2SP published the materially revised, stable
v1.0.0 specification on 2026-08-03. Both texts, their commits, checksums, and a
semantic change table are preserved in the
[versioned specification archive](specs/README.md).
The proof records are indexed separately in the
[versioned research archive](research/README.md).

The compatibility file [`sequencehash.md`](sequencehash.md) remains v0.1.0 so
that the current Lean source links retain their meaning. The v1.0.0 model and
proofs are a separate migration target. The PDF papers were supplied locally
and are not downloaded by the build.

Build the development with:

```text
lake build SequenceHash
```

## Milestones

- [x] Exact 128-bit byte encoding and unique sequence parsing, including
  empty items and item-boundary ambiguity.
- [x] Pure C2SP construction and collision accounting: equal outputs on
  distinct accepted inputs reflect an actual collision of the underlying
  hash. No unconditional collision-freedom claim is made for a finite-output
  hash.
- [x] End-to-end RandomSystems converter with literal byte-string calls,
  sharp two/three-call bounds, and deterministic plus law-level realization.
- [ ] SequenceHash indifferentiability from a random oracle. The
  short-customization case exposes a domain-separated hash-then-random-function
  core; the full theorem must also simulate the public primitive interface and
  account for long-customization overlap with the raw `Derive` query.
- [ ] SequenceMAC PRF security, proved directly in both the standard model and
  the ideal-compression model. Keep the modular indifferentiability corollary as
  a third, logically separate route.
- [ ] Prove the adapted Dodis--Ristenpart--Steinberger--Tessaro simulator bound
  that discharges `sequenceMAC_md_h_indiff`'s explicit `h_drst` premise on the
  direct PDS/`Δ` surface for canonical `sequenceFunction` over `MD[f]`. Audit optional
  selected-AC packaging only after a faithful live carrier/action seam exists.
- [ ] Tight generic security in the random-compression model, following the
  supplied 2025 paper and the promoted H-technique tooling.
- [ ] Run the repository-wide RandomSystems, curated H-technique surface, and
  legacy anti-drift gates.

The pure modules are Mathlib-only. RandomSystems and constructive-cryptography
instantiations are kept in later modules so foundational dependencies remain
one-way.

## Security targets

SequenceHash and SequenceMAC share the `SequenceFunction` syntax, but their
security statements and principal proof techniques are different.

| Construction | Instantiation | Primary security statement | Principal proof route |
| --- | --- | --- | --- |
| SequenceHash | `K = ''`, `F = F_SEQHSH` | Indifferentiability from a random oracle, including the public primitive interface and its simulator | Conditional equivalence |
| SequenceMAC | Secret `K`, `F = F_SEQMAC` | PRF security in the standard model | Direct reduction to the compression-family assumptions |
| SequenceMAC | Secret `K`, `F = F_SEQMAC` | PRF security in the ideal-compression model | Direct H-technique analysis |
| SequenceMAC | Secret `K`, `F = F_SEQMAC` | PRF security as a modular corollary | A sufficiently general allowed-key `SequenceFunction` indifferentiability theorem, followed by restriction to a secret key |

The last row is a separate, indirect route. Indifferentiability of the literal
unkeyed SequenceHash instance alone does not imply PRF security of
SequenceMAC. Coupling, signed representatives, and other alternative analyses
belong only in end appendices of the corresponding pen-and-paper study; the
main SequenceHash proof is by conditional equivalence.

The stable-version pen-and-paper chapters are
[Conditional Equivalence for SequenceHash](../papers/notes/SEQUENCEHASH_CE_INDIFFERENTIABILITY.md)
and [PRF Security of SequenceMAC](../papers/notes/SEQUENCEMAC_PRF_SECURITY.md).
