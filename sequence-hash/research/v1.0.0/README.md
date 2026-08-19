# SequenceHash v1.0.0 research program

This directory indexes the pen-and-paper security analysis of the stable
construction merged on 2026-08-03.

- Specification: [`../../specs/v1.0.0/sequencehash.md`](../../specs/v1.0.0/sequencehash.md)
- SequenceHash target: indifferentiability from a random oracle, with the main
  proof by conditional equivalence.
- SequenceMAC targets: direct PRF security in the standard model; direct PRF
  security in the ideal-compression model by the H-technique; and a separate
  modular PRF corollary through allowed-key `SequenceFunction`
  indifferentiability.

Paper-facing chapters:

- [Conditional Equivalence for SequenceHash](../../../papers/notes/SEQUENCEHASH_CE_INDIFFERENTIABILITY.md)
- [A Framing-Aware Simulator for SequenceHash over Merkle--Damgård](../../../papers/notes/SEQUENCEHASH_MD_SMART_SIMULATOR.md)
- [PRF Security of SequenceMAC](../../../papers/notes/SEQUENCEMAC_PRF_SECURITY.md)

Alternative coupling and signed-representative analyses are kept only in the
final appendices of those chapters.

Current evidence boundary: the fixed-tag, short-customization SequenceHash
bound is derived both over a public random oracle and directly over an ideal
Merkle--Damgård compression function.  The direct proof uses a framing-aware
one-graph simulator and gives the finite bound (7.4), with the simple envelope
$2\sigma^2/N$ in place of DRST's HMAC envelope $13\sigma^2/N$. The stable-v1
byte/block parser, long-customization link, and simultaneous-tag refinements
remain outside the Lean development. The published NMAC/HMAC endpoints used
for SequenceMAC are source-checked, while their literal v1.0.0 schedule and
key-entropy bridges remain open. No stable v1.0.0 Lean theorem is claimed yet.
