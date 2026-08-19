# SequenceHash specification archive

This directory preserves the specification versions used by the research and
formalization. Each snapshot is pinned to an immutable upstream commit and is
kept byte-for-byte identical to that source.

| Version | Status | Upstream commit | Date | SHA-256 |
| --- | --- | --- | --- | --- |
| [`v0.1.0`](v0.1.0/sequencehash.md) | Public draft; model used by the existing Lean development | [`d5f4751a8ccc44c20dfdf8f3eed0dec095a41654`](https://github.com/C2SP/C2SP/commit/d5f4751a8ccc44c20dfdf8f3eed0dec095a41654) | 2026-05-04 | `8ab85affcae19f2c7c532ec7442edc499b9acd4f2dd921e5fc59e57c77c897b5` |
| [`v1.0.0`](v1.0.0/sequencehash.md) | Current stable specification | [`3bc97b2329fee167f7ff39efbbbc316c84876105`](https://github.com/C2SP/C2SP/commit/3bc97b2329fee167f7ff39efbbbc316c84876105) | 2026-08-03 | `63a3db48455cf3643203ac8665720042ae1f62498e374351b0d228ec4157f101` |

The stable rendered specification is
[c2sp.org/sequencehash](https://c2sp.org/sequencehash). The repository's
top-level [`sequencehash.md`](../sequencehash.md) remains an identical copy of
the v0.1.0 snapshot so that the existing v0.1.0 Lean files and their source
links do not silently change meaning.

## Semantic changes in v1.0.0

The transition to v1.0.0 changes the construction, not merely its editorial
status.

| Component | v0.1.0 | v1.0.0 |
| --- | --- | --- |
| Item encoding | `EncodeLSBF(len(x)) || x` | `x || EncodeLSBF(len(x))` |
| Key derivation | One untweaked block `K' = Derive(K,H,b)` | `K_I = Derive(K,H,0x55)` and `K_O = Derive(K,H,0xaa)` |
| Customization derivation | `S' = Derive(S,H,b)` | `S' = Derive(S,H,0x00)` |
| Key-block position | The shared `K'` follows each header | `K_I` and `K_O` precede the inner and outer headers |
| Publication status | Draft | Stable |

Consequently, proofs about the v0.1.0 shared-key run-up do not transfer to
v1.0.0 by renaming. In particular, v1.0.0 SequenceMAC has an HMAC-style pair
of related key blocks and requires an explicit key-schedule argument before an
NMAC theorem can be applied.

## Upstream history

- 2026-03-31: the initial proposal entered the C2SP repository.
- 2026-05-04: v0.1.0 was merged as the public draft.
- 2026-07-28: rendering metadata was added without changing the version.
- 2026-08-03: v1.0.0 was merged and declared stable in
  [C2SP pull request 311](https://github.com/C2SP/C2SP/pull/311).

The snapshots were last checked against the official C2SP repository on
2026-08-04.
