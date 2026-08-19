# Random Systems in Lean 4

A formalization of Maurer's random systems framework for cryptographic
indistinguishability proofs — DDS/PDS, behaviors, transcript laws, games with
monotone binary outputs, the H-coefficient technique, and applications
(Sum-of-Permutations, XoP, Hash-then-PRF, strong/tweakable PRPs, URF/URP
switching).

## What are random systems?

A **random system** answers queries probabilistically: in round `i` it
receives `Xᵢ` and produces `Yᵢ`, which may depend on the whole history.
Concretely (following Maurer EUROCRYPT'02, the CR18 lecture notes, and
Lanzenberger–Maurer TCC'20):

- a **DDS** is a deterministic lookup table `s : X⁺ ⇀ Y`;
- a **PDS law** (`ProbPDS`) is a probability distribution over DDSs —
  the repository's public statement language;
- a **random system** proper is the behavioral/transcript-law equivalence
  class of a PDS; the **advantage** `Adv(S,T)` is the supremum of transcript
  distances over adaptive environments.

See `DESIGN.md` §3 for the four equivalent views of a PDS and the planned
unification.

## Documentation

Four root documents:

- **`DESIGN.md`** — architecture, modeling discipline, statement/proof
  policies, automation stack, CR18 deviations register, the system-views
  unification design.
- **`STATUS.md`** — current state, build gates, public-surface inventory,
  quarantine/retirement map, known gaps, downstream notes, open work.
- **[FOUNDATIONS.md](FOUNDATIONS.md)** — mandatory notation, source-faithful
  Maurer--Lanzenberger definitions and coupling theorems, the signed
  representative extension, and the required structure of pen-and-paper
  research notes.
- **[AGENTS.md](AGENTS.md)** — repository workflow and reading order for
  agents.
- `papers/` — source PDFs/extractions and reading notes (including the
  LM20 orbit-proof and CBC-MAC expositions under `papers/notes/`).

## Layout

```
RandomSystems/            -- the library (single lake lib, glob-built)
  …                       -- probability core + PFun/CR18 surface
  HTechnique/             -- H-coefficient application layer (public API: Surface)
  Legacy/                 -- pre-migration bounded API + applications
attic/                    -- parked never-buildable files (see STATUS.md §5)
papers/                   -- sources and notes
```

## Building

```bash
lake build RandomSystems                        # everything (~8.4k jobs)
lake build RandomSystems.HTechnique.All         # curated surface (legacy-free)
lake run htechniqueCheck                        # surface audit + surface build
```

Requires the pinned Lean 4 toolchain (`lean-toolchain`) and Mathlib.

## References

- Lanzenberger & Maurer, *Coupling of Random Systems* (TCC 2020)
- Maurer, *Indistinguishability of Random Systems* (EUROCRYPT 2002)
- Maurer, *Cryptography Foundations* lecture notes (2018), `papers/CR18_LN.txt`
- Maurer, Pietrzak & Renner, *Indistinguishability Amplification* (CRYPTO 2007)

## License

Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license.
