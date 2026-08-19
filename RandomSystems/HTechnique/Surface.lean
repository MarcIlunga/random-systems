/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.HashThenPRF
import RandomSystems.HTechnique.SecurityDefs
import RandomSystems.HTechnique.SoPBoundary
import RandomSystems.HTechnique.StrongPRP

/-!
# H-technique migration surface

This module is the curated public surface for the H-technique migration.

`All.lean` is a build aggregate.  This file is narrower: it imports the modules
that should survive the eventual promotion from
`RandomSystems.HTechnique` to the main random-systems surface:

* law-level CR18 transcript objects and deterministic-environment transcript
  distributions, imported through the security/application endpoints;
* paper-facing security advantage wrappers over `ProbPDS`;
* the migrated SoP application boundary;
* the migrated fixed-query HashThenPRF application endpoint.
* concrete strong/tweakable PRP model objects and source-facing advantage names
  whose ideals are constructed internally.

Public theorem headers on this surface should speak in terms of law-level
systems/environments (`ProbPDS`, `ProbPDE`), deterministic CR18 environments,
and named transcript spaces.  Raw sample spaces, probability laws, RVs,
representative objects, or implementation-path transcript carrier instances
belong in construction adapters and legacy boundaries, not in the final
application-facing statements.

Representative-level transcript bridges, legacy bounded-system compatibility,
implementation slices, counting internals, fixed-query machinery, and proof
automation remain available through their own modules and the `All` aggregate,
but this file is the surface to benchmark before deprecating the old
H-technique path.
-/
