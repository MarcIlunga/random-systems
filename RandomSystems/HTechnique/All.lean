/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Derivation
import RandomSystems.HTechnique.HCTR2Paper
import RandomSystems.HTechnique.Surface
import RandomSystems.HTechnique.Tactics
import RandomSystems.HTechnique.IdealCompression

/-!
# H-technique aggregate

The curated surface plus its proof automation.  This target is legacy-free:
it imports no `RandomSystems.Legacy.*` module.  The legacy gates,
representative compatibility layer, and anti-drift pins are build-checked by
the separate `RandomSystems.HTechnique.LegacyChecks` target.

```bash
lake build RandomSystems.HTechnique.All
lake build RandomSystems.HTechnique.LegacyChecks
```
-/
