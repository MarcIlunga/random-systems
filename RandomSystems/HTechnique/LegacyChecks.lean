/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.FixedQueryCompatibility
import RandomSystems.HTechnique.LegacyBoundary
import RandomSystems.HTechnique.LegacyStatelessBridge
import RandomSystems.HTechnique.SoP.LegacyVisibleEquiv
import RandomSystems.HTechnique.SoP.XoPLegacyBridge
import RandomSystems.HTechnique.SoPLegacyBoundary

/-!
# H-technique legacy checks (compatibility-only build gate)

This aggregate keeps the legacy gates, the representative compatibility
layer they import, and the anti-drift pin modules build-checked without
putting them on the main surface: `RandomSystems.HTechnique.All` is
legacy-free, and this target is the only H-technique module tree that
imports `RandomSystems.Legacy.*`.

```bash
lake build RandomSystems.HTechnique.LegacyChecks
```

These modules die with the `RandomSystems.Legacy` tree; the pins
(`SoP.LegacyVisibleEquiv`, `SoP.XoPLegacyBridge`) must stay green until
then — a pin failure means a refactor changed the mathematics.
-/
