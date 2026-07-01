/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.Surface
import NextGen.Migration.HTechnique.FixedQueryCompatibility
import NextGen.Migration.HTechnique.LegacyBoundary
import NextGen.Migration.HTechnique.LegacyStatelessBridge
import NextGen.Migration.HTechnique.SoPLegacyBoundary
import NextGen.Migration.HTechnique.Tactics

/-!
# H-technique migration aggregate

Build this target while migrating H-technique and the SoP application.  It
imports the curated migration surface, the compatibility/build boundary, and
migration-local proof automation:

```bash
lake build NextGen.Migration.HTechnique.All
```
-/
