/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Instances.URF

/-!
# Legacy bounded stateless transcript bridge

Compatibility re-export for application-independent stateless transcript facts
that used to live in this migration folder.

The declarations now live in their natural owners:

* `RandomSystems.Transcript`: `Transcript.compatibleWithEnv` and the generic
  `DDS.ofFunq` adaptive/fixed-query replay lemmas.
* `RandomSystems.Instances.URF`: the `URFfunOf` adaptive transcript mass lemmas.

Migration note: this module is compatibility-only.  Downstream applications
should import the owning `RandomSystems` modules directly. This file remains
only to avoid breaking older migration imports while the H-technique port is
being reconciled.
-/
