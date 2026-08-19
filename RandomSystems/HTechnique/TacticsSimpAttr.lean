/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Attr.Register

/-!
# H-technique simp attributes

This module declares migration-local simp sets used by the H-technique proof
automation.  The declarations live in their own file because Mathlib simp
attributes cannot be registered and used in the same module.
-/

/-- `htechnique_dist_simp` is the migration-local distribution bookkeeping simp
set.  It contains only shrinking rewrites for finite transcript-law adapters,
fixed-input deterministic lifts, and total weights. -/
register_simp_attr htechnique_dist_simp
