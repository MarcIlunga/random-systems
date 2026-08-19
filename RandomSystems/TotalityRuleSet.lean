/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aesop

/-!
# `Cr18Total` aesop rule set

Extensible rule set for CR18 totality side conditions.  Application layers
tag their constructor-totality lemmas
`@[aesop safe apply (rule_sets := [Cr18Total])]` at birth; the `cr18_total`
tactic (in `RandomSystems.TotalityTactics`) consults the rule set after its
fast built-in chain.  The declaration lives in its own module because aesop
rule sets only become usable in modules that import the declaring one.
-/

declare_aesop_rule_sets [Cr18Total] (default := false)
