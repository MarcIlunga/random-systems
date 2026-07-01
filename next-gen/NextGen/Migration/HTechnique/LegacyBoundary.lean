/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.PDS
import NextGen.GameOf
import NextGen.Theorem417
import NextGen.SwitchingLemma
import NextGen.CR18Tactics
import NextGen.Migration.HTechnique.Counting
import NextGen.Migration.HTechnique.Density
import NextGen.Migration.HTechnique.TranscriptLaw
import NextGen.Migration.HTechnique.LegacyBoundedTranscript

/-!
# H-technique target boundary

This module is deliberately a support boundary, not the new API.  It is
imported by the aggregate build target `All`, not by the curated
future-promotion `Surface`.

The target surface is the PFun/`NextGen` CR18 stack.  The external source
project is `/Users/marcilunga/Documents/ToB/research/fv/h-technique`, but it
already depends on this `random-systems` repository.  Therefore this repository
must not add a Lake dependency on `HTechnique`: that would create a package
cycle.  We port source declarations into sibling `NextGen.Migration.HTechnique`
modules instead.

The boundary compiles only if the current `NextGen` transcript/game/switching
surface and the first migrated H-technique counting/density slices are
available, including the generic transcript-law bridge.  New migrated lemmas
should live in sibling modules and should not import `RandomSystems.*`
directly.
-/
