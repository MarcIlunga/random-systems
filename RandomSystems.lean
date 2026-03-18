/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import RandomSystems.StatDist
import RandomSystems.DDS
import RandomSystems.DDE
import RandomSystems.Transcript
import RandomSystems.PDS
import RandomSystems.Equiv
import RandomSystems.Successor
import RandomSystems.Coupling
import RandomSystems.Advantage
import RandomSystems.FundamentalTheorem
import RandomSystems.SystemCoupling
import RandomSystems.Construction
import RandomSystems.HConstruction
import RandomSystems.Combiner
import RandomSystems.Amplification
import RandomSystems.ConditionBased
import RandomSystems.Instances.BoolDDS
import RandomSystems.Instances.URF
import RandomSystems.Instances.URP
import RandomSystems.Applications.PRPPRFSwitching
import RandomSystems.Applications.PRPPRFSwitchingGeneral
import RandomSystems.Applications.CBCMAC
import RandomSystems.Applications.CascadePRF
import RandomSystems.Applications.CascadeCircle
import RandomSystems.Applications.BonehShoupCascade
import RandomSystems.Applications.CTRMode
import RandomSystems.CC.Resource
import RandomSystems.CC.Advantage
import RandomSystems.CC.Composition
import RandomSystems.CC.OTP

/-!
# Maurer's Random Systems Framework

Lean 4 formalization of Lanzenberger-Maurer (TCC 2020):
"Coupling of Random Systems."

A random system is an equivalence class of distributions over
deterministic systems. The distinguishing advantage equals the
infimum statistical distance over representatives (Theorem 1).
-/
