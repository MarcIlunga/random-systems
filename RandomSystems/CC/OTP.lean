/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CC.Composition
import RandomSystems.Instances.URF
import Mathlib.Data.ZMod.Basic

/-!
# Constructive Cryptography: One-Time Pad

The first concrete CC construction: the one-time pad achieves
perfect security (ε = 0).

## Overview

In Maurer's framework (2011, Section 3.3), the OTP is the canonical
example of a CC construction:

  (AUT ‖ KEY) →^{(otp-enc, otp-dec), 0} SEC

## Model

We formalize a single-query, fixed-length version over `Fin N`:

- **Message/Key/Ciphertext space** = `Fin N`
- **Security bound** ε = 0 (perfect security)

### Mathematical Content

The real adversary view samples a key `k` uniformly from `Fin N` and
computes ciphertext `c = m + k`. This is a PDS supported on `N`
translation functions (mass `1/N` each), *not* the full URF which
assigns mass `1/N^N` to all `N^N` functions.

The proof shows these two PDS are *PDS-equivalent*: they produce
identical transcript distributions for every input sequence. The
argument proceeds in two steps:

1. **Bijection preserves uniformity** (`fTransform_bijection_uniform`):
   since `(m + ·)` is a bijection on `Fin N`, the output distribution
   `m + k` for uniform `k` is itself uniform.

2. **URF evaluation is uniform** (`URF_eval_eq_uniform`): evaluating the
   URF at any fixed input also produces the uniform distribution on
   outputs, via fiber counting on the DDS function space.

Both sides factor as `fTransform embed (uniform (Fin N))`, giving
equality of transcript distributions and hence zero advantage.

## References

- Maurer, "Constructive Cryptography" (2011), Section 3.3
- Coretti-Maurer-Tackmann, "Constructing Confidential Channels" (2013)
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

namespace CC

namespace OTP

/-! ### Single-Interface OTP Theorem -/

section SingleInterface

variable (N : ℕ) [NeZero N]

private instance instNE : Nonempty (DDS (Fin N) (Fin N) 1) := ⟨DDS.ofFun id⟩

/-- The real adversary-view PDS: sample key `k` uniformly, encrypt as `m + k`.

This distribution is supported on `N` translation functions (each with
mass `1/N`), NOT the full URF which has mass `1/N^N` on all `N^N`
functions. The two are PDS-equivalent but definitionally distinct. -/
def otpRealView : PDS (Fin N) (Fin N) 1 where
  dist := Dist.fTransform
    (fun k => DDS.ofFun (· + k))
    (Dist.uniform (Fin N))

/-- The ideal adversary-view PDS: URF (uniform random function).

The ideal secure channel reveals nothing about `m` beyond the fixed
length, so the adversary sees uniform randomness. -/
def idealView : PDS (Fin N) (Fin N) 1 := Instances.URF

/-- Core bridge lemma: the transcript distributions of the real and ideal
views agree for all input sequences.

Both sides factor as `fTransform embed (uniform (Fin N))` where
`embed y = fun _ => (inputs 0, y)`:
- LHS: composition of fTransforms + `fTransform_bijection_uniform`
  (translation `(m + ·)` is a bijection on `Fin N`)
- RHS: composition of fTransforms + `URF_eval_eq_uniform`
  (fiber counting: evaluating URF at a point gives uniform output) -/
theorem otpRealView_transcriptDist_eq (inputs : Fin 1 → Fin N) :
    (otpRealView N).transcriptDist inputs = (idealView N).transcriptDist inputs := by
  set m := inputs 0
  set embed : Fin N → Transcript (Fin N) (Fin N) 1 := fun y _ => (m, y)
  -- LHS = fTransform embed (uniform (Fin N))
  have h_lhs : (otpRealView N).transcriptDist inputs =
      Dist.fTransform embed (Dist.uniform (Fin N)) := by
    simp only [PDS.transcriptDist, otpRealView]
    rw [Dist.fTransform_comp]
    have h_comp : (fun s => DDS.transcript s inputs) ∘
        (fun k : Fin N => DDS.ofFun (· + k)) = embed ∘ (m + ·) := by
      funext k; simp only [Function.comp_apply]
      rw [DDS.transcript_q1]; simp only [DDS.firstQuery, DDS.ofFun]; rfl
    rw [h_comp, ← Dist.fTransform_comp, Dist.fTransform_bijection_uniform _
      ⟨fun _ _ h => add_left_cancel h, fun b => ⟨-m + b, by simp⟩⟩]
  -- RHS = fTransform embed (uniform (Fin N))
  have h_rhs : (idealView N).transcriptDist inputs =
      Dist.fTransform embed (Dist.uniform (Fin N)) := by
    simp only [PDS.transcriptDist, idealView, Instances.URF]
    have h_eq : (fun s : DDS (Fin N) (Fin N) 1 => DDS.transcript s inputs) =
        embed ∘ (fun s => s.firstQuery Nat.zero_lt_one m) := by
      funext s; simp only [Function.comp_apply]; rw [DDS.transcript_q1]
    rw [h_eq, ← Dist.fTransform_comp]
    congr 1
    exact Instances.URF_eval_eq_uniform m
  rw [h_lhs, h_rhs]

/-- **OTP PDS Equivalence**: the real and ideal adversary views are
PDS-equivalent (produce identical transcript distributions).

This is the core mathematical content of OTP security. The two PDS
have different underlying distributions over DDS (N translation
functions vs all N^N functions), but produce the same observable
behavior at every input. -/
theorem otp_real_equiv_ideal :
    otpRealView N ≡ₚ idealView N :=
  otpRealView_transcriptDist_eq N

/-- **OTP Perfect Secrecy**: the distinguishing advantage between the
real and ideal adversary views is zero. -/
theorem otp_advantage_zero :
    advantage (otpRealView N) (idealView N) = (0 : NNReal) := by
  rw [advantage_respects_equiv (otp_real_equiv_ideal N) (PDS.equiv_refl _)]
  exact advantage_self (idealView N)

end SingleInterface

/-! ### Full Multi-Interface CC Construction

2-interface resource:
- Interface 0: honest parties (modeled as URF)
- Interface 1: adversary (real: OTP encryption, ideal: URF) -/

section MultiInterface

variable (N : ℕ) [NeZero N]

private instance instNE₂ : Nonempty (DDS (Fin N) (Fin N) 1) := ⟨DDS.ofFun id⟩

/-- The real CC resource: URF at the honest interface, OTP encryption
at the adversary interface. -/
def realResource :
    CCResource (fun (_ : Fin 2) => Fin N) (fun _ => Fin N) (fun _ => 1) :=
  Function.update (fun _ => Instances.URF) 1 (otpRealView N)

/-- The ideal CC resource: URF at every interface. -/
def idealResource :
    CCResource (fun (_ : Fin 2) => Fin N) (fun _ => Fin N) (fun _ => 1) :=
  fun _ => Instances.URF

/-- The simulator: identity converter at the adversary interface. -/
def simulator : Converter (Fin N) (Fin N) 1 :=
  Converter.id (Fin N) (Fin N) 1

/-- The real and ideal resources are PDS-equivalent at every interface.

- Interface 0: both are URF (trivially equivalent)
- Interface 1: `otpRealView ≡ₚ URF` (by `otp_real_equiv_ideal`) -/
theorem realResource_equiv_idealResource :
    realResource N ≡ᵣ idealResource N := by
  intro i
  simp only [realResource, idealResource]
  by_cases hi : i = 1
  · subst hi
    rw [Function.update_self]
    exact otp_real_equiv_ideal N
  · rw [Function.update_of_ne hi]
    exact PDS.equiv_refl _

/-- **OTP CC Construction**: perfect security (ε = 0).

Maurer 2011, Section 3.3:
  (AUT ‖ KEY) →^{(otp-enc, otp-dec), 0} SEC -/
def otpConstruction :
    CCConstruction (realResource N) (idealResource N) (1 : Fin 2) where
  conv := simulator N
  ε := 0
  secure := by
    rw [show applyConverter (1 : Fin 2) (simulator N) (realResource N) =
        realResource N from applyConverter_id 1 (realResource N)]
    have h := resourceAdvantage_respects_equiv
      (realResource_equiv_idealResource N) (CCResource.equiv_refl (idealResource N))
    rw [h]
    exact le_of_eq (resourceAdvantage_self (idealResource N))

/-- The OTP achieves zero resource-level advantage. -/
theorem otp_resource_advantage_zero :
    resourceAdvantage
      (applyConverter (1 : Fin 2) (simulator N) (realResource N))
      (idealResource N) = 0 := by
  apply le_antisymm
  · exact (otpConstruction N).secure
  · exact zero_le _

end MultiInterface

end OTP

end CC

end RandomSystems
