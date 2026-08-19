/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Systems

/-!
# Jost §2.2.6, the construction proof (Prop. 2.2.17)

The thesis proof is one sentence: *"This follows from observing
`c CPA_0 = π_E [AuthChan, Key]` and `c CPA_1 = σ_E SecChan`, where Eve's
output matches by definition and Bob's output matches by correctness of the
scheme."*  This file is that sentence, expanded to its actual content:

* **Leaf 1** (`realMachine_toDDS_eq_gameMachine`):
  `π_E [AuthChan, Key] = c CPA_0` — per seed, a bisimulation whose relation
  says the CPA transcript's plaintext/ciphertext store is the image of the
  channel buffer, with each stored ciphertext the encryption of its
  plaintext under the shared key at its lookup position's tape entry.
  Bob's clause is where `dec_enc` (perfect correctness) fires.
* **Leaf 2** (`idealMachine_toDDS_eq_gameMachine`):
  `σ_E SecChan = c CPA_1` — per seed, a bisimulation identifying the
  simulator's zero-string encryptions with `CPA_1`'s right-hand challenge
  answers.  No correctness needed, exactly as in the thesis.
* **Headline** (`construction`, Prop. 2.2.17): the two leaves are *law
  equalities* under the shared uniform seed (`Machine.lawOf_congr` — the
  identity coupling), so for EVERY functional Φ of the two laws,
  `Φ real ideal = Φ (c CPA_0) (c CPA_1)`.  Instantiating Φ with any
  distinguisher's advantage functional is the thesis's
  `ε(D) := Δ^{Dc}(CPA_0, CPA_1)` transport; no metric infrastructure is
  consumed because nothing weaker than equality was proved.

Family I throughout (exact identities); the routing rationale and the
rejected alternatives are recorded in `sketches/jost-2-2-6.md`.
-/

namespace RandomSystems.CR18.TypedResource.Jost226

open JostFigure22

variable {K R M C L : Type} [Inhabited R] [DecidableEq L]

/-! ## Leaf 1: `π_E [AuthChan, Key] = c CPA_0`, per seed -/

/-- The leaf-1 bisimulation relation at seed `(k, t)`.  Left state:
`π`'s send counter × (`AuthChan` buffer × `Key`'s unit).  Right state:
`c`'s (pairs store × delivered plaintext) × `CPA_0`'s challenge counter.
Reading order: the three counters track the store's length; the channel
buffer is the ciphertext column of the store; Bob's pending ciphertext
decrypts to `c`'s delivered plaintext; every stored ciphertext is the
encryption of its plaintext at its lookup position's tape entry. -/
def realGameRel (E : EncScheme K R M C L) {cap : ℕ} (k : K) (t : Fin cap → R) :
    (ℕ × (ChanState C × Unit)) → ((List (M × C) × Option M) × ℕ) → Prop :=
  fun left right =>
    left.1 = right.1.1.length ∧
    right.2 = right.1.1.length ∧
    left.2.1.count = right.1.1.length ∧
    (∀ i, left.2.1.sent i = (logLookup right.1.1 i).map Prod.snd) ∧
    left.2.1.delivered.bind (E.dec k) = right.1.2 ∧
    ∀ i p, logLookup right.1.1 i = some p →
      p.2 = E.enc k (tapeAt t (i - 1)) p.1

/-- **Leaf 1** (thesis p. 30, first identity): at every seed, the protocol
attached to `[AuthChan, Key]` and the reduction attached to `CPA_0` are the
same deterministic resource.  Bob's case is "by correctness of the scheme";
every other case is "by definition". -/
theorem realMachine_toDDS_eq_gameMachine (E : EncScheme K R M C L) {cap : ℕ}
    (seed : Seed K R cap) :
    (realMachine E seed).toDDS = (gameMachine E false (cap := cap) seed).toDDS := by
  refine Machine.toDDS_eq_of_bisim (realGameRel E seed.1 seed.2)
    ⟨rfl, rfl, rfl,
      fun i => by
        simp [realMachine, gameMachine, Converter.attach, Machine.par,
          piConv, cConv, authChan, keyMachine, cpaMachine, logLookup,
          Option.map],
      rfl,
      fun i p hp => by
        simp [gameMachine, Converter.attach, cConv, cpaMachine, logLookup]
          at hp⟩ ?_
  rintro ⟨n, auth, u⟩ ⟨⟨pairs, delivered⟩, cnt⟩
    ⟨hn, hcnt, hcount, hsent, hdeliver, hpair⟩ ⟨interface, input⟩
  dsimp only at hn hcnt hcount hsent hdeliver hpair
  match interface, input with
  | .A, .send m =>
      refine ⟨?_, ?_⟩
      · simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          E.len_zeroOf, Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          E.len_zeroOf, Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨by simp [hn], by simp [hcnt], by simp [hcount], ?_, hdeliver, ?_⟩
        · intro i
          dsimp only
          rw [logLookup_append, hcount]
          by_cases hit : i = pairs.length + 1
          · subst hit
            simp [hn, hcnt]
          · rw [Function.update_of_ne (by omega), if_neg hit]
            exact hsent i
        · intro i p hp
          rw [logLookup_append] at hp
          by_cases hit : i = pairs.length + 1
          · rw [if_pos hit] at hp
            injection hp with hp'
            subst hp'
            simp [hit, hcnt]
          · rw [if_neg hit] at hp
            exact hpair i p hp
  | .B, .receive =>
      refine ⟨?_, ?_⟩
      · simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind]
        exact hdeliver
      · intro next₁ next₂ move₁ move₂
        simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        exact ⟨hn, hcnt, hcount, hsent, hdeliver, hpair⟩
  | .E, .leak i =>
      refine ⟨?_, ?_⟩
      · simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind, hsent i, logLookup_map]
      · intro next₁ next₂ move₁ move₂
        simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        exact ⟨hn, hcnt, hcount, hsent, hdeliver, hpair⟩
  | .E, .deliver i =>
      refine ⟨?_, ?_⟩
      · simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨hn, hcnt, hcount, hsent, ?_, hpair⟩
        rw [hsent i, logLookup_map]
        cases hlk : logLookup pairs i with
        | none => rfl
        | some p => simp [hpair i p hlk, E.dec_enc]
  | .F, .deliver i =>
      refine ⟨?_, ?_⟩
      · simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [realMachine, gameMachine, Converter.attach_step, Machine.par,
          Machine.runProg, piConv, cConv, authChan, keyMachine, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨hn, hcnt, hcount, hsent, ?_, hpair⟩
        rw [hsent i, logLookup_map]
        cases hlk : logLookup pairs i with
        | none => rfl
        | some p => simp [hpair i p hlk, E.dec_enc]

/-! ## Leaf 2: `σ_E SecChan = c CPA_1`, per seed -/

/-- The leaf-2 bisimulation relation at seed `(k, t)` — the simulator's key
and tape ARE `CPA_1`'s key and tape (the identity coupling).  The secure
channel's plaintext log is the plaintext column of `c`'s store; delivered
messages agree; every stored ciphertext is the zero-string encryption of
its plaintext's length at its lookup position's tape entry. -/
def idealGameRel (E : EncScheme K R M C L) {cap : ℕ} (k : K) (t : Fin cap → R) :
    (Unit × ChanLog M) → ((List (M × C) × Option M) × ℕ) → Prop :=
  fun left right =>
    right.1.1.map Prod.fst = left.2.log ∧
    right.2 = right.1.1.length ∧
    left.2.delivered = right.1.2 ∧
    ∀ i p, logLookup right.1.1 i = some p →
      p.2 = E.enc k (tapeAt t (i - 1)) (E.zeroOf (E.len p.1))

/-- **Leaf 2** (thesis p. 30, second identity): at every seed, the simulator
attached to `SecChan` and the reduction attached to `CPA_1` are the same
deterministic resource.  Eve's zero-string encryptions match "by
definition"; no correctness assumption is consumed. -/
theorem idealMachine_toDDS_eq_gameMachine (E : EncScheme K R M C L) {cap : ℕ}
    (seed : Seed K R cap) :
    (idealMachine E seed).toDDS = (gameMachine E true (cap := cap) seed).toDDS := by
  refine Machine.toDDS_eq_of_bisim (idealGameRel E seed.1 seed.2)
    ⟨rfl, rfl, rfl,
      fun i p hp => by
        simp [gameMachine, Converter.attach, cConv, cpaMachine, logLookup]
          at hp⟩ ?_
  rintro ⟨u, chan⟩ ⟨⟨pairs, delivered⟩, cnt⟩
    ⟨hlog, hcnt, hdeliver, hpair⟩ ⟨interface, input⟩
  dsimp only at hlog hcnt hdeliver hpair
  match interface, input with
  | .A, .send m =>
      refine ⟨?_, ?_⟩
      · simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          E.len_zeroOf, Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          E.len_zeroOf, Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨by simp [hlog], by simp [hcnt], hdeliver, ?_⟩
        intro i p hp
        rw [logLookup_append] at hp
        by_cases hit : i = pairs.length + 1
        · rw [if_pos hit] at hp
          injection hp with hp'
          subst hp'
          simp [hit, hcnt]
        · rw [if_neg hit] at hp
          exact hpair i p hp
  | .B, .receive =>
      refine ⟨?_, ?_⟩
      · simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind, hdeliver]
      · intro next₁ next₂ move₁ move₂
        simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        exact ⟨hlog, hcnt, hdeliver, hpair⟩
  | .E, .leak i =>
      have hlook : logLookup chan.log i = (logLookup pairs i).map Prod.fst := by
        rw [← hlog, logLookup_map]
      refine ⟨?_, ?_⟩
      · cases hlk : logLookup pairs i with
        | none =>
            simp [idealMachine, gameMachine, Converter.attach_step,
              Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
              Option.map, Option.bind, hlook, hlk, logLookup_map]
        | some p =>
            simp [idealMachine, gameMachine, Converter.attach_step,
              Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
              Option.map, Option.bind, hlook, hlk, logLookup_map,
              hpair i p hlk]
      · intro next₁ next₂ move₁ move₂
        simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        exact ⟨hlog, hcnt, hdeliver, hpair⟩
  | .E, .deliver i =>
      refine ⟨?_, ?_⟩
      · simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨hlog, hcnt, ?_, hpair⟩
        rw [← hlog, logLookup_map]
  | .F, .deliver i =>
      refine ⟨?_, ?_⟩
      · simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind]
      · intro next₁ next₂ move₁ move₂
        simp [idealMachine, gameMachine, Converter.attach_step,
          Machine.runProg, sigmaConv, cConv, secChan, cpaMachine,
          Option.map, Option.bind] at move₁ move₂
        first
          | subst move₁
          | (injection move₁ with h₁; subst h₁)
        first
          | subst move₂
          | (injection move₂ with h₂; subst h₂)
        refine ⟨hlog, hcnt, ?_, hpair⟩
        rw [← hlog, logLookup_map]

/-! ## The headline: Prop. 2.2.17 -/

variable [Fintype K] [Nonempty K] [Fintype R]

open RandomSystems (Dist)

/-- The real-world law IS the reduction against `CPA_0`: leaf 1 lifted
through the identity coupling of the uniform seed. -/
theorem real_eq_game (E : EncScheme K R M C L) (cap : ℕ) :
    real (M := M) (C := C) E cap = game E false cap :=
  Machine.lawOf_congr Dist.uniform_isProbDist fun seed _ =>
    realMachine_toDDS_eq_gameMachine E seed

/-- The ideal-world law IS the reduction against `CPA_1`: leaf 2 lifted
through the identity coupling of the uniform seed (the simulator's key is
`CPA_1`'s key). -/
theorem ideal_eq_game (E : EncScheme K R M C L) (cap : ℕ) :
    ideal (M := M) (C := C) E cap = game E true cap :=
  Machine.lawOf_congr Dist.uniform_isProbDist fun seed _ =>
    idealMachine_toDDS_eq_gameMachine E seed

/-- **Prop. 2.2.17, the transport form.**  Because both leaves are law
*equalities*, EVERY functional of the (real, ideal) pair — in particular
any distinguisher's advantage `D ↦ Δ^D(·,·)`, on the native laws or on
their `DependentPDS.Prob.flatten` images — takes the same value on
`(c CPA_0, c CPA_1)`.  Instantiating Φ with the advantage of a distinguisher
`D` is exactly the thesis's `ε(D) := Δ^{Dc}(CPA_0, CPA_1)`: the reduction
`c` is already inside the game laws, so the distinguisher absorption is
definitional and the simulation-based construction
`[AuthChan, Key] ⊢—(π_E, σ_E, ε)→ SecChan` holds with NO metric slack. -/
theorem construction {α : Sort*} (E : EncScheme K R M C L) (cap : ℕ)
    (Φ : DependentPDS.Prob (conSig M C) (conBnd M C) →
      DependentPDS.Prob (conSig M C) (conBnd M C) → α) :
    Φ (real E cap) (ideal E cap) = Φ (game E false cap) (game E true cap) := by
  rw [real_eq_game, ideal_eq_game]

end RandomSystems.CR18.TypedResource.Jost226
