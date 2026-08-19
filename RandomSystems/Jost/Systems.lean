/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Combinators
import RandomSystems.Jost.LawCoupling

/-!
# Jost §2.2.6, the systems: scheme, resources, protocol, simulator, reduction

Every box of the thesis's worked example (pp. 26–30), authored as a package.
`AuthChan` and `Key` are reused verbatim from `JostFigure22`
(`ResourceMachine.lean`); this module adds the missing boxes — `SecChan`,
`CPA_b`, the protocol converters `π_E = (π_A, π_B)` (Fig. 2.3), the simulator
`σ_E` (Fig. 2.4a), and the reduction `c` (Prop. 2.2.17) — and assembles the
three composite laws `real`, `ideal`, `game b`.

## Randomness discipline (eager seed, DESIGN of `sketches/jost-2-2-6.md`)

The carrier is a law over *deterministic* systems, so every sampling step of
the thesis's pseudocode is a seed coordinate:

* `E.Enc(k, m)` — probabilistic encryption becomes `enc : K → R → M → C`
  with an explicit randomness argument, drawn from a pre-sampled tape.
* The tape is finite (`Fin cap → R`, a `Fintype`) and extended totally by
  `default` past `cap` (`tapeAt`).  No machine carries a query cap and no
  guard branches exist: past `cap` the tape repeats `default`, which
  degrades the *meaning* of the CPA games (they are the `cap`-query-bounded
  games) but not a single identity proved here — both sides of each leaf
  read the same extended tape.
* The simulator's own key (Fig. 2.4a `k ← E.K`) is the ideal family's seed
  coordinate; on the game side the same coordinate is `CPA_1`'s key.

Correctness of the scheme is *perfect* (`dec_enc`), exactly as Prop. 2.2.17
assumes; §2.2.6's message-length leak is kept abstract as `len : M → L` with
the all-zero representative `zeroOf : L → M`.
-/

namespace RandomSystems.CR18.TypedResource.Jost226

open JostFigure22

/-! ## The symmetric encryption scheme -/

/-- A symmetric encryption scheme with explicit encryption randomness and an
abstract message-length functional.  `dec_enc` is Prop. 2.2.17's "perfectly
correct"; `len_zeroOf` says `0^{|m|}` has the length it advertises. -/
structure EncScheme (K R M C L : Type) where
  enc : K → R → M → C
  dec : K → C → Option M
  len : M → L
  zeroOf : L → M
  dec_enc : ∀ k r m, dec k (enc k r m) = some m
  len_zeroOf : ∀ l, len (zeroOf l) = l

/-- Total read of a finite randomness tape: `default` past the end.  Both
sides of every leaf identity read the same extended tape, so the junk value
cancels; its only role is keeping the seed space finite. -/
def tapeAt {R : Type} [Inhabited R] {cap : ℕ} (tape : Fin cap → R) (n : ℕ) : R :=
  if h : n < cap then tape ⟨n, h⟩ else default

/-- The seed of one protocol run: the shared key and the encryption tape.
Real, ideal, and game families are all indexed by this one space — the
identity coupling of Prop. 2.2.17's proof is literally `rfl` on it. -/
abbrev Seed (K R : Type) (cap : ℕ) := K × (Fin cap → R)

variable {K R M C L : Type}

/-! ## Signatures

The **constructed boundary** is shared by all three composites: Alice sends
plaintexts, Bob receives `Option M`, Eve sees ciphertext leaks and delivers,
F delivers.  `chanIn M` is Fig. 2.2's input alphabet, reused. -/

/-- Outer output alphabets of the constructed system: Eve's leak fibre
carries ciphertexts. -/
def conOut (M C : Type) : Iface → Type
  | .A => Ok
  | .B => Option M
  | .E => EveOut C
  | .F => Ok

/-- The constructed (outer) signature. -/
abbrev conSig (M C : Type) : SignatureUniverse :=
  SignatureUniverse.ofInterfaces (chanIn M) (conOut M C)

/-- The constructed boundary. -/
abbrev conBnd (M C : Type) : Boundary (conSig M C) Iface :=
  Boundary.ofInterfaces (chanIn M) (conOut M C)

/-- `SecChan`'s output alphabets: Eve's leak fibre carries only lengths. -/
def secOut (M L : Type) : Iface → Type
  | .A => Ok
  | .B => Option M
  | .E => EveOut L
  | .F => Ok

/-- The one-interface IND-CPA boundary: a single challenge query. -/
inductive CPAIn (M : Type) | challenge (left right : M)

/-! ## The two new resources -/

/-- Fig. 2.2's secure channel (p. 23 description): identical to `AuthChan`
except that Eve's `leak` reveals only the message length.  Log-state
presentation (`ChanLog`), which `ResourceMachine.lean` proved
interchangeable with the pointwise one. -/
def secChan (len : M → L) :
    InterfaceMachine (chanIn M) (secOut M L) where
  State := ChanLog M
  init := ⟨[], none⟩
  step state query :=
    match query with
    | ⟨.A, .send m⟩ => some ({ state with log := state.log ++ [m] }, .ok)
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ =>
        some (state, .leaked ((logLookup state.log i).map len))
    | ⟨.E, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)
    | ⟨.F, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)

/-- Fig. 2.4b's left-or-right IND-CPA resource at a fixed seed: the
`require |m₀| = |m₁|` guard answers `⊥` as a value, and the challenge
counter advances only on a successful encryption (randomness is consumed
by encryptions, not by rejected queries). -/
def cpaMachine [Inhabited R] [DecidableEq L] (E : EncScheme K R M C L)
    (b : Bool) {cap : ℕ} (seed : Seed K R cap) :
    InterfaceMachine (fun _ : Unit => CPAIn M) (fun _ : Unit => Option C) where
  State := ℕ
  init := 0
  step count query :=
    match query with
    | ⟨(), .challenge left right⟩ =>
        if E.len left = E.len right then
          some (count + 1,
            some (E.enc seed.1 (tapeAt seed.2 count) (if b then right else left)))
        else
          some (count, none)

/-! ## The protocol converters (Fig. 2.3)

`π_A` encrypts and forwards; `π_B` receives and decrypts.  Both fetch the
key per use — Fig. 2.3 fetches once at Initialization, and `Key` answers
constantly, so the two are the same resource; the per-use form needs no
converter initialization block.  At `E` and `F` the protocol is the
identity, which is what "the simulator/adversary interface is not
converted" means at the package level. -/

/-- The real system's inner signature: `[AuthChan, Key]`. -/
abbrev realInnerSig (C K : Type) : SignatureUniverse :=
  (SignatureUniverse.ofInterfaces (chanIn C) (chanOut C)).par (keySig K)

/-- The real system's inner boundary. -/
abbrev realInnerBnd (C K : Type) :
    Boundary (realInnerSig C K) (Iface ⊕ KeyIface) :=
  Boundary.par (Boundary.ofInterfaces (chanIn C) (chanOut C)) (keyBoundary K)

/-- Fig. 2.3, both converters as one package over the constructed boundary
(identity clauses at `E` and `F`).  The converter's own state is `π_A`'s
send counter — the tape index. -/
def piConv [Inhabited R] (E : EncScheme K R M C L) {cap : ℕ}
    (tape : Fin cap → R) :
    Converter (conSig M C) (conBnd M C) (realInnerSig C K) (realInnerBnd C K) where
  State := ℕ
  init := 0
  step count query :=
    match query with
    | ⟨.A, .send m⟩ =>
        .call ⟨.inr .a, .fetch⟩ fun k =>
        .call ⟨.inl .A, .send (E.enc k (tapeAt tape count) m)⟩ fun _ =>
        .ret (count + 1, .ok)
    | ⟨.B, .receive⟩ =>
        .call ⟨.inr .b, .fetch⟩ fun k =>
        .call ⟨.inl .B, .receive⟩ fun ciphertext? =>
        .ret (count, ciphertext?.bind (E.dec k))
    | ⟨.E, .leak i⟩ =>
        .call ⟨.inl .E, .leak i⟩ fun answer => .ret (count, answer)
    | ⟨.E, .deliver i⟩ =>
        .call ⟨.inl .E, .deliver i⟩ fun answer => .ret (count, answer)
    | ⟨.F, .deliver i⟩ =>
        .call ⟨.inl .F, .deliver i⟩ fun answer => .ret (count, answer)

/-! ## The simulator (Fig. 2.4a) -/

/-- Fig. 2.4a's `σ_E`: on `(leak, i)` it asks `SecChan` for the length and
answers an encryption of `0^ℓ` under its **own** key; everything else is
forwarded.  The thesis's `M_A[·]` cache is unnecessary here because the
tape is indexed by the leak index `i` itself, so repeated leaks are stable
by construction.  Stateless. -/
def sigmaConv [Inhabited R] (E : EncScheme K R M C L) {cap : ℕ}
    (key : K) (tape : Fin cap → R) :
    Converter (conSig M C) (conBnd M C)
      (SignatureUniverse.ofInterfaces (chanIn M) (secOut M L))
      (Boundary.ofInterfaces (chanIn M) (secOut M L)) where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨.A, .send m⟩ =>
        .call ⟨.A, .send m⟩ fun _ => .ret ((), .ok)
    | ⟨.B, .receive⟩ =>
        .call ⟨.B, .receive⟩ fun message? => .ret ((), message?)
    | ⟨.E, .leak i⟩ =>
        .call ⟨.E, .leak i⟩ fun answer =>
        .ret ((), match answer with
          | .leaked none => .leaked none
          | .leaked (some l) =>
              .leaked (some (E.enc key (tapeAt tape (i - 1)) (E.zeroOf l)))
          | .ok => .leaked none)
    | ⟨.E, .deliver i⟩ =>
        .call ⟨.E, .deliver i⟩ fun _ => .ret ((), .ok)
    | ⟨.F, .deliver i⟩ =>
        .call ⟨.F, .deliver i⟩ fun _ => .ret ((), .ok)

/-! ## The reduction (Prop. 2.2.17's `c`) -/

/-- Prop. 2.2.17's reduction: emulates the constructed boundary in front of
a CPA resource.  On a send it plays the challenge pair `(m, 0^{|m|})` and
stores the plaintext/ciphertext pair; Bob reads stored plaintexts; Eve reads
stored ciphertexts.  The `none` branch of the challenge answer is
unreachable (`len_zeroOf` satisfies the game's guard) but the package
requires the decision. -/
def cConv (E : EncScheme K R M C L) :
    Converter (conSig M C) (conBnd M C)
      (SignatureUniverse.ofInterfaces (fun _ : Unit => CPAIn M)
        (fun _ : Unit => Option C))
      (Boundary.ofInterfaces (fun _ : Unit => CPAIn M)
        (fun _ : Unit => Option C)) where
  State := List (M × C) × Option M
  init := ([], none)
  step state query :=
    match query with
    | ⟨.A, .send m⟩ =>
        .call ⟨(), .challenge m (E.zeroOf (E.len m))⟩ fun ciphertext? =>
        .ret (match ciphertext? with
          | some c => ((state.1 ++ [(m, c)], state.2), .ok)
          | none => (state, .ok))
    | ⟨.B, .receive⟩ => .ret (state, state.2)
    | ⟨.E, .leak i⟩ =>
        .ret (state, .leaked (logLookup (state.1.map Prod.snd) i))
    | ⟨.E, .deliver i⟩ =>
        .ret ((state.1, logLookup (state.1.map Prod.fst) i), .ok)
    | ⟨.F, .deliver i⟩ =>
        .ret ((state.1, logLookup (state.1.map Prod.fst) i), .ok)

/-! ## The three composite families and their laws -/

variable [Inhabited R] [DecidableEq L]

/-- `π_E [AuthChan, Key]` at a fixed seed. -/
def realMachine (E : EncScheme K R M C L) {cap : ℕ} (seed : Seed K R cap) :
    Machine (conSig M C) (conBnd M C) :=
  (piConv E seed.2).attach ((authChan C).par (keyMachine K seed.1))

/-- `σ_E SecChan` at a fixed seed (the simulator's key and tape). -/
def idealMachine (E : EncScheme K R M C L) {cap : ℕ} (seed : Seed K R cap) :
    Machine (conSig M C) (conBnd M C) :=
  (sigmaConv E seed.1 seed.2).attach (secChan E.len)

/-- `c CPA_b` at a fixed seed. -/
def gameMachine (E : EncScheme K R M C L) (b : Bool) {cap : ℕ}
    (seed : Seed K R cap) : Machine (conSig M C) (conBnd M C) :=
  (cConv E).attach (cpaMachine E b seed)

variable [Fintype K] [Nonempty K] [Fintype R]

open RandomSystems (Dist)

/-- The real-world law: `π_E [AuthChan, Key]` under the uniform seed. -/
noncomputable def real (E : EncScheme K R M C L) (cap : ℕ) :
    DependentPDS.Prob (conSig M C) (conBnd M C) :=
  Machine.lawOf (realMachine E (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

/-- The ideal-world law: `σ_E SecChan` under the uniform seed. -/
noncomputable def ideal (E : EncScheme K R M C L) (cap : ℕ) :
    DependentPDS.Prob (conSig M C) (conBnd M C) :=
  Machine.lawOf (idealMachine E (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

/-- The reduction against `CPA_b`, under the uniform seed. -/
noncomputable def game (E : EncScheme K R M C L) (b : Bool) (cap : ℕ) :
    DependentPDS.Prob (conSig M C) (conBnd M C) :=
  Machine.lawOf (gameMachine E b (cap := cap))
    (Dist.uniform (Seed K R cap)) Dist.uniform_isProbDist

end RandomSystems.CR18.TypedResource.Jost226
