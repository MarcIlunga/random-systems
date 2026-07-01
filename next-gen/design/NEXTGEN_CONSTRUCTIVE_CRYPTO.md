# Next-gen Constructive Cryptography — Design

A design for a CR18 Chapter 5 ("Constructive Cryptography") layer built **directly on**
the next-gen PFun-native random-systems library (`random-systems/next-gen/NextGen/`).

> Convention. All "CR18 §x / Def y" references are to the lecture notes
> `random-systems/papers/CR18_LN.txt`. All `file:line` references are to
> `random-systems/next-gen/NextGen/` unless noted. This is a **design document**:
> the Lean below is statement-shape (signatures + `sorry`), not finished proof code.

---

## 0. The cr18-formalize lens applied to CC

The skill's chain (`cr18-formalize/SKILL.md:12`): pick the **first** faithful type —
predicate → function → product → subtype → reuse-a-generic-def — and never default to a
`structure`, an execution model, `Bool`, or `Decidable`/`Fintype` on a carrier.

CR18's Chapter 5 is unusually kind to this lens, because Maurer himself defines CC's
objects as the *lightest* possible things:

- **Resource specification** = "a subset of Φ" (Def 5.3, `CR18_LN.txt:5875`). A `Set`/predicate.
- **Constructor / construction** = "a function Φ → Φ" extended to specifications (§5.2.2,
  `CR18_LN.txt:5897`); a *construction relation* is "a subset of Ω × Γ × Ω, i.e. a relation"
  (Def 5.1, `CR18_LN.txt:5852`). A function, then a `Prop`.
- **Construction statement** `R --γ--> S` = "`γ(R) ⊆ S`" (Def 5.4, `CR18_LN.txt:5903`). A `Prop`
  (set inclusion).
- **Relaxation** = a function `P(Φ) → P(Φ)` with `R ⊆ ρ(R)` (Def 5.5, `CR18_LN.txt:5913`). A function.
- **ε-relaxation of a PDS spec** = `{R' | ∃R∈R, ∆(R,R') ≤ ε}` (§5.3.4, `CR18_LN.txt:6065`). A `Set`-builder.

So the **entire abstract CC story is a Prop over a Set of resources, where a resource is a
concrete PDS** (`CR18_LN.txt:5873`: "resources are probabilistic discrete systems (PDS)"). No new
operational object is introduced by Chapter 5 — it is a thin propositional layer above the
random-systems objects already formalized in next-gen.

This immediately condemns the heavyweight approach (see §6) and points at the design below.

---

## 1. Core abstraction: a CC resource IS a (multi-interface) PDS specification

### 1.1 The concrete resource — reuse `PFunDDS.Resource`

next-gen already has the exact object CR18 §5.3.1 asks for. CR18 §5.3.1
(`CR18_LN.txt:6006`) says a resource has *interfaces* (party `A`,`B`,…, adversary `E`, free
`F`). next-gen's `PFunDDS.Resource` (`PFunDDS.lean:703`) is:

```lean
abbrev Resource (I : Type u) (A : Type v) (B : Type w) : Type _ := DDS (I × A) B
```

i.e. "a DDS whose input alphabet has been partitioned into interface-tagged fibers"
(`PFunDDS.lean:700-704`), with the interface partition `Xᵢ = {i}×A` already proven disjoint and
covering (`interfaceAlphabet`, `interfaceAlphabet_disjoint` `PFunDDS.lean:739`,
`iUnion_interfaceAlphabet` `PFunDDS.lean:749`). **This is Maurer's `X = X₁ ∪ … ∪ Xₙ` interface
partition, verbatim.** A *probabilistic* resource is then a distribution over it — reuse
`PFunPDS` (`PDS.lean:60`) lifted to the interface-tagged alphabet:

```lean
/-- A probabilistic CC resource: a PDS over the interface-tagged alphabet.
    `I` = interface labels (party/adversary/free), `A` = per-interface input, `B` = output. -/
abbrev PResource (I : Type u) (A : Type v) (B : Type w) : Type _ :=
  PFunPDS (I × A) B          -- = Dist (PFunDDS.Resource I A B)
```

Decision: **reuse, do not invent.** `PResource` is a one-line abbrev over existing types.

### 1.2 A resource *specification* is a predicate (Def 5.3)

CR18 Def 5.3 (`CR18_LN.txt:5875`): "A resource specification is a subset of Φ." Lightest faithful
type = `Set` / predicate. No structure.

```lean
/-- CR18 Def 5.3: a resource specification is a subset of (probabilistic) resources. -/
abbrev ResourceSpec (I A B) : Type _ := Set (PResource I A B)
```

"`R` is as specific as `S`" = `R ⊆ S` (Def 5.3, `CR18_LN.txt:5877`) — it is literally `⊆` on `Set`.
Nothing to define.

### 1.3 A converter / protocol — reuse the two existing presentations

next-gen gives **two equivalent presentations** of a converter, and CC uses both:

1. **The DDC object** `PFunConverter.DDC U V X Y` (`PFunConverter.lean:36`), with
   `attachAt : (i : P) → DDC X Y X Y → Resource P X Y → Resource P X Y`
   (`PFunConverter.lean:1600`) — *applying a converter at one interface of a resource*. This is
   exactly CR18 §5.3.2's `αⁱR` and the protocol construction
   `R ↦ π₁^{P₁} ⋯ πₙ^{Pₙ} R` (Def 5.8, `CR18_LN.txt:6022-6024`).
2. **The function-on-systems view** `c : DDS X Y → DDS U V` (`ReductionByConverter.lean:51`):
   "A converter `c` is, by CR18 §3.4.6, its action on systems — a function"
   (`ReductionByConverter.lean:11`). This is the cleanest carrier for the **abstract**
   constructor `γ : Φ → Φ` of §5.2.2.

Decision: **a CC constructor at the abstract level (Def 5.4) is the function-view**, and the
**concrete protocol (Def 5.8) is a tuple of `DDC`s applied via `attachAt`**, with a lemma bridging
the two (the protocol *induces* a function on resources). The constructor is a *function*, never a
structure — matching §1 of the lens and `ReductionByConverter.lean:11`.

```lean
/-- CR18 §5.2.2: an abstract constructor is a function on (probabilistic) resources,
    the pushforward of a function on the underlying deterministic resources. -/
abbrev Constructor (I A B I' A' B') : Type _ :=
  PResource I A B → PResource I' A' B'

/-- CR18 Def 5.8: a protocol is one converter per party interface. Applying it
    is iterated `attachAt`. (Stated for a single shared (A,B) interface alphabet.) -/
def protocolApply [DecidableEq P] (π : P → PFunConverter.DDC A B A B)
    (parties : List P) (R : PResource P A B) : PResource P A B :=
  -- pushforward of "attach πₚ at interface p, for each p in `parties`" over the PDS
  Dist.fTransform
    (fun s => parties.foldr (fun p s' => PFunConverter.attachAt p (π p) s') s) R
```

> `DecidableEq P` here is **not** a carrier-`DecidableEq` smell (§4 of the lens): it is used only
> to fold converter-attachment over a *list of interface labels* (which interface am I attaching
> at), exactly as the existing `attachAt` machinery already does. It is decidability of the
> *interface index set*, not of a resource/behavior carrier. Keep it off `A`/`B`. (See open
> question Q3.)

---

## 2. The construction relation `R --π--> S`

### 2.1 Abstract construction (Def 5.4) — a Prop, set inclusion

CR18 Def 5.4 (`CR18_LN.txt:5903`): `R --γ--> S :⇔ γ(R) ⊆ S`, where `γ(R) = {γ(R) | R ∈ R}`
(`CR18_LN.txt:5898`). Lightest faithful type = `Prop`. The mapped-specification `γ(R)` is
`Set.image` of the constructor.

```lean
/-- CR18 Def 5.4: `R --γ--> S` iff `γ(R) ⊆ S` (the image of `R` under `γ` is in `S`). -/
def Constructs (γ : Constructor I A B I' A' B')
    (R : ResourceSpec I A B) (S : ResourceSpec I' A' B') : Prop :=
  γ '' R ⊆ S
```

This is the **most abstract** construction notion (Lemma 5.1, `CR18_LN.txt:5910`, is composability
of *exactly this*). Composability is then `Set.image_comp` — see §3.

### 2.2 The cryptographically interesting instance: ε-relaxation + simulator

Pure set-inclusion is too rigid for crypto; CR18 §5.3.4–5.3.7 relaxes the *right-hand* spec. The
two relaxations that carry the cryptographic content:

**ε-relaxation** (§5.3.4, `CR18_LN.txt:6065`): `Rε = {R' | ∃R∈R, ∆(R,R') ≤ ε}`. Reuse next-gen's
`maxAdvantage`/`Δ(S,T)` (`Distinguishing.lean:64`, notation `Δ(S, T)` `Distinguishing.lean:67`).

> **Q1 RESOLVED (team-lead): full-resource `Δ`.** A CC resource is `PResource I A B = PFunPDS (I×A) B`,
> which already has the shape `PFunPDS X Y` that `Δ` (`Distinguishing.lean:45`) is stated on, with
> `X = I × A`. So `asPDS : PResource I A B → PFunPDS (I×A) B := id` and `Δ` applies directly — the
> distinguisher is connected to **all free + adversary interfaces at once**. The ∗-relaxation
> (Def 5.9, "arbitrary α at E") stays a **separate** notion (§2.2 below). This is standard CC.

```lean
/-- CR18 §5.3.4: the ε-relaxation of a resource spec, using the next-gen
    distinguishing metric `Δ` (Distinguishing.lean:64) on the full resource.
    `asPDS = id` (a resource IS a `(I×A, B)`-PDS). -/
def epsRelax (ε : ℝ) (S : ResourceSpec I A B) : ResourceSpec I A B :=
  { R' | ∃ R ∈ S, (Δ( asPDS R, asPDS R' ) : ℝ) ≤ ε }
```

**∗-relaxation / the simulation paradigm** (§5.3.6–5.3.7, `CR18_LN.txt:6121`, `:6140`): this is the
heart of simulation-based security. CR18 §5.3.7 (`CR18_LN.txt:6091-6112`) states it concretely:

> consider real `U` and ideal `V` with an E-interface, and a simulator `σ` such that **`U ≡ σ^E V`**.
> Then `∀α ∃β. α^E U ≡ β^E V` with `β = ασ`.

So the **construction-with-simulator relation** is: *there exists a simulator converter σ attached
at the adversary interface E such that the real resource (protocol applied to the assumed resource)
is ε-close to the ideal resource with σ attached.* This is the single central CC security
statement.

```lean
/-- CR18 §5.3.7 simulation-based construction `[Rᵢ] --π,σ--> S` (with ε error):
    the real world `π·R` is Δ-within-ε of the ideal world `σ^E·S`.
    `E` is the (fixed) adversary interface; `σ` is attached there.
    `R` = assumed resource, `S` = constructed (ideal) resource, `π` = protocol. -/
def ConstructsWithSim
    (π : P → PFunConverter.DDC A B A B)       -- protocol (party converters)
    (E : P)                                    -- adversary interface
    (σ : PFunConverter.DDC A B A B)            -- simulator at E
    (ε : ℝ)
    (R S : PResource P A B) : Prop :=
  (Δ( asPDS (protocolApply π parties R) ,
       asPDS (Dist.fTransform (PFunConverter.attachAt E σ) S) ) : ℝ) ≤ ε
```

This is the **chosen central security definition**. Note it is built **entirely** from existing
pieces: `attachAt` (converter application), `Dist.fTransform` (pushforward of a converter over a
PDS), and `Δ` (distinguishing advantage). The only genuinely new content is the *shape* of the
statement (the ∀α∃β quantifier is discharged by the `β = ασ` translation, recorded as a lemma —
see §4, mirroring `ReductionByConverter.rhoC` `ReductionByConverter.lean:54`).

### 2.3 Game-relaxation (§5.3.8) — DECISION NEEDED (user review)

> **This is the one load-bearing modeling call where Maurer is deliberately informal**
> (Def 5.10 footnote 7, `CR18_LN.txt:6153`: "It is not difficult to make this definition
> mathematically rigorous." — but he doesn't). The final choice is the user's. Below are **two
> alternative `T̂⊢`-as-`Set` models** with tradeoffs; **nothing here is locked in.** Both obey the
> lightest-faithful discipline (a `Set`/`Prop` over the *existing* concrete game objects — `DDS`,
> the MBO bit `Y × Bool`, `b(S)` behavior — **no new operational layer**).

CR18 §5.3.8 (`CR18_LN.txt:6151`) defines the game-relaxation `T̂⊢` and Lemmas 5.2/5.3
(`CR18_LN.txt:6163`, `:6172`):

> Def 5.10: for a system `T` enhanced with an MBO to a game `T̂`, `T̂⊢` is "the set of PDS that behave
> as `T` as long as the MBO is 0 and behave arbitrarily once the MBO is 1."
> Lemma 5.2: `Ŝ ≡_g T̂ ⟹ S ⊆ T̂⊢`.   Lemma 5.3: `Ŝ |≡ T ⟹ S ⊆ T̂⊢`.

This is **the bridge** that makes CC constructions discharge to the already-proven §4 game bound: a
construction obligation `Δ([q]R, [q]S) ≤ ε` reduces, via game-relaxation, to a `maxWinProb`/`Γ`
bound on the game `Ŝ` — exactly Theorem 4.17, used to prove Lemma 4.19 (`CR18_LN.txt:5720-5731`).

**The explicit discharge target (already proven in next-gen):**
`Theorem417.lean:398` `theorem_4_17_condEquiv` —
```lean
theorem theorem_4_17_condEquiv (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (maxWinProb Shat : ℝ)
```
i.e. `Ŝ |≡ T ⟹ ∆^D(Ŝ⁻, T) ≤ Γ(Ŝ)` (per-`D`; the `Δ`-form follows by `advantage_le_maxAdvantage`
`Distinguishing.lean:71`). `CondEquiv` is `Shat |≡ T` (`CondEquiv.lean:115`), and its hypotheses
(`isProbDist`, `MonotoneMBO` = `DDS.IsGame`, `TotalOnNonempty`, `QueriesExactly`) are **exactly
Maurer's standing assumptions** (lens §3) — so any `T̂⊢` model must carry precisely these and no
more.

#### Model A — `T̂⊢` as a behavioral agreement spec (recommended starting point)

`T̂⊢` = the set of PDSs `R` (enhanced with `T̂`'s MBO to a game `R̂`) whose **not-yet-won
prewin-behavior equals `T̂`'s** — i.e. `massYAfalse R̂ = massYAfalse T̂` on every history where the
game is still won-free (`Aᵢ = 0`). This is *exactly* the `massYAfalse`/`gamePrewinBehavior`-equality
set — the primitive `theorem_4_17_condEquiv` is stated on (`CondEquiv.lean:58`,
`Lemma415.lean:227`). "Behave arbitrarily once `Aᵢ = 1`" = the constraint touches only the `Aᵢ=0`
mass `massYAfalse`, leaving post-win behavior free by construction.

```lean
/-- Def 5.10, Model A: `R ∈ T̂⊢` iff `R`'s game-enhancement has the **same not-yet-won
    prewin-behavior** as `T̂`. The constraint *is* the `massYAfalse`-equality the §4 layer uses;
    no opaque helper. `Tgame = gameEnhance T Ŝ` (Theorem417.lean:51); `R̂` is `R` under the same MBO. -/
def gameRelaxA (Tgame : PFunPDS X (Y × Bool)) : ResourceSpec_single X Y :=
  { R | ∀ (i : ℕ) (xs : Vector X (i+1)) (ys : Vector Y (i+1)),
          CondEquiv.massYAfalse (mboEnhance R Tgame) i ys xs
            = CondEquiv.massYAfalse Tgame i ys xs }   -- prewin-behavior equality (Aᵢ=0)
```
- **Pro:** the constraint *is* `massYAfalse`-equality — the **exact** primitive
  `theorem_4_17_condEquiv` speaks (`CondEquiv.lean:58`, `massYAfalse_eq_mass_gameMatches`
  `Lemma415.lean:227`). Lemma 5.3 is then "`Ŝ |≡ T` is (cross-multiplied) `massYAfalse` equality ⟹
  membership" — short, the faithfulness signal. Reuses `MonotoneMBO`/`IsGame` (Def 3.22), no fresh
  monotonicity (lens §3, §5). No helper predicate to invent.
- **Con:** needs `mboEnhance R Tgame` (lift `R` under `T̂`'s MBO) to compare prewin-behaviors —
  reuses `gameEnhance`/`combineSys` (`Theorem417.lean:33,51`). `DecidableEq`/`Fintype`-free
  (`massYAfalse` is classical `Dist.mass` over a `Prop`, lens §4).
- **Coarser variant (rejected):** a Bool-level "behavior agrees until the MBO bit first flips"
  set is *coarser* and tempting, but it reintroduces an operational "run until flip" reading and a
  `Decidable` flip-test — exactly the operational/`Decidable` smell the lens forbids (§2, §4). The
  `massYAfalse`-equality set above is the behavior-primitive form and is preferred.

#### Model B — `T̂⊢` as the ∆-closure of the conditional-equivalence class

`T̂⊢` = `{ R | ∃ Ŝ, Ŝ |≡ T ∧ R = ignoreMBO Ŝ }` — the image, under "forget the MBO", of all games
conditionally-equivalent to `T`. This is the most *operationally direct* reading of Lemma 5.3 (it is
almost its statement), and makes the bridge to `theorem_4_17_condEquiv` definitional.

```lean
/-- Def 5.10, Model B: the forget-MBO image of the CondEquiv class of `T`. -/
def gameRelaxB (T : PFunPDS X Y) : ResourceSpec_single X Y :=
  { R | ∃ Shat : PFunPDS X (Y × Bool), (Shat |≡ T) ∧ R = PFunPDS.ignoreMBO Shat }
```
- **Pro:** Lemma 5.3 (`Ŝ |≡ T ⟹ ignoreMBO Ŝ ∈ T̂⊢`) is `fun h => ⟨Ŝ, h, rfl⟩` — *trivially* true,
  and the CC construction bound is then `theorem_4_17_condEquiv` applied to the witness `Ŝ`. Zero
  new behavior plumbing.
- **Con:** it is **defined by the conclusion it should support**, so it risks being *too* tied to
  `CondEquiv` and not capturing "behaves arbitrarily after MBO=1" as an independent semantic object;
  Lemma 5.2 (the *game-equivalence* `≡_g` route, `CR18_LN.txt:6163`) is then less natural to state.
  It is more of a *proof-driving* definition than a *faithful* one.

#### Recommendation (for user to confirm)

Start with **Model A** (faithful, behavior-native), and **prove Model B's set is contained in
Model A's** as a sanity lemma — that containment is exactly Lemma 5.3's content and is the bridge to
`theorem_4_17_condEquiv`. If Model A's `behaviorAgreesOnMBOzero` helper proves awkward, fall back to
Model B. **Do not pick blindly:** the test is which one makes Lemma 5.2 (`≡_g`) *and* Lemma 5.3
(`|≡`) both short — Model A is the bet, Model B is the escape hatch.

---

## 3. Composition theorems

### 3.1 Serial composability (Lemma 5.1 / Def 5.2, Eq 5.1)

CR18 (5.1) (`CR18_LN.txt:5795`): `R --a--> S ∧ S --b--> T ⟹ R --(a∘b)--> T`. For the abstract
notion (Def 5.4) this is **`Set.image` functoriality** — nearly `rfl`:

```lean
/-- CR18 Lemma 5.1: the abstract construction notion is composable. -/
theorem Constructs.comp
    {γ : Constructor I A B I' A' B'} {γ' : Constructor I' A' B' I'' A'' B''}
    {R : ResourceSpec I A B} {S : ResourceSpec I' A' B'} {T : ResourceSpec I'' A'' B''}
    (h₁ : Constructs γ R S) (h₂ : Constructs γ' S T) :
    Constructs (γ' ∘ γ) R T := by
  -- (γ' ∘ γ) '' R = γ' '' (γ '' R) ⊆ γ' '' S ⊆ T
  rw [Set.image_comp]
  exact (Set.image_subset γ' h₁).trans h₂
```

This is the "construction does not automatically satisfy (5.1); it must be proved" obligation
(`CR18_LN.txt:5799`) — and for the natural Def-5.4 notion it is a two-line proof. Good sign the
model is right (short proof = faithful, per cr18-prove).

### 3.2 Composability of the simulation construction (the cryptographic composition theorem)

The cryptographically meaningful theorem composes `ConstructsWithSim` with **additive error** and
**composed simulator/protocol**. This is where the next-gen pieces do real work:

```lean
/-- Serial composition of simulation-based constructions, with additive error.
    Real `R` --π,σ,ε--> `S` and `S` --π',σ',ε'--> `T`
    gives `R` --(π'∘π),(σ∘σ'),(ε+ε')--> `T`.
    Mirrors CR18 §5.3.7's `β = ασ` translation and the triangle inequality on Δ. -/
theorem ConstructsWithSim.comp
    (h₁ : ConstructsWithSim π  E σ  ε  R S)
    (h₂ : ConstructsWithSim π' E σ' ε' S T) :
    ConstructsWithSim (π' ∘ₚ π) E (σ ∘ᶜ σ') (ε + ε') R T := by
  -- L1 triangle inequality for Δ (ε+ε')            [UPSTREAM-CANDIDATE §7]
  -- L3 converter-application non-expanding for Δ    (§5.2.3 "non-expanding", CR18_LN.txt:5933)
  -- L4 simulator-translation  α^E(σ^E S) = (ασ)^E S (attachAt ∘ cascade; analog of rhoC)
  sorry
```

The three obligations decompose cleanly onto existing/near-existing facts:
- **(1) triangle inequality `Δ(R,T) ≤ Δ(R,S) + Δ(S,T)`** — a generic `Distinguishing` lemma
  (currently `Δ` is a signed `sSup`, `Distinguishing.lean:64`; the triangle holds for the absolute
  metric — see Q2). Tag `UPSTREAM-CANDIDATE`.
- **(2) non-expansion `Δ(γR, γS) ≤ Δ(R,S)`** — CR18 §5.2.3 calls γ "non-expanding"
  (`CR18_LN.txt:5933`). For converter application this is the data-processing inequality: a
  distinguisher against `γR`/`γS` is a distinguisher against `R`/`S` precomposed with `γ`. This is
  the `Distinguishing`-side analog of the *winner-transform* `ρ[c] = (· ∘ c)`
  (`ReductionByConverter.lean:54`, `rhoC_apply` `:64`).
- **(3) simulator composition `α^E(σ^E S) = (ασ)^E S`** — converter associativity:
  `attachAt E α (attachAt E σ S) = attachAt E (α ⊲ σ) S`. The next-gen cascade
  (`PFunDDS.cascade` / `cascadeConverter` `PFunConverter.lean:695`) supplies `α ⊲ σ`; the equation
  is the `attachAt`-level statement of CR18 §5.3.7's `β^E V = (ασ)^E V = α^E(σ^E V)`
  (`CR18_LN.txt:6112`).

### 3.3 Parallel composability (Eq 5.3)

CR18 (5.3) (`CR18_LN.txt:5820`): `⋀ᵢ (Rᵢ --aᵢ--> Sᵢ) ⟹ [R₁,…,Rₖ] --[a₁,…,aₖ]--> [S₁,…,Sₖ]`. The
tuple-resource `[R₁,…,Rₖ]` is next-gen's `PFunDDS.parallel` over `Fin k` interfaces
(`PFunDDS.lean:360`), and `[a₁,…,aₖ]` is the family of converters applied at distinct interfaces —
`attachAt` at distinct `i` **commute** (`attachEntryD_comm` `PFunConverter.lean:1266`,
`attachHistory_comm` `:1287`), which is exactly the independence Eq 5.3 needs.

```lean
/-- CR18 (5.3): parallel composition of constructions over a finite interface family. -/
theorem ConstructsWithSim.parallel {k : ℕ}
    (R S : Fin k → PResource P A B)
    (π : Fin k → P → PFunConverter.DDC A B A B) (σ : Fin k → PFunConverter.DDC A B A B)
    (ε : Fin k → ℝ)
    (h : ∀ i, ConstructsWithSim (π i) E (σ i) (ε i) (R i) (S i)) :
    ConstructsWithSim (parProtocol π) E (parSim σ) (∑ i, ε i)
      (parResource R) (parResource S) := by
  -- parResource = pushforward of `PFunDDS.parallel`; distinct-interface attaches commute
  sorry
```

The ε-bound is the union bound `∑ᵢ εᵢ`; the structural core (attaches at distinct interfaces
commute, distinguisher restricted to one interface) is exactly the `parallel`/`restrict`
infrastructure (`PFunDDS.lean:356-700`, esp. `restrict_keptPrefix_parallel`,
`parallel_output_update_self/ne`).

---

## 4. Worked Lean sketches (the three load-bearing definitions)

These three are the spine. (Universe/`variable` boilerplate elided; `sorry` for proofs.)

### Sketch A — the central security definition (CR18 §5.3.7)

```lean
namespace RandomSystems.CR18.CC
open RandomSystems (Dist) PFunConverter PFunDDS

variable {P A B : Type*} [DecidableEq P]

/-- The real world: the protocol `π` applied to assumed resource `R`. -/
noncomputable def realWorld (π : P → DDC A B A B) (parties : List P)
    (R : PResource P A B) : PResource P A B :=
  Dist.fTransform (fun s => parties.foldr (fun p s' => attachAt p (π p) s') s) R

/-- The ideal world: simulator `σ` attached at the adversary interface `E` of ideal `S`. -/
noncomputable def idealWorld (E : P) (σ : DDC A B A B)
    (S : PResource P A B) : PResource P A B :=
  Dist.fTransform (attachAt E σ) S

/-- **CR18 §5.3.7 — simulation-based construction with ε error.** -/
def ConstructsWithSim (π : P → DDC A B A B) (parties : List P) (E : P)
    (σ : DDC A B A B) (ε : ℝ) (R S : PResource P A B) : Prop :=
  (Δ( asPDS (realWorld π parties R), asPDS (idealWorld E σ S) ) : ℝ) ≤ ε
```

where `asPDS : PResource P A B → PFunPDS (P × A) B := id` (a `Resource` *is* a `(P×A, B)`-PDS;
`Δ` is stated on `PFunPDS X Y` `Distinguishing.lean:45`, so this is a definitional view, modulo Q1).

### Sketch B — the simulator-translation lemma (CR18 §5.3.7, `α ↦ ασ`)

```lean
/-- **CR18 §5.3.7, the `β = ασ` translation** (`CR18_LN.txt:6110-6112`):
    for any adversary converter α at E, α^E(σ^E S) = (ασ)^E S, so the universal
    `∀α ∃β. α^E U ≡ β^E V` is witnessed by `β = ασ`. This is the CC-level analog
    of `ReductionByConverter.rhoC_apply` (ReductionByConverter.lean:64). -/
theorem attach_sim_translate (E : P) (α σ : DDC A B A B) (S : PResource P A B) :
    Dist.fTransform (attachAt E α) (idealWorld E σ S)
      = idealWorld E (α ⊲ σ) S := by
  -- attachAt E α (attachAt E σ s) = attachAt E (α ⊲ σ) s,  then push through fTransform
  sorry
```

### Sketch C — the composition theorem (CR18 Eq 5.1, simulator/ε form)

(Statement as in §3.2; the proof obligations enumerated there.)

```lean
theorem ConstructsWithSim.comp
    {π π' : P → DDC A B A B} {parties : List P} {E : P} {σ σ' : DDC A B A B}
    {ε ε' : ℝ} {R S T : PResource P A B}
    (h₁ : ConstructsWithSim π  parties E σ  ε  R S)
    (h₂ : ConstructsWithSim π' parties E σ' ε' S T) :
    ConstructsWithSim (fun p => π' p ⊲ π p) parties E (σ ⊲ σ') (ε + ε') R T := by
  -- triangle(Δ) + non-expansion(Δ, attachAt) + attach_sim_translate
  sorry
```

---

## 5. Mapping table {CR18 CC concept → next-gen Lean}

| CR18 concept (line) | next-gen type/def | reuse / new |
| --- | --- | --- |
| PDS = resource (`:5873`) | `PFunPDS X Y` = `Dist (DDS X Y)` (`PDS.lean:60`) | **reuse** |
| Interfaces A/B/E/F (`:6006`) | `PFunDDS.Resource I A B = DDS (I×A) B` (`PFunDDS.lean:703`); `interfaceAlphabet` (`:724`) | **reuse** |
| Probabilistic resource | `PResource I A B := PFunPDS (I×A) B` | **new** (1-line abbrev) |
| Resource spec, Def 5.3 (`:5875`) | `ResourceSpec := Set (PResource ..)` | **new** (abbrev) |
| "as specific as" `R ⊆ S` (`:5877`) | `⊆` on `Set` | **reuse** (`Set`) |
| Constructor `γ:Φ→Φ` §5.2.2 (`:5897`) | `Constructor := PResource→PResource`; function-view `DDS X Y → DDS U V` (`ReductionByConverter.lean:51`) | **reuse** |
| Converter at interface `αⁱR` (`:6022`) | `PFunConverter.attachAt` (`PFunConverter.lean:1600`) | **reuse** |
| Protocol π (tuple), Def 5.8 (`:6022`) | `protocolApply` (fold of `attachAt`) | **new** (thin) |
| `γ(R) = {γ(R)\|R∈R}` (`:5898`) | `Set.image γ R` | **reuse** (Mathlib) |
| Construction `R--γ-->S`, Def 5.4 (`:5903`) | `Constructs γ R S := γ '' R ⊆ S` | **new** (Prop) |
| Composability, Lemma 5.1 (`:5910`) | `Constructs.comp` via `Set.image_comp` | **new** (thin) |
| Relaxation ρ, Def 5.5 (`:5913`) | `P(Φ)→P(Φ)` with `R⊆ρR` = a function + Prop | **new** (abbrev) |
| Distinguishing advantage ∆ (`:6065`) | `maxAdvantage` / `Δ(S,T)` (`Distinguishing.lean:64`) | **reuse** |
| ε-relaxation §5.3.4 (`:6065`) | `epsRelax ε S` (Set-builder over `Δ`) | **new** |
| Simulator `σ`, `U ≡ σ^E V` §5.3.7 (`:6105`) | `idealWorld E σ S` via `attachAt E σ` | **new** |
| `β = ασ` translation (`:6112`) | `attach_sim_translate` (analog of `rhoC_apply` `ReductionByConverter.lean:64`) | **new** |
| ∗-relaxation, Def 5.9 (`:6121`) | `Set`-builder `{α^E R \| α∈Σ}` over `attachAt` | **new** |
| Game-relaxation `T̂⊢`, Def 5.10 (`:6151`) | `ResourceSpec` agreeing-until-MBO; bridges via `b(S)`/`DDS.IsGame` | **new** (bridge) |
| Lemmas 5.2/5.3 (`:6163`,`:6172`) | bridge theorems game-equiv/cond-equiv ⟹ `⊆ T̂⊢` | **new** |
| `∆([q]R,[q]P) ≤ Γ(b[q]R̂)` Thm 4.17 (Lem 4.19 `:5727`) | existing `Γ`/`maxWinProb` + filter `[q]` (`queryLimit` `PFunConverter.lean:321`) | **reuse** |
| Parallel `[R₁,…,Rₖ]` (`:5803`) | `PFunDDS.parallel` (`PFunDDS.lean:360`) | **reuse** |
| Parallel converters commute (Eq 5.3) | `attachEntryD_comm`/`attachHistory_comm` (`PFunConverter.lean:1266`,`:1287`) | **reuse** |
| Parameterized resource `{φᵣR}`, Def 5.11 (`:6236`) | family `fun r => queryLimitApply r R` (`PFunConverter.lean:345`) | **reuse** |

**Net new surface area: ~8 definitions (all abbrev/Prop/thin) + the bridge & composition
theorems.** Everything cryptographic (`Δ`, converter application, parallel, query filters, behavior,
games) is reused.

---

## 6. Critique of the existing `constructive-crypto` repo

(`constructive-crypto/ConstructiveCrypto/`, `lean_lib ConstructiveCrypto`.)

The existing repo is built on an **abstract algebraic axiomatization**, not on the concrete
random-systems objects:

- `Resource.lean:61` — `structure IndexedResourceAlgebra` with carrier `Resource : Type u → Type v`
  and **axiom fields** `dist`, `relabel`, `par`, `empty`, plus laws (`dist_self`, `dist_triangle`,
  `par_comm`, …). `Resource.lean:182` — `structure CCAlgebra (I : Type*)` likewise carries
  `Resource : Type*`, `dist`, `ParOp`, etc.
- `Composition.lean:205` — `structure CCAlgebra.ConstructionRelation` carries `realizes`, `id`,
  `comp` as **fields** with the composition law as a field obligation.

Against the cr18-formalize lens (`SKILL.md:10-20`):

1. **Heaviest-possible default (lens §1).** CC's objects are, in CR18, a `Set` and a `Prop` over
   *concrete PDSs* (Def 5.1/5.3/5.4, `CR18_LN.txt:5852`,`:5875`,`:5903`). The repo instead posits an
   abstract structure with a carrier type-family and axiom fields. This is the "a structure is not a
   function / a property is a Prop not a one-field structure" anti-pattern at the largest scale: the
   *entire theory* is re-axiomatized rather than instantiated. `dist`/`dist_triangle` as **fields**
   re-posit a metric that next-gen already *constructs* as `Δ` from distinguishers
   (`Distinguishing.lean:64`) — and CR18 §5.3.4 *defines* the ε-relaxation in terms of that
   constructed `∆`, not an abstract metric.

2. **Parallel framework / no reuse (lens §5).** The abstract `CCAlgebra.Resource` does not reuse
   `PFunDDS.Resource` (`PFunDDS.lean:703`), `PFunPDS` (`PDS.lean:60`), `attachAt`
   (`PFunConverter.lean:1600`), `parallel` (`PFunDDS.lean:360`), or `Δ` (`Distinguishing.lean:64`).
   It is a second, disconnected formalization of the same theory — precisely the "no parallel
   frameworks; restate via the canonical def" rule. There is no proven bridge from the abstract
   algebra down to the concrete random-systems objects, so its theorems are about an *axiomatized*
   CC, not about the URF/URP/CBC resources the rest of the project reasons over.

3. **`DecidableEq` on the interface carrier (lens §4).** `Composition.lean:171`
   `CCAlgebra.theorem2RealWorld [DecidableEq I]` and `:182` carry `DecidableEq I`. On an
   *interface-label* set this is the benign case (cf. Q3) — but combined with the abstract carrier it
   signals the model is reasoning about interfaces operationally (finset folds over an abstract
   algebra) rather than via the already-proven `interfaceAlphabet` partition
   (`PFunDDS.lean:724-754`).

4. **`relabel : (I ≃ J) → Resource I → Resource J` as an axiom field** (`Resource.lean:67`)
   re-encodes interface renaming abstractly, where next-gen gets it for free from the tagged
   alphabet `I × A` (renaming = `Sum.map`/`Equiv` on the tag, a pushforward).

**Verdict.** The existing repo is *upside-down*: it builds CC as a top-down axiom system and would
need a (currently absent) downward bridge to the concrete systems. The design here is *bottom-up*:
CC is a thin `Set`/`Prop` layer **on** the concrete next-gen PDS/converter/Δ objects, so every CC
statement is automatically a statement about real resources (URF, URP, CBC-MAC, HCTR2). The abstract
algebra is recoverable later, if wanted, as a *derived* `instance` proven *from* the concrete layer
— never as the primitive.

---

## 7. UPSTREAM-CANDIDATE lemmas to prove (the explicit obligation list)

Per team-lead: **prove, never posit** (cr18-formalize §3; the old repo's `dist`/`dist_triangle`
axiom *fields* are exactly the mistake to avoid — relocating ≠ assuming). The CC layer's ε-accounting
and composition rest on these, all stated on the concrete next-gen `Δ`/`attachAt`/`Set` objects and
tagged `UPSTREAM-CANDIDATE`:

| # | Lemma | Statement | Discharges via |
| --- | --- | --- | --- |
| L1 | **Δ subadditivity (triangle)** | `Δ(S,U) ≤ Δ(S,T) + Δ(T,U)` | per-`D`: `∆^D(S,U) = ∆^D(S,T)+∆^D(T,U)` is `rfl` on `verdictProb` differences (`Distinguishing.lean:45`); then `sSup` is subadditive over the (bdd, `bddAbove_advantage_image` `:51`) image. ε accumulates here. |
| L2 | **verdict-negation closure ⟹ `sup ∆^D = sup \|∆^D\|`** | the distinguisher class is closed under `Z ↦ 1−Z` (negate the verdict bit, `PFunDDS.verdict` `PDS.lean:2136`), so `Δ(S,T) = sup_D \|∆^D(S,T)\|` and `Δ(S,T) = Δ(T,S)` | makes the **signed** `Δ` (`Distinguishing.lean:14-17`, kept signed) a genuine **pseudo-metric** for CC distance — the symmetry/abs CC needs without abandoning Maurer's signed `⟨S\|T⟩`. |
| L3 | **Δ non-expansion under converter application** | `Δ(γR, γS) ≤ Δ(R,S)` (§5.2.3 "non-expanding", `CR18_LN.txt:5933`) | data-processing: a distinguisher `D` against `γR/γS` is `D ∘ γ` against `R/S` — the `Distinguishing`-side analog of the winner-transform `ρ[c] = (·∘c)` (`ReductionByConverter.lean:54`, `rhoC_apply` `:64`). |
| L4 | **simulator-translation** | `attachAt E α (attachAt E σ s) = attachAt E (α ⊲ σ) s`, then pushed through `Dist.fTransform` (`attach_sim_translate`, Sketch B) | CR18 §5.3.7's `β^E V = (ασ)^E V = α^E(σ^E V)` (`CR18_LN.txt:6112`); cascade `α ⊲ σ` from `PFunDDS.cascade`/`cascadeConverter` (`PFunConverter.lean:695`). |
| L5 | **serial composability (abstract, Lemma 5.1)** | `Constructs γ R S → Constructs γ' S T → Constructs (γ'∘γ) R T` | `Set.image_comp` + `Set.image_subset` (Mathlib) — 2 lines (§3.1). |
| L6 | **serial composability (simulator/ε, Eq 5.1)** | `ConstructsWithSim.comp` (§3.2) | L1 (triangle, ε+ε') + L3 (non-expansion) + L4 (simulator translation). |
| L7 | **parallel composability (Eq 5.3)** | `ConstructsWithSim.parallel` (§3.3), ε = `∑ᵢ εᵢ` | `PFunDDS.parallel` (`PFunDDS.lean:360`) + `attachHistory_comm` (`PFunConverter.lean:1287`, distinct-interface) + L1 (union bound). |
| L8 | **protocol order-independence (Q4)** | `protocolApply` independent of party-list order (distinct interfaces) | `attachHistory_comm`/`attachEntryD_comm` (`PFunConverter.lean:1287`,`:1266`). |
| L9 | **Lemma 5.3 (game-relax bridge)** | `Ŝ \|≡ T ⟹ ignoreMBO Ŝ ∈ T̂⊢` (model A or B, §2.3) | model A: `CondEquiv` (`CondEquiv.lean:115`) is cross-multiplied `massYAfalse`-equality ⟹ membership is `rfl`-ish; bound then = **`theorem_4_17_condEquiv` (`Theorem417.lean:398`)**, `Ŝ\|≡T ⟹ ∆^D(Ŝ⁻,T) ≤ Γ(Ŝ)`, Δ-form via `advantage_le_maxAdvantage` (`Distinguishing.lean:71`). |
| L10 | **Lemma 5.2 (game-relax bridge, `≡_g`)** | `Ŝ ≡_g T̂ ⟹ S ⊆ T̂⊢` | game-equivalence `gameEquiv_winFun_eq` (`GameEquivalence.lean:79`) + the chosen `T̂⊢` model. |

L9/L10 depend on the **Q5 `T̂⊢` model decision** (§2.3) — they are *sketched*, not provable until the
user picks model A or B.

## 8. Open modeling questions / risks

- **Q1 — RESOLVED (team-lead): full-resource `Δ`.** The central definition uses `Δ` on the whole
  composed resource (`asPDS = id`); distinguisher connected to all free + adversary interfaces. The
  ∗-relaxation (Def 5.9, arbitrary α at E) is a **separate** notion, not the metric. (Was: full vs
  interface-restricted `Δ`.)

- **Q2 — RESOLVED (team-lead): keep `Δ` signed; PROVE the metric properties.** `Δ` stays Maurer's
  signed `⟨S|T⟩` (`Distinguishing.lean:14-17`). The triangle (L1) and verdict-negation-closure /
  abs-symmetry (L2) are **proven** UPSTREAM-CANDIDATE lemmas, never axioms — this is precisely the
  `dist_triangle`-as-axiom-field mistake the old repo makes and we avoid. ε in `ConstructsWithSim`
  accumulates via L1.

- **Q5 — RESOLVED to a DESIGN SKETCH (team-lead): see §2.3 "DECISION NEEDED".** Two `T̂⊢` models
  (A: behavioral agreement on MBO-0 histories; B: forget-MBO image of the `CondEquiv` class) with
  tradeoffs; **the final pick is the user's.** Both reduce the CC construction obligation to the
  already-proven `theorem_4_17_condEquiv` (`Theorem417.lean:398`). Recommendation: start with Model
  A, keep Model B as escape hatch; the test is which makes both Lemma 5.2 (L10) and Lemma 5.3 (L9)
  short.

- **Q3 — `DecidableEq P` on interface labels.** `protocolApply`/`attachAt`-folds use `DecidableEq P`
  (which interface to attach at). This is decidability of the *index set*, not a carrier — the lens
  forbids `DecidableEq`/`Fintype` on `A`/`B`/behavior carriers, and this isn't one. Still, confirm
  `attachAt` itself doesn't already force it, and prefer a `Fintype`-free fold if `P` is finite via a
  `List` of parties (as sketched). *Recommendation: keep `DecidableEq P` only, never touch `A`/`B`.*

- **Q4 — protocol = `List`-fold vs simultaneous attach.** CR18 Def 5.8 attaches all party
  converters "simultaneously" (`π₁^{P₁}⋯πₙ^{Pₙ}R`). The fold is order-sensitive in syntax but
  order-*insensitive* in result by `attachHistory_comm` (`PFunConverter.lean:1287`) — provided the
  party interfaces are distinct. Need a lemma `protocolApply` is independent of party order (follows
  from `attachHistory_comm`). *Risk:* if two converters share an interface, order matters — but CC
  protocols put one converter per interface, so distinctness is a standing, paper-true hypothesis.

- **Q5 — game-relaxation rigor (Def 5.10, `CR18_LN.txt:6151-6153`).** Maurer footnotes "It is not
  difficult to make this definition mathematically rigorous" but does not. `T̂⊢` = "PDS that behave
  as `T` while MBO is 0, arbitrarily once it is 1." Modeling this as a `Set` of PDSs requires the MBO
  to be a first-class part of the game `T̂` — reuse `DDS.IsGame` / the behavior `b(S)` rather than
  positing fresh monotonicity (lens §3). *Risk:* this is the one place real modeling judgement is
  needed; everything else is mechanical. Lemmas 5.2/5.3 are the bridges that make CC constructions
  discharge to the already-proven §4 game bounds (Thm 4.17), so this is worth getting exactly right.

- **Q6 — `noncomputable`.** `attachAt`, `Dist.fTransform`, `Δ` are all `noncomputable`; the CC layer
  inherits this. Fine for a stating/proving layer (no `#eval` expected), consistent with the rest of
  next-gen.
