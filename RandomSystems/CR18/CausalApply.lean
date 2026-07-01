/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.PFunDDS
import RandomSystems.Dist

/-!
# Causal converter application (`causalApply`) — the function-native, transcript-free apply

CR18 Def 3.9 ("Application of a converter to a resource") is left informal. The faithful realization
is **not** an operational `PFun.fix` over interaction transcripts, but the **functional system
algebra** of Matt–Maurer–Portmann–Renner–Tackmann, *Toward an Algebraic Theory of Systems* (TCS
2018):

* §4.1: a system **is** a function; connecting an input interface to an output interface is a
  **fixed point** of that function, and the connected system is again a function — derived from the
  components, with no transcript.
* §6: for **causal** systems (an output depends only on strictly-earlier inputs) the fixed point is
  **unique** and is reached by a **finite unrolling** (Thm 6.2) — no least-fixed-point choice, no
  Kahn-sequence/`PFun.fix` machinery. Deterministic discrete converters are causal, so this is their
  realization.
* Composition-order invariance (Thm 4.6 / 6.6) is the abstract form of `C^q S^q = (C S)^q`.

## Architecture (memoryless is a special case of the general)

A memoryless resource `s : X → Y` **is** the causal history-function that reads only the current
input, `Ŝ(x₁,…,xₙ) = s(xₙ)` (`lastInput` below). So the general apply threads the converter's
inner-queries through a causal system function `List X →. Y` (the attached DDS's function), and the
**memoryless** apply is that general apply fed `lastInput s`. This file builds the memoryless core
first (`causalDrive`/`causalApply`, matching the HCTR2 development); the general `List X →. Y`
version and the `causalApply step s = causalApplyGen step (lastInput s)` bridge follow.

**UPSTREAM home** for the HCTR2 `causalApply` (this is the generic, HCTR2-independent core).
-/

namespace RandomSystems.CR18.CausalApply

variable {U X Y V : Type*}

/-! ### Memoryless core (Matt §6 finite unrolling, resource a function `X → Y`) -/

/-- **Causal driver.** Thread one converter step map over a memoryless resource oracle `s : X → Y`.
`fuel` bounds the number of consecutive inside-calls (CR18 Def 3.8 requires a finite such bound; for
a concrete converter it is its inside-call count). `Sum.inl x` is the *composing* step (query `s`,
append the answer to the inner-answer history); `Sum.inr v` is the *self-standing* step (the outer
answer). -/
def causalDrive (step : List Y → X ⊕ V) (s : X → Y) : ℕ → List Y → Option V
  | 0,        _   => none
  | fuel + 1, acc =>
      match step acc with
      | Sum.inl x => causalDrive step s fuel (acc ++ [s x])
      | Sum.inr v => some v

/-- One *composing* step: an inner-query `x` appends the resource's answer `s x` and recurses. -/
theorem causalDrive_inl (step : List Y → X ⊕ V) (s : X → Y) (fuel : ℕ) (acc : List Y) {x : X}
    (h : step acc = Sum.inl x) :
    causalDrive step s (fuel + 1) acc = causalDrive step s fuel (acc ++ [s x]) := by
  rw [causalDrive, h]

/-- One *self-standing* step: the outer-answer `v` stops the driver. -/
theorem causalDrive_inr (step : List Y → X ⊕ V) (s : X → Y) (fuel : ℕ) (acc : List Y) {v : V}
    (h : step acc = Sum.inr v) :
    causalDrive step s (fuel + 1) acc = some v := by
  rw [causalDrive, h]

/-- `causalDrive` is monotone in fuel once it has answered: extra fuel never changes a `some`
(causality ⇒ a unique fixed point — Matt's monotonicity for Kahn networks). -/
theorem causalDrive_some_mono (step : List Y → X ⊕ V) (s : X → Y) :
    ∀ {fuel acc v}, causalDrive step s fuel acc = some v →
      causalDrive step s (fuel + 1) acc = some v := by
  intro fuel
  induction fuel with
  | zero => intro acc v h; simp [causalDrive] at h
  | succ n ih =>
      intro acc v h
      simp only [causalDrive] at h ⊢
      cases hstep : step acc with
      | inl x => simp only [hstep] at h ⊢; exact ih h
      | inr w => simp only [hstep] at h ⊢; exact h

/-- Monotone up to any larger fuel: once answered, every larger fuel gives the same answer. -/
theorem causalDrive_mono_le (step : List Y → X ⊕ V) (s : X → Y) {fuel fuel' : ℕ} {acc : List Y}
    {v : V} (hle : fuel ≤ fuel') (h : causalDrive step s fuel acc = some v) :
    causalDrive step s fuel' acc = some v := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]; exact causalDrive_some_mono step s ih

/-! ### Fuel-free apply: the eventual value (Matt §6 — `fuel` is the unrolling counter, hidden)

The mathematical apply is the **unique** value reached by finite unrolling; `fuel` is only the
unrolling counter (CR18 Def 3.8's finite inner-call bound). `causalDrive` is monotone in fuel, so the
value at any large-enough fuel is the same — we expose that fuel-independent value as a `Part`,
undefined exactly when the unrolling diverges (a non-productive converter). The outer apply
statements then carry **no `fuel`**. -/

/-- The eventual value of a fuel-indexed `Part` family (defined where some fuel succeeds). -/
noncomputable def eventual {W : Type*} (g : ℕ → Part W) : Part W :=
  Part.assert (∃ fuel, (g fuel).Dom) fun h => g h.choose

/-- For a fuel-monotone family, the eventual value is membership at *some* fuel (fuel-independent). -/
theorem mem_eventual {W : Type*} {g : ℕ → Part W}
    (hmono : ∀ {f f' : ℕ} {w : W}, f ≤ f' → w ∈ g f → w ∈ g f') {w : W} :
    w ∈ eventual g ↔ ∃ fuel, w ∈ g fuel := by
  rw [eventual, Part.mem_assert_iff]
  constructor
  · rintro ⟨_, hw⟩; exact ⟨_, hw⟩
  · rintro ⟨fuel, hfuel⟩
    have hdom : ∃ f, (g f).Dom := ⟨fuel, Part.dom_iff_mem.mpr ⟨w, hfuel⟩⟩
    refine ⟨hdom, ?_⟩
    have hv : (g hdom.choose).get hdom.choose_spec ∈ g hdom.choose := Part.get_mem _
    have h1 : w ∈ g (max hdom.choose fuel) := hmono (le_max_right _ _) hfuel
    have h2 : (g hdom.choose).get hdom.choose_spec ∈ g (max hdom.choose fuel) :=
      hmono (le_max_left _ _) hv
    rw [Part.mem_unique h1 h2]; exact hv

/-- **Causal application** (fuel-free) of a converter step map to a *memoryless* resource `s : X → Y`
— the eventual value of the finite unrolling (Matt §6 unique fixed point). Partial, undefined exactly
where the converter is not productive. -/
noncomputable def causalApply (step : U → List Y → X ⊕ V) (s : X → Y) (u : U) : Part V :=
  eventual fun fuel => Part.ofOption (causalDrive (step u) s fuel [])

theorem mem_causalApply (step : U → List Y → X ⊕ V) (s : X → Y) (u : U) (v : V) :
    v ∈ causalApply step s u ↔ ∃ fuel, causalDrive (step u) s fuel [] = some v := by
  have hmono : ∀ {f f' : ℕ} {w : V}, f ≤ f' →
      w ∈ Part.ofOption (causalDrive (step u) s f []) →
        w ∈ Part.ofOption (causalDrive (step u) s f' []) := by
    intro f f' w hle hw
    rw [Part.mem_ofOption] at hw ⊢
    exact causalDrive_mono_le (step u) s hle hw
  rw [causalApply, mem_eventual hmono]
  simp [Part.mem_ofOption]

/-! ### General core (Matt §6): the system is its causal function `Raw X Y = List X →. Y`

Here the resource is a *history-dependent* system function on the inner-query history (a full DDS,
via `S.1`). Memoryless is the special case `S = functionEvaluator s` (reads only the current inner
query) — `driveG_functionEvaluator` below proves it reduces to the memoryless `causalDrive`. -/

/-- General causal driver: thread the converter's inner-queries through a *history-dependent* system
function `S : Raw X Y`, keeping the inner-query history `xs` (fed to `S`) and the inner-answer
history `ys` (fed to the converter `innerStep`). Returns the outer answer `V` together with the
final inner-query history, so a stateful `S` carries over to the next outer query. -/
def driveG (innerStep : List Y → X ⊕ V) (S : PFunDDS.Raw X Y) :
    ℕ → List X → List Y → Part (V × List X)
  | 0,        _,  _  => Part.none
  | fuel + 1, xs, ys =>
      match innerStep ys with
      | Sum.inl x => (S (xs ++ [x])).bind fun y => driveG innerStep S fuel (xs ++ [x]) (ys ++ [y])
      | Sum.inr v => Part.some (v, xs)

/-- `functionEvaluator`'s raw function answers the most-recent inner query — it reads only the last
input, which is exactly what makes a memoryless system a (degenerate) causal system. -/
theorem functionEvaluator_raw_append (s : X → Y) (xs : List X) (x : X) :
    (PFunDDS.functionEvaluator s).1 (xs ++ [x]) = Part.some (s x) := by
  have hdom : ((PFunDDS.functionEvaluator s).1 (xs ++ [x])).Dom := by
    simp [PFunDDS.functionEvaluator]
  rw [← Part.some_get hdom]
  congr 1
  simp [PFunDDS.functionEvaluator]

/-- **Memoryless is a special case of the general apply.** Driving the converter through the
*memoryless* system `functionEvaluator s` (which reads only the current inner query) yields exactly
the memoryless `causalDrive` on the outer-answer (`Prod.fst`) component. -/
theorem driveG_functionEvaluator (innerStep : List Y → X ⊕ V) (s : X → Y) :
    ∀ (fuel : ℕ) (xs : List X) (ys : List Y),
      (driveG innerStep (PFunDDS.functionEvaluator s).1 fuel xs ys).map Prod.fst
        = Part.ofOption (causalDrive innerStep s fuel ys) := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; simp [driveG, causalDrive]
  | succ n ih =>
      intro xs ys
      simp only [driveG, causalDrive]
      cases hstep : innerStep ys with
      | inl x =>
          simp only [functionEvaluator_raw_append, Part.bind_some]
          exact ih (xs ++ [x]) (ys ++ [s x])
      | inr v => simp

/-- `driveG` is monotone in fuel: once it returns an answer, more fuel keeps it. -/
theorem driveG_mono (innerStep : List Y → X ⊕ V) (S : PFunDDS.Raw X Y) :
    ∀ {fuel : ℕ} {xs : List X} {ys : List Y} {r : V × List X},
      r ∈ driveG innerStep S fuel xs ys → r ∈ driveG innerStep S (fuel + 1) xs ys := by
  intro fuel
  induction fuel with
  | zero => intro xs ys r h; simp [driveG] at h
  | succ n ih =>
      intro xs ys r h
      simp only [driveG] at h ⊢
      cases hstep : innerStep ys with
      | inl x =>
          simp only [hstep, Part.mem_bind_iff] at h ⊢
          obtain ⟨y, hy, hr⟩ := h
          exact ⟨y, hy, ih hr⟩
      | inr v => simp only [hstep] at h ⊢; exact h

/-! ### The applied system as a DDS (closure)

CR18 Def 3.9 left applying a converter to a resource informal ("one would have to show that `αs` is
a `(U,V)`-DDS"). We realize it function-natively: `driveOuter` iterates the outer queries, threading
the *inner-query history* (so a stateful system carries over) via `driveG`; the result is a valid
`DDS U V` whose partial function is the threading of the converter's step-function and the system's
function — no transcript. (Like `PFunConverter.apply`, the DDS is partial, undefined exactly where
the inner loop diverges; *validity needs no productivity hypothesis*.) -/

/-- Drive the converter over an *outer-query history*, threading the inner-query history `xs` across
the outer queries and collecting the outer answers (the converter is memoryless-outer: each outer
query restarts the inner-answer history at `[]`). -/
def driveOuter (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ) :
    List X → List U → Part (List V × List X)
  | xs, []       => Part.some ([], xs)
  | xs, u :: rest =>
      (driveG (step u) S fuel xs []).bind fun r =>
        (driveOuter step S fuel r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

/-- Each completed outer query produces exactly one outer answer. -/
theorem driveOuter_length (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (xs : List X) (us : List U) {r : List V × List X} (h : r ∈ driveOuter step S fuel xs us) :
    r.1.length = us.length := by
  induction us generalizing xs r with
  | nil => simp only [driveOuter, Part.mem_some_iff] at h; subst h; simp
  | cons u rest ih =>
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

/-- The outer iteration splits over a concatenation of outer histories. -/
theorem driveOuter_append (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (xs : List X) (a b : List U) :
    driveOuter step S fuel xs (a ++ b) =
      (driveOuter step S fuel xs a).bind fun ra =>
        (driveOuter step S fuel ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing xs with
  | nil =>
      simp only [List.nil_append, driveOuter, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons u rest ih =>
      simp only [List.cons_append, driveOuter, ih, Part.bind_assoc, Part.bind_map,
        Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-- `driveOuter` is monotone in fuel (from `driveG_mono`). -/
theorem driveOuter_mono (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) {fuel : ℕ} :
    ∀ {us : List U} {xs : List X} {r : List V × List X},
      r ∈ driveOuter step S fuel xs us → r ∈ driveOuter step S (fuel + 1) xs us := by
  intro us
  induction us with
  | nil => intro xs r h; simpa [driveOuter] using h
  | cons u rest ih =>
      intro xs r h
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h ⊢
      obtain ⟨r1, hr1, rr, hrr, hr⟩ := h
      exact ⟨r1, driveG_mono (step u) S hr1, rr, ih hrr, hr⟩

/-- The per-fuel applied raw function: replay from the empty inner-query history, return the last
outer answer (`driveOuterAt`). The fuel-free `applyRaw`/`applyG` below take the eventual value. -/
def applyRawAt (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ) : PFunDDS.Raw U V :=
  fun us => (driveOuter step S fuel [] us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

/-- **CR18 Def 3.9, per fuel.** The fuel-`fuel` applied converter — a valid `DDS U V` (closure, no
productivity needed). The fuel-free `applyG` below is its eventual value. -/
def applyGAt (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ) : PFunDDS.DDS U V :=
  ⟨applyRawAt step S fuel, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]; rintro ⟨v, hv⟩; simp [applyRawAt, driveOuter] at hv
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [applyRawAt, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, _hvr⟩ := hv
      rw [driveOuter_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, _hr2⟩ := hr
      have hlen : ra.1.length = l₁.length := driveOuter_length step S fuel [] l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        apply hne
        apply List.eq_nil_of_length_eq_zero
        rw [← hlen, hnil, List.length_nil]
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [applyRawAt, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]
      exact Part.mem_some _⟩

@[simp] theorem applyGAt_toPFun (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ) :
    (applyGAt step S fuel).1 = applyRawAt step S fuel := rfl

/-- One outer query: `driveOuter` over `[u]` runs `driveG` once and wraps the single answer. -/
theorem driveOuter_singleton (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (xs : List X) (u : U) :
    driveOuter step S fuel xs [u]
      = (driveG (step u) S fuel xs []).bind fun r => Part.some ([r.1], r.2) := by
  simp only [driveOuter, Part.map_some]

/-- Per-fuel single-query relating: the applied response is the `driveG` threading. -/
theorem applyRawAt_singleton (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ) (u : U) :
    applyRawAt step S fuel [u] = (driveG (step u) S fuel [] []).map Prod.fst := by
  unfold applyRawAt
  rw [driveOuter_singleton, Part.bind_assoc]
  simp only [Part.bind_some, List.getLast?_singleton]
  exact Part.bind_some_eq_map Prod.fst _

theorem applyRawAt_functionEvaluator_singleton (step : U → List Y → X ⊕ V) (s : X → Y) (fuel : ℕ)
    (u : U) :
    applyRawAt step (PFunDDS.functionEvaluator s).1 fuel [u]
      = Part.ofOption (causalDrive (step u) s fuel []) := by
  rw [applyRawAt_singleton, driveG_functionEvaluator]

/-- `applyRawAt` is monotone in fuel (from `driveOuter_mono`). -/
theorem applyRawAt_mono (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) {fuel : ℕ} {us : List U}
    {v : V} (h : v ∈ applyRawAt step S fuel us) : v ∈ applyRawAt step S (fuel + 1) us := by
  simp only [applyRawAt, Part.mem_bind_iff] at h ⊢
  obtain ⟨r, hr, hv⟩ := h
  exact ⟨r, driveOuter_mono step S hr, hv⟩

theorem applyRawAt_mono_le (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) {fuel fuel' : ℕ}
    {us : List U} {v : V} (hle : fuel ≤ fuel') (h : v ∈ applyRawAt step S fuel us) :
    v ∈ applyRawAt step S fuel' us := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have he : fuel + (n + 1) = (fuel + n) + 1 := by ring
      rw [he]; exact applyRawAt_mono step S ih

/-! ### Fuel-free applied DDS

`applyG step S` is the eventual value (over fuel) of `applyGAt step S fuel` — **no `fuel` in the
signature**. Closure transports through `eventual` (`applyRawAt`'s monotonicity + each `applyGAt`'s
validity). -/

/-- The fuel-free applied raw function: the eventual value of the per-fuel applied raw. -/
noncomputable def applyRaw (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) : PFunDDS.Raw U V :=
  fun us => eventual fun fuel => applyRawAt step S fuel us

theorem mem_applyRaw (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (us : List U) (v : V) :
    v ∈ applyRaw step S us ↔ ∃ fuel, v ∈ applyRawAt step S fuel us :=
  mem_eventual (hmono := fun hle hw => applyRawAt_mono_le step S hle hw)

/-- **CR18 Def 3.9, function-native and fuel-free.** Applying the converter `step` to a system
function `S` is a valid `DDS U V` — Maurer's "missing object", the eventual value of the finite
unrolling; no `fuel`, partial exactly where the converter is non-productive. -/
noncomputable def applyG (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) : PFunDDS.DDS U V :=
  ⟨applyRaw step S, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      obtain ⟨fuel, hfuel⟩ := (mem_applyRaw step S [] v).mp hv
      refine PFunDDS.empty_not_mem (applyGAt step S fuel) ?_
      rw [PFunDDS.dom, PFun.mem_dom]
      exact ⟨v, hfuel⟩
    · intro l₁ l₂ hpre hne hdom
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      obtain ⟨fuel, hfuel⟩ := (mem_applyRaw step S l₂ v).mp hv
      have hl₂ : l₂ ∈ PFunDDS.dom (applyGAt step S fuel) := by
        rw [PFunDDS.dom, PFun.mem_dom]; exact ⟨v, hfuel⟩
      have hl₁ := PFunDDS.prefix_closed (applyGAt step S fuel) hpre hne hl₂
      rw [PFunDDS.dom, PFun.mem_dom] at hl₁
      obtain ⟨v', hv'⟩ := hl₁
      rw [PFun.mem_dom]
      exact ⟨v', (mem_applyRaw step S l₁ v').mpr ⟨fuel, hv'⟩⟩⟩

@[simp] theorem applyG_toPFun (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) :
    (applyG step S).1 = applyRaw step S := rfl

/-- **Memoryless instance (fuel-free).** Applying the converter to the *memoryless* system
`functionEvaluator s` (single outer query) is exactly the fuel-free memoryless `causalApply` — the
general DDS apply restricts to the concrete memoryless apply, with no `fuel` anywhere. -/
theorem applyRaw_functionEvaluator_singleton (step : U → List Y → X ⊕ V) (s : X → Y) (u : U) :
    applyRaw step (PFunDDS.functionEvaluator s).1 [u] = causalApply step s u := by
  rw [applyRaw, causalApply]
  congr 1
  funext fuel
  exact applyRawAt_functionEvaluator_singleton step s fuel u

/-! ## Converter application distributes over parallel composition

CR18 §4.7.1 / Matt Thm 4.6/6.6: the q-fold converter applied to the parallel of `q` systems is the
parallel of the per-copy applies (hence `C^q S^q = (C S)^q`). The engine is the routing (R)
(`PFunDDS.parallel_raw_pure_tag`): the parallel routes tag-`i` queries to component `i`, so the
q-fold converter's copy-`i` inner loop factors to `step` over `S i`. -/

open PFunDDS in
variable {q : ℕ} in
/-- The q-fold converter's per-copy step: outer query `⟨i,u⟩` runs `step u`, routing every inner
query to component `i`. -/
def tagStep (step : U → List Y → X ⊕ V) (iu : Σ _ : Fin q, U) :
    List (Σ _ : Fin q, Y) → (Σ _ : Fin q, X) ⊕ (Σ _ : Fin q, V) :=
  fun ys => match step iu.2 (PFunDDS.restrict iu.1 ys) with
    | Sum.inl x => Sum.inl ⟨iu.1, x⟩
    | Sum.inr v => Sum.inr ⟨iu.1, v⟩

open PFunDDS in
/-- **Routing (step 1).** Driving the q-fold converter's copy-`i` step over the parallel system on a
pure-tag-`i` history factors to driving `step u` over component `S i`, retagged into component `i`. -/
theorem driveG_tagStep_pure {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) (i : Fin q) (u : U)
    (step : U → List Y → X ⊕ V) (fuel : ℕ) (xs₀ : List X) (ys₀ : List Y) :
    driveG (tagStep step ⟨i, u⟩) (PFunDDS.parallel S).1 fuel
        (xs₀.map (Sigma.mk i)) (ys₀.map (Sigma.mk i))
      = (driveG (step u) (S i).1 fuel xs₀ ys₀).map
          (fun r => (⟨i, r.1⟩, r.2.map (Sigma.mk i))) := by
  induction fuel generalizing xs₀ ys₀ with
  | zero => simp [driveG]
  | succ n ih =>
      cases hstep : step u ys₀ with
      | inr v => simp [driveG, tagStep, PFunDDS.restrict_map_self, hstep]
      | inl x =>
          simp only [driveG, tagStep, PFunDDS.restrict_map_self, hstep]
          have h1 : xs₀.map (Sigma.mk i) ++ [(⟨i, x⟩ : Σ _ : Fin q, X)]
              = (xs₀ ++ [x]).map (Sigma.mk i) := by simp
          rw [h1, PFunDDS.parallel_raw_pure_tag, Part.map_bind, Part.bind_map]
          congr 1
          funext y₀
          have h2 : ys₀.map (Sigma.mk i) ++ [(⟨i, y₀⟩ : Σ _ : Fin q, Y)]
              = (ys₀ ++ [y₀]).map (Sigma.mk i) := by simp
          rw [h2, ih]

/-- **Apply-level routing for one outer query (step 2).** Applying the q-fold converter to the
parallel system, on a single tagged outer query `⟨i,u⟩`, is component `i`'s apply on `u`, retagged.
Per fuel; follows from `driveG_tagStep_pure` (step 1) at the empty inner history. -/
theorem applyRawAt_tagStep_singleton {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) (i : Fin q) (u : U)
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    applyRawAt (tagStep step) (PFunDDS.parallel S).1 fuel [⟨i, u⟩]
      = (applyRawAt step (S i).1 fuel [u]).map (Sigma.mk i) := by
  rw [applyRawAt_singleton (tagStep step) (PFunDDS.parallel S).1 fuel ⟨i, u⟩,
      applyRawAt_singleton step (S i).1 fuel u,
      show ([] : List (Σ _ : Fin q, X)) = ([] : List X).map (Sigma.mk i) from rfl,
      show ([] : List (Σ _ : Fin q, Y)) = ([] : List Y).map (Sigma.mk i) from rfl,
      driveG_tagStep_pure]
  simp [Part.map_map, Function.comp_def]

/-- **Clone corollary (step 3), single outer query.** For `q` clones of one system `S` (the clone
power `S^[q] = parallel (fun _ => S)`), applying the q-fold converter on one tagged outer query
`⟨i,u⟩` is `S`'s own apply on `u`, retagged into copy `i` — the per-copy content of `C^q S^q = (CS)^q`
(CR18 §4.7.1; deterministic anchor à la Matt). -/
theorem applyRawAt_tagStep_clone_singleton {q : ℕ} (S : PFunDDS.DDS X Y) (i : Fin q) (u : U)
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    applyRawAt (tagStep step) (PFunDDS.parallel (fun _ : Fin q => S)).1 fuel [⟨i, u⟩]
      = (applyRawAt step S.1 fuel [u]).map (Sigma.mk i) :=
  applyRawAt_tagStep_singleton (fun _ => S) i u step fuel

/-! ### Multi-query routing (full `applyG` over `parallel`)

The single-query results above suffice for one outer query, where the inner-query history is pure-tag.
For the full system equality we need the *mixed*-history routing: across outer queries the threaded
inner-query history accumulates every copy's tagged queries. The forward/backward routing lemmas
below track only the per-component `restrict` of the threaded history (no reconstruction of the full
mixed history), driven by `parallel_raw_concat_tag` (R for valid mixed histories). -/

/-- The inner-query history `driveG` threads only ever grows (append-only). -/
theorem driveG_snd_prefix (innerStep : List Y → X ⊕ V) (S : PFunDDS.Raw X Y) :
    ∀ {fuel : ℕ} {xs : List X} {ys : List Y} {r : V × List X},
      r ∈ driveG innerStep S fuel xs ys → xs <+: r.2 := by
  intro fuel
  induction fuel with
  | zero => intro xs ys r h; simp [driveG] at h
  | succ n ih =>
      intro xs ys r h
      simp only [driveG] at h
      cases hstep : innerStep ys with
      | inl x =>
          simp only [hstep, Part.mem_bind_iff] at h
          obtain ⟨y, _hy, hr⟩ := h
          exact (List.prefix_append xs [x]).trans (ih hr)
      | inr v =>
          simp only [hstep, Part.mem_some_iff] at h
          subst h; exact List.prefix_rfl

/-- A valid history `xs` (each component restriction empty or accepted) stays valid in `S` after the
parallel answers a tag-`i` query, since only component `i`'s restriction is extended. -/
private theorem hinv_concat {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) {i : Fin q} {xs : List (Σ _ : Fin q, X)}
    {x : X} (hinv : ∀ j, PFunDDS.restrict j xs = [] ∨ PFunDDS.restrict j xs ∈ PFunDDS.dom (S j))
    (hx : PFunDDS.restrict i xs ++ [x] ∈ PFunDDS.dom (S i)) :
    ∀ j, PFunDDS.restrict j (xs ++ [(⟨i, x⟩ : Σ _ : Fin q, X)]) = []
        ∨ PFunDDS.restrict j (xs ++ [(⟨i, x⟩ : Σ _ : Fin q, X)]) ∈ PFunDDS.dom (S j) := by
  intro j
  by_cases hji : j = i
  · subst hji; rw [PFunDDS.restrict_concat_self]; exact Or.inr hx
  · rw [PFunDDS.restrict_concat_ne (Ne.symm hji)]; exact hinv j

/-- **Forward routing.** A parallel `driveG` run on a valid history with pure-tag-`i` answers induces
the component-`i` run on the restriction; the threaded history's `i`-restriction becomes the
component run's, and other restrictions are untouched. -/
theorem driveG_tagStep_forward {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) (i : Fin q) (u : U)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {xs : List (Σ _ : Fin q, X)} {ys₀ : List Y} {v : Σ _ : Fin q, V}
      {xs' : List (Σ _ : Fin q, X)},
      (v, xs') ∈ driveG (tagStep step ⟨i, u⟩) (PFunDDS.parallel S).1 fuel xs (ys₀.map (Sigma.mk i)) →
      (∀ j, PFunDDS.restrict j xs = [] ∨ PFunDDS.restrict j xs ∈ PFunDDS.dom (S j)) →
      ∃ w : V, v = ⟨i, w⟩ ∧
        (w, PFunDDS.restrict i xs') ∈ driveG (step u) (S i).1 fuel (PFunDDS.restrict i xs) ys₀ ∧
        ∀ j, j ≠ i → PFunDDS.restrict j xs' = PFunDDS.restrict j xs := by
  intro fuel
  induction fuel with
  | zero => intro xs ys₀ v xs' h _; simp [driveG] at h
  | succ n ih =>
      intro xs ys₀ v xs' h hinv
      simp only [driveG, tagStep, PFunDDS.restrict_map_self] at h
      cases hstep : step u ys₀ with
      | inr w =>
          simp only [hstep, Part.mem_some_iff, Prod.mk.injEq] at h
          obtain ⟨hv, hxs'⟩ := h
          refine ⟨w, hv, ?_, ?_⟩
          · subst hxs'; simp only [driveG, hstep, Part.mem_some_iff]
          · intro j _; rw [hxs']
      | inl x =>
          simp only [hstep, Part.mem_bind_iff] at h
          obtain ⟨y, hy, hrec⟩ := h
          rw [PFunDDS.parallel_raw_concat_tag S xs x hinv, Part.mem_map_iff] at hy
          obtain ⟨w', hw', hyeq⟩ := hy
          have hx : PFunDDS.restrict i xs ++ [x] ∈ PFunDDS.dom (S i) := by
            rw [PFunDDS.dom, PFun.mem_dom]; exact ⟨w', hw'⟩
          have hys : ys₀.map (Sigma.mk i) ++ [y] = (ys₀ ++ [w']).map (Sigma.mk i) := by
            rw [← hyeq]; simp
          rw [hys] at hrec
          obtain ⟨w, hvw, hrun, hother⟩ := ih hrec (hinv_concat S hinv hx)
          rw [PFunDDS.restrict_concat_self] at hrun
          refine ⟨w, hvw, ?_, ?_⟩
          · simp only [driveG, hstep, Part.mem_bind_iff]
            exact ⟨w', hw', hrun⟩
          · intro j hj
            rw [hother j hj, PFunDDS.restrict_concat_ne (Ne.symm hj)]

/-- **Backward routing.** Conversely, a component-`i` `driveG` run on a valid history reconstructs a
parallel run that answers `⟨i,w⟩` and whose threaded history has `i`-restriction the component run's
and other restrictions untouched. (The harder direction, for the domain equality.) -/
theorem driveG_tagStep_backward {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) (i : Fin q) (u : U)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {xs : List (Σ _ : Fin q, X)} {ys₀ : List Y} {w : V} {zs : List X},
      (w, zs) ∈ driveG (step u) (S i).1 fuel (PFunDDS.restrict i xs) ys₀ →
      (∀ j, PFunDDS.restrict j xs = [] ∨ PFunDDS.restrict j xs ∈ PFunDDS.dom (S j)) →
      ∃ xs' : List (Σ _ : Fin q, X),
        ((⟨i, w⟩ : Σ _ : Fin q, V), xs')
            ∈ driveG (tagStep step ⟨i, u⟩) (PFunDDS.parallel S).1 fuel xs (ys₀.map (Sigma.mk i)) ∧
        PFunDDS.restrict i xs' = zs ∧ ∀ j, j ≠ i → PFunDDS.restrict j xs' = PFunDDS.restrict j xs := by
  intro fuel
  induction fuel with
  | zero => intro xs ys₀ w zs h _; simp [driveG] at h
  | succ n ih =>
      intro xs ys₀ w zs h hinv
      simp only [driveG] at h
      cases hstep : step u ys₀ with
      | inr v =>
          simp only [hstep, Part.mem_some_iff, Prod.mk.injEq] at h
          obtain ⟨hw, hzs⟩ := h
          refine ⟨xs, ?_, hzs.symm, fun j _ => rfl⟩
          simp only [driveG, tagStep, PFunDDS.restrict_map_self, hstep, Part.mem_some_iff, hw]
      | inl x =>
          simp only [hstep, Part.mem_bind_iff] at h
          obtain ⟨w', hw', hrec⟩ := h
          have hx : PFunDDS.restrict i xs ++ [x] ∈ PFunDDS.dom (S i) := by
            rw [PFunDDS.dom, PFun.mem_dom]; exact ⟨w', hw'⟩
          rw [show PFunDDS.restrict i xs ++ [x]
                = PFunDDS.restrict i (xs ++ [(⟨i, x⟩ : Σ _ : Fin q, X)])
              from (PFunDDS.restrict_concat_self i x xs).symm] at hrec
          obtain ⟨xs', hpar, hri, hother⟩ := ih hrec (hinv_concat S hinv hx)
          refine ⟨xs', ?_, hri, ?_⟩
          · simp only [driveG, tagStep, PFunDDS.restrict_map_self, hstep, Part.mem_bind_iff]
            refine ⟨⟨i, w'⟩, ?_, ?_⟩
            · rw [PFunDDS.parallel_raw_concat_tag S xs x hinv, Part.mem_map_iff]
              exact ⟨w', hw', rfl⟩
            · rw [show ys₀.map (Sigma.mk i) ++ [(⟨i, w'⟩ : Σ _ : Fin q, Y)]
                    = (ys₀ ++ [w']).map (Sigma.mk i) from by simp]
              exact hpar
          · intro j hj
            rw [hother j hj, PFunDDS.restrict_concat_ne (Ne.symm hj)]

/-- A completed `driveG` run's final inner-query history is either the initial one (no inner query
made) or lands in the system's domain (its last inner query was answered). -/
theorem driveG_snd_dom (innerStep : List Y → X ⊕ V) (S : PFunDDS.Raw X Y) :
    ∀ {fuel : ℕ} {xs : List X} {ys : List Y} {r : V × List X},
      r ∈ driveG innerStep S fuel xs ys → r.2 = xs ∨ r.2 ∈ S.Dom := by
  intro fuel
  induction fuel with
  | zero => intro xs ys r h; simp [driveG] at h
  | succ n ih =>
      intro xs ys r h
      simp only [driveG] at h
      cases hstep : innerStep ys with
      | inl x =>
          simp only [hstep, Part.mem_bind_iff] at h
          obtain ⟨y, hy, hrec⟩ := h
          rcases ih hrec with heq | hdom
          · right; rw [heq, PFun.mem_dom]; exact ⟨y, hy⟩
          · right; exact hdom
      | inr v =>
          simp only [hstep, Part.mem_some_iff] at h
          subst h; left; rfl

/-- **Forward driveOuter routing.** A parallel multi-query run on a valid history induces, for each
component `j`, a component run over the `j`-restricted outer history, whose final inner history is
the `j`-restriction of the parallel run's; and the parallel run's final history stays valid. -/
theorem driveOuter_tagStep_forward {q : ℕ} (S : Fin q → PFunDDS.DDS X Y)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {xs : List (Σ _ : Fin q, X)} {us : List (Σ _ : Fin q, U)}
      {vs : List (Σ _ : Fin q, V)} {xs' : List (Σ _ : Fin q, X)},
      (vs, xs') ∈ driveOuter (tagStep step) (PFunDDS.parallel S).1 fuel xs us →
      (∀ j, PFunDDS.restrict j xs = [] ∨ PFunDDS.restrict j xs ∈ PFunDDS.dom (S j)) →
      (∀ j, ∃ vsj, (vsj, PFunDDS.restrict j xs')
          ∈ driveOuter step (S j).1 fuel (PFunDDS.restrict j xs) (PFunDDS.restrict j us))
        ∧ (∀ j, PFunDDS.restrict j xs' = [] ∨ PFunDDS.restrict j xs' ∈ PFunDDS.dom (S j)) := by
  intro fuel xs us
  induction us generalizing xs with
  | nil =>
      intro vs xs' h hinv
      simp only [driveOuter, Part.mem_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, hxs'⟩ := h
      subst hxs'
      refine ⟨fun j => ⟨[], ?_⟩, hinv⟩
      simp [driveOuter, PFunDDS.restrict_nil]
  | cons u₀ rest ih =>
      intro vs xs' h hinv
      obtain ⟨i₀, u₀'⟩ := u₀
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r, hr, rr, hrr, hvxs⟩ := h
      rw [Prod.mk.injEq] at hvxs
      obtain ⟨_, hxs'eq⟩ := hvxs
      -- route the first (tag i₀) query
      obtain ⟨r1, r2⟩ := r
      rw [show ([] : List (Σ _ : Fin q, Y)) = ([] : List Y).map (Sigma.mk i₀) from rfl] at hr
      obtain ⟨w, hr1, hcomp, hother⟩ := driveG_tagStep_forward S i₀ u₀' step hr hinv
      -- validity of the threaded history r2
      have hr2valid : ∀ j, PFunDDS.restrict j r2 = [] ∨ PFunDDS.restrict j r2 ∈ PFunDDS.dom (S j) := by
        intro j
        by_cases hj : j = i₀
        · rw [hj]
          rcases driveG_snd_dom (step u₀') (S i₀).1 hcomp with heq | hdom
          · have heq' : PFunDDS.restrict i₀ r2 = PFunDDS.restrict i₀ xs := heq
            rw [heq']; exact hinv i₀
          · exact Or.inr hdom
        · rw [hother j hj]; exact hinv j
      obtain ⟨hruns, hxs'valid⟩ := ih hrr hr2valid
      subst hxs'eq
      refine ⟨fun j => ?_, hxs'valid⟩
      obtain ⟨vsj, hvsj⟩ := hruns j
      by_cases hj : j = i₀
      · refine ⟨w :: vsj, ?_⟩
        rw [hj] at hvsj ⊢
        rw [PFunDDS.restrict_cons_self]
        simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(w, PFunDDS.restrict i₀ r2), hcomp, (vsj, PFunDDS.restrict i₀ rr.2), hvsj, by simp⟩
      · refine ⟨vsj, ?_⟩
        rw [PFunDDS.restrict_cons_ne (Ne.symm hj)]
        rw [hother j hj] at hvsj
        exact hvsj

/-- **Backward driveOuter routing.** Conversely, if on a valid history every component converges over
its restricted outer history, the parallel multi-query run converges. (Domain reconstruction.) -/
theorem driveOuter_tagStep_backward {q : ℕ} (S : Fin q → PFunDDS.DDS X Y)
    (step : U → List Y → X ⊕ V) :
    ∀ {fuel : ℕ} {xs : List (Σ _ : Fin q, X)} {us : List (Σ _ : Fin q, U)},
      (∀ j, PFunDDS.restrict j xs = [] ∨ PFunDDS.restrict j xs ∈ PFunDDS.dom (S j)) →
      (∀ j, ∃ rj, rj ∈ driveOuter step (S j).1 fuel (PFunDDS.restrict j xs) (PFunDDS.restrict j us)) →
      ∃ r, r ∈ driveOuter (tagStep step) (PFunDDS.parallel S).1 fuel xs us := by
  intro fuel xs us
  induction us generalizing xs with
  | nil => intro _ _; exact ⟨([], xs), by simp [driveOuter]⟩
  | cons u₀ rest ih =>
      intro hinv hcv
      obtain ⟨i₀, u₀'⟩ := u₀
      obtain ⟨rji₀, hrji₀⟩ := hcv i₀
      rw [PFunDDS.restrict_cons_self] at hrji₀
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hrji₀
      obtain ⟨r', hr', rr', hrr', _⟩ := hrji₀
      obtain ⟨w, zsi₀⟩ := r'
      obtain ⟨xs2, hpar1, hri2, hother2⟩ := driveG_tagStep_backward S i₀ u₀' step hr' hinv
      have hxs2valid : ∀ j, PFunDDS.restrict j xs2 = [] ∨ PFunDDS.restrict j xs2 ∈ PFunDDS.dom (S j) := by
        intro j
        by_cases hj : j = i₀
        · rw [hj, hri2]
          rcases driveG_snd_dom (step u₀') (S i₀).1 hr' with heq | hdom
          · have heq' : zsi₀ = PFunDDS.restrict i₀ xs := heq
            rw [heq']; exact hinv i₀
          · exact Or.inr hdom
        · rw [hother2 j hj]; exact hinv j
      have hcv2 : ∀ j, ∃ rj, rj ∈ driveOuter step (S j).1 fuel (PFunDDS.restrict j xs2) (PFunDDS.restrict j rest) := by
        intro j
        by_cases hj : j = i₀
        · rw [hj, hri2]; exact ⟨rr', hrr'⟩
        · obtain ⟨rj, hrj⟩ := hcv j
          rw [PFunDDS.restrict_cons_ne (Ne.symm hj)] at hrj
          rw [hother2 j hj]; exact ⟨rj, hrj⟩
      obtain ⟨r2run, hr2run⟩ := ih hxs2valid hcv2
      refine ⟨(⟨i₀, w⟩ :: r2run.1, r2run.2), ?_⟩
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
      refine ⟨(⟨i₀, w⟩, xs2), ?_, r2run, hr2run, by simp⟩
      rw [show ([] : List (Σ _ : Fin q, Y)) = ([] : List Y).map (Sigma.mk i₀) from rfl]
      exact hpar1

/-- Peel the last outer query: the applied response on `us0 ++ [u']` runs the prefix, then `driveG`
on the last query from the threaded history. -/
theorem applyRawAt_append_singleton (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (us0 : List U) (u' : U) :
    applyRawAt step S fuel (us0 ++ [u'])
      = (driveOuter step S fuel [] us0).bind
          (fun ra => (driveG (step u') S fuel ra.2 []).map Prod.fst) := by
  unfold applyRawAt
  rw [driveOuter_append, Part.bind_assoc]
  congr 1
  funext ra
  rw [Part.bind_map, driveOuter_singleton, Part.bind_assoc]
  simp only [Part.bind_some, List.getLast?_concat]
  exact Part.bind_some_eq_map Prod.fst _

/-- If the applied DDS is defined on `us`, the underlying `driveOuter` run converges. -/
theorem driveOuter_dom_of_apply (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (us : List U) (h : us ∈ PFunDDS.dom (applyGAt step S fuel)) :
    ∃ r, r ∈ driveOuter step S fuel [] us := by
  rw [PFunDDS.dom, PFun.mem_dom] at h
  obtain ⟨v, hv⟩ := h
  rw [applyGAt_toPFun] at hv
  simp only [applyRawAt, Part.mem_bind_iff] at hv
  obtain ⟨r, hr, _⟩ := hv
  exact ⟨r, hr⟩

/-- **Conditional routing equation.** On a history `us0 ++ [⟨j,u'⟩]` whose prefix `us0` is valid for
the applied components, the parallel apply routes the whole response to component `j`'s apply on the
`j`-restriction, retagged. (Both directions: forward via `driveOuter/driveG_tagStep_forward`, backward
reconstructing the parallel run via the `_backward` lemmas; single-valuedness of `driveOuter` aligns
the per-component prefix run with the parallel one.) -/
theorem applyRawAt_tagStep_route {q : ℕ} (S : Fin q → PFunDDS.DDS X Y)
    (step : U → List Y → X ⊕ V) (fuel : ℕ) (us0 : List (Σ _ : Fin q, U)) (j : Fin q) (u' : U)
    (hinvT : ∀ i, PFunDDS.restrict i us0 = [] ∨
        PFunDDS.restrict i us0 ∈ PFunDDS.dom (applyGAt step (S i).1 fuel)) :
    applyRawAt (tagStep step) (PFunDDS.parallel S).1 fuel (us0 ++ [⟨j, u'⟩])
      = (applyRawAt step (S j).1 fuel (PFunDDS.restrict j us0 ++ [u'])).map (Sigma.mk j) := by
  have hnil : ∀ i, PFunDDS.restrict i ([] : List (Σ _ : Fin q, X)) = []
      ∨ PFunDDS.restrict i ([] : List (Σ _ : Fin q, X)) ∈ PFunDDS.dom (S i) :=
    fun i => Or.inl (PFunDDS.restrict_nil i)
  have hcv0 : ∀ i, ∃ rj, rj ∈ driveOuter step (S i).1 fuel
      (PFunDDS.restrict i ([] : List (Σ _ : Fin q, X))) (PFunDDS.restrict i us0) := by
    intro i
    rw [PFunDDS.restrict_nil]
    rcases hinvT i with he | hd
    · rw [he]; exact ⟨([], []), by simp [driveOuter]⟩
    · exact driveOuter_dom_of_apply step (S i).1 fuel (PFunDDS.restrict i us0) hd
  rw [applyRawAt_append_singleton (tagStep step) (PFunDDS.parallel S).1 fuel us0 ⟨j, u'⟩,
      applyRawAt_append_singleton step (S j).1 fuel (PFunDDS.restrict j us0) u']
  ext v
  simp only [Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨ra, hra, ⟨vp, xs'⟩, hdg, hveq⟩
    obtain ⟨hruns, hra2valid⟩ :=
      driveOuter_tagStep_forward S step hra hnil
    rw [show ([] : List (Σ _ : Fin q, Y)) = ([] : List Y).map (Sigma.mk j) from rfl] at hdg
    obtain ⟨w, hvpeq, hcompdg, _⟩ := driveG_tagStep_forward S j u' step hdg hra2valid
    obtain ⟨vsj, hvsj⟩ := hruns j
    rw [PFunDDS.restrict_nil] at hvsj
    refine ⟨w, ⟨(vsj, PFunDDS.restrict j ra.2), hvsj, (w, PFunDDS.restrict j xs'), hcompdg, rfl⟩, ?_⟩
    rw [← hveq, hvpeq]
  · rintro ⟨w, ⟨raj, hraj, ⟨w2, zs⟩, hcompdg, hw2eq⟩, hveq⟩
    obtain ⟨ra, hra⟩ := driveOuter_tagStep_backward S step hnil hcv0
    obtain ⟨hruns, hra2valid⟩ := driveOuter_tagStep_forward S step hra hnil
    obtain ⟨vsj, hvsj⟩ := hruns j
    rw [PFunDDS.restrict_nil] at hvsj
    have hraj2 : raj.2 = PFunDDS.restrict j ra.2 := congrArg Prod.snd (Part.mem_unique hraj hvsj)
    rw [hraj2] at hcompdg
    obtain ⟨xs', hpardg, _, _⟩ := driveG_tagStep_backward S j u' step hcompdg hra2valid
    refine ⟨ra, hra, (⟨j, w2⟩, xs'), hpardg, ?_⟩
    rw [← hveq, ← hw2eq]

/-- Converse of `driveOuter_dom_of_apply`: a converging `driveOuter` run on a nonempty history
witnesses the applied DDS's domain. -/
theorem mem_dom_applyGAt_of_driveOuter (step : U → List Y → X ⊕ V) (S : PFunDDS.Raw X Y) (fuel : ℕ)
    (us : List U) (hne : us ≠ []) (r : List V × List X) (h : r ∈ driveOuter step S fuel [] us) :
    us ∈ PFunDDS.dom (applyGAt step S fuel) := by
  have hlen : r.1.length = us.length := driveOuter_length step S fuel [] us h
  have hr1ne : r.1 ≠ [] := by
    intro hnil; apply hne; apply List.eq_nil_of_length_eq_zero
    rw [← hlen, hnil, List.length_nil]
  rw [PFunDDS.dom, PFun.mem_dom]
  refine ⟨r.1.getLast hr1ne, ?_⟩
  rw [applyGAt_toPFun]
  simp only [applyRawAt, Part.mem_bind_iff]
  exact ⟨r, h, by rw [List.getLast?_eq_some_getLast hr1ne]; exact Part.mem_some _⟩

/-- **Apply distributes over parallel composition (per fuel).** Applying the q-fold converter to the
parallel of `q` systems equals the parallel of the per-copy applies (CR18 §4.7.1 / Matt Thm 4.6/6.6).
Raw equality per outer history: on `us0 ++ [⟨j,u'⟩]` with a valid prefix both sides route to component
`j`'s apply (`applyRawAt_tagStep_route` and `parallel_raw_concat_tag`); otherwise both diverge. -/
theorem applyGAt_tagStep_parallel {q : ℕ} (S : Fin q → PFunDDS.DDS X Y)
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    applyGAt (tagStep step) (PFunDDS.parallel S) fuel
      = PFunDDS.parallel (fun i => applyGAt step (S i).1 fuel) := by
  set T : Fin q → PFunDDS.DDS U V := fun i => applyGAt step (S i).1 fuel with hT
  apply Subtype.ext
  funext us
  show applyRawAt (tagStep step) (PFunDDS.parallel S).1 fuel us = (PFunDDS.parallel T).1 us
  rcases List.eq_nil_or_concat us with rfl | ⟨us0, ju', rfl⟩
  · rw [Part.eq_none_iff'.mpr (PFunDDS.empty_not_mem (PFunDDS.parallel T))]
    simp [applyRawAt, driveOuter]
  · obtain ⟨j, u'⟩ := ju'
    rw [List.concat_eq_append]
    by_cases hpv : ∀ i, PFunDDS.restrict i us0 = [] ∨ PFunDDS.restrict i us0 ∈ PFunDDS.dom (T i)
    · rw [applyRawAt_tagStep_route S step fuel us0 j u' hpv,
          PFunDDS.parallel_raw_concat_tag T us0 u' hpv, applyGAt_toPFun]
    · simp only [not_forall, not_or] at hpv
      obtain ⟨i, hi_ne, hi_ndom⟩ := hpv
      have hpre : PFunDDS.restrict i us0 <+: PFunDDS.restrict i (us0 ++ [(⟨j, u'⟩ : Σ _ : Fin q, U)]) :=
        PFunDDS.restrict_prefix i (List.prefix_append _ _)
      have hRnone : (PFunDDS.parallel T).1 (us0 ++ [⟨j, u'⟩]) = Part.none := by
        rw [Part.eq_none_iff']
        intro hdom
        have hdom' : (us0 ++ [(⟨j, u'⟩ : Σ _ : Fin q, U)]) ∈ PFunDDS.dom (PFunDDS.parallel T) := hdom
        rw [PFunDDS.mem_parallel_dom] at hdom'
        rcases hdom'.2 i with hnil | hdomi
        · exact hi_ne (List.prefix_nil.mp (hnil ▸ hpre))
        · exact hi_ndom (PFunDDS.prefix_closed (T i) hpre hi_ne hdomi)
      have hLnone : applyRawAt (tagStep step) (PFunDDS.parallel S).1 fuel (us0 ++ [⟨j, u'⟩])
          = Part.none := by
        rw [Part.eq_none_iff']
        intro hdom
        rw [Part.dom_iff_mem] at hdom
        obtain ⟨v, hv⟩ := hdom
        simp only [applyRawAt, Part.mem_bind_iff] at hv
        obtain ⟨r, hr, _⟩ := hv
        obtain ⟨hruns, _⟩ := driveOuter_tagStep_forward S step hr (fun k => Or.inl (PFunDDS.restrict_nil k))
        obtain ⟨vsi, hvsi⟩ := hruns i
        rw [PFunDDS.restrict_nil] at hvsi
        have hne : PFunDDS.restrict i (us0 ++ [(⟨j, u'⟩ : Σ _ : Fin q, U)]) ≠ [] :=
          fun h => hi_ne (List.prefix_nil.mp (h ▸ hpre))
        have hidom := mem_dom_applyGAt_of_driveOuter step (S i).1 fuel _ hne _ hvsi
        exact hi_ndom (PFunDDS.prefix_closed (T i) hpre hi_ne hidom)
      rw [hLnone, hRnone]

/-- **Clone corollary (step 3): `C^q S^q = (C S)^q` (deterministic, per fuel).** Applying the q-fold
converter to the `q`-fold clone power `S^[q] = parallel (fun _ => S)` of one system equals the
parallel of `q` copies of `C` applied to `S` — Maurer's `C^q S^q = (C S)^q` (CR18 §4.7.1), the
deterministic anchor à la Matt. Immediate from `applyGAt_tagStep_parallel` at the constant family. -/
theorem applyGAt_tagStep_clone {q : ℕ} (S : PFunDDS.DDS X Y) (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    applyGAt (tagStep step) (PFunDDS.parallel (fun _ : Fin q => S)) fuel
      = PFunDDS.parallel (fun _ : Fin q => applyGAt step S.1 fuel) :=
  applyGAt_tagStep_parallel (fun _ => S) step fuel

/-- **Apply distributes over parallel composition (fuel-free).** The fuel-free version of
`applyGAt_tagStep_parallel`: `applyG (tagStep step) (parallel S) = parallel (i ↦ applyG step (S i))`.
The per-fuel equality transports through the fuel-`eventual` because `parallel` commutes with it
(`PFunDDS.parallel_eventual`): the parallel converges at the `Finset.sup` of the per-component fuels. -/
theorem applyG_tagStep_parallel {q : ℕ} (S : Fin q → PFunDDS.DDS X Y) (step : U → List Y → X ⊕ V) :
    applyG (tagStep step) (PFunDDS.parallel S) = PFunDDS.parallel (fun i => applyG step (S i).1) := by
  apply Subtype.ext
  funext us
  rw [applyG_toPFun]
  apply Part.ext
  intro v
  rw [mem_applyRaw]
  have hconv : ∀ fuel, applyRawAt (tagStep step) (PFunDDS.parallel S) fuel us
      = (PFunDDS.parallel (fun i => applyGAt step (S i).1 fuel)).1 us := fun fuel =>
    congrArg (fun D : PFunDDS.DDS (Σ _ : Fin q, U) (Σ _ : Fin q, V) => D.1 us)
      (applyGAt_tagStep_parallel S step fuel)
  simp_rw [hconv]
  rw [PFunDDS.parallel_eventual (fun fuel i => applyGAt step (S i).1 fuel)
        (fun i => applyG step (S i).1)
        (fun hle hw => applyRawAt_mono_le step _ hle hw)
        (fun i l w => by simp only [applyG_toPFun, mem_applyRaw, applyGAt_toPFun]) us v]

/-- **Clone corollary, fuel-free: `C^q S^q = (C S)^q`.** The fuel-free `applyGAt_tagStep_clone`. -/
theorem applyG_tagStep_clone {q : ℕ} (S : PFunDDS.DDS X Y) (step : U → List Y → X ⊕ V) :
    applyG (tagStep step) (PFunDDS.parallel (fun _ : Fin q => S))
      = PFunDDS.parallel (fun _ : Fin q => applyG step S.1) :=
  applyG_tagStep_parallel (fun _ => S) step

/-! ### Probabilistic case (step 4): distributions over system families

A *probabilistic* system family is a distribution over deterministic ones (a PDS in disguise, à la
Lanzenberger–Maurer Def 8). The deterministic equality `applyGAt_tagStep_parallel` holds for *every*
sample, so it lifts through the pushforward `Dist.fTransform`: the **distribution** of the q-fold
converter applied to a random parallel system equals the distribution of the parallel of the per-copy
applies. With `D := Dist.iidPow μ q` (Def 4.9) this is the probabilistic `C^q S^q = (C S)^q` for the
i.i.d. power; the generic statement covers any joint law. (LZM line 532 / remark 379-387: the
behavior-level product is *justified* by this deterministic lift.) -/
theorem fTransform_applyGAt_tagStep_parallel {q : ℕ} (D : Dist (Fin q → PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    Dist.fTransform (fun Ss => applyGAt (tagStep step) (PFunDDS.parallel Ss) fuel) D
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyGAt step (Ss i).1 fuel)) D :=
  congrArg (fun f => Dist.fTransform f D) (funext fun Ss => applyGAt_tagStep_parallel Ss step fuel)

/-- **`C^q S^q = (C S)^q`, probabilistic (i.i.d. power).** The distribution of the q-fold converter
applied to the `q`-fold i.i.d. power of a random system `μ` equals the distribution of `q` independent
copies of `C` applied to `μ`. Instance of `fTransform_applyGAt_tagStep_parallel` at `Dist.iidPow`. -/
theorem fTransform_iidPow_applyGAt_tagStep {q : ℕ} (μ : Dist (PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    Dist.fTransform (fun Ss => applyGAt (tagStep step) (PFunDDS.parallel Ss) fuel) (Dist.iidPow μ q)
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyGAt step (Ss i).1 fuel))
          (Dist.iidPow μ q) :=
  fTransform_applyGAt_tagStep_parallel (Dist.iidPow μ q) step fuel

/-! #### Caveat-2 extension 1: fuel-free probabilistic

The fuel-free deterministic equality `applyG_tagStep_parallel` lifts through the pushforward exactly as
the per-fuel one did — so the probabilistic statement is itself fuel-free (no `fuel` budget). -/

/-- **Apply distributes over parallel, probabilistic and fuel-free.** Pushforward of
`applyG_tagStep_parallel`: the distribution of the q-fold converter applied to a random parallel
system equals the distribution of the parallel of the per-copy (fuel-free) applies, for any joint
law `D`. -/
theorem fTransform_applyG_tagStep_parallel {q : ℕ} (D : Dist (Fin q → PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) :
    Dist.fTransform (fun Ss => applyG (tagStep step) (PFunDDS.parallel Ss)) D
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyG step (Ss i).1)) D :=
  congrArg (fun f => Dist.fTransform f D) (funext fun Ss => applyG_tagStep_parallel Ss step)

/-- `C^q S^q = (C S)^q`, probabilistic, i.i.d. power (Def 4.9), fuel-free. -/
theorem fTransform_iidPow_applyG_tagStep {q : ℕ} (μ : Dist (PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) :
    Dist.fTransform (fun Ss => applyG (tagStep step) (PFunDDS.parallel Ss)) (Dist.iidPow μ q)
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyG step (Ss i).1)) (Dist.iidPow μ q) :=
  fTransform_applyG_tagStep_parallel (Dist.iidPow μ q) step

/-! #### Caveat-2 extension 2: the clone power (Def 4.10)

Beside the i.i.d. power `S^q` (Def 4.9, independent copies) sits the **clone** power `S^[q]` (Def 4.10,
`q` fully-correlated copies). The same pushforward lift gives `C^q S^[q] = (C S)^[q]` — the generic
`fTransform_applyG…` at `Dist.clonePow` rather than `Dist.iidPow`. -/

/-- `C^q S^[q] = (C S)^[q]`, probabilistic, clone power (Def 4.10), per fuel. -/
theorem fTransform_clonePow_applyGAt_tagStep {q : ℕ} (μ : Dist (PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) (fuel : ℕ) :
    Dist.fTransform (fun Ss => applyGAt (tagStep step) (PFunDDS.parallel Ss) fuel) (Dist.clonePow μ q)
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyGAt step (Ss i).1 fuel))
          (Dist.clonePow μ q) :=
  fTransform_applyGAt_tagStep_parallel (Dist.clonePow μ q) step fuel

/-- `C^q S^[q] = (C S)^[q]`, probabilistic, clone power (Def 4.10), fuel-free. -/
theorem fTransform_clonePow_applyG_tagStep {q : ℕ} (μ : Dist (PFunDDS.DDS X Y))
    (step : U → List Y → X ⊕ V) :
    Dist.fTransform (fun Ss => applyG (tagStep step) (PFunDDS.parallel Ss)) (Dist.clonePow μ q)
      = Dist.fTransform (fun Ss => PFunDDS.parallel (fun i => applyG step (Ss i).1)) (Dist.clonePow μ q) :=
  fTransform_applyG_tagStep_parallel (Dist.clonePow μ q) step

end RandomSystems.CR18.CausalApply
