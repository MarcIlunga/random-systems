/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.RelateGameDistinguishing
import RandomSystems.DistSimp

/-!
# CR18 Theorem 4.17 — conditional equivalence ⟹ indistinguishability (precise PDF form)

CR18 Theorem 4.17: *if for an `(X,Y)`-system `S` one can define an MBO such that `Ŝ |≡ T`, then
`∆(S,T) ≤ Γ(bŜ)`.* The proof enhances `T` with an MBO to a game `T̂` so that `Ŝ ≡ᵍ T̂` and `T̂⁻ = T`
(eq. 4.39), and applies Lemma 4.16. We follow the PDF: the hypothesis is `Ŝ |≡ T` (`CondEquiv`,
Def 4.19), and `T̂` is built internally as the **independent product** of `T`'s `Y`-process and `Ŝ`'s
`A`-process — `p^{T̂}_{YⁱAᵢ|Xⁱ} = p^T_{Yⁱ|Xⁱ} · p^{Ŝ}_{Aᵢ|Xⁱ}` — so that
`massYAfalse T̂ = massY T · massAfalse Ŝ`, which `CondEquiv` (eq. 4.38) turns into `massYAfalse Ŝ`.

Round 1: the `T̂` construction (`combineSys`, `gameEnhance`).
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

namespace PFunDDS

/-- **The combiner** (CR18 eq. 4.39, deterministic layer): from a realization `t ← T` (an `(X,Y)`-DDS)
and `ŝ ← Ŝ` (a game), the game whose `Y`-output is `t`'s and whose MBO bit is `ŝ`'s — defined exactly
where both are. This realizes the independent product `T`'s-`Y` ⊗ `Ŝ`'s-`A`. -/
def combineSys (t : DDS X Y) (s : DDS X (Y × Bool)) : DDS X (Y × Bool) :=
  ⟨fun l => ⟨l ∈ dom t ∧ l ∈ dom s, fun h => (output t l h.1, (output s l h.2).2)⟩, by
    refine ⟨fun h => empty_not_mem t h.1, ?_⟩
    intro l₁ l₂ hpre hne hdom
    exact ⟨prefix_closed t hpre hne hdom.1, prefix_closed s hpre hne hdom.2⟩⟩

@[simp] theorem mem_dom_combineSys (t : DDS X Y) (s : DDS X (Y × Bool)) (l : List X) :
    l ∈ dom (combineSys t s) ↔ l ∈ dom t ∧ l ∈ dom s := Iff.rfl

theorem output_combineSys (t : DDS X Y) (s : DDS X (Y × Bool)) (l : List X)
    (h : l ∈ dom (combineSys t s)) :
    output (combineSys t s) l h = (output t l h.1, (output s l h.2).2) := rfl

end PFunDDS

/-- **CR18 eq. (4.39) — the MBO-enhanced `T̂`**: push the combiner through the independent product
`T ×ᵈ Ŝ`. `T̂` answers `Yⁱ` like `T` and the MBO `Aᵢ` like `Ŝ`, independently — the game made
game-equivalent to `Ŝ` whose `T̂⁻` is `T`. -/
noncomputable def gameEnhance (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool)) :
    PFunPDS X (Y × Bool) :=
  Dist.fTransform (fun p => PFunDDS.combineSys p.1 p.2) (Dist.prod T Shat)

/-! ## Round 2 — eq. (4.39), the not-won mass of `T̂` factors (`p^{T̂}_{YⁱAᵢ=0|Xⁱ} = p^T_{Yⁱ|Xⁱ}·p^{Ŝ}_{Aᵢ=0|Xⁱ}`)

This is the *middle line* of CR18 eq. (4.39): the independent product `T̂`'s not-won transcript mass is
`T`'s output mass times `Ŝ`'s not-won (`Aᵢ=0`) mass. It is a single rectangle split: the not-won event of
`combineSys t ŝ` is `(t produces yⁱ) ∧ (ŝ all-false on the prefixes)` — a condition on `t` alone and a
condition on `ŝ` alone — so `mass_fTransform` + `mass_prod_and` close it. No interaction unfolding. -/

open RandomSystems.CR18.CondEquiv (massYAfalse massY massAfalse massDom)
open scoped RandomSystems.CR18.CondEquiv

/-- `Ŝ`'s **all-false** mass `p^{Ŝ}_{Aᵢ=0|Xⁱ}` cumulated over the prefixes: the weight of games `ŝ ← Ŝ`
whose MBO bit is `false` on **every** prefix of `xⁱ` (the genuine cumulative not-won event `Aᵢ = 0`,
which for a *monotone* MBO coincides with the last-bit `massAfalse`). Indexed by `ys` only to share the
prefix count with `massYAfalse`. -/
noncomputable def massAllFalse (Shat : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : NNReal :=
  Dist.mass Shat (fun s =>
    ∀ k : Fin ys.toList.length,
      ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s,
        (PFunDDS.output s (xs.toList.take (k.1 + 1)) h).2 = false)

/-- **CR18 eq. (4.39), middle line**: the not-won transcript mass of the MBO-enhanced `T̂ = gameEnhance T Ŝ`
factors as `massY T · massAllFalse Ŝ` — `T`'s `Yⁱ`-output mass times `Ŝ`'s cumulative `Aᵢ=0` mass. The
not-won event of `combineSys t ŝ` is a rectangle (`t` produces `yⁱ`; `ŝ` is all-false), closed by
`mass_fTransform` + `mass_prod_and`. -/
theorem massYAfalse_gameEnhance (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (i : ℕ) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse (gameEnhance T Shat) i ys xs
      = massY T i ys xs * massAllFalse Shat i ys xs := by
  rw [gameEnhance]
  unfold massYAfalse
  rw [Dist.mass_fTransform]
  rw [Dist.mass_congr (Dist.prod T Shat)
    (Q := fun p =>
      (∀ k : Fin ys.toList.length,
        ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom p.1,
          PFunDDS.output p.1 (xs.toList.take (k.1 + 1)) h = ys.toList.get k)
      ∧ (∀ k : Fin ys.toList.length,
        ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom p.2,
          (PFunDDS.output p.2 (xs.toList.take (k.1 + 1)) h).2 = false))
    ?_]
  · rw [Dist.mass_prod_and T Shat
      (fun t => ∀ k : Fin ys.toList.length,
        ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom t,
          PFunDDS.output t (xs.toList.take (k.1 + 1)) h = ys.toList.get k)
      (fun s => ∀ k : Fin ys.toList.length,
        ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s,
          (PFunDDS.output s (xs.toList.take (k.1 + 1)) h).2 = false)]
    rfl
  · rintro ⟨t, s⟩
    constructor
    · intro hc
      refine ⟨fun k => ?_, fun k => ?_⟩
      · obtain ⟨h, h1, _⟩ := hc k
        exact ⟨h.1, by rw [PFunDDS.output_combineSys] at h1; exact h1⟩
      · obtain ⟨h, _, h2⟩ := hc k
        exact ⟨h.2, by rw [PFunDDS.output_combineSys] at h2; exact h2⟩
    · rintro ⟨hPt, hPs⟩ k
      obtain ⟨ht, hvt⟩ := hPt k
      obtain ⟨hs, hvs⟩ := hPs k
      exact ⟨⟨ht, hs⟩, by rw [PFunDDS.output_combineSys]; exact hvt,
                         by rw [PFunDDS.output_combineSys]; exact hvs⟩

/-! ## Round 3 — the monotone bridge and the conditional-equivalence closure

`massAllFalse = massAfalse` is the **monotone MBO** fact (Maurer: the MBO is monotone, so `Aᵢ = 0` —
the cumulative not-won event — is read either as "false on every prefix" or just "false at `xⁱ`"). Then
`CondEquiv` (eq. 4.38) plus `T`-totality (`massDom T = 1`) turn the factoring into `massYAfalse Ŝ`. -/

/-- Support-restricted mass congruence (UPSTREAM-CANDIDATE): events that agree on the support have equal
mass, even if they differ off-support (where the weight is `0`). -/
theorem mass_congr_support {A : Type*} (X : Dist A) {P Q : A → Prop}
    (h : ∀ a ∈ X.support, P a ↔ Q a) : X.mass P = X.mass Q := by
  classical
  unfold Dist.mass Finsupp.sum
  refine Finset.sum_congr rfl fun a ha => ?_
  have hPQ : P a ↔ Q a := h a (by simpa using ha)
  show (if P a then X a else 0) = (if Q a then X a else 0)
  by_cases hP : P a
  · rw [if_pos hP, if_pos (hPQ.mp hP)]
  · rw [if_neg hP, if_neg (mt hPQ.mpr hP)]

/-- **The monotonicity consequence of CR18 Def 3.22** (`DDS.IsGame`): for a game `g`, if the MBO bit is
`false` at a history `l₂` then it is `false` at every nonempty prefix `l₁` — "once won, stays won",
read backwards. Derived from `IsMBO (outputHistory g l₂)` (the `Bool` projection is `Monotone`), so we
reuse Def 3.22 rather than positing monotonicity afresh. -/
theorem PFunDDS.outputBit_false_of_isGame {g : PFunDDS.DDS X (Y × Bool)} (hg : g.IsGame)
    {l₁ l₂ : List X} (hpre : l₁ <+: l₂) (hne : l₁ ≠ [])
    (h₁ : l₁ ∈ PFunDDS.dom g) (h₂ : l₂ ∈ PFunDDS.dom g)
    (hb : (PFunDDS.output g l₂ h₂).2 = false) : (PFunDDS.output g l₁ h₁).2 = false := by
  have hmono := hg l₂ h₂
  have hlen1 : 0 < l₁.length := List.length_pos_iff.mpr hne
  have hle : l₁.length ≤ l₂.length := hpre.length_le
  have hl2pos : 0 < l₂.length := lt_of_lt_of_le hlen1 hle
  have hohlen : (PFunDDS.outputHistory g l₂ h₂).length = l₂.length := List.length_ofFn
  -- the two indices: l₁ sits at l₁.length-1, l₂ at l₂.length-1
  set i₁ : Fin (PFunDDS.outputHistory g l₂ h₂).length :=
    ⟨l₁.length - 1, by rw [hohlen]; omega⟩ with hi₁
  set i₂ : Fin (PFunDDS.outputHistory g l₂ h₂).length :=
    ⟨l₂.length - 1, by rw [hohlen]; omega⟩ with hi₂
  have hij : i₁ ≤ i₂ := by simp only [hi₁, hi₂, Fin.mk_le_mk]; omega
  -- read off the two entries
  have htake1 : l₂.take (l₁.length - 1 + 1) = l₁ := by
    rw [Nat.sub_add_cancel hlen1]; exact (List.prefix_iff_eq_take.mp hpre).symm
  have htake2 : l₂.take (l₂.length - 1 + 1) = l₂ := by
    rw [Nat.sub_add_cancel hl2pos, List.take_length]
  have hent1 : ((PFunDDS.outputHistory g l₂ h₂).get i₁).2 = (PFunDDS.output g l₁ h₁).2 := by
    simp only [PFunDDS.outputHistory, List.get_ofFn]
    exact congrArg Prod.snd (PFunDDS.output_congr g htake1 _ h₁)
  have hent2 : ((PFunDDS.outputHistory g l₂ h₂).get i₂).2 = (PFunDDS.output g l₂ h₂).2 := by
    simp only [PFunDDS.outputHistory, List.get_ofFn]
    exact congrArg Prod.snd (PFunDDS.output_congr g htake2 _ h₂)
  have hle2 := hmono hij
  simp only [] at hle2
  rw [hent1, hent2, hb] at hle2
  exact le_antisymm hle2 (Bool.false_le _)

/-- Under a monotone MBO, the cumulative all-prefixes-false mass equals the last-bit `massAfalse`:
`p^{Ŝ}_{Aᵢ=0|Xⁱ}` is the same read either way. Forward is "take the last prefix"; backward is monotone
(`false` at `xⁱ` ⟹ `false` at every prefix) plus prefix-closure of the domain. -/
theorem massAllFalse_eq_massAfalse (Shat : PFunPDS X (Y × Bool)) (hmono : MonotoneMBO Shat)
    (i : ℕ) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massAllFalse Shat i ys xs = massAfalse Shat xs.toList := by
  unfold massAllFalse massAfalse
  refine mass_congr_support Shat fun s hs => ?_
  have hlen : xs.toList.length = i + 1 := by simp [Vector.length_toList]
  have hyslen : ys.toList.length = i + 1 := by simp [Vector.length_toList]
  have hxsne : xs.toList ≠ [] := by intro hc; rw [hc] at hlen; simp at hlen
  have htake : xs.toList.take (i + 1) = xs.toList := List.take_of_length_le (le_of_eq hlen)
  constructor
  · intro hall
    have hk : (i : ℕ) < ys.toList.length := by rw [hyslen]; omega
    obtain ⟨h, hb⟩ := hall ⟨i, hk⟩
    refine ⟨htake ▸ h, ?_⟩
    rw [PFunDDS.output_congr s htake.symm (htake ▸ h) h]
    exact hb
  · rintro ⟨h, hb⟩ k
    have hpre : xs.toList.take (k.1 + 1) <+: xs.toList := List.take_prefix _ _
    have hne : xs.toList.take (k.1 + 1) ≠ [] := by
      rw [Ne, List.take_eq_nil_iff]; push_neg; exact ⟨Nat.succ_ne_zero _, hxsne⟩
    have hd : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s := PFunDDS.prefix_closed s hpre hne h
    exact ⟨hd, PFunDDS.outputBit_false_of_isGame (hmono s hs) hpre hne hd h hb⟩

/-- `massYAfalse Ŝ ≤ massAllFalse Ŝ`: the not-won transcript event (`yⁱ` produced *and* all-false)
refines the all-false event. Used for the degenerate `massAfalse = 0` branch of the closure. -/
theorem massYAfalse_le_massAllFalse (Shat : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse Shat i ys xs ≤ massAllFalse Shat i ys xs := by
  unfold massYAfalse massAllFalse
  exact mass_mono Shat fun s hsp k => ⟨(hsp k).choose, (hsp k).choose_spec.2⟩

/-- Bounded-totality form of `massYAfalse_gameEnhance_eq_abstract`.

UPSTREAM-CANDIDATE: this is the eq. (4.39) mass bridge in the form needed by `[q]`-filtered systems.
Only the concrete transcript length `i+1` is inspected, so `TotalUpTo T (i+1)` is the tight
assumption; global `TotalOnNonempty` is just a compatibility wrapper. -/
theorem massYAfalse_gameEnhance_eq_of_totalUpTo (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (hCE : Shat |≡ T) (hTprob : T.isProbDist) (hmono : MonotoneMBO Shat)
    (i : ℕ) (hTtot : TotalUpTo T (i + 1)) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse (gameEnhance T Shat) i ys xs = massYAfalse Shat i ys xs := by
  have hlen : xs.toList.length = i + 1 := by simp [Vector.length_toList]
  have hxsne : xs.toList ≠ [] := by intro hc; rw [hc] at hlen; simp at hlen
  rw [massYAfalse_gameEnhance, massAllFalse_eq_massAfalse Shat hmono]
  by_cases hA : massAfalse Shat xs.toList = 0
  · rw [hA, mul_zero]
    refine le_antisymm (zero_le _) ?_
    calc massYAfalse Shat i ys xs
        ≤ massAllFalse Shat i ys xs := massYAfalse_le_massAllFalse Shat i ys xs
      _ = massAfalse Shat xs.toList := massAllFalse_eq_massAfalse Shat hmono i ys xs
      _ = 0 := hA
  · have hdom1 : massDom T xs.toList = 1 :=
      massDom_eq_one_of_totalUpTo T hTprob hTtot hxsne (by simp [hlen])
    have hce := hCE i xs ys hA (by rw [hdom1]; exact one_ne_zero)
    rw [hdom1, mul_one] at hce
    exact hce.symm

/-- **CR18 eq. (4.39) — abstract helper (free `Ŝ`)**: the MBO-enhanced `T̂ = gameEnhance T Ŝ` has the
*same* not-won transcript mass as `Ŝ`. This is the whole content of `Ŝ ≡ᵍ T̂` at the level the consumers
(Lemma 4.15, Lemma 4.16) use it. This compatibility form keeps the historical global-totality API; the
tighter theorem is `massYAfalse_gameEnhance_eq_of_totalUpTo`.

**This is the generic algebra helper, not the paper-facing endpoint.** It takes the *derived* game `Ŝ` as a
free parameter with property hypotheses (`hCE`, `hmono`) — the scaffold the cardinal rule forbids for a CR18
result (MODELING_REVIEW #6 / fix F1.3). The **paper-facing public eq. (4.39)** is
`RandomSystems.CR18.eq_4_39` (below), which takes the **base** `S T : PFunPDS X Y` and the MBO `cond`,
constructs `Ŝ := gameOf S cond` and `T̂ := gameEnhance T Ŝ` in its own statement, and *discharges* `hmono`
via `monotoneMBO_gameOf` and `hShat`/`hStot` via the enhancement construction. This helper is kept as a
proof ingredient. -/
theorem massYAfalse_gameEnhance_eq_abstract (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (hCE : Shat |≡ T) (hTprob : T.isProbDist) (hTtot : CondEquiv.TotalOnNonempty T)
    (hmono : MonotoneMBO Shat)
    (i : ℕ) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    massYAfalse (gameEnhance T Shat) i ys xs = massYAfalse Shat i ys xs := by
  exact massYAfalse_gameEnhance_eq_of_totalUpTo T Shat hCE hTprob hmono i
    (TotalUpTo_of_totalOnNonempty hTtot (i + 1)) ys xs

/-! ## Round 4 — `massYAfalse`-equality variants of the Lemma 4.16 / Theorem 4.17 chain

`≡ᵍ` is consumed in the chain **only** as pointwise `massYAfalse` equality (`distNotWonZ1_congr_gameEquiv`
and `winProbBehavior_congr_gameEquiv` both reduce to it). We thread that equality directly, so the chain
applies to `Ŝ` and `T̂ = gameEnhance T Ŝ` — whose `massYAfalse` agree (Round 3) — without ever proving the
full `≡ᵍ` (the cumulative↔per-step kernel inversion, which Maurer never performs either). -/

/-- Pointwise equality of the not-won transcript masses — the entire content `≡ᵍ` contributes to the
Lemma 4.16 / Theorem 4.17 chain. -/
def MassYAfalseEq (S T : PFunPDS X (Y × Bool)) : Prop :=
  ∀ (i : ℕ) (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)),
    massYAfalse S i ys xs = massYAfalse T i ys xs

/-- Fixed-round pointwise equality of not-won transcript masses.

UPSTREAM-CANDIDATE: bounded-totality form of `MassYAfalseEq`; filtered Theorem-4.17 instances only
need equality at the exact query round consumed by Lemma 4.16. -/
def MassYAfalseEqAt (S T : PFunPDS X (Y × Bool)) (i : ℕ) : Prop :=
  ∀ (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)),
    massYAfalse S i ys xs = massYAfalse T i ys xs

theorem MassYAfalseEq.symm {S T : PFunPDS X (Y × Bool)} (h : MassYAfalseEq S T) :
    MassYAfalseEq T S := fun i ys xs => (h i ys xs).symm

theorem MassYAfalseEqAt.symm {S T : PFunPDS X (Y × Bool)} {i : ℕ}
    (h : MassYAfalseEqAt S T i) : MassYAfalseEqAt T S i := by
  intro ys xs
  exact (h ys xs).symm

theorem MassYAfalseEq.at {S T : PFunPDS X (Y × Bool)} (h : MassYAfalseEq S T) (i : ℕ) :
    MassYAfalseEqAt S T i := by
  intro ys xs
  exact h i ys xs

/-- Fixed-round mass-variant of `distNotWonZ1_congr_gameEquiv`. -/
theorem distNotWonZ1_congr_mass_at (D : Dist (PFunDDS.DDD X Y)) {S T : PFunPDS X (Y × Bool)}
    {i : ℕ} (hEq : MassYAfalseEqAt S T i) : distNotWonZ1 D S i = distNotWonZ1 D T i := by
  unfold distNotWonZ1
  refine tsum_congr fun p => ?_
  rw [hEq p.2 p.1]

/-- mass-variant of `distNotWonZ1_congr_gameEquiv`: the `Aq=0` cancellation needs only `massYAfalse` eq. -/
theorem distNotWonZ1_congr_mass (D : Dist (PFunDDS.DDD X Y)) {S T : PFunPDS X (Y × Bool)}
    (hEq : MassYAfalseEq S T) (i : ℕ) : distNotWonZ1 D S i = distNotWonZ1 D T i := by
  unfold distNotWonZ1
  refine tsum_congr fun p => ?_
  rw [hEq i p.2 p.1]

/-- Fixed-round mass-variant of `winProbBehavior_congr_gameEquiv`. -/
theorem winProbBehavior_congr_mass_at (W : Dist (PFunDDS.Winner X Y))
    {G H : PFunPDS X (Y × Bool)}
    (hG : G.isProbDist) (hH : H.isProbDist) {i : ℕ} (hEq : MassYAfalseEqAt G H i) :
    winProbBehavior W G i = winProbBehavior W H i := by
  have hGw : G.weight = 1 := hG
  have hHw : H.weight = 1 := hH
  unfold winProbBehavior notWonProbBehavior
  rw [hGw, hHw]
  congr 1
  refine tsum_congr fun p => ?_
  rw [hEq p.2 p.1]

/-- mass-variant of `winProbBehavior_congr_gameEquiv`: Lemma 4.15 needs only `massYAfalse` eq (+ weight 1). -/
theorem winProbBehavior_congr_mass (W : Dist (PFunDDS.Winner X Y)) {G H : PFunPDS X (Y × Bool)}
    (hG : G.isProbDist) (hH : H.isProbDist) (hEq : MassYAfalseEq G H) (i : ℕ) :
    winProbBehavior W G i = winProbBehavior W H i := by
  have hGw : G.weight = 1 := hG
  have hHw : H.weight = 1 := hH
  unfold winProbBehavior notWonProbBehavior
  rw [hGw, hHw]
  congr 1
  refine tsum_congr fun p => ?_
  rw [hEq i p.2 p.1]

/-- Fixed-round mass-variant of `lemma_4_16'`: same PDF chain, but the game-equivalence input is only
the not-won mass equality at the exact query round `i`.

UPSTREAM-CANDIDATE: bounded-totality Theorem-4.17 infrastructure for filtered games. -/
theorem lemma_4_16'_mass_at (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEqAt S T i)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ) := by
  have hQ' : ∀ w ∈ (Dist.fTransform PFunDDS.ddToDDE D).support, QueriesExactly w (i + 1) := by
    intro w hw; obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw; exact hQ d hd
  have hcancel : (Dist.prod D T).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2)
      = (Dist.prod D S).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2) := by
    rw [verdictNotWon_eq_distNotWonZ1 D T i hQ hTotT, verdictNotWon_eq_distNotWonZ1 D S i hQ hTotS,
      distNotWonZ1_congr_mass_at D hEq]
  refine lemma_4_16_assemble_abstract D S T ?_ ?_ hcancel ?_ ?_
  · unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · rw [winProb_ddToDDE, winProb_eq_prod_mass]
  · rw [winProb_eq_behavior _ T i hQ' hTotT, winProb_eq_behavior _ S i hQ' hTotS,
      winProbBehavior_congr_mass_at _ hT hS hEq.symm]

/-- mass-variant **assembly helper** (`_abstract`) of `lemma_4_16'`: same PDF chain, with the two `≡ᵍ`
congruences replaced by their `massYAfalse`-equality forms (`MassYAfalseEq S T`).

NOTE (MODELING_REVIEW #5 / fix F1.5): this is **not** a paper-facing endpoint. It takes the central
content — the pointwise not-won mass equality `MassYAfalseEq S T` — **as a hypothesis** rather than
proving it for a constructed game, so it is an abstract scaffold (the same smell as
`lemma_4_16_assemble_abstract`). The `_abstract` suffix marks the non-endpoint helper role; the body is
unchanged. It is kept public because downstream files (`BlindConverter.lean`, `BlindAbsorption.lean`) must
call it to instantiate the constructed game `Ŝ`; the paper-facing endpoints are `lemma_4_16'`
(RelateGameDistinguishing.lean) and `RandomSystems.CR18.theorem_4_17` (GameOf.lean). -/
theorem lemma_4_16'_mass_abstract (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEq S T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ) := by
  have hQ' : ∀ w ∈ (Dist.fTransform PFunDDS.ddToDDE D).support, QueriesExactly w (i + 1) := by
    intro w hw; obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw; exact hQ d hd
  have hcancel : (Dist.prod D T).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2)
      = (Dist.prod D S).mass
        (fun dg => PFunDDS.verdict dg.1 (PFunDDS.ignoreMBO dg.2) ∧ ¬ winsDDS (PFunDDS.ddToDDE dg.1) dg.2) := by
    rw [verdictNotWon_eq_distNotWonZ1 D T i hQ hTotT, verdictNotWon_eq_distNotWonZ1 D S i hQ hTotS,
      distNotWonZ1_congr_mass D hEq i]
  refine lemma_4_16_assemble_abstract D S T ?_ ?_ hcancel ?_ ?_
  · unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO
    rw [winProb_fTransform_game, winProb_eq_prod_mass]
  · rw [winProb_ddToDDE, winProb_eq_prod_mass]
  · rw [winProb_eq_behavior _ T i hQ' hTotT, winProb_eq_behavior _ S i hQ' hTotS,
      winProbBehavior_congr_mass _ hT hS hEq.symm i]

/-- mass-variant **assembly helper** (`_abstract`) of the adaptive corollary: `⟨S⁻|T⁻⟩(D) ≤ Γ(S)` from
`massYAfalse`-equality of the two games.

NOTE (MODELING_REVIEW #5 / fix F1.5): like `lemma_4_16'_mass_abstract`, this takes the central content
`MassYAfalseEq S T` **as a hypothesis** rather than proving it for a constructed game, so it is an abstract
assembly scaffold, not a CR18 endpoint. The `_abstract` suffix marks its non-endpoint helper role; it
remains public so downstream proof engineering can reuse and inspect the step. The paper-facing endpoint is
`RandomSystems.CR18.theorem_4_17` (GameOf.lean). -/
theorem theorem_4_17_mass_abstract (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEq S T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ) ≤ (maxWinProb S : ℝ) := by
  refine (lemma_4_16'_mass_abstract D S T i hS hT hEq hQ hTotS hTotT).trans ?_
  have hD' : (Dist.fTransform PFunDDS.ddToDDE D).isProbDist := by
    exact Dist.fTransform_isProbDist PFunDDS.ddToDDE hD
  exact_mod_cast winProb_le_maxWinProb (Dist.fTransform PFunDDS.ddToDDE D) S hD'

/-- Fixed-round mass-variant of the adaptive Theorem-4.17 corollary.

UPSTREAM-CANDIDATE: this is the exact form needed by `[q]`-filtered systems. It avoids promoting the
single queried round's eq. (4.39) mass equality into a global `MassYAfalseEq`. -/
theorem theorem_4_17_mass_at (D : Dist (PFunDDS.DDD X Y)) (S T : PFunPDS X (Y × Bool)) (i : ℕ)
    (hS : S.isProbDist) (hT : T.isProbDist) (hEq : MassYAfalseEqAt S T i)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1))
    (hTotS : TotalUpTo S (i + 1)) (hTotT : TotalUpTo T (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T) : ℝ) ≤ (maxWinProb S : ℝ) := by
  refine (lemma_4_16'_mass_at D S T i hS hT hEq hQ hTotS hTotT).trans ?_
  have hD' : (Dist.fTransform PFunDDS.ddToDDE D).isProbDist := by
    exact Dist.fTransform_isProbDist PFunDDS.ddToDDE hD
  exact_mod_cast winProb_le_maxWinProb (Dist.fTransform PFunDDS.ddToDDE D) S hD'

/-! ## Round 5 — `T̂` is a total game with `T̂⁻ = T`, and the precise-PDF Theorem 4.17

The enhancement is a probability distribution (`gameEnhance_isProbDist`), is total wherever `T` and `Ŝ`
are (`gameEnhance_totalUpTo`), and — the eq. (4.39) marginal **`T̂⁻ = T`** — ignoring its MBO recovers `T`
(`ignoreMBO_gameEnhance`), because on `Ŝ`'s (total) support `ignoreMBO (combineSys t ŝ) = t` and the
first-coordinate marginal of `T ×ᵈ Ŝ` is `T`. Then `Ŝ |≡ T` instantiates the chain. -/

/-- `Fintype`-free singleton mass `X(·=a) = X a` (the library `mass_singleton` carries `[Fintype A]`,
which the `DDS` carriers must not have). -/
theorem mass_singleton' {A : Type*} (X : Dist A) (a : A) :
    X.mass (fun b => b = a) = X a := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- First-coordinate marginal of an independent product is the first factor (second a prob. dist.).
`Fintype`-free, via `mass_prod_and` + `mass_true`. -/
theorem fTransform_fst_prod {A B : Type*} (X : Dist A) (Y : Dist B) (hY : Y.weight = 1) :
    Dist.fTransform Prod.fst (Dist.prod X Y) = X := by
  classical
  refine Finsupp.ext fun a => ?_
  rw [← mass_singleton' (Dist.fTransform Prod.fst (Dist.prod X Y)) a, Dist.mass_fTransform,
    Dist.mass_congr (Dist.prod X Y) (Q := fun p => p.1 = a ∧ (fun _ : B => True) p.2)
      (fun p => by simp),
    Dist.mass_prod_and X Y (fun u => u = a) (fun _ => True), Dist.mass_true,
    mass_singleton' X a, hY, mul_one]

/-- On `Ŝ`'s (total) support, ignoring the MBO of `combineSys t ŝ` recovers `t`: the `Y`-output is `t`'s
and the domain `dom t ∩ dom ŝ` collapses to `dom t` since `ŝ` is defined on every nonempty history. -/
theorem ignoreMBO_combineSys_eq {t : PFunDDS.DDS X Y} {s : PFunDDS.DDS X (Y × Bool)}
    (hs : ∀ l : List X, l ≠ [] → l ∈ PFunDDS.dom s) :
    PFunDDS.ignoreMBO (PFunDDS.combineSys t s) = t := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · exact fun h => h.1
  · intro hd
    exact ⟨hd, hs l fun he => PFunDDS.empty_not_mem t (he ▸ hd)⟩

/-- **CR18 eq. (4.39), the marginal `T̂⁻ = T`**: ignoring `T̂`'s MBO recovers `T`. -/
theorem ignoreMBO_gameEnhance (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (hShat : Shat.isProbDist) (hStot : CondEquiv.TotalOnNonempty Shat) :
    PFunPDS.ignoreMBO (gameEnhance T Shat) = T := by
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO gameEnhance
  simp only [dist_simp]
  have hcongr : Dist.fTransform (PFunDDS.ignoreMBO ∘ fun p => PFunDDS.combineSys p.1 p.2)
        (Dist.prod T Shat)
      = Dist.fTransform Prod.fst (Dist.prod T Shat) := by
    unfold Dist.fTransform
    refine Finsupp.mapDomain_congr fun p hp => ?_
    have hval : Dist.prod T Shat p = T p.1 * Shat p.2 := Dist.prod_apply T Shat p.1 p.2
    have hp2 : p.2 ∈ Shat.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul (hval ▸ Finsupp.mem_support_iff.mp hp))
    exact ignoreMBO_combineSys_eq fun l hl => hStot p.2 hp2 l hl
  rw [hcongr, fTransform_fst_prod T Shat hShat]

/-- `T̂ = gameEnhance T Ŝ` is a probability distribution. -/
theorem gameEnhance_isProbDist (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool))
    (hT : T.isProbDist) (hShat : Shat.isProbDist) : (gameEnhance T Shat).isProbDist := by
  unfold gameEnhance
  exact Dist.fTransform_isProbDist _ (Dist.prod_isProbDist T Shat hT hShat)

/-- `T̂` is total (up to `q`) wherever both `T` and `Ŝ` are: its domain is `dom T ∩ dom Ŝ`. -/
theorem gameEnhance_totalUpTo (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool)) (q : ℕ)
    (hT : TotalUpTo T q) (hShat : TotalUpTo Shat q) : TotalUpTo (gameEnhance T Shat) q := by
  intro g hg xs hne hlen
  obtain ⟨p, hp, rfl⟩ := mem_support_fTransform _ _ hg
  have hval : Dist.prod T Shat p = T p.1 * Shat p.2 := Dist.prod_apply T Shat p.1 p.2
  have hne0 : Dist.prod T Shat p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hp1 : p.1 ∈ T.support :=
    Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul (hval ▸ hne0))
  have hp2 : p.2 ∈ Shat.support :=
    Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul (hval ▸ hne0))
  exact ⟨hT p.1 hp1 xs hne hlen, hShat p.2 hp2 xs hne hlen⟩

/-! ### Bounded `T̂⁻ = T` infrastructure

The global equality `ignoreMBO_gameEnhance` is too strong for `[q]`-filtered systems. The filtered
Theorem-4.17 proof only needs equality of verdict probabilities for distinguishers that make exactly
`q` queries, so we prove that bounded observable equality directly.
-/

/-- Exact-query verdicts are determined by the output history after the exact query round.

UPSTREAM-CANDIDATE: this is the generic "stop after `q`" readout lemma for CR18 distinguishers. It
keeps later bounded congruence proofs from unfolding the existential `verdict` every time. -/
theorem PFunDDS.verdict_iff_at_exact (d : PFunDDS.DDD X Y) (s : PFunDDS.DDS X Y) (q : ℕ)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q) :
    PFunDDS.verdict d s ↔
      d.val (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) q))
        = Sum.inr true := by
  constructor
  · intro hv
    have hlenq :
        (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) q)).length = q := by
      rw [transcriptOutputs_length]
      exact transcript_length_eq hQ.1 (le_refl q)
    have hstop :
        PFunDDS.ddToDDE d
          (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) q)) = none :=
      hQ.2 _ (by rw [hlenq])
    obtain ⟨n, hn⟩ := hv
    rcases le_or_gt q n with hqn | hnq
    · have hfreeze :
          PFunDDS.transcript s (PFunDDS.ddToDDE d) n =
            PFunDDS.transcript s (PFunDDS.ddToDDE d) q :=
        transcript_freeze hstop hqn
      rwa [hfreeze] at hn
    · have hlenn :
          (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) n)).length = n := by
        rw [transcriptOutputs_length]
        exact transcript_length_eq hQ.1 (le_of_lt hnq)
      have hsome :
          (PFunDDS.ddToDDE d
            (PFunDDS.transcriptOutputs (PFunDDS.transcript s (PFunDDS.ddToDDE d) n))).isSome :=
        hQ.1 _ (by rw [hlenn]; exact hnq)
      simp [PFunDDS.ddToDDE, hn] at hsome
  · intro h
    exact ⟨q, h⟩

/-- On histories within the query budget, the fully-defined completion of `T̂⁻ = (combineSys t ŝ)⁻`
returns exactly `t`'s fully-defined output.

UPSTREAM-CANDIDATE: bounded deterministic form of the `T̂⁻ = T` marginal. It is deliberately stated
at the output level, not as DDS equality, because `[q]`-filtered systems are only total on histories
of length `≤ q`. -/
theorem PFunDDS.output_fullyDefined_ignoreMBO_combineSys_eq_of_totalUpTo
    (t : PFunDDS.DDS X Y) (s : PFunDDS.DDS X (Y × Bool)) (q : ℕ)
    (ht : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom t)
    (hs : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom s)
    {xs : List X} (hne : xs ≠ []) (hlen : xs.length ≤ q) :
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.ignoreMBO (PFunDDS.combineSys t s))) xs
        (by rw [PFunDDS.dom_fullyDefined]; exact hne)
      = PFunDDS.output (PFunDDS.fullyDefined t) xs
          (by rw [PFunDDS.dom_fullyDefined]; exact hne) := by
  have hdomt : xs ∈ PFunDDS.dom t := ht xs hne hlen
  have hdoms : xs ∈ PFunDDS.dom s := hs xs hne hlen
  have hpre : xs.dropLast <+: xs := xs.dropLast_prefix
  have hpret : xs.dropLast ∈ PFunDDS.dom t ∨ xs.dropLast = [] := by
    by_cases hnil : xs.dropLast = []
    · exact Or.inr hnil
    · exact Or.inl (PFunDDS.prefix_closed t hpre hnil hdomt)
  have hpres : xs.dropLast ∈ PFunDDS.dom s ∨ xs.dropLast = [] := by
    by_cases hnil : xs.dropLast = []
    · exact Or.inr hnil
    · exact Or.inl (PFunDDS.prefix_closed s hpre hnil hdoms)
  have hdomt' : xs.dropLast ++ [xs.getLast hne] ∈ PFunDDS.dom t := by
    rwa [List.dropLast_append_getLast hne]
  have hdoms' : xs.dropLast ++ [xs.getLast hne] ∈ PFunDDS.dom s := by
    rwa [List.dropLast_append_getLast hne]
  have hpreComb :
      xs.dropLast ∈ PFunDDS.dom (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) ∨
        xs.dropLast = [] := by
    rcases hpret with hpt | hpt
    · rcases hpres with hps | hps
      · exact Or.inl ⟨hpt, hps⟩
      · exact Or.inr hps
    · exact Or.inr hpt
  have hdomComb' :
      xs.dropLast ++ [xs.getLast hne] ∈
        PFunDDS.dom (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) :=
    ⟨hdomt', hdoms'⟩
  calc
    PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.ignoreMBO (PFunDDS.combineSys t s))) xs
        (by rw [PFunDDS.dom_fullyDefined]; exact hne)
        = PFunDDS.output (PFunDDS.fullyDefined (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)))
            (xs.dropLast ++ [xs.getLast hne]) (by rw [PFunDDS.dom_fullyDefined]; simp) := by
          exact PFunDDS.output_congr _
            (List.dropLast_append_getLast hne).symm _ _
    _ = some (PFunDDS.output (PFunDDS.ignoreMBO (PFunDDS.combineSys t s))
          (xs.dropLast ++ [xs.getLast hne]) hdomComb') := by
          rw [PFunDDS.output_fullyDefined_append_of_mem
            (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) xs.dropLast (xs.getLast hne)
            hpreComb hdomComb']
    _ = some (PFunDDS.output t (xs.dropLast ++ [xs.getLast hne]) hdomt') := by
          rw [PFunDDS.output_ignoreMBO, PFunDDS.output_combineSys]
    _ = PFunDDS.output (PFunDDS.fullyDefined t) (xs.dropLast ++ [xs.getLast hne])
          (by rw [PFunDDS.dom_fullyDefined]; simp) := by
          rw [PFunDDS.output_fullyDefined_append_of_mem t xs.dropLast (xs.getLast hne) hpret hdomt']
    _ = PFunDDS.output (PFunDDS.fullyDefined t) xs
          (by rw [PFunDDS.dom_fullyDefined]; exact hne) := by
          exact PFunDDS.output_congr _ (List.dropLast_append_getLast hne) _ _

/-- Up to the exact query budget, a distinguisher sees the same transcript against `T̂⁻` and `T`.

UPSTREAM-CANDIDATE: bounded deterministic transcript form of the `T̂⁻ = T` marginal. -/
theorem PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo
    (d : PFunDDS.DDD X Y) (t : PFunDDS.DDS X Y) (s : PFunDDS.DDS X (Y × Bool)) (q : ℕ)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q)
    (ht : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom t)
    (hs : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom s) :
    PFunDDS.transcript (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) (PFunDDS.ddToDDE d) q =
      PFunDDS.transcript t (PFunDDS.ddToDDE d) q := by
  suffices hmain : ∀ n : ℕ, n ≤ q →
      PFunDDS.transcript (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) (PFunDDS.ddToDDE d) n =
        PFunDDS.transcript t (PFunDDS.ddToDDE d) n by
    exact hmain q (le_refl q)
  intro n
  induction n with
  | zero =>
      intro _hle
      rfl
  | succ n ih =>
      intro hle
      have hprefix :
          PFunDDS.transcript (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) (PFunDDS.ddToDDE d) n =
            PFunDDS.transcript t (PFunDDS.ddToDDE d) n :=
        ih (by omega)
      have hlenT :
          (PFunDDS.transcriptOutputs (PFunDDS.transcript t (PFunDDS.ddToDDE d) n)).length = n := by
        rw [transcriptOutputs_length]
        exact transcript_length_eq hQ.1 (by omega)
      have hsome :
          (PFunDDS.ddToDDE d
            (PFunDDS.transcriptOutputs (PFunDDS.transcript t (PFunDDS.ddToDDE d) n))).isSome :=
        hQ.1 _ (by rw [hlenT]; omega)
      obtain ⟨x, hfireT⟩ := Option.isSome_iff_exists.mp hsome
      have hfireComb :
          PFunDDS.ddToDDE d
            (PFunDDS.transcriptOutputs
              (PFunDDS.transcript (PFunDDS.ignoreMBO (PFunDDS.combineSys t s))
                (PFunDDS.ddToDDE d) n)) = some x := by
        rw [hprefix]
        exact hfireT
      have hinputLen :
          (PFunDDS.transcriptInputs (PFunDDS.transcript t (PFunDDS.ddToDDE d) n) ++ [x]).length ≤ q := by
        have hlenRun : (PFunDDS.transcript t (PFunDDS.ddToDDE d) n).length = n :=
          transcript_length_eq hQ.1 (by omega)
        rw [List.length_append, transcriptInputs_length, hlenRun]
        simpa using hle
      rw [transcript_succ_fire hfireComb, transcript_succ_fire hfireT, hprefix]
      rw [PFunDDS.output_fullyDefined_ignoreMBO_combineSys_eq_of_totalUpTo t s q ht hs
        (by simp) hinputLen]

/-- Exact-query distinguishers cannot distinguish `T̂⁻ = (combineSys t ŝ)⁻` from `t` under bounded
totality.

UPSTREAM-CANDIDATE: bounded deterministic verdict form of the `T̂⁻ = T` marginal. -/
theorem PFunDDS.verdict_ignoreMBO_combineSys_iff_of_totalUpTo
    (d : PFunDDS.DDD X Y) (t : PFunDDS.DDS X Y) (s : PFunDDS.DDS X (Y × Bool)) (q : ℕ)
    (hQ : QueriesExactly (PFunDDS.ddToDDE d) q)
    (ht : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom t)
    (hs : ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom s) :
    PFunDDS.verdict d (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) ↔
      PFunDDS.verdict d t := by
  rw [PFunDDS.verdict_iff_at_exact d (PFunDDS.ignoreMBO (PFunDDS.combineSys t s)) q hQ,
    PFunDDS.verdict_iff_at_exact d t q hQ,
    PFunDDS.transcript_ignoreMBO_combineSys_eq_of_totalUpTo d t s q hQ ht hs]

/-- Bounded observable form of `ignoreMBO_gameEnhance`: exact-query distinguishers have the same
verdict probability against `T̂⁻` and `T`.

UPSTREAM-CANDIDATE: this is the probabilistic, `[q]`-compatible replacement for the global DDS equality
`ignoreMBO_gameEnhance` inside filtered Theorem-4.17 applications. -/
theorem verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo
    (D : Dist (PFunDDS.DDD X Y)) (T : PFunPDS X Y) (Shat : PFunPDS X (Y × Bool)) (q : ℕ)
    (hShat : Shat.isProbDist)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) q)
    (hT : TotalUpTo T q) (hShatTot : TotalUpTo Shat q) :
    verdictProb D (PFunPDS.ignoreMBO (gameEnhance T Shat)) = verdictProb D T := by
  unfold verdictProb PFunPDS.ignoreMBO PFunPDS.stripMBO gameEnhance
  rw [winProb_fTransform_game, winProb_fTransform_game]
  have hmarg :
      GamePerf.winProb PFunDDS.verdict D T =
        GamePerf.winProb (fun w g => PFunDDS.verdict w g.1) D (Dist.prod T Shat) := by
    calc
      GamePerf.winProb PFunDDS.verdict D T
          = GamePerf.winProb PFunDDS.verdict D (Dist.fTransform Prod.fst (Dist.prod T Shat)) := by
            rw [fTransform_fst_prod T Shat hShat]
      _ = GamePerf.winProb (fun w g => PFunDDS.verdict w g.1) D (Dist.prod T Shat) := by
            rw [winProb_fTransform_game]
  calc
    GamePerf.winProb
        (fun w g => PFunDDS.verdict w (PFunDDS.stripMBO (PFunDDS.combineSys g.1 g.2)))
        D (Dist.prod T Shat)
        = GamePerf.winProb (fun w g => PFunDDS.verdict w g.1) D (Dist.prod T Shat) := by
          rw [winProb_eq_prod_mass, winProb_eq_prod_mass]
          refine mass_congr_support (Dist.prod D (Dist.prod T Shat)) fun p hp => ?_
          have hval : Dist.prod D (Dist.prod T Shat) p = D p.1 * (Dist.prod T Shat) p.2 :=
            Dist.prod_apply D (Dist.prod T Shat) p.1 p.2
          have hne : D p.1 * (Dist.prod T Shat) p.2 ≠ 0 :=
            hval ▸ Finsupp.mem_support_iff.mp hp
          have hd : p.1 ∈ D.support :=
            Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
          have hpTS : p.2 ∈ (Dist.prod T Shat).support :=
            Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
          have hvalTS : Dist.prod T Shat p.2 = T p.2.1 * Shat p.2.2 :=
            Dist.prod_apply T Shat p.2.1 p.2.2
          have hneTS : T p.2.1 * Shat p.2.2 ≠ 0 :=
            hvalTS ▸ Finsupp.mem_support_iff.mp hpTS
          have htmem : p.2.1 ∈ T.support :=
            Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hneTS)
          have hsmem : p.2.2 ∈ Shat.support :=
            Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hneTS)
          exact PFunDDS.verdict_ignoreMBO_combineSys_iff_of_totalUpTo p.1 p.2.1 p.2.2 q
            (hQ p.1 hd) (hT p.2.1 htmem) (hShatTot p.2.2 hsmem)
    _ = GamePerf.winProb PFunDDS.verdict D T := hmarg.symm

/-- Bounded-totality form of the conditional-equivalence Theorem-4.17 adaptive helper.

UPSTREAM-CANDIDATE: filtered systems satisfy `TotalUpTo`, not global `TotalOnNonempty`. This endpoint
matches the PDF proof while using only the histories actually inspected by an exact `(i+1)`-query
distinguisher. -/
theorem theorem_4_17_condEquiv_abstract_of_totalUpTo
    (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : TotalUpTo Shat (i + 1)) (hTtot : TotalUpTo T (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (maxWinProb Shat : ℝ) := by
  have hEq : MassYAfalseEqAt Shat (gameEnhance T Shat) i :=
    fun ys xs => (massYAfalse_gameEnhance_eq_of_totalUpTo T Shat hCE hT hmono i hTtot ys xs).symm
  have hEnhProb : (gameEnhance T Shat).isProbDist :=
    gameEnhance_isProbDist T Shat hT hShat
  have hEnhTot : TotalUpTo (gameEnhance T Shat) (i + 1) :=
    gameEnhance_totalUpTo T Shat (i + 1) hTtot hStot
  have key := theorem_4_17_mass_at D Shat (gameEnhance T Shat) i hShat
    hEnhProb hEq hQ hStot hEnhTot hD
  have hVP :
      verdictProb D (PFunPDS.ignoreMBO (gameEnhance T Shat)) = verdictProb D T :=
    verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo D T Shat (i + 1) hShat hQ hTtot hStot
  rwa [advantage, hVP] at key

/-- **CR18 Theorem 4.17 — abstract helper (adaptive bound, free `Ŝ`)**: *if for an `(X,Y)`-system one
can define an MBO so that the game `Ŝ` is conditionally equivalent to `T` (`Ŝ |≡ T`, Def 4.19), then the
distinguishing advantage of any `D` between `S = Ŝ⁻` and `T` is bounded by the maximal game-winning
probability of `Ŝ`* — `⟨S|T⟩(D) ≤ Γ(Ŝ)`. The proof enhances `T` to `T̂ = gameEnhance T Ŝ` with `T̂⁻ = T`
(`ignoreMBO_gameEnhance`) and `massYAfalse T̂ = massYAfalse Ŝ` (`massYAfalse_gameEnhance_eq_abstract`, eq. 4.39),
then applies the Lemma 4.16 chain (`theorem_4_17_mass_abstract`). Side conditions are exactly Maurer's standing
assumptions: probability distributions, monotone MBO, games defined on the histories under discussion,
fixed query count.

**This is the abstract conditional-equivalence helper, not the paper-facing endpoint.** It takes the
*derived* game `Ŝ` as a free parameter with property hypotheses (`hCE`, `hmono`) — the scaffold the
cardinal rule forbids for a CR18 theorem (MODELING_REVIEW #1). The **paper-facing public Theorem 4.17**
is `RandomSystems.CR18.theorem_4_17` (in `GameOf.lean`), which takes the **base** `S T : PFunPDS X Y`,
constructs `Ŝ := gameOf S cond` in its own statement, *proves* `ignoreMBO Ŝ = S` and `MonotoneMBO Ŝ`,
and concludes the PDF's blind bound `∆(S,T) ≤ Γ(bŜ)`. This helper is kept (proof unchanged) for the
adaptive `Γ(Ŝ)` half of the chain.

**Scope note.** This is the **adaptive** bound `Γ(Ŝ)`. The PDF's headline conclusion is the strictly
*stronger* `∆(S,T) ≤ Γ(bŜ)`, the **non-adaptive** (blind) game-winning probability (`Γ(bŜ) ≤ Γ(Ŝ)`). -/
theorem theorem_4_17_condEquiv_abstract (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (maxWinProb Shat : ℝ) := by
  have hTU : TotalUpTo T (i + 1) := TotalUpTo_of_totalOnNonempty hTtot (i + 1)
  have hSU : TotalUpTo Shat (i + 1) := TotalUpTo_of_totalOnNonempty hStot (i + 1)
  have hEq : MassYAfalseEq Shat (gameEnhance T Shat) :=
    fun j ys xs => (massYAfalse_gameEnhance_eq_of_totalUpTo T Shat hCE hT hmono j
      (TotalUpTo_of_totalOnNonempty hTtot (j + 1)) ys xs).symm
  have key := theorem_4_17_mass_abstract D Shat (gameEnhance T Shat) i hShat
    (gameEnhance_isProbDist T Shat hT hShat) hEq hQ
    hSU (gameEnhance_totalUpTo T Shat (i + 1) hTU hSU) hD
  rwa [ignoreMBO_gameEnhance T Shat hShat hStot] at key

end RandomSystems.CR18
