/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.BlindConverter

/-!
# CR18 eq. (4.40) — absorbing `T̃` into the winner: the all-`D` Theorem 4.17

This file upgrades the blind sharpening of Theorem 4.17 (`theorem_4_17_condEquiv_blind_abstract`, which
assumed the distinguisher `D` was already non-adaptive) to **every** distinguisher `D`, recovering the PDF's
headline `∆(S,T) ≤ Γ(bŜ)` *without* the non-adaptivity hypothesis. The remaining gap was Maurer's
eq. (4.40):

> `T̂ = T̃·bŜ`, hence `Ŝ(D) = bŜ(D·T̃)` — "absorbing `T̃` into the winner (see (4.10))".

`T̃` (Def 4.21) copies the left-interface queries to the right interface and **ignores the replies it
receives** there. Absorbing it into the winner `D` produces a **blind** game-winner for `bŜ`: the
winner replays `D`'s interaction against the fixed realization `T`-reply transcript and never consults
the live game's `Y`-outputs, so its query schedule depends only on the round number — exactly `IsBlind`.

We implement this at the **behavior primitive**, not as an operational converter cascade. The key fact,
already proven upstream, is that the enhanced game's not-won mass factors (`massYAfalse_gameEnhance` +
`massAllFalse_eq_massAfalse`): `massYAfalse (gameEnhance T Ŝ) = massY T · massAfalse Ŝ`. So `T`'s reply
process enters `Ŝ(D)`'s not-won mass *only* as a marginal of the winner factor — and the absorbed blind
winner is exactly that `T`-marginal of `D`. Concretely:

* `absorbedWinner d t` (the action of `D·T̃`) replays `ddToDDE d` against `t` (an `(X,Y)`-DDS): its query
  at reply-history length `k` is `d`'s `(k+1)`-st query when fed `t`'s answers to `d`'s first `k`
  queries. Depends only on the length ⟹ `IsBlind`.
* O1: `absorbedWinnerDist D T` is blind-supported.
* O2 (the absorption identity): `Ŝ(D-as-winner against gameEnhance T Ŝ) = (absorbedWinnerDist D T)(Ŝ)`.
  The substantive content is the **winner-factor marginal**
  `winnerFactor (absorbedWinnerDist D T) xⁱ = ∑_{yⁱ} winnerFactor (D-as-winner) (xⁱ,yⁱ) · massY T yⁱ xⁱ`,
  proven by the existing forced-run machinery (`run_proj`/`run_to_matches`) on the trivially-false game
  `tagFalse t` (whose `Y`-process is `t`).

The closing helper `theorem_4_17_condEquiv_absorbed_abstract` then has **exactly** the hypotheses of the
blind helper *minus* `hblind` (the public base-object endpoint that routes through it is
`RandomSystems.CR18.theorem_4_17`, GameOf.lean; cf. MODELING_REVIEW #3 / fix F1.2).
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open Classical
open scoped RandomSystems.CR18.CondEquiv

universe u v

variable {X : Type u} {Y : Type v}

namespace PFunDDS

/-! ## `tagFalse` — a plain `(X,Y)`-system as a never-winning game

The copying converter `T̃` produces the game side's `Y`-outputs from `T`; the MBO bit is supplied by
`Ŝ`. To reuse the forced-run machinery (`run_proj`/`run_to_matches`, which is stated on games
`DDS X (Y × Bool)`), we view the `(X,Y)`-DDS `t` as the game `tagFalse t` that emits `t`'s output with
a constant `false` MBO — a game no winner ever wins (`winsDDS`), and whose `Y`-process (`ignoreMBO`)
is `t`. -/

/-- The plain `(X,Y)`-system `t`, tagged with a constant-`false` MBO: a game whose `Y`-output is `t`'s
and whose MBO bit is always `false` (never won), same domain as `t`. -/
def tagFalse (t : DDS X Y) : DDS X (Y × Bool) :=
  ⟨fun l => (t.1 l).map (fun y => (y, false)), by
    have hdomeq : ∀ l : List X, (Part.map (fun y : Y => (y, false)) (t.1 l)).Dom ↔ (t.1 l).Dom :=
      fun l => by rw [Part.map_Dom]
    refine ⟨fun h => empty_not_mem t ((hdomeq []).mp h), ?_⟩
    intro l₁ l₂ hpre hne hdom
    exact (hdomeq l₁).mpr (prefix_closed t hpre hne ((hdomeq l₂).mp hdom))⟩

@[simp] theorem mem_dom_tagFalse (t : DDS X Y) (l : List X) :
    l ∈ dom (tagFalse t) ↔ l ∈ dom t := by
  show (Part.map (fun y : Y => (y, false)) (t.1 l)).Dom ↔ (t.1 l).Dom
  rw [Part.map_Dom]

theorem output_tagFalse (t : DDS X Y) (l : List X) (h : l ∈ dom (tagFalse t)) :
    output (tagFalse t) l h = (output t l ((mem_dom_tagFalse t l).mp h), false) := rfl

/-- `(tagFalse t)⁻ = t`: ignoring the constant-`false` MBO recovers the plain system. -/
@[simp] theorem ignoreMBO_tagFalse (t : DDS X Y) : ignoreMBO (tagFalse t) = t := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  show (Part.map Prod.fst (Part.map (fun y : Y => (y, false)) (t.1 l))).Dom ↔ (t.1 l).Dom
  rw [Part.map_Dom, Part.map_Dom]

/-- Every `some`-output along any run of `tagFalse t` carries MBO bit `false`: the game never wins. -/
theorem transcriptOutputs_tagFalse_false (e : DDE X (Y × Bool)) (t : DDS X Y) (n : ℕ) :
    ∀ z : Y × Bool, (some z : Option (Y × Bool))
      ∈ (transcript (tagFalse t) e n)↓ᵧ → z.2 = false := by
  induction n with
  | zero => intro z hz; rw [transcript_zero] at hz; simp [transcriptOutputs] at hz
  | succ n ih =>
      intro z hz
      rcases hfire : e (transcript (tagFalse t) e n)↓ᵧ with _ | x
      · rw [transcript_succ_stall hfire] at hz; exact ih z hz
      · rw [transcript_succ_fire hfire, transcriptOutputs_append] at hz
        rcases List.mem_append.mp hz with hz' | hz'
        · exact ih z hz'
        · -- the freshly-appended output is `(tagFalse t)⊥`'s, which is `none` or `some (·, false)`
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
          -- read the appended entry off the fully-defined completion of `tagFalse t`
          set l := (transcript (tagFalse t) e n)↓ₓ ++ [x] with hl
          rw [output_fullyDefined] at hz'
          set cand := keptPrefix (tagFalse t) l.dropLast ++ [l.getLast (by simp [hl])] with hcand
          by_cases hd : cand ∈ dom (tagFalse t)
          · rw [dif_pos hd, output_tagFalse] at hz'
            rw [Option.some_inj.mp hz']
          · rw [dif_neg hd] at hz'
            exact absurd hz' (by simp)

/-- No winner ever wins `tagFalse t`: every MBO bit along the run is `false`. -/
theorem not_winsDDS_tagFalse (w : Winner X Y) (t : DDS X Y) : ¬ winsDDS w (tagFalse t) := by
  rintro ⟨n, y, hmem⟩
  have := transcriptOutputs_tagFalse_false (winnerView w) t n (y, true) hmem
  simp at this

end PFunDDS

/-! ## The absorbed (blind) winner `D·T̃` -/

/-- **CR18 eq. (4.40), winner level — `D·T̃`.** The action of absorbing the copying converter `T̃`
(Def 4.21) into a deterministic distinguisher `d`: the **blind** game-winner that replays `d`'s
interaction against the *fixed* realization `t` (the `T`-reply transcript) rather than the live game.
At a reply-history of length `k` it issues `d`'s `(k+1)`-st query when fed `t`'s answers to `d`'s first
`k` queries — read off the forced run `transcript t (ddToDDE d)`. It IGNORES the live reply values,
consulting only their *number* (`l.length`), so it is `IsBlind`. -/
noncomputable def absorbedWinner (d : PFunDDS.DDD X Y) (t : PFunDDS.DDS X Y) : PFunDDS.Winner X Y :=
  fun l => PFunDDS.ddToDDE d
    (PFunDDS.transcriptOutputs (PFunDDS.transcript t (PFunDDS.ddToDDE d) l.length))

/-- `absorbedWinner d t` is blind: its query depends only on the reply-history length. -/
theorem isBlind_absorbedWinner (d : PFunDDS.DDD X Y) (t : PFunDDS.DDS X Y) :
    IsBlind (absorbedWinner d t) := by
  intro l₁ l₂ hlen
  simp only [absorbedWinner, hlen]

open PFunDDS in
/-- The absorbed winner makes **exactly `i+1` queries** when `d` does: it just replays `d`'s queries
against `t`, so its query/stop pattern tracks `d`'s. Below `i+1` the run has length `= |l|` (no early
stall, `transcript_length_eq`) and `d` queries; at/after `i+1` the run freezes at length `i+1`
(`transcript_freeze`) and `d` stops. -/
theorem queriesExactly_absorbedWinner (d : DDD X Y) (t : DDS X Y) (i : ℕ)
    (hQ : QueriesExactly (ddToDDE d) (i + 1)) :
    QueriesExactly (absorbedWinner d t) (i + 1) := by
  constructor
  · intro l hl
    show (ddToDDE d (transcript t (ddToDDE d) l.length)↓ᵧ).isSome
    have hlen : (transcript t (ddToDDE d) l.length)↓ᵧ.length = l.length := by
      rw [transcriptOutputs_length, transcript_length_eq hQ.1 (le_of_lt hl)]
    exact hQ.1 _ (by rw [hlen]; exact hl)
  · intro l hl
    show ddToDDE d (transcript t (ddToDDE d) l.length)↓ᵧ = none
    -- the run freezes at `i+1`; its output history has length `i+1`, so `d` stops.
    have hstop : ddToDDE d (transcript t (ddToDDE d) (i + 1))↓ᵧ = none := by
      apply hQ.2
      rw [transcriptOutputs_length, transcript_length_eq hQ.1 (le_refl (i + 1))]
    have hfreeze : transcript t (ddToDDE d) l.length = transcript t (ddToDDE d) (i + 1) :=
      transcript_freeze hstop hl
    rw [hfreeze]; exact hstop

/-- **`absorbedWinnerDist D T`** — the probabilistic absorbed winner `D·T̃`: push the deterministic
absorption through the independent product `D ×ᵈ T` (the distinguisher is sampled from `D`, the
reply transcript from `T`). -/
noncomputable def absorbedWinnerDist (D : Dist (PFunDDS.DDD X Y)) (T : PFunPDS X Y) :
    Dist (PFunDDS.Winner X Y) :=
  Dist.fTransform (fun p => absorbedWinner p.1 p.2) (Dist.prod D T)

/-- `absorbedWinnerDist` is a probability distribution when its distinguisher and system
distributions are.

UPSTREAM-CANDIDATE: probability-mass preservation for the absorbed-winner construction. -/
theorem absorbedWinnerDist_isProbDist (D : Dist (PFunDDS.DDD X Y)) (T : PFunPDS X Y)
    (hD : D.isProbDist) (hT : T.isProbDist) :
    (absorbedWinnerDist D T).isProbDist := by
  unfold absorbedWinnerDist
  exact Dist.fTransform_isProbDist _ (Dist.prod_isProbDist D T hD hT)

/-! ## O1 — the absorbed winner distribution is blind-supported -/

/-- **O1**: every winner in `absorbedWinnerDist D T`'s support is blind, so it is admissible in the
`Γ(bŜ)` supremum. -/
theorem isBlindDist_absorbedWinnerDist (D : Dist (PFunDDS.DDD X Y)) (T : PFunPDS X Y) :
    IsBlindDist (absorbedWinnerDist D T) := by
  intro w hw
  obtain ⟨p, _, rfl⟩ := mem_support_fTransform _ _ hw
  exact isBlind_absorbedWinner p.1 p.2

/-! ## O2 — the absorption identity

The substantive content is the **winner-factor marginal** (`winnerFactor_absorbedWinnerDist_eq`):
the absorbed winner's query-schedule probability is the `T`-marginal of `D`'s. Both the existence and
the uniqueness of the matching transcript come from the forced-run machinery (`run_proj` /
`run_to_matches`) on the never-winning game `tagFalse t` (whose `Y`-process is `t`). -/

open PFunDDS in
/-- **Forced-run identity for the absorbed winner.** When the transcript `(xⁱ, yⁱ)` is consistent with
`ddToDDE d` (`winnerMatches`) and with `tagFalse t` (`gameMatches`), the absorbed winner's run *is* that
forced run: at every round `k ≤ i+1` the output history it feeds `d` is exactly `(yⁱ.take k).map some`.
This is `run_proj` for the game `tagFalse t` (whose `Y`-outputs are `t`'s), projected back through
`ignoreMBO (tagFalse t) = t`. -/
theorem absorbed_run_eq (d : DDD X Y) (t : DDS X Y) (i : ℕ)
    (xs : Vector X (i + 1)) (ys : Vector Y (i + 1))
    (hWM : winnerMatches (ddToDDE d) i xs ys) (hGM : gameMatches (tagFalse t) i ys xs) :
    ∀ {k : ℕ}, k ≤ i + 1 →
      (transcript t (ddToDDE d) k)↓ᵧ = (ys.toList.take k).map some := by
  intro k hk
  -- `t = ignoreMBO (tagFalse t)`, so the `t`-run is the `Y`-projection of the `tagFalse t` game run.
  have hproj : transcript t (ddToDDE d) k
      = projT (transcript (tagFalse t) (winnerView (ddToDDE d)) k) := by
    rw [← ignoreMBO_tagFalse t]; exact transcript_ignoreMBO (tagFalse t) (ddToDDE d) k
  rw [hproj, projT_outputs, (run_proj (ddToDDE d) (tagFalse t) i xs ys hWM hGM hk).2]
  rw [List.map_map]
  refine List.map_congr_left (fun y _ => ?_)
  simp

open PFunDDS in
/-- **`Q → R`**: a transcript `(xⁱ, yⁱ)` consistent with `ddToDDE d` and `tagFalse t` makes the
absorbed winner match the query schedule `xⁱ` (for *any* reply history `ys₀`, since the absorbed winner
is blind). One direction of the marginal fiber's existence characterization. -/
theorem winnerMatches_absorbedWinner_of_matches (d : DDD X Y) (t : DDS X Y) (i : ℕ)
    (xs : Vector X (i + 1)) (ys ys₀ : Vector Y (i + 1))
    (hWM : winnerMatches (ddToDDE d) i xs ys) (hGM : gameMatches (tagFalse t) i ys xs) :
    winnerMatches (absorbedWinner d t) i xs ys₀ := by
  intro k
  have hk : (k : ℕ) < xs.toList.length := k.2
  have hklt : (k : ℕ) < i + 1 := by simpa using hk
  -- the blind winner ignores reply values, consulting only the length `k`
  have hlen : ((ys₀.toList.take k.1).map some).length = k.1 := by
    simp only [List.length_map, List.length_take, Vector.length_toList]; omega
  show ddToDDE d (transcript t (ddToDDE d) ((ys₀.toList.take k.1).map some).length)↓ᵧ
      = some (xs.toList.get k)
  rw [hlen, absorbed_run_eq d t i xs ys hWM hGM (by omega : k.1 ≤ i + 1)]
  -- now exactly `winnerMatches (ddToDDE d)`'s `k`-th equation
  exact hWM ⟨k.1, hk⟩

/-- A blind winner's query schedule is determined by the reply history `ys₀`: two transcripts it
matches against the *same* `ys₀` have the same query sequence. (Used to pin the schedule `xⁱ` produced
by `run_to_matches` to the one in the marginal lemma's index.) -/
theorem winnerMatches_inj_xs {w : PFunDDS.Winner X Y} (i : ℕ)
    {xs xs' : Vector X (i + 1)} {ys₀ : Vector Y (i + 1)}
    (h : winnerMatches w i xs ys₀) (h' : winnerMatches w i xs' ys₀) : xs = xs' := by
  have hxlen : xs.toList.length = i + 1 := by simp
  have hxlen' : xs'.toList.length = i + 1 := by simp
  apply Vector.toList_inj.mp
  apply List.ext_get (by rw [hxlen, hxlen'])
  intro k hk hk'
  have hkx : k < xs.toList.length := hk
  have hkx' : k < xs'.toList.length := hk'
  -- the `ys₀.take` fed to `w` is the same length-`k` history on both sides
  have e1 := h ⟨k, hkx⟩
  have e2 := h' ⟨k, hkx'⟩
  simp only at e1 e2
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact Option.some_inj.mp (e1.symm.trans e2)

/-- `tagFalse t`'s game-consistency event is exactly `t`'s cumulative-output event: the constant-`false`
MBO bit is automatically consistent, and the `Y`-output is `t`'s. Hence `T`'s mass of it is `massY T`. -/
theorem mass_gameMatches_tagFalse (T : PFunPDS X Y) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    Dist.mass T (fun t => gameMatches (PFunDDS.tagFalse t) i ys xs) = CondEquiv.massY T i ys xs := by
  unfold CondEquiv.massY PFunPDS.cumulativeBehavior
  refine Dist.mass_congr T fun t => ?_
  constructor
  · intro hg k
    obtain ⟨h, hv, _⟩ := hg k
    refine ⟨(PFunDDS.mem_dom_tagFalse t _).mp h, ?_⟩
    rwa [PFunDDS.output_tagFalse] at hv
  · intro ht k
    obtain ⟨h, hv⟩ := ht k
    refine ⟨(PFunDDS.mem_dom_tagFalse t _).mpr h, ?_, ?_⟩
    · rw [PFunDDS.output_tagFalse]; exact hv
    · rw [PFunDDS.output_tagFalse]

/-! ### The marginal-lemma fiber: existence and uniqueness -/

open PFunDDS in
/-- **Existence half of the marginal fiber.** On the support of `D ×ᵈ T`, the absorbed winner matches
the query schedule `xⁱ` *iff* there is a consistent transcript `(xⁱ, yⁱ)` — the `T`-reply transcript `yⁱ`
produced when `ddToDDE d` is run against `t`. Forward: `run_to_matches` produces a matching transcript
whose schedule, by `winnerMatches_inj_xs`, equals `xⁱ`. Backward: `winnerMatches_absorbedWinner_of_matches`. -/
theorem absorbed_fiber_hex (D : Dist (DDD X Y)) (T : PFunPDS X Y) (i : ℕ)
    (xs : Vector X (i + 1)) (ys₀ : Vector Y (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1))
    (hT : TotalUpTo T (i + 1)) :
    ∀ p ∈ (Dist.prod D T).support,
      (winnerMatches (absorbedWinner p.1 p.2) i xs ys₀
        ↔ ∃ ys : Vector Y (i + 1),
            winnerMatches (ddToDDE p.1) i xs ys ∧ gameMatches (tagFalse p.2) i ys xs) := by
  rintro ⟨d, t⟩ hp
  have hdmem : d ∈ D.support := by
    have hne : (Dist.prod D T) (d, t) ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [Dist.prod_apply] at hne
    exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
  have htmem : t ∈ T.support := by
    have hne : (Dist.prod D T) (d, t) ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [Dist.prod_apply] at hne
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
  have hQE : QueriesExactly (ddToDDE d) (i + 1) := hQ d hdmem
  have hsome : ∀ h : List (Option (Y × Bool)), h.length < i + 1 →
      (winnerView (ddToDDE d) h).isSome := fun h hh => hQE.1 _ (by rwa [List.length_map])
  have hgtot : ∀ xl : List X, xl ≠ [] → xl.length ≤ i + 1 → xl ∈ dom (tagFalse t) :=
    fun xl hne hlen => (mem_dom_tagFalse t xl).mpr (hT t htmem xl hne hlen)
  constructor
  · intro hR
    obtain ⟨xs', ys', hWM', hGM'⟩ :=
      run_to_matches (ddToDDE d) (tagFalse t) i hsome hgtot (not_winsDDS_tagFalse (ddToDDE d) t)
    -- the absorbed winner matches `xs'`; combined with `hR` (matches `xs`), schedules coincide
    have hRx' : winnerMatches (absorbedWinner d t) i xs' ys₀ :=
      winnerMatches_absorbedWinner_of_matches d t i xs' ys' ys₀ hWM' hGM'
    have hxx : xs = xs' := winnerMatches_inj_xs i hR hRx'
    subst hxx
    exact ⟨ys', hWM', hGM'⟩
  · rintro ⟨ys, hWM, hGM⟩
    exact winnerMatches_absorbedWinner_of_matches d t i xs ys ys₀ hWM hGM

open PFunDDS in
/-- **Uniqueness half of the marginal fiber.** A consistent transcript `(xⁱ, yⁱ)` is unique: both
`winnerMatches`+`gameMatches` candidates equal the forced run (`run_proj`), so their `yⁱ` agree. -/
theorem absorbed_fiber_huniq (D : Dist (DDD X Y)) (T : PFunPDS X Y) (i : ℕ)
    (xs : Vector X (i + 1)) :
    ∀ p ∈ (Dist.prod D T).support, ∀ ys ys' : Vector Y (i + 1),
      (winnerMatches (ddToDDE p.1) i xs ys ∧ gameMatches (tagFalse p.2) i ys xs) →
      (winnerMatches (ddToDDE p.1) i xs ys' ∧ gameMatches (tagFalse p.2) i ys' xs) →
      ys = ys' := by
  rintro ⟨d, t⟩ _ ys ys' ⟨hWM, hGM⟩ ⟨hWM', hGM'⟩
  -- both `yⁱ` are the output projection of the (forced) run of `ddToDDE d` vs `tagFalse t`.
  have e1 := (run_proj (ddToDDE d) (tagFalse t) i xs ys hWM hGM (le_refl (i + 1))).2
  have e2 := (run_proj (ddToDDE d) (tagFalse t) i xs ys' hWM' hGM' (le_refl (i + 1))).2
  apply Vector.toList_inj.mp
  have hmap : ys.toList.map (fun y => some (y, false)) = ys'.toList.map (fun y => some (y, false)) := by
    rw [List.take_of_length_le (show ys.toList.length ≤ i + 1 by simp)] at e1
    rw [List.take_of_length_le (show ys'.toList.length ≤ i + 1 by simp)] at e2
    rw [← e1, ← e2]
  exact List.map_injective_iff.mpr (fun a b hab => by simpa using hab) hmap

open PFunDDS in
/-- **O2 — the winner-factor marginal (the substantive lemma).** The absorbed (blind) winner's
query-schedule probability `winnerFactor (D·T̃) xⁱ` is the **`T`-marginal** of `D`'s winner factor:
`∑_{yⁱ} winnerFactor (D-as-winner) (xⁱ,yⁱ) · p^T_{Yⁱ|Xⁱ}(yⁱ,xⁱ)`. This is `T̃` absorbed into the winner
(eq. 4.40): the copying converter feeds `D` the `T`-replies, marginalizing the game's visible outputs.
Both sides are masses over `D ×ᵈ T`; the identity is the fiber decomposition (`mass_eq_tsum_of_unique`)
into the rectangle `winnerMatches (ddToDDE d) ∧ gameMatches (tagFalse t)`, then `mass_prod_and`. -/
theorem winnerFactor_absorbedWinnerDist_eq (D : Dist (DDD X Y)) (T : PFunPDS X Y) (i : ℕ)
    (xs : Vector X (i + 1)) (ys₀ : Vector Y (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1))
    (hT : TotalUpTo T (i + 1)) :
    winnerFactor (absorbedWinnerDist D T) i xs ys₀
      = ∑' ys : Vector Y (i + 1),
          winnerFactor (Dist.fTransform ddToDDE D) i xs ys * CondEquiv.massY T i ys xs := by
  unfold winnerFactor absorbedWinnerDist
  rw [Dist.mass_fTransform]
  rw [mass_eq_tsum_of_unique (Dist.prod D T)
        (fun p => winnerMatches (absorbedWinner p.1 p.2) i xs ys₀)
        (fun p ys => winnerMatches (ddToDDE p.1) i xs ys ∧ gameMatches (tagFalse p.2) i ys xs)
        (absorbed_fiber_hex D T i xs ys₀ hQ hT)
        (absorbed_fiber_huniq D T i xs)]
  refine tsum_congr fun ys => ?_
  rw [Dist.mass_prod_and D T
        (fun d => winnerMatches (ddToDDE d) i xs ys)
        (fun t => gameMatches (tagFalse t) i ys xs)]
  rw [mass_gameMatches_tagFalse T i ys xs]
  congr 1
  rw [Dist.mass_fTransform]

/-! ### Marginalizing the game's visible output: `∑_{yⁱ} massYAfalse Ŝ = massAllFalse Ŝ` -/

open PFunDDS in
/-- **Summing the not-won transcript mass over the visible outputs gives the all-false mass.** For a
fixed input schedule `xⁱ`, the game's `Y`-output transcript is *determined* by each realization, so
`∑_{yⁱ} p^{Ŝ}_{Yⁱ,Aᵢ=0|Xⁱ}(yⁱ,xⁱ) = p^{Ŝ}_{Aᵢ=0|Xⁱ}(xⁱ) = massAfalse Ŝ` (the cumulative all-prefixes-
false mass, here read at the last bit via the monotone MBO). `mass_eq_tsum_of_unique` on `Ŝ` with
`gameMatches` as the unique-per-`yⁱ` fiber of the all-false event; the all-false ↔ last-bit-false bridge
is `massAllFalse_eq_massAfalse` (no dummy `Vector Y` is needed — the `Fin (i+1)` event carries the
length). -/
theorem tsum_massYAfalse_eq_massAfalse (Shat : PFunPDS X (Y × Bool)) (hmono : MonotoneMBO Shat)
    (i : ℕ) (xs : Vector X (i + 1)) :
    ∑' ys : Vector Y (i + 1), CondEquiv.massYAfalse Shat i ys xs
      = CondEquiv.massAfalse Shat xs.toList := by
  -- the all-false event, phrased on `Fin (i+1)` so it is `Vector Y`-free
  have hfiber : ∑' ys : Vector Y (i + 1), CondEquiv.massYAfalse Shat i ys xs
      = Dist.mass Shat (fun s => ∀ k : Fin (i + 1),
          ∃ h : xs.toList.take (k.1 + 1) ∈ dom s, (output s (xs.toList.take (k.1 + 1)) h).2 = false) := by
    refine (mass_eq_tsum_of_unique Shat
        (fun s => ∀ k : Fin (i + 1),
          ∃ h : xs.toList.take (k.1 + 1) ∈ dom s, (output s (xs.toList.take (k.1 + 1)) h).2 = false)
        (fun s ys => gameMatches s i ys xs) ?_ ?_).symm
    · -- hex
      intro s _
      constructor
      · intro hall
        refine ⟨Vector.ofFn fun k : Fin (i + 1) =>
            (output s (xs.toList.take (k.1 + 1)) (hall k).choose).1, fun k => ?_⟩
        have hky : (k : ℕ) < i + 1 := by have := k.2; simpa using this
        obtain ⟨h, hb⟩ := hall ⟨k.1, hky⟩
        refine ⟨h, ?_, hb⟩
        rw [List.get_eq_getElem, Vector.getElem_toList, Vector.getElem_ofFn hky,
          output_congr s rfl h (hall ⟨k.1, hky⟩).choose]
      · rintro ⟨ys, hg⟩ k
        obtain ⟨h, _, hb⟩ := hg ⟨k.1, by have := k.2; simpa using this⟩
        exact ⟨h, hb⟩
    · -- huniq
      intro s _ ys ys' hg hg'
      apply Vector.toList_inj.mp
      apply List.ext_get (by simp)
      intro k hk hk'
      obtain ⟨h1, hv1, _⟩ := hg ⟨k, by simpa using hk⟩
      obtain ⟨h2, hv2, _⟩ := hg' ⟨k, by simpa using hk'⟩
      rw [← hv1, ← hv2, output_congr s rfl h1 h2]
  -- the all-false event equals the last-bit `massAfalse` (monotone MBO), via support congruence
  rw [hfiber, CondEquiv.massAfalse]
  refine mass_congr_support Shat fun s hs => ?_
  have hlen : xs.toList.length = i + 1 := by simp
  have hxsne : xs.toList ≠ [] := by intro hc; rw [hc] at hlen; simp at hlen
  have htake : xs.toList.take (i + 1) = xs.toList := List.take_of_length_le (le_of_eq hlen)
  constructor
  · -- forward: take the last prefix `xⁱ`
    intro hall
    obtain ⟨h, hb⟩ := hall ⟨i, by omega⟩
    refine ⟨htake ▸ h, ?_⟩
    rw [PFunDDS.output_congr s htake.symm (htake ▸ h) h]; exact hb
  · -- backward: monotone MBO ⟹ false at `xⁱ` propagates to every prefix
    rintro ⟨h, hb⟩ k
    have hpre : xs.toList.take (k.1 + 1) <+: xs.toList := List.take_prefix _ _
    have hne : xs.toList.take (k.1 + 1) ≠ [] := by
      rw [Ne, List.take_eq_nil_iff]; simp only [not_or]; exact ⟨Nat.succ_ne_zero _, hxsne⟩
    have hd : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom s := PFunDDS.prefix_closed s hpre hne h
    exact ⟨hd, PFunDDS.outputBit_false_of_isGame (hmono s hs) hpre hne hd h hb⟩

/-! ### The not-won absorption identity (the `winProbBehavior` core of O2) -/

open scoped Classical in
/-- **Summability companion to `mass_eq_tsum_of_unique`** (UPSTREAM-CANDIDATE): under the same
uniqueness hypothesis, the per-index mass family `fun p => P.mass (Q · p)` is summable. The per-`a`
indicator `fun p => if Q a p then P a else 0` is summable (`huniq` ⟹ at most one `p`), and the family
is the *finite* sum of these over `P.support`. -/
theorem summable_mass_of_unique {A ι : Type*} (P : Dist A) (Q : A → ι → Prop)
    (huniq : ∀ a ∈ P.support, ∀ p p', Q a p → Q a p' → p = p') :
    Summable (fun p => P.mass (fun a => Q a p)) := by
  have hmass : ∀ p, P.mass (fun a => Q a p)
      = ∑ a ∈ P.support, (if Q a p then P a else 0) := fun _ => rfl
  rw [show (fun p => P.mass (fun a => Q a p))
        = fun p => ∑ a ∈ P.support, (if Q a p then P a else 0) from funext hmass]
  refine summable_sum fun a ha => ?_
  by_cases h : ∃ p, Q a p
  · obtain ⟨p₀, hp₀⟩ := h
    refine summable_of_ne_finset_zero (s := {p₀}) fun p hp => ?_
    rw [if_neg fun hQ => hp (by
      simpa using huniq a (by simpa using ha) p p₀ hQ hp₀)]
  · exact summable_of_ne_finset_zero (s := ∅) fun p _ => if_neg fun hQ => h ⟨p, hQ⟩

open PFunDDS in
/-- The not-won transcript term as a rectangle mass over `W ×ᵈ G`: the conjunction
`winnerMatches (·.1) ∧ gameMatches (·.2)` (`mass_prod_and` read backwards). -/
theorem term_eq_rect_mass (W : Dist (Winner X Y)) (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)) :
    winnerFactor W i xs ys * CondEquiv.massYAfalse G i ys xs
      = (Dist.prod W G).mass
          (fun wg => winnerMatches wg.1 i xs ys ∧ gameMatches wg.2 i ys xs) := by
  rw [winnerFactor, massYAfalse_eq_mass_gameMatches,
    Dist.mass_prod_and W G (fun w => winnerMatches w i xs ys) (fun g => gameMatches g i ys xs)]

open PFunDDS in
/-- **The not-won transcript family is summable** (unconditionally). Each term is a rectangle mass
(`term_eq_rect_mass`); the matching transcript is unique per realization (`run_proj`), so
`summable_mass_of_unique` applies. -/
theorem summable_notWonTerm (W : Dist (Winner X Y)) (G : PFunPDS X (Y × Bool)) (i : ℕ) :
    Summable (fun p : Vector X (i + 1) × Vector Y (i + 1) =>
      winnerFactor W i p.1 p.2 * CondEquiv.massYAfalse G i p.2 p.1) := by
  have hrw : (fun p : Vector X (i + 1) × Vector Y (i + 1) =>
        winnerFactor W i p.1 p.2 * CondEquiv.massYAfalse G i p.2 p.1)
      = fun p => (Dist.prod W G).mass
          (fun wg => winnerMatches wg.1 i p.1 p.2 ∧ gameMatches wg.2 i p.2 p.1) :=
    funext fun p => term_eq_rect_mass W G i p.1 p.2
  rw [hrw]
  refine summable_mass_of_unique (Dist.prod W G) _ ?_
  rintro ⟨w, g⟩ _ ⟨px, py⟩ ⟨px', py'⟩ ⟨hWM, hGM⟩ ⟨hWM', hGM'⟩
  -- both transcripts are the (forced) run of `w` vs `g`
  have e1 := run_proj w g i px py hWM hGM (le_refl (i + 1))
  have e2 := run_proj w g i px' py' hWM' hGM' (le_refl (i + 1))
  have hxeq : px.toList = px'.toList := by
    have h1 := e1.1; have h2 := e2.1
    rw [List.take_of_length_le (show px.toList.length ≤ i + 1 by simp)] at h1
    rw [List.take_of_length_le (show px'.toList.length ≤ i + 1 by simp)] at h2
    rw [← h1, ← h2]
  have hyeq : py.toList = py'.toList := by
    have h1 := e1.2; have h2 := e2.2
    rw [List.take_of_length_le (show py.toList.length ≤ i + 1 by simp)] at h1
    rw [List.take_of_length_le (show py'.toList.length ≤ i + 1 by simp)] at h2
    have hmap : py.toList.map (fun y => some (y, false))
        = py'.toList.map (fun y => some (y, false)) := by rw [← h1, ← h2]
    exact List.map_injective_iff.mpr (fun a b hab => by simpa using hab) hmap
  exact Prod.ext_iff.mpr ⟨Vector.toList_inj.mp hxeq, Vector.toList_inj.mp hyeq⟩

open PFunDDS in
/-- The inner (`yⁱ`-only, at fixed `xⁱ`) not-won family is summable — the same rectangle-mass
uniqueness, indexed by `yⁱ`. -/
theorem summable_notWonTerm_inner (W : Dist (Winner X Y)) (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (xs : Vector X (i + 1)) :
    Summable (fun ys : Vector Y (i + 1) =>
      winnerFactor W i xs ys * CondEquiv.massYAfalse G i ys xs) := by
  have hrw : (fun ys : Vector Y (i + 1) =>
        winnerFactor W i xs ys * CondEquiv.massYAfalse G i ys xs)
      = fun ys => (Dist.prod W G).mass
          (fun wg => winnerMatches wg.1 i xs ys ∧ gameMatches wg.2 i ys xs) :=
    funext fun ys => term_eq_rect_mass W G i xs ys
  rw [hrw]
  refine summable_mass_of_unique (Dist.prod W G) _ ?_
  rintro ⟨w, g⟩ _ py py' ⟨hWM, hGM⟩ ⟨hWM', hGM'⟩
  have e1 := (run_proj w g i xs py hWM hGM (le_refl (i + 1))).2
  have e2 := (run_proj w g i xs py' hWM' hGM' (le_refl (i + 1))).2
  apply Vector.toList_inj.mp
  rw [List.take_of_length_le (show py.toList.length ≤ i + 1 by simp)] at e1
  rw [List.take_of_length_le (show py'.toList.length ≤ i + 1 by simp)] at e2
  have hmap : py.toList.map (fun y => some (y, false))
      = py'.toList.map (fun y => some (y, false)) := e1.symm.trans e2
  exact List.map_injective_iff.mpr (fun a b hab => by simpa using hab) hmap

/-- **`notWonProbBehavior` as an iterated transcript sum.** Fubini on the (summable) not-won family:
sum over `xⁱ` of the inner `yⁱ`-sum `∑_{yⁱ} winnerFactor W (xⁱ,yⁱ) · massYAfalse G (yⁱ,xⁱ)`. -/
theorem notWonProbBehavior_eq_tsum_tsum (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ) :
    notWonProbBehavior W G i
      = ∑' xs : Vector X (i + 1), ∑' ys : Vector Y (i + 1),
          winnerFactor W i xs ys * CondEquiv.massYAfalse G i ys xs := by
  rw [notWonProbBehavior]
  exact (summable_notWonTerm W G i).tsum_prod' (fun xs => summable_notWonTerm_inner W G i xs)

open PFunDDS in
/-- **O2 — the not-won absorption identity.** The core of eq. (4.40) at the behavior level: the not-won
probability of `D`-as-winner against the enhanced game `T̂ = gameEnhance T Ŝ` equals that of the absorbed
**blind** winner `D·T̃` against `Ŝ`. Both are iterated transcript sums (`notWonProbBehavior_eq_tsum_tsum`);
per `xⁱ` both inner sums collapse to `G(xⁱ) · p^{Ŝ}_{Aᵢ=0|Xⁱ}(xⁱ)` where
`G(xⁱ) = ∑_{yⁱ} winnerFactor(D-as-winner)(xⁱ,yⁱ) · p^T_{Yⁱ|Xⁱ}(yⁱ,xⁱ)`:
* LHS uses `massYAfalse (gameEnhance T Ŝ) = massY T · massAfalse Ŝ` (eq. 4.39 factoring + monotone MBO);
* RHS uses the winner-factor marginal (`winnerFactor_absorbedWinnerDist_eq`, the absorbed winner's
  schedule is the `T`-marginal of `D`'s) plus marginalizing `massYAfalse Ŝ` over `yⁱ`
  (`tsum_massYAfalse_eq_massAllFalse`). -/
theorem notWonProbBehavior_absorption (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ) (hmono : MonotoneMBO Shat)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1))
    (hT : TotalUpTo T (i + 1)) :
    notWonProbBehavior (Dist.fTransform ddToDDE D) (gameEnhance T Shat) i
      = notWonProbBehavior (absorbedWinnerDist D T) Shat i := by
  rw [notWonProbBehavior_eq_tsum_tsum, notWonProbBehavior_eq_tsum_tsum]
  refine tsum_congr fun xs => ?_
  -- abbreviate the common inner factor `G(xⁱ) = ∑_{yⁱ} winnerFactor(fT ddToDDE D)(xⁱ,yⁱ) · massY T(yⁱ,xⁱ)`
  set Gx : NNReal := ∑' ys : Vector Y (i + 1),
    winnerFactor (Dist.fTransform ddToDDE D) i xs ys * CondEquiv.massY T i ys xs with hGx
  -- LHS inner: massYAfalse of the enhanced game factors as `massY T · massAfalse Ŝ`
  have hLHS : (∑' ys : Vector Y (i + 1),
        winnerFactor (Dist.fTransform ddToDDE D) i xs ys
          * CondEquiv.massYAfalse (gameEnhance T Shat) i ys xs)
      = Gx * CondEquiv.massAfalse Shat xs.toList := by
    rw [hGx, ← NNReal.tsum_mul_right]
    refine tsum_congr fun ys => ?_
    rw [massYAfalse_gameEnhance, massAllFalse_eq_massAfalse Shat hmono]
    ring
  -- RHS inner: the absorbed winner factor is `Gx` (blind, ys-independent), then sum `massYAfalse Ŝ`
  have hRHS : (∑' ys : Vector Y (i + 1),
        winnerFactor (absorbedWinnerDist D T) i xs ys * CondEquiv.massYAfalse Shat i ys xs)
      = Gx * CondEquiv.massAfalse Shat xs.toList := by
    have hfac : ∀ ys : Vector Y (i + 1),
        winnerFactor (absorbedWinnerDist D T) i xs ys = Gx := fun ys => by
      rw [winnerFactor_absorbedWinnerDist_eq D T i xs ys hQ hT, hGx]
    rw [show (∑' ys : Vector Y (i + 1),
            winnerFactor (absorbedWinnerDist D T) i xs ys * CondEquiv.massYAfalse Shat i ys xs)
          = ∑' ys : Vector Y (i + 1), Gx * CondEquiv.massYAfalse Shat i ys xs from
        tsum_congr fun ys => by rw [hfac ys]]
    rw [NNReal.tsum_mul_left, tsum_massYAfalse_eq_massAfalse Shat hmono i xs]
  rw [hLHS, hRHS]

open PFunDDS in
/-- **O2 — the absorption identity (`winProb` level).** `Ŝ(D-as-winner against T̂) = Ŝ(D·T̃)`: the
winning probability of `D` against the enhanced game `T̂ = gameEnhance T Ŝ` equals that of the absorbed
blind winner `D·T̃` against `Ŝ`. Both `winProb`s reduce to `winProbBehavior` (`winProb_eq_behavior`,
using `queriesExactly_absorbedWinner` for the absorbed winner's query bound); the weights are all `1`
and the not-won masses agree (`notWonProbBehavior_absorption`).

UPSTREAM-CANDIDATE: bounded-totality form of the absorption step. This is the right reusable version
for filtered systems: the proof only needs the systems to be total up to the exact query length. -/
theorem winProb_absorption_of_totalUpTo (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hD : D.isProbDist) (hmono : MonotoneMBO Shat)
    (hSU : TotalUpTo Shat (i + 1)) (hTU : TotalUpTo T (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) :
    winProb (Dist.fTransform ddToDDE D) (gameEnhance T Shat)
      = winProb (absorbedWinnerDist D T) Shat := by
  have hGEU : TotalUpTo (gameEnhance T Shat) (i + 1) := gameEnhance_totalUpTo T Shat (i + 1) hTU hSU
  -- query bounds on the two winner supports
  have hQL : ∀ w ∈ (Dist.fTransform ddToDDE D).support, QueriesExactly w (i + 1) := by
    intro w hw; obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw; exact hQ d hd
  have hQR : ∀ w ∈ (absorbedWinnerDist D T).support, QueriesExactly w (i + 1) := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := mem_support_fTransform _ _ hw
    have hdmem : p.1 ∈ D.support := by
      have hne : (Dist.prod D T) p ≠ 0 := Finsupp.mem_support_iff.mp hp
      rw [Dist.prod_apply] at hne
      exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    exact queriesExactly_absorbedWinner p.1 p.2 i (hQ p.1 hdmem)
  rw [winProb_eq_behavior _ _ i hQL hGEU, winProb_eq_behavior _ _ i hQR hSU,
    winProbBehavior, winProbBehavior, notWonProbBehavior_absorption D Shat T i hmono hQ hTU]
  -- the leading weight·weight terms coincide (all probability distributions)
  have hwL : (Dist.fTransform ddToDDE D).weight = 1 := Dist.fTransform_isProbDist _ hD
  have hwGE : (gameEnhance T Shat).weight = 1 := gameEnhance_isProbDist T Shat hT hShat
  have hwR : (absorbedWinnerDist D T).weight = 1 := absorbedWinnerDist_isProbDist D T hD hT
  rw [hwL, hwGE, hwR, hShat]

open PFunDDS in
theorem winProb_absorption (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hD : D.isProbDist) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) :
    winProb (Dist.fTransform ddToDDE D) (gameEnhance T Shat)
      = winProb (absorbedWinnerDist D T) Shat :=
  winProb_absorption_of_totalUpTo D Shat T i hShat hT hD hmono
    (TotalUpTo_of_totalOnNonempty hStot (i + 1))
    (TotalUpTo_of_totalOnNonempty hTtot (i + 1)) hQ

/-! ## CR18 Theorem 4.17 — the all-`D` bound, per-winner form (the composable result)

The genuinely useful conclusion is the **per-winner** bound: `∆^D(S,T) ≤ Ŝ(D·T̃)`, the winning
probability of the *specific* blind game-winner `D·T̃` against `Ŝ`. `D·T̃` is blind **and** makes exactly
`i+1` queries (it replays `D`, pinned by `hQ` via `queriesExactly_absorbedWinner`), so it is precisely the
object a concrete instantiation bounds directly (e.g. for the URP-URF switching lemma,
`Ŝ(blind (q+1)-query winner) ≤ pcoll(2ⁿ, q+1)`). Taking the `Γ(bŜ)` supremum afterwards is the **lossy**
last step: the unfiltered `Γᵇ` overshoots for concrete games (a blind winner with unbounded queries wins
the collision game w.p. ≈ 1, so `Γᵇ(R̂) ≈ 1`, not a `q`-bounded quantity). So the per-winner form is the
primary theorem; the `Γ(bŜ)` form is a thin corollary that does **not** compose downstream. -/

open PFunDDS in
/-- **Bounded CR18 Theorem 4.17 — the eq. (4.40) absorption, per-winner form.**
Same per-winner absorbed bound as `theorem_4_17_condEquiv_absorbed_winProb_abstract`, but with the
tight `TotalUpTo · (i+1)` hypotheses needed by filtered systems. The proof only inspects the exact
`(i+1)`-query transcript layer, so it uses the fixed-round `massYAfalse` equality and the verdict-level
bounded replacement for `ignoreMBO_gameEnhance`.

UPSTREAM-CANDIDATE: bounded-totality absorbed Theorem-4.17 helper. -/
theorem theorem_4_17_condEquiv_absorbed_winProb_abstract_of_totalUpTo
    (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hSU : TotalUpTo Shat (i + 1)) (hTU : TotalUpTo T (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (winProb (absorbedWinnerDist D T) Shat : ℝ) := by
  have hEq : MassYAfalseEqAt Shat (gameEnhance T Shat) i :=
    fun ys xs => (massYAfalse_gameEnhance_eq_of_totalUpTo T Shat hCE hT hmono i hTU ys xs).symm
  have hGEU : TotalUpTo (gameEnhance T Shat) (i + 1) :=
    gameEnhance_totalUpTo T Shat (i + 1) hTU hSU
  have key := lemma_4_16'_mass_at D Shat (gameEnhance T Shat) i hShat
    (gameEnhance_isProbDist T Shat hT hShat) hEq hQ hSU hGEU
  have hVP :
      verdictProb D (PFunPDS.ignoreMBO (gameEnhance T Shat)) = verdictProb D T :=
    verdictProb_ignoreMBO_gameEnhance_eq_of_totalUpTo D T Shat (i + 1) hShat hQ hTU hSU
  rw [advantage, hVP] at key
  unfold advantage
  refine key.trans ?_
  have hQ' : ∀ w ∈ (Dist.fTransform ddToDDE D).support, QueriesExactly w (i + 1) := by
    intro w hw; obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw; exact hQ d hd
  have hbridge : winProb (Dist.fTransform ddToDDE D) Shat
      = winProb (Dist.fTransform ddToDDE D) (gameEnhance T Shat) := by
    rw [winProb_eq_behavior _ Shat i hQ' hSU,
      winProb_eq_behavior _ (gameEnhance T Shat) i hQ' hGEU,
      winProbBehavior_congr_mass_at _ hShat (gameEnhance_isProbDist T Shat hT hShat) hEq]
  rw [hbridge, winProb_absorption_of_totalUpTo D Shat T i hShat hT hD hmono hSU hTU hQ]

open PFunDDS in
/-- **CR18 Theorem 4.17 — the eq. (4.40) absorption, per-winner form (all `D`, the composable bound).**
If a game `Ŝ` is conditionally equivalent to `T` (`Ŝ |≡ T`, Def 4.19), the distinguishing advantage of
**any** `D` between `S = Ŝ⁻` and `T` is bounded by the winning probability of the **blind** absorbed
game-winner `D·T̃` against `Ŝ`: `∆^D(S,T) ≤ Ŝ(D·T̃)`. This is the eq. (4.40) absorption *stopping before
the `Γ(bŜ)` supremum* — Maurer's "absorbing `T̃` into the winner" (eq. 4.10), but kept at the level of
the concrete winner `D·T̃` so the bound composes with a concrete winning-probability estimate.

The proof opens exactly as `theorem_4_17_condEquiv_blind_abstract` (Lemma 4.16 mass form), bounding the
advantage by `Ŝ(D-as-winner)`; bridges (via `winProbBehavior_congr_mass`, eq. 4.39) to
`Ŝ(D-as-winner against T̂)`; and absorbs (`winProb_absorption`, the eq. 4.40 marginal
`winnerFactor_absorbedWinnerDist_eq`) to `Ŝ(D·T̃)`. Hypotheses are **exactly** those of
`theorem_4_17_condEquiv_blind_abstract` minus `hblind`: probability
distributions, monotone MBO, totality on the histories under discussion, fixed query count.

The absorbed winner `absorbedWinnerDist D T` is **blind** (`isBlindDist_absorbedWinnerDist`) and makes
exactly `i+1` queries on its support (`queriesExactly_absorbedWinner`), so it is the per-winner object
that concrete bounds (the switching lemma's `pcoll`) consume. Mirrors `ch4-closer`'s
`theorem_4_17_condEquiv_blind_winProb_abstract` shape.

**ABSTRACT HELPER (MODELING_REVIEW #3, fix F1.2).** Free-`Ŝ` form: it takes the derived game `Shat` with
property hypotheses (`hCE`/`hmono`), so it is the right *proof ingredient* but not the paper endpoint
(the statement starts after the hard modeling step). The base-object, in-statement-constructed public
Theorem 4.17 is `RandomSystems.CR18.theorem_4_17` (GameOf.lean), which sets `Ŝ := gameOf S cond`, proves
`ignoreMBO Ŝ = S`/`MonotoneMBO Ŝ`, and routes through these absorbed helpers. The crucial faithfulness
gain over `theorem_4_17_condEquiv_blind_abstract` is that **blindness is derived** here (the absorbed
winner `D·T̃` is blind for *any* `D`, CR18_LN.txt:5694), so there is **no `hblind` hypothesis on `D`**. -/
theorem theorem_4_17_condEquiv_absorbed_winProb_abstract
    (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (winProb (absorbedWinnerDist D T) Shat : ℝ) := by
  have hSU : TotalUpTo Shat (i + 1) := TotalUpTo_of_totalOnNonempty hStot (i + 1)
  have hTU : TotalUpTo T (i + 1) := TotalUpTo_of_totalOnNonempty hTtot (i + 1)
  exact theorem_4_17_condEquiv_absorbed_winProb_abstract_of_totalUpTo D Shat T i
    hShat hT hCE hmono hSU hTU hQ hD

open PFunDDS in
/-- **CR18 Theorem 4.17 (the PDF's headline `∆(S,T) ≤ Γ(bŜ)`, all `D`) — thin corollary.** The non-adaptive
maximal-game-winning-probability bound, obtained from the per-winner form
(`theorem_4_17_condEquiv_absorbed_winProb_abstract`) by the single, **lossy** step of replacing `Ŝ(D·T̃)` with the
`Γ(bŜ)` supremum (`winProb_le_blindMaxWinProb`, valid since `D·T̃` is blind, O1).

**This bound does not compose downstream.** `Γᵇ` (`blindMaxWinProb`, Def 4.20) is the **unfiltered** sup
over blind winners — no query bound — so it **overshoots** for concrete games: a blind winner with
unbounded queries wins the §4.11.3 collision game w.p. ≈ 1, hence `Γᵇ(R̂) ≈ 1`, not a `q`-bounded quantity.
Use this corollary only for the abstract headline statement; for any concrete instance (the URP-URF
switching lemma) use the **per-winner** `theorem_4_17_condEquiv_absorbed_winProb_abstract` and bound the
concrete `Ŝ(D·T̃)` directly (`D·T̃` is blind and exactly-`(i+1)`-query, e.g. `≤ pcoll(2ⁿ, i+1)`).

**ABSTRACT HELPER (MODELING_REVIEW #3, fix F1.2).** Free-`Ŝ` form (takes `Shat` with `hCE`/`hmono`),
hence the right proof ingredient but **not** the paper endpoint. Blindness is **derived** (no `hblind`),
which is the faithful improvement over `theorem_4_17_condEquiv_blind_abstract`. The `_abstract` suffix
marks its non-endpoint helper role; the base-object, in-statement-constructed public Theorem 4.17 that
calls this is `RandomSystems.CR18.theorem_4_17` (GameOf.lean). -/
theorem theorem_4_17_condEquiv_absorbed_abstract_of_totalUpTo
    (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hSU : TotalUpTo Shat (i + 1)) (hTU : TotalUpTo T (i + 1))
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ) := by
  refine (theorem_4_17_condEquiv_absorbed_winProb_abstract_of_totalUpTo D Shat T i
    hShat hT hCE hmono hSU hTU hQ hD).trans ?_
  have hAbsProb : (absorbedWinnerDist D T).isProbDist := absorbedWinnerDist_isProbDist D T hD hT
  exact_mod_cast winProb_le_blindMaxWinProb (absorbedWinnerDist D T) Shat
    (isBlindDist_absorbedWinnerDist D T) hAbsProb

open PFunDDS in
theorem theorem_4_17_condEquiv_absorbed_abstract
    (D : Dist (DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (ddToDDE d) (i + 1)) (hD : D.isProbDist) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ) := by
  exact theorem_4_17_condEquiv_absorbed_abstract_of_totalUpTo D Shat T i
    hShat hT hCE hmono
    (TotalUpTo_of_totalOnNonempty hStot (i + 1))
    (TotalUpTo_of_totalOnNonempty hTtot (i + 1)) hQ hD

end RandomSystems.CR18
