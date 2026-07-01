/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.WinProb

/-!
# CR18 Lemma 4.15 — `G ≡ᵍ H ⟹ G̅(W) = H̅(W)`, in the Dist-over-`DDS` layer

Maurer's proof, mapped to the **single** behavior layer where `massYAfalse`/`≡ᵍ`/#1/piece A live —
no RV `transcriptDist`, no cross-layer bridge:

* (4.36) game cumulative `= ∏` pre-winning — `massYAfalse_eq_prewin_prod` (reuses the Dist Lemma 3.2,
  `cumulativeBehavior_eq_behavior_prod`).
* (4.35) `P^{WG}_{XqYq,Aq=0}` factors winner·game — `Dist.mass_prod_and'` (Fintype-free), game factor
  `= massYAfalse`, via the `s⊥=s` in-domain link (`output_fullyDefined_append_of_mem`).
* "each term equal for `G≡ᵍH`" — `massYAfalse_congr_gameEquiv` (piece A).
* (4.37) `G̅(W) = 1 − Σ` terms — `winProb_add_notWonProb` + the fiber sum below.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

attribute [local instance] Classical.propDecidable

open scoped Classical in
/-- **Fiber partition of a `Dist.mass`** (UPSTREAM-CANDIDATE, generic): the mass of `R` is the sum,
over the finite set of values `f` takes on the support, of the masses of "`R` and `f · = v`". This is
how CR18 eq (4.37) sums over transcripts — `Fintype`-free (sum over the support image). -/
theorem mass_eq_sum_fiber {A B : Type*} (P : Dist A) (f : A → B) (R : A → Prop) :
    P.mass R = ∑ v ∈ P.support.image f, P.mass (fun a => R a ∧ f a = v) := by
  rw [Dist.mass, Finsupp.sum,
    ← Finset.sum_fiberwise_of_maps_to (g := f) (t := P.support.image f)
      (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Dist.mass, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hR : R a <;> by_cases hv : f a = v <;> simp [hR, hv]

/-! ### Bridge building blocks -/

/-- Compatibility wrapper over `RandomSystems.Dist.mass_prod_eq_double_sum`.
The theorem belongs to the shared distribution API; this CR18-local spelling is
kept while older Lemma-4.15 code is migrated. -/
theorem mass_prod_eq_double_sum {A B : Type*} (P : Dist A) (Q : Dist B) (R : A × B → Prop) :
    (Dist.prod P Q).mass R
      = P.sum fun a wa => Q.sum fun b wb => if R (a, b) then wa * wb else 0 := by
  exact Dist.mass_prod_eq_double_sum P Q R

open scoped Classical in
/-- **P0 — `GamePerf.winProb` is a product-distribution mass** (CR18 (4.34) read as `Pr` over the
independent winner×game experiment): `winProb win W G = (W ×ᵈ G).mass ⟦win⟧`. This is the entry to
the fiber/rectangle pipeline (`mass_eq_sum_fiber`, `mass_prod_and`) for the (4.35) bridge. -/
theorem winProb_eq_prod_mass {Winner Game : Type*} (win : Winner → Game → Prop)
    (W : Dist Winner) (G : Dist Game) :
    GamePerf.winProb win W G = (Dist.prod W G).mass (fun p => win p.1 p.2) := by
  rw [mass_prod_eq_double_sum, GamePerf.winProb]
  refine Finsupp.sum_congr fun w _ => Finsupp.sum_congr fun g _ => ?_
  by_cases h : win w g <;> simp [h, mul_comm]

/-! ### Transcript step automation (the mechanical core of the (4.35) unfolding)

The interaction unfolding is one induction on the round count; what was missing is the simp/grind
lemma set that makes each step routine. We build it here: the two step-equations (stall / append),
length, and the input/output projections of one step. Tagged `@[simp]` so the induction in the
kernel is solver-driven. -/

section TranscriptStep
open PFunDDS
variable {s : DDS X Y} {e : DDE X Y}

@[simp] theorem transcript_zero : transcript s e 0 = [] := rfl

/-- One step that **stalls** (environment stops): the transcript is unchanged. -/
@[grind] theorem transcript_succ_stall {n : ℕ} (h : e (transcript s e n)↓ᵧ = none) :
    transcript s e (n + 1) = transcript s e n := by
  simp only [transcript, h]

/-- One step that **fires** (environment queries `x`): append `(x, s⊥(inputs ++ [x]))`. -/
@[grind] theorem transcript_succ_fire {n : ℕ} {x : X} (h : e (transcript s e n)↓ᵧ = some x) :
    transcript s e (n + 1) =
      transcript s e n ++
        [(x, output s⊥ ((transcript s e n)↓ₓ ++ [x]) (by simp [fullyDefined, dom]))] := by
  simp only [transcript, h]

@[simp, grind] theorem transcriptInputs_append
    (t : List (X × Option Y)) (p : X × Option Y) : (t ++ [p])↓ₓ = t↓ₓ ++ [p.1] := by
  simp [transcriptInputs]

@[simp, grind] theorem transcriptOutputs_append
    (t : List (X × Option Y)) (p : X × Option Y) : (t ++ [p])↓ᵧ = t↓ᵧ ++ [p.2] := by
  simp [transcriptOutputs]

@[simp, grind] theorem transcriptInputs_length (t : List (X × Option Y)) :
    t↓ₓ.length = t.length := by simp [transcriptInputs]

@[simp, grind] theorem transcriptOutputs_length (t : List (X × Option Y)) :
    t↓ᵧ.length = t.length := by simp [transcriptOutputs]

/-- **`run_round h`** — the CR18-theory per-step tactic: fire one transcript round using the firing
witness `h : e …↓ᵧ = some x` (Def 3.7), then normalize the `↓ₓ`/`↓ᵧ` projections of the appended
prefix to their step normal form. This is the (4.35) unfolding, one round, as a tactic. -/
macro "run_round " h:term : tactic =>
  `(tactic| rw [transcript_succ_fire $h] <;> (try simp only [transcriptInputs_append, transcriptOutputs_append, transcriptInputs_length, transcriptOutputs_length]))

/-- The transcript prefix at step `n` has length at most `n` (it grows by ≤ 1 per step, less on a
stall). With the no-early-stall hypothesis it is exactly `n` (`transcript_length_eq` below). -/
theorem transcript_length_le (n : ℕ) : (transcript s e n).length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases h : e (transcript s e n)↓ᵧ with _ | x
      · rw [transcript_succ_stall h]; omega
      · run_round h; simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- **No early stall ⟹ length is exact**: if the environment queries on every output history shorter
than `q`, then for `n ≤ q` the transcript prefix has length exactly `n` (every step fires). The
`q`-query winner satisfies the hypothesis via `QueriesExactly`. -/
theorem transcript_length_eq {q : ℕ}
    (hq : ∀ h : List (Option Y), h.length < q → (e h).isSome) :
    ∀ {n : ℕ}, n ≤ q → (transcript s e n).length = n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hlen : (transcript s e n).length = n := ih (Nat.le_of_succ_le hn)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
        (hq (transcript s e n)↓ᵧ (by grind))
      run_round hx
      grind

/-- **Prefix coherence** (getElem-free): under no early stall, the run at step `m` is the length-`m`
prefix of the run at any later step `n`. This is the keystone that lets every per-round fact be read
off `transcript … m` directly — no dependent `getElem`, so none of the `motive is not type correct`
walls. -/
theorem transcript_take {q : ℕ}
    (hq : ∀ h : List (Option Y), h.length < q → (e h).isSome) :
    ∀ {m n : ℕ}, m ≤ n → n ≤ q → (transcript s e n).take m = transcript s e m := by
  intro m n
  induction n with
  | zero => intro hm _; obtain rfl : m = 0 := Nat.le_zero.mp hm; simp
  | succ n ih =>
      intro hm hn
      have hlenn : (transcript s e n).length = n := transcript_length_eq hq (Nat.le_of_succ_le hn)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
        (hq (transcript s e n)↓ᵧ (by rw [transcriptOutputs_length, hlenn]; omega))
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [transcript_succ_fire hx, List.take_append_of_le_length (by rw [hlenn]; exact hmn)]
        exact ih hmn (Nat.le_of_succ_le hn)
      · obtain rfl : m = n + 1 := le_antisymm hm hge
        exact List.take_of_length_le (transcript_length_eq hq hn).le

/-- **Freeze after stop**: once the environment stalls at step `q` (e.g. the `q`-query winner has made
all its queries), the transcript never grows again — `transcript m = transcript q` for all `m ≥ q`.
The other half of the query bound (with `transcript_length_eq`), used to rule out wins past round `q`. -/
theorem transcript_freeze {q : ℕ} (hstop : e (transcript s e q)↓ᵧ = none) :
    ∀ {m : ℕ}, q ≤ m → transcript s e m = transcript s e q := by
  intro m
  induction m with
  | zero => intro hm; obtain rfl : q = 0 := Nat.le_zero.mp hm; rfl
  | succ m ih =>
      intro hm
      rcases Nat.lt_or_ge q (m + 1) with h | h
      · have hmq : q ≤ m := Nat.lt_succ_iff.mp h
        rw [transcript_succ_stall (by rw [ih hmq]; exact hstop), ih hmq]
      · obtain rfl : m + 1 = q := le_antisymm h hm; rfl

end TranscriptStep

/-! ### The behavior-side winning probability (Maurer's primitive)

Maurer never runs the operational interaction for Lemma 4.15: his primitive is the **transcript
distribution** (4.35)/(4.37). We follow him — define the winning probability of `W` against `G` by
the transcript-distribution sum, in which `G` enters **only** through `massYAfalse G` (the game
factor `p^G_{Yⁱ,Aᵢ=0|Xⁱ}`). On this primitive Lemma 4.15 is immediate: substitute the pre-winning
congruence `massYAfalse_congr_gameEquiv` (piece A) under the sum.

The connection back to the **operational** winning probability (`winProb`, via `winsDDS`, Def 3.23)
is the single bridge theorem `notWonProb_eq_behavior` — the (4.35) factorization that decouples the
adaptive interleaving. It is mandatory for soundness (otherwise `winProbBehavior` is a different
number wearing the name) and is proved below from the isolated fiber kernel, not assumed away. -/

/-- **Winner consistency** with a transcript `(xⁱ, yⁱ)` (CR18 (4.35), winner side): the deterministic
winner `w` would produce exactly the query sequence `xⁱ` when fed the outputs `yⁱ⁻¹`. The `k`-th query
`xₖ₊₁ = w(y₁,…,yₖ)` reads the first `k` outputs (not the last `yᵢ₊₁`); the winner reads only `Y`, never
the MBO bit (Def 3.23), so the history is the plain `Option Y` list `(yⁱ.take k).map some`. A condition
on `w` **alone** — this is what makes the (4.35) event a rectangle. -/
def winnerMatches (w : PFunDDS.Winner X Y) (i : ℕ)
    (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)) : Prop :=
  ∀ k : Fin xs.toList.length,
    w ((ys.toList.take k.1).map some) = some (xs.toList.get k)

/-- **Game consistency** with a transcript `(xⁱ, yⁱ)` (CR18 (4.35), game side): the deterministic game
`g`, on each input prefix `xᵏ⁺¹`, outputs `yₖ₊₁` with MBO bit `false`. This is **exactly** the predicate
inside `CondEquiv.massYAfalse` (so `G.mass (gameMatches · ) = massYAfalse G`, definitionally) — a
condition on `g` **alone**. -/
def gameMatches (g : PFunDDS.DDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) : Prop :=
  ∀ k : Fin ys.toList.length,
    ∃ h : xs.toList.take (k.1 + 1) ∈ PFunDDS.dom g,
      (PFunDDS.output g (xs.toList.take (k.1 + 1)) h).1 = ys.toList.get k ∧
      (PFunDDS.output g (xs.toList.take (k.1 + 1)) h).2 = false

/-- The game factor `massYAfalse G` is the mass of `gameMatches` (holds by definition — `gameMatches`
*is* `massYAfalse`'s event). This is the definitional hinge of the (4.35) rectangle's game side. -/
theorem massYAfalse_eq_mass_gameMatches (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (ys : Vector Y (i + 1)) (xs : Vector X (i + 1)) :
    CondEquiv.massYAfalse G i ys xs = Dist.mass G (fun g => gameMatches g i ys xs) :=
  rfl

/-- **The winner factor** `p^W_{Xⁱ|Yⁱ⁻¹}(xⁱ, yⁱ⁻¹)` of CR18 (4.35): the probability, over the random
choice of deterministic winner `w ← W`, that `w` is consistent with `(xⁱ, yⁱ)` (`winnerMatches`).
Depends on `W` alone — not on the game. -/
noncomputable def winnerFactor (W : Dist (PFunDDS.Winner X Y)) (i : ℕ)
    (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)) : NNReal :=
  Dist.mass W (fun w => winnerMatches w i xs ys)

/-- **CR18 (4.35)+(4.37), behavior side**: the not-won probability of winner `W` against game `G`
(for a winner making `i + 1` queries), as the transcript-distribution sum
`∑_{xⁱ,yⁱ} p^W_{Xⁱ|Yⁱ⁻¹}(xⁱ,yⁱ⁻¹) · p^G_{Yⁱ,Aᵢ=0|Xⁱ}(yⁱ,xⁱ)`. The game `G` enters **only** through
`massYAfalse G` (the game factor), which is the entire point: Lemma 4.15 follows by congruence of
that factor. The sum is over all transcripts as a `tsum` (the carriers `X`, `Y` may be infinite;
only finitely many transcripts have nonzero winner factor). -/
noncomputable def notWonProbBehavior (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ) : NNReal :=
  ∑' p : Vector X (i + 1) × Vector Y (i + 1),
    winnerFactor W i p.1 p.2 * CondEquiv.massYAfalse G i p.2 p.1

/-- **CR18 (4.34)/(4.37), behavior side**: the winning probability of `W` against `G`, as
`weight·weight − notWonProbBehavior` (`= 1 − Σ…` for probability distributions). This is Maurer's
`G(W)` built on the transcript-distribution primitive — `G` enters only via `massYAfalse G`. -/
noncomputable def winProbBehavior (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ) : NNReal :=
  W.weight * G.weight - notWonProbBehavior W G i

/-- A winner `w` **makes exactly `q` queries**: it issues a query (`isSome`) on every output history
shorter than `q`, and stops (`⊣ = none`) on every history of length `≥ q`. This is Maurer's "winner
making a fixed number `q` of queries". The *exactness* matters: with only an upper bound, runs that
halt early have **no** length-`q` transcript, so the `(i+1)`-transcript sum would under-count the
not-won mass and the bridge below would be **false**. (Exactly-`q` is the standard WLOG, the MBO being
monotone.) -/
def QueriesExactly (w : PFunDDS.Winner X Y) (q : ℕ) : Prop :=
  (∀ h : List (Option Y), h.length < q → (w h).isSome) ∧
  (∀ h : List (Option Y), q ≤ h.length → w h = none)

/-- **`[q]`-bounded totality** — the faithful game-side query bound (CR18 §3.4.3, the filter `[q]`).
Every realization in `G`'s support is defined on every **nonempty query history of length `≤ q`**.
This is exactly the domain of a `[q]`-filtered total game (`PFunDDS.filterQueries q`, below): the bridge
only ever inspects prefixes of length `≤ q`, so it needs definedness only there — *not* the global
`CondEquiv.TotalOnNonempty` (total on all histories, which a filtered game fails). Weaker hypothesis,
same proof. -/
def TotalUpTo (G : PFunPDS X Y) (q : ℕ) : Prop :=
  ∀ g ∈ G.support, ∀ xs : List X, xs ≠ [] → xs.length ≤ q → xs ∈ PFunDDS.dom g

/-- Global totality (Maurer's "defined on the histories under discussion") implies the `[q]`-bounded
form, for every `q` — so the relaxed bridge subsumes the old one. -/
theorem TotalUpTo_of_totalOnNonempty {G : PFunPDS X Y} (h : CondEquiv.TotalOnNonempty G) (q : ℕ) :
    TotalUpTo G q := fun g hg xs hne _ => h g hg xs hne

/-- On a `q`-bounded-total system, the `T`-side normalizer is the full weight for every nonempty
history of length at most `q`.

UPSTREAM-CANDIDATE: bounded form of `CondEquiv.massDom_eq_weight_of_totalOnNonempty`; this is the
right normalizer for filtered systems, which are intentionally not globally total. -/
theorem massDom_eq_weight_of_totalUpTo (T : PFunPDS X Y) {q : ℕ}
    (hTot : TotalUpTo T q) {xs : List X} (hxs : xs ≠ []) (hlen : xs.length ≤ q) :
    CondEquiv.massDom T xs = T.weight := by
  unfold CondEquiv.massDom Dist.mass Dist.weight
  refine Finsupp.sum_congr fun t ht => ?_
  rw [if_pos (hTot t ht xs hxs hlen)]

/-- On a probability distribution that is total up to `q`, the `T`-side normalizer is `1` for every
nonempty history of length at most `q`. -/
theorem massDom_eq_one_of_totalUpTo (T : PFunPDS X Y) {q : ℕ}
    (hT : T.isProbDist) (hTot : TotalUpTo T q) {xs : List X}
    (hxs : xs ≠ []) (hlen : xs.length ≤ q) :
    CondEquiv.massDom T xs = 1 := by
  rw [massDom_eq_weight_of_totalUpTo T hTot hxs hlen]
  exact hT

/-- **`mass ≠ 0 ⟹ witness on the support`** for a pushforward (UPSTREAM-CANDIDATE): every element of
`(fTransform f X).support` is `f` of some support element (`fTransform = Finsupp.mapDomain`). -/
theorem mem_support_fTransform {A B : Type*} (f : A → B) (X : Dist A) {b : B}
    (hb : b ∈ (Dist.fTransform f X).support) : ∃ a ∈ X.support, f a = b := by
  classical
  have hsub : (Dist.fTransform f X).support ⊆ X.support.image f := Finsupp.mapDomain_support
  simpa using hsub hb

/-! The canonical `[q]` filter now lives next to the objects it acts on:
`PFunDDS.filterQueries` in `PFunDDS.lean`, and the PDS pushforward
`PFunPDS.filterQueries` in `PDS.lean`. Lemma 4.15 only uses that operation. -/

/-- **The `[q]`-filtered total game satisfies the bridge's bounded-totality hypothesis.** This closes
the loop: applying Maurer's `[q]` filter to a total game produces exactly a `TotalUpTo · q` game — so
the relaxed bridge (`notWonProb_eq_behavior` with `TotalUpTo G (i+1)`) applies to `[i+1]`-filtered
games, the idiomatic objects of CR18 §4.10/§5/§6 (`Γ([q]G)`). -/
theorem totalUpTo_filterQueries {G : PFunPDS X Y} (q : ℕ) (hG : CondEquiv.TotalOnNonempty G) :
    TotalUpTo (⌈q⌉ G) q := by
  intro g' hg' xs hne hlen
  obtain ⟨g, hg, rfl⟩ := mem_support_fTransform _ _ hg'
  exact (PFunDDS.mem_dom_filterQueries q g xs).mpr ⟨hG g hg xs hne, hlen⟩

section RunCharacterization
open PFunDDS

/-- List helper: `l.take (m+1) = l.take m ++ [l.get ⟨m,h⟩]` (one element peeled off the end of a
prefix). The bridge between the round-indexed `take (k+1)` of `gameMatches` and the append step. -/
theorem take_succ_get' {α : Type*} (l : List α) (m : ℕ) (h : m < l.length) :
    l.take (m + 1) = l.take m ++ [l.get ⟨m, h⟩] := by
  rw [List.get_eq_getElem, List.take_succ, List.getElem?_eq_getElem h]
  rfl

/-- **The interaction unfolding (CR18 (4.35), forward).** If `w` is consistent with `(xⁱ,yⁱ)`
(`winnerMatches`) and `g` is consistent with all-`false` MBO (`gameMatches`), then the run is *forced*:
at every round `m ≤ i+1` its input projection is `xⁱ.take m` and its output projection is
`yⁱ.take m` tagged with `some (·, false)`. One induction, solver-driven by the step lemmas; firing is
supplied by `winnerMatches` (no separate query-bound needed here). -/
theorem run_proj (w : Winner X Y) (g : DDS X (Y × Bool)) (i : ℕ)
    (xs : Vector X (i + 1)) (ys : Vector Y (i + 1))
    (hWM : winnerMatches w i xs ys) (hGM : gameMatches g i ys xs) :
    ∀ {m : ℕ}, m ≤ i + 1 →
      (transcript g (winnerView w) m)↓ₓ = xs.toList.take m ∧
      (transcript g (winnerView w) m)↓ᵧ
        = (ys.toList.take m).map (fun y => some (y, false)) := by
  have hxlen : xs.toList.length = i + 1 := by simp
  have hylen : ys.toList.length = i + 1 := by simp
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ m ih =>
      intro hm
      obtain ⟨ihx, ihy⟩ := ih (Nat.le_of_succ_le hm)
      have hmlt : m < i + 1 := hm
      have hmx : m < xs.toList.length := by omega
      have hmy : m < ys.toList.length := by omega
      -- the step fires, with query `xₘ₊₁ = xs[m]`
      have hx : winnerView w (transcript g (winnerView w) m)↓ᵧ
          = some (xs.toList.get ⟨m, hmx⟩) := by
        show w (((transcript g (winnerView w) m)↓ᵧ).map (Option.map Prod.fst)) = _
        rw [ihy]
        simp only [List.map_map]
        have hcomp : ((Option.map Prod.fst) ∘ (fun y : Y => some (y, false))) = some := by
          funext y; simp
        rw [hcomp]
        exact hWM ⟨m, hmx⟩
      -- game answer at this round, via gameMatches and s⊥ = s
      obtain ⟨hdomg, hval1, hval2⟩ := hGM ⟨m, hmy⟩
      have hsucc : xs.toList.take (m + 1) = xs.toList.take m ++ [xs.toList.get ⟨m, hmx⟩] :=
        take_succ_get' _ _ hmx
      have hl : xs.toList.take m ∈ dom g ∨ xs.toList.take m = [] := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · right; subst hm0; simp
        · left
          have hpre : xs.toList.take m <+: xs.toList.take (m + 1) := by
            rw [hsucc]; exact List.prefix_append _ _
          have hne : xs.toList.take m ≠ [] := by
            have : 0 < (xs.toList.take m).length := by rw [List.length_take]; omega
            exact List.ne_nil_of_length_pos this
          exact prefix_closed g hpre hne (hsucc ▸ hdomg)
      have hnext : xs.toList.take m ++ [xs.toList.get ⟨m, hmx⟩] ∈ dom g := hsucc ▸ hdomg
      have hnext' : (transcript g (winnerView w) m)↓ₓ ++ [xs.toList.get ⟨m, hmx⟩] ∈ dom g := by
        rw [ihx]; exact hnext
      have hl' : (transcript g (winnerView w) m)↓ₓ ∈ dom g ∨
          (transcript g (winnerView w) m)↓ₓ = [] := by rw [ihx]; exact hl
      rw [transcript_succ_fire hx]
      refine ⟨?_, ?_⟩
      · rw [transcriptInputs_append, ihx]; exact hsucc.symm
      · rw [transcriptOutputs_append, ihy, take_succ_get' ys.toList m hmy, List.map_append]
        simp only [List.map_cons, List.map_nil]
        congr 1
        rw [output_fullyDefined_append_of_mem g _ _ hl' hnext',
          output_congr g (by rw [ihx]; exact hsucc.symm) hnext' hdomg]
        exact congrArg (fun z => [some z]) (Prod.ext_iff.mpr ⟨hval1, hval2⟩)

/-- **The interaction unfolding (CR18 (4.35), backward).** For a `q = i+1`-query winner (`hsome`)
against a **total** game (`hgtot`, every nonempty query history is in `dom g` — Maurer's "defined on
the histories under discussion") that the winner does **not** win, the run *is* a matching transcript:
there exist `xs, ys` with `winnerMatches w xs ys` and `gameMatches g ys xs`. Reads the run off
round-by-round (mirror of `run_proj`). The game-totality is essential — a partial game can produce a
`none`-output `¬won` run with no matching transcript. -/
theorem run_to_matches (w : Winner X Y) (g : DDS X (Y × Bool)) (i : ℕ)
    (hsome : ∀ h : List (Option (Y × Bool)), h.length < i + 1 → (winnerView w h).isSome)
    (hgtot : ∀ xs : List X, xs ≠ [] → xs.length ≤ i + 1 → xs ∈ dom g)
    (hnwin : ¬ winsDDS w g) :
    ∃ (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)),
      winnerMatches w i xs ys ∧ gameMatches g i ys xs := by
  -- List-level run structure with the per-round match facts, built by induction.
  have hP : ∀ m, m ≤ i + 1 → ∃ (xl : List X) (yl : List Y),
      xl.length = m ∧ yl.length = m ∧
      (transcript g (winnerView w) m)↓ₓ = xl ∧
      (transcript g (winnerView w) m)↓ᵧ = yl.map (fun y => some (y, false)) ∧
      (∀ k, k < m → w ((yl.take k).map some) = xl[k]?) ∧
      (∀ k, k < m → ∃ h : xl.take (k + 1) ∈ dom g,
          (output g (xl.take (k + 1)) h).2 = false ∧
            some (output g (xl.take (k + 1)) h).1 = yl[k]?) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨[], [], rfl, rfl, rfl, rfl, by simp, by simp⟩
    | succ m ih =>
        intro hm
        obtain ⟨xl, yl, hxl, hyl, hpx, hpy, hwm, hgm⟩ := ih (Nat.le_of_succ_le hm)
        have hmlt : m < i + 1 := hm
        -- the step fires with query `xm`
        obtain ⟨xm, hxm⟩ : ∃ xm, winnerView w (transcript g (winnerView w) m)↓ᵧ = some xm :=
          Option.isSome_iff_exists.mp (hsome _ (by rw [hpy]; simpa [hyl] using hmlt))
        have hwq : w (yl.map fun y => some y) = some xm := by
          have h := hxm; rw [hpy] at h
          simpa [winnerView, List.map_map, Function.comp] using h
        have hstep := transcript_succ_fire hxm
        -- the game answer at this round, defined by totality
        have hl : xl ∈ dom g ∨ xl = [] := by
          rcases eq_or_ne xl [] with h | h
          · exact Or.inr h
          · exact Or.inl (hgtot xl h (by rw [hxl]; omega))
        have hnext : xl ++ [xm] ∈ dom g :=
          hgtot _ (by simp) (by simp only [List.length_append, List.length_cons,
            List.length_nil, hxl]; omega)
        have houtdef : output g⊥ (xl ++ [xm]) (by simp [fullyDefined, dom])
            = some (output g (xl ++ [xm]) hnext) :=
          output_fullyDefined_append_of_mem g xl xm hl hnext
        -- not winning forces the new MBO bit to be `false`
        have hbf : (output g (xl ++ [xm]) hnext).2 = false := by
          by_contra hbt
          rw [Bool.not_eq_false] at hbt
          refine hnwin ⟨m + 1, (output g (xl ++ [xm]) hnext).1, ?_⟩
          rw [hstep, transcriptOutputs_append, hpx, houtdef]
          exact List.mem_append.mpr (Or.inr (by
            simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact congrArg some (Prod.ext rfl hbt.symm)))
        refine ⟨xl ++ [xm], yl ++ [(output g (xl ++ [xm]) hnext).1],
          by simp [hxl], by simp [hyl], ?_, ?_, ?_, ?_⟩
        · rw [hstep, transcriptInputs_append, hpx]
        · rw [hstep, transcriptOutputs_append, hpx, hpy, houtdef]
          simp only [List.map_append, List.map_cons, List.map_nil]
          exact congrArg (fun z => yl.map (fun y => some (y, false)) ++ [z])
            (congrArg some (Prod.ext rfl hbf))
        · intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]
            exact hwm k hk'
          · rw [List.take_left' hyl, List.getElem?_append_right (le_of_eq hxl), hxl,
              Nat.sub_self, List.getElem?_cons_zero]
            simpa using hwq
        · intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
          · rw [show (xl ++ [xm]).take (k + 1) = xl.take (k + 1) from
                List.take_append_of_le_length (by omega),
              List.getElem?_append_left (by omega)]
            exact hgm k hk'
          · rw [show (xl ++ [xm]).take (k + 1) = xl ++ [xm] from
                List.take_of_length_le (by simp [hxl]),
              List.getElem?_append_right (le_of_eq hyl), hyl, Nat.sub_self,
              List.getElem?_cons_zero]
            exact ⟨hnext, hbf, rfl⟩
  -- package at m = i+1
  obtain ⟨xl, yl, hxl, hyl, _, _, hwm, hgm⟩ := hP (i + 1) (le_refl _)
  have hxs : (⟨xl.toArray, by simp [hxl]⟩ : Vector X (i + 1)).toList = xl := by
    simp [Vector.toList]
  have hys : (⟨yl.toArray, by simp [hyl]⟩ : Vector Y (i + 1)).toList = yl := by
    simp [Vector.toList]
  refine ⟨⟨xl.toArray, by simp [hxl]⟩, ⟨yl.toArray, by simp [hyl]⟩, ?_, ?_⟩
  · intro k
    have hkx : (k : ℕ) < xl.length := by simpa [hxs] using k.2
    have hv := hwm k.1 (by omega)
    rw [List.getElem?_eq_getElem hkx] at hv
    simpa [hxs, hys, List.get_eq_getElem] using hv
  · intro k
    have hky : (k : ℕ) < yl.length := by simpa [hys] using k.2
    obtain ⟨h, hb, hv⟩ := hgm k.1 (by omega)
    rw [List.getElem?_eq_getElem hky] at hv
    refine ⟨by simpa [hxs] using h, ?_, by simpa [hxs] using hb⟩
    simp only [hys, hxs, List.get_eq_getElem]
    exact Option.some_inj.mp hv

end RunCharacterization

open scoped Classical in
/-- **Measure assembly engine** (UPSTREAM-CANDIDATE, generic): if on the support each `R a` is
equivalent to a *unique* index `p` with `Q a p`, then `P.mass R = ∑' p, P.mass (Q · p)`. The finitary
fiber identity behind CR18 (4.37) — the not-won mass equals the sum over transcripts of the
per-transcript mass. All the `tsum` mechanics live here, once. -/
theorem mass_eq_tsum_of_unique {A ι : Type*} (P : Dist A)
    (R : A → Prop) (Q : A → ι → Prop)
    (hex : ∀ a ∈ P.support, (R a ↔ ∃ p, Q a p))
    (huniq : ∀ a ∈ P.support, ∀ p p', Q a p → Q a p' → p = p') :
    P.mass R = ∑' p, P.mass (fun a => Q a p) := by
  classical
  have hfun_pos : ∀ a ∈ P.support, ∀ p₀, Q a p₀ →
      (fun p => if Q a p then P a else 0) = (fun p => if p = p₀ then P a else 0) := by
    intro a ha p₀ hp₀
    funext p
    by_cases hp : Q a p
    · rw [if_pos hp, if_pos (huniq a ha p p₀ hp hp₀)]
    · rw [if_neg hp, if_neg (fun he => hp (by rw [he]; exact hp₀))]
  have hinner : ∀ a ∈ P.support,
      (∑' p, (if Q a p then P a else 0)) = (if R a then P a else 0) := by
    intro a ha
    by_cases h : ∃ p, Q a p
    · obtain ⟨p₀, hp₀⟩ := h
      rw [hfun_pos a ha p₀ hp₀, tsum_ite_eq, if_pos ((hex a ha).mpr ⟨p₀, hp₀⟩)]
    · have hz : (fun p => if Q a p then P a else 0) = (fun _ => (0 : NNReal)) := by
        funext p; rw [if_neg (fun hp => h ⟨p, hp⟩)]
      rw [hz, tsum_zero, if_neg (fun hr => h ((hex a ha).mp hr))]
  have hsum : ∀ a ∈ P.support, Summable (fun p => if Q a p then P a else 0) := by
    intro a ha
    by_cases h : ∃ p, Q a p
    · obtain ⟨p₀, hp₀⟩ := h
      rw [hfun_pos a ha p₀ hp₀]
      exact summable_of_ne_finset_zero (s := {p₀}) (fun p hp => if_neg (by simpa using hp))
    · have hz : (fun p => if Q a p then P a else 0) = (fun _ => (0 : NNReal)) := by
        funext p; rw [if_neg (fun hp => h ⟨p, hp⟩)]
      rw [hz]; exact summable_zero
  have hmassR : P.mass R = ∑ a ∈ P.support, (if R a then P a else 0) := rfl
  have hmassQ : ∀ p, P.mass (fun a => Q a p) = ∑ a ∈ P.support, (if Q a p then P a else 0) :=
    fun _ => rfl
  rw [hmassR,
    show (∑' p, P.mass (fun a => Q a p))
        = ∑' p, ∑ a ∈ P.support, (if Q a p then P a else 0) from tsum_congr hmassQ,
    Summable.tsum_finsetSum hsum]
  exact Finset.sum_congr rfl fun a ha => (hinner a ha).symm

open PFunDDS in
/-- **The bridge kernel (CR18 (4.35)).**

The operational not-won probability fibers over transcripts into the **rectangle** events: reaching a
fixed length-`(i+1)` transcript `(xⁱ,yⁱ)` un-won is the conjunction of `winnerMatches` (a fact about
`w` alone) and `gameMatches` (a fact about `g` alone). This is the entire operational content of
(4.35): unfold the `(i+1)`-round adaptive run (`winsDDS`, Def 3.23) and decouple the interleaving.
Uses exactly-`(i+1)` queries (`hW`). Everything *after* this — the actual factorization into the
winner factor times `massYAfalse` — is the elementary `mass_prod_and` (proven, below).

Isolated here as the pure interaction unfolding; needed once, reused for §4.10.3. Mandatory for
soundness (otherwise `winProbBehavior` is disconnected from game-winning). -/
theorem notWonProb_eq_fiber (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (hW : ∀ w ∈ W.support, QueriesExactly w (i + 1))
    (hG : TotalUpTo G (i + 1)) :
    notWonProb W G =
      ∑' p : Vector X (i + 1) × Vector Y (i + 1),
        (Dist.prod W G).mass
          (fun wg => winnerMatches wg.1 i p.1 p.2 ∧ gameMatches wg.2 i p.2 p.1) := by
  rw [notWonProb, winProb_eq_prod_mass]
  refine mass_eq_tsum_of_unique (Dist.prod W G) (fun wg => ¬ winsDDS wg.1 wg.2)
    (fun wg (p : Vector X (i + 1) × Vector Y (i + 1)) =>
      winnerMatches wg.1 i p.1 p.2 ∧ gameMatches wg.2 i p.2 p.1) ?_ ?_
  · -- hex: on the support, `¬ winsDDS` ↔ ∃ a matching transcript (the existence characterization).
    rintro ⟨w, g⟩ hwg
    have hwmem : w ∈ W.support := by
      have : (Dist.prod W G) (w, g) ≠ 0 := Finsupp.mem_support_iff.mp hwg
      rw [Dist.prod_apply] at this
      exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul this)
    have hQE : QueriesExactly w (i + 1) := hW w hwmem
    -- the winner queries through round `i+1` (`isSome`) and stops after (`= none`), lifted to `winnerView`
    have hsome : ∀ h : List (Option (Y × Bool)), h.length < i + 1 →
        (PFunDDS.winnerView w h).isSome := by
      intro h hh; exact hQE.1 _ (by rwa [List.length_map])
    have hlen : (PFunDDS.transcript g (PFunDDS.winnerView w) (i + 1)).length = i + 1 :=
      transcript_length_eq hsome (le_refl (i + 1))
    have hstop : PFunDDS.winnerView w (PFunDDS.transcript g (PFunDDS.winnerView w) (i + 1))↓ᵧ = none :=
      hQE.2 _ (by simp [hlen])
    constructor
    · -- mp: `¬ winsDDS` → ∃ matching transcript  (BACKWARD extraction, via `run_to_matches`).
      -- Game-totality (Maurer's "defined on the histories under discussion") is what makes it true;
      -- without it a partial game gives a `none`-output `¬won` run with no matching transcript.
      intro hnwin
      have hgmem : g ∈ G.support := by
        have hne : (Dist.prod W G) (w, g) ≠ 0 := Finsupp.mem_support_iff.mp hwg
        rw [Dist.prod_apply] at hne
        exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
      obtain ⟨xs, ys, hWM, hGM⟩ := run_to_matches w g i hsome (hG g hgmem) hnwin
      exact ⟨(xs, ys), hWM, hGM⟩
    · -- mpr: ∃ matching transcript → `¬ winsDDS`  (FORWARD, via run_proj + freeze)
      rintro ⟨⟨px, py⟩, hWM, hGM⟩ ⟨n, y, hmem⟩
      have hmem' : some (y, true)
          ∈ (PFunDDS.transcript g (PFunDDS.winnerView w) (min n (i + 1)))↓ᵧ := by
        rcases Nat.lt_or_ge n (i + 1) with hn | hn
        · rwa [min_eq_left (le_of_lt hn)]
        · rw [min_eq_right hn]
          rwa [transcript_freeze hstop hn] at hmem
      rw [(run_proj w g i px py hWM hGM (min_le_right n (i + 1))).2] at hmem'
      obtain ⟨y', _, hy'⟩ := List.mem_map.mp hmem'
      exact absurd hy' (by simp)
  · -- huniq: a matching transcript is unique — both equal the (forced) run, via `run_proj`.
    rintro ⟨w, g⟩ _ ⟨px, py⟩ ⟨px', py'⟩ ⟨hWM, hGM⟩ ⟨hWM', hGM'⟩
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

/-- **The bridge (CR18 (4.35)): operational `notWonProb` = behavior `notWonProbBehavior`.** The
algebraic half — *proven* — of the factorization: each transcript's rectangle mass factors via
`mass_prod_and` into `winnerFactor · massYAfalse`. The only operational input is the fiber kernel
`notWonProb_eq_fiber` (the isolated interaction unfolding). With that kernel, the bridge is real. -/
theorem notWonProb_eq_behavior (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (hW : ∀ w ∈ W.support, QueriesExactly w (i + 1))
    (hG : TotalUpTo G (i + 1)) :
    notWonProb W G = notWonProbBehavior W G i := by
  rw [notWonProb_eq_fiber W G i hW hG, notWonProbBehavior]
  refine tsum_congr fun p => ?_
  rw [Dist.mass_prod_and W G (fun w => winnerMatches w i p.1 p.2)
        (fun g => gameMatches g i p.2 p.1)]
  rw [winnerFactor, massYAfalse_eq_mass_gameMatches]

/-- **Operational `winProb` = behavior `winProbBehavior`** — corollary of the bridge plus the
elementary `winProb_add_notWonProb`. This is a genuine derivation from the fiber kernel, so the
operational and behavior models are joined here. -/
theorem winProb_eq_behavior (W : Dist (PFunDDS.Winner X Y))
    (G : PFunPDS X (Y × Bool)) (i : ℕ)
    (hW : ∀ w ∈ W.support, QueriesExactly w (i + 1))
    (hG : TotalUpTo G (i + 1)) :
    winProb W G = winProbBehavior W G i := by
  unfold winProbBehavior
  rw [← notWonProb_eq_behavior W G i hW hG]
  exact eq_tsub_of_add_eq (winProb_add_notWonProb W G)

/-- **CR18 Lemma 4.15** (behavior primitive), `G ≡ᵍ H ⟹ G(W) = H(W)` — *immediate*. On Maurer's
transcript-distribution primitive the game enters only through `massYAfalse`, so the whole proof is
the pre-winning congruence (piece A) substituted termwise under the `tsum`. No interaction-unfolding,
no MBO machinery: exactly Maurer's three-line argument, with (4.35)/(4.36)/(4.37) discharged by the
definition and `massYAfalse_congr_gameEquiv`. -/
theorem winProbBehavior_congr_gameEquiv (W : Dist (PFunDDS.Winner X Y))
    {G H : PFunPDS X (Y × Bool)} (hG : G.isProbDist) (hH : H.isProbDist)
    (hGH : G ≡ᵍ H) (i : ℕ) :
    winProbBehavior W G i = winProbBehavior W H i := by
  have hGw : G.weight = 1 := hG
  have hHw : H.weight = 1 := hH
  unfold winProbBehavior notWonProbBehavior
  rw [hGw, hHw]
  congr 1
  refine tsum_congr fun p => ?_
  rw [massYAfalse_congr_gameEquiv hG hH hGH p.2 p.1]

end RandomSystems.CR18
