/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CBCMAC

/-!
# CBC-MAC beyond the birthday bound in `ℓ` — structure graphs via conditional equivalence

The Jha–Nandi route (ePrint 2016/161, correcting BPR05's structure-graph analysis): the
CBC-MAC bound `𝒪(q²ℓ/2ⁿ)` — *linear* in the block length — in the CR18
conditional-equivalence frame.

* **The internal structure graph** of a message set under a round function `f`: the vertices
  are the *internal* chaining values (the states before each block — the MACs are excluded),
  the inputs are the distinct *internal* round-function inputs (the terminal edges are
  excluded), and an **accident** is a chance vertex-collision — `#inputs + 1 − #vertices`.
  A repeated input (a *forced* collision) is not an accident: it does not grow `#inputs`.
  Internality is what makes the MBO **output-blind**: the event is a function of `f` at the
  internal inputs only, so the terminal re-randomisation (`cbcShift`) fixes it — counting the
  MACs as vertices would couple the conditioning to the outputs and falsify the conditional
  equivalence.  The graph is carried as `Finset` cardinalities: the statements need counting,
  not adjacency theory.
* **The tolerant MBO** `cbcGraphBad`: unlike `cbcBad` (any nontrivial input collision), only
  `≥ 2` internal accidents or a *terminal-involving* input collision are bad.  A single
  internal accident is tolerated — this is exactly the `ℓ`-linear win (`q·qL`
  terminal-involving site pairs instead of all `(qL)²`).
* **Conditional equivalence** (`cbcGraphGame_condEquiv`, proven): on histories without a bad
  event, CBC *is* the VIL-URF, in the presence of tolerated internal accidents.  The proof is
  the eq. (6.2) engine verbatim: the MBO supplies the freshness interface `cbcFresh` through
  its terminal clause alone, and — being output-blind — is invariant under `cbcShift`; the
  accident count plays no role in this leg.
* **The counting leg** (`blindMaxWinProb_cbcGraphGame_le`, open): the JN combinatorics — the
  `a`-fold freshness charge and the accident-1 output-relevance count, the corrected BPR05
  Lemma 10.  Constants provisional; the claim is the shape `q²L/|X| + (qL)⁴/|X|²`.

Maurer's Thm 4.17 already reduces to the *blind*, fixed-message-set setting that
structure-graph lemmas assume — the BPR/JN adaptivity reduction is not re-proven here.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-! ## The internal structure graph -/

/-- **Internal vertices**: the chaining values *before* each block — the root `0` and every
internal state; the MACs (the states after the last block) are excluded.  Output-blindness of
the MBO lives here. -/
def structVertices (f : X → X) (ms : List (List X)) : Finset X :=
  insert 0 (ms.toFinset.biUnion fun bs =>
    (Finset.range bs.length).image fun j => cbcState f (bs.take j))

/-- **Internal inputs**: the distinct round-function inputs of the non-terminal edges — the
edge identities, already quotiented by forced collisions (a repeated input is one edge). -/
def structInputs (f : X → X) (ms : List (List X)) : Finset X :=
  ms.toFinset.biUnion fun bs =>
    (Finset.range (bs.length - 1)).image fun j => cbcInput f bs j

/-- **Accidents** (BPR05 / JN16 §3): the chance vertex-collisions — internal inputs beyond a
spanning tree of the internal values.  `structAccidents f ms = 0` ⟺ the internal graph is the
message trie. -/
def structAccidents (f : X → X) (ms : List (List X)) : ℕ :=
  (structInputs f ms).card + 1 - (structVertices f ms).card

/-- **The tolerant MBO.**  Bad ⟺ two internal accidents have occurred, or some queried
message's *terminal* round-function input meets another call site carrying a distinct key.
A single internal accident is *not* bad — the `ℓ`-linear win.  The event is output-blind:
every clause is a function of `f` at the internal inputs only. -/
def cbcGraphBad (f : X → X) (bf : M → List X) (l : List M) : Prop :=
  2 ≤ structAccidents f (l.map bf) ∨
    ∃ m ∈ l, ∃ m' ∈ l, ∃ j < (bf m').length,
      bf m ≠ (bf m').take (j + 1) ∧ cbcLastInput f bf m = cbcInput f (bf m') j

instance (f : X → X) (bf : M → List X) (l : List M) : Decidable (cbcGraphBad f bf l) := by
  unfold cbcGraphBad; infer_instance

/-! ## Graph theorems -/

/-- Every internal input's `f`-image is an internal vertex (the target of an internal edge is
the next internal state). -/
theorem image_structInputs_subset (f : X → X) (ms : List (List X)) :
    ∀ u ∈ structInputs f ms, f u ∈ structVertices f ms := by
  intro u hu
  obtain ⟨bs, hbs, hj⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨j, hjr, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hjr
  refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨bs, hbs, Finset.mem_image.mpr
    ⟨j + 1, Finset.mem_range.mpr (by omega), ?_⟩⟩)
  exact cbcState_take_succ_eq f bs (t := j) (by omega)

/-- Every non-root internal vertex is the `f`-image of an internal input. -/
theorem structVertices_eq_root_or_image (f : X → X) (ms : List (List X)) :
    ∀ v ∈ structVertices f ms, v = 0 ∨ ∃ u ∈ structInputs f ms, f u = v := by
  intro v hv
  rcases Finset.mem_insert.mp hv with h0 | hv
  · exact Or.inl h0
  obtain ⟨bs, hbs, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨j, hjr, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hjr
  cases j with
  | zero => exact Or.inl rfl
  | succ j' =>
      refine Or.inr ⟨cbcInput f bs j', Finset.mem_biUnion.mpr ⟨bs, hbs, Finset.mem_image.mpr
        ⟨j', Finset.mem_range.mpr (by omega), rfl⟩⟩, ?_⟩
      exact (cbcState_take_succ_eq f bs (t := j') (by omega)).symm

/-- **Accidents are monotone** in the message set: a new internal vertex needs a new internal
input to produce it (`V₂ ⊆ V₁ ∪ f '' (I₂ \ I₁)`), so the deficit `#inputs + 1 − #vertices`
never decreases. -/
theorem structAccidents_mono (f : X → X) {ms₁ ms₂ : List (List X)}
    (h : ms₁.toFinset ⊆ ms₂.toFinset) :
    structAccidents f ms₁ ≤ structAccidents f ms₂ := by
  classical
  have hI : structInputs f ms₁ ⊆ structInputs f ms₂ :=
    Finset.biUnion_subset_biUnion_of_subset_left _ h
  have hVsub : structVertices f ms₂
      ⊆ structVertices f ms₁ ∪ (structInputs f ms₂ \ structInputs f ms₁).image f := by
    intro v hv
    rcases structVertices_eq_root_or_image f ms₂ v hv with rfl | ⟨u, hu, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_insert_self 0 _)
    by_cases hu1 : u ∈ structInputs f ms₁
    · exact Finset.mem_union_left _ (image_structInputs_subset f ms₁ u hu1)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, hu1⟩, rfl⟩)
  have hVcard : (structVertices f ms₂).card
      ≤ (structVertices f ms₁).card
        + ((structInputs f ms₂).card - (structInputs f ms₁).card) := by
    calc (structVertices f ms₂).card
        ≤ (structVertices f ms₁ ∪ (structInputs f ms₂ \ structInputs f ms₁).image f).card :=
          Finset.card_le_card hVsub
      _ ≤ (structVertices f ms₁).card
            + ((structInputs f ms₂ \ structInputs f ms₁).image f).card :=
          Finset.card_union_le _ _
      _ ≤ (structVertices f ms₁).card + (structInputs f ms₂ \ structInputs f ms₁).card :=
          Nat.add_le_add_left (Finset.card_image_le) _
      _ = (structVertices f ms₁).card
            + ((structInputs f ms₂).card - (structInputs f ms₁).card) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hI]
  have hIcard : (structInputs f ms₁).card ≤ (structInputs f ms₂).card :=
    Finset.card_le_card hI
  unfold structAccidents
  omega

/-- The tolerant MBO is monotone in the query history. -/
theorem cbcGraphBad_monotone (f : X → X) (bf : M → List X)
    {l₁ l₂ : List M} (hpre : l₁ <+: l₂) (h : cbcGraphBad f bf l₁) : cbcGraphBad f bf l₂ := by
  rcases h with hacc | ⟨m, hm, m', hm', j, hj, hkey, hval⟩
  · exact Or.inl (le_trans hacc (structAccidents_mono f fun bs hbs => by
      rw [List.mem_toFinset] at hbs ⊢
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hbs
      exact List.mem_map.mpr ⟨m, hpre.subset hm, rfl⟩))
  · exact Or.inr ⟨m, hpre.subset hm, m', hpre.subset hm', j, hj, hkey, hval⟩

/-- The tolerant MBO supplies the engine's freshness interface — through its terminal clause
alone; the accident count plays no role. -/
theorem cbcFresh_of_not_cbcGraphBad (f : X → X) (bf : M → List X) {l : List M}
    (h : ¬ cbcGraphBad f bf l) : cbcFresh f bf l :=
  fun m hm m' hm' j' hj' hkey hval =>
    h (Or.inr ⟨m, hm, m', hm', j', hj', hkey, hval⟩)

/-! ## Output-blindness: invariance under the terminal re-randomisation -/

/-- Internal states are invariant under `cbcShift` — algebra on `cbcInput_cbcShift`
(`state = input − block`). -/
private theorem cbcState_take_cbcShift (f : X → X) (bf : M → List X) {l : List M}
    (δ : ↥l.toFinset → X) (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) {m : M} (hm : m ∈ l) {j : ℕ} (hj : j < (bf m).length) :
    cbcState (cbcShift f bf l δ) ((bf m).take j) = cbcState f ((bf m).take j) := by
  have h := cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm hj
  unfold cbcInput at h
  exact add_right_cancel h

/-- **The internal structure graph is invariant under `cbcShift`** — every clause of the
tolerant MBO is a function of `f` at the internal inputs, which the terminal shift fixes. -/
theorem cbcGraphBad_cbcShift (f : X → X) (bf : M → List X) {l : List M}
    (δ : ↥l.toFinset → X) (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) :
    cbcGraphBad (cbcShift f bf l δ) bf l ↔ cbcGraphBad f bf l := by
  have hmem : ∀ bs ∈ (l.map bf).toFinset, ∃ m ∈ l, bf m = bs := fun bs hbs => by
    rw [List.mem_toFinset] at hbs
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hbs
    exact ⟨m, hm, rfl⟩
  have hV : structVertices (cbcShift f bf l δ) (l.map bf) = structVertices f (l.map bf) := by
    unfold structVertices
    congr 1
    refine Finset.biUnion_congr rfl fun bs hbs => ?_
    obtain ⟨m, hm, rfl⟩ := hmem bs hbs
    refine Finset.image_congr fun j hj => ?_
    rw [Finset.mem_coe, Finset.mem_range] at hj
    exact cbcState_take_cbcShift f bf δ hbf_pf hbf_ne hfresh hm hj
  have hI : structInputs (cbcShift f bf l δ) (l.map bf) = structInputs f (l.map bf) := by
    unfold structInputs
    refine Finset.biUnion_congr rfl fun bs hbs => ?_
    obtain ⟨m, hm, rfl⟩ := hmem bs hbs
    refine Finset.image_congr fun j hj => ?_
    rw [Finset.mem_coe, Finset.mem_range] at hj
    exact cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm (by omega)
  have hlast : ∀ m ∈ l, cbcLastInput (cbcShift f bf l δ) bf m = cbcLastInput f bf m := by
    intro m hm
    unfold cbcLastInput
    exact cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm
      (by have := List.length_pos_of_ne_nil (hbf_ne m); omega)
  have hacc : structAccidents (cbcShift f bf l δ) (l.map bf) = structAccidents f (l.map bf) := by
    unfold structAccidents
    rw [hV, hI]
  unfold cbcGraphBad
  rw [hacc]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨m, hm, m', hm', j, hj, hkey, hval⟩
    rw [hlast m hm, cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm' hj] at hval
    exact ⟨m, hm, m', hm', j, hj, hkey, hval⟩
  · rintro ⟨m, hm, m', hm', j, hj, hkey, hval⟩
    refine ⟨m, hm, m', hm', j, hj, hkey, ?_⟩
    rw [hlast m hm, cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm' hj]
    exact hval

/-- `cbcShift` preserves `¬cbcGraphBad`. -/
theorem not_cbcGraphBad_cbcShift (f : X → X) (bf : M → List X) {l : List M}
    (δ : ↥l.toFinset → X) (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hbad : ¬ cbcGraphBad f bf l) :
    ¬ cbcGraphBad (cbcShift f bf l δ) bf l := by
  rw [cbcGraphBad_cbcShift f bf δ hbf_pf hbf_ne (cbcFresh_of_not_cbcGraphBad f bf hbad)]
  exact hbad

/-! ## The game `ĈBC^G 𝖱` and its standing facts -/

/-- The tolerant MBO's monotonicity in `decide`d form — the shape the history-game laws consume. -/
private theorem cbcGraphBad_decide_monotone (f : X → X) (bf : M → List X) :
    ∀ {l₁ l₂ : List M}, l₁ <+: l₂ →
      decide (cbcGraphBad f bf l₁) = true →
      decide (cbcGraphBad f bf l₂) = true := fun hpre hb => by
  simpa using cbcGraphBad_monotone f bf hpre (by simpa using hb)

/-- **The game `ĈBC^G 𝖱` per deterministic round function**: CBC tagged with the tolerant
structure-graph MBO. -/
noncomputable def cbcGraphGameDDS (f : X → X) (bf : M → List X) :
    PFunDDS.DDS M (X × Bool) :=
  PFunDDS.historyEvaluator fun l hne =>
    (cbcState f (bf (l.getLast hne)), decide (cbcGraphBad f bf l))

/-- **The game `ĈBC^G 𝖱`** as a probabilistic system. -/
noncomputable def cbcGraphGame (bf : M → List X) : PFunPDS M (X × Bool) :=
  Dist.fTransform (fun f : X → X => cbcGraphGameDDS f bf) (Dist.uniform (X → X))

/-- The tolerant MBO is monotone — each realization is an MBO game (CR18 Def 3.22). -/
theorem cbcGraphGame_monotoneMBO (bf : M → List X) : MonotoneMBO (cbcGraphGame bf) :=
  CondEquiv.monotoneMBO_fTransform_historyEvaluator (Dist.uniform (X → X))
    (fun f l hne => cbcState f (bf (l.getLast hne)))
    (fun f l => decide (cbcGraphBad f bf l))
    (fun f => cbcGraphBad_decide_monotone f bf)

/-- The game is a probability system. -/
theorem cbcGraphGame_isProbDist (bf : M → List X) : (cbcGraphGame bf).isProbDist := by
  unfold cbcGraphGame
  cr18_prob

/-- The game is total on nonempty histories. -/
theorem cbcGraphGame_totalOnNonempty (bf : M → List X) :
    CondEquiv.TotalOnNonempty (cbcGraphGame bf) :=
  CondEquiv.totalOnNonempty_fTransform_historyEvaluator (Dist.uniform (X → X))
    (fun f l hne => (cbcState f (bf (l.getLast hne)), decide (cbcGraphBad f bf l)))

/-- Stripping the tolerant MBO also returns `casc[CBC, 𝖱]` — same outputs as `ĈBC 𝖱`, a
different monitor. -/
theorem cbcGraphGame_ignoreMBO (bf : M → List X) :
    PFunPDS.ignoreMBO (cbcGraphGame bf) = cbcReal bf := by
  have h : PFunPDS.ignoreMBO (cbcGraphGame bf) = PFunPDS.ignoreMBO (cbcGame bf) := by
    rw [cbcGame_eq_fTransform_cbcGameDDS]
    unfold PFunPDS.ignoreMBO PFunPDS.stripMBO cbcGraphGame
    simp only [dist_simp]
    rw [show (PFunDDS.stripMBO ∘ fun f : X → X => cbcGraphGameDDS f bf)
        = (PFunDDS.stripMBO ∘ fun f : X → X => cbcGameDDS f bf) from by
      funext f; rfl]
  rw [h]
  exact cbcGame_ignoreMBO bf

attribute [cr18_standing] cbcGraphGame_monotoneMBO cbcGraphGame_isProbDist
  cbcGraphGame_totalOnNonempty cbcGraphGame_ignoreMBO

/-! ## The conditional equivalence -/

/-- **Game side**: the transcript's `A`-false mass is the probability of no bad event. -/
private theorem massAfalse_cbcGraphGame (bf : M → List X) {xs : List M} (hne : xs ≠ []) :
    CondEquiv.massAfalse (cbcGraphGame bf) xs
      = (Dist.uniform (X → X)).mass fun f => ¬ cbcGraphBad f bf xs :=
  (CondEquiv.massAfalse_fTransform_historyEvaluator (Dist.uniform (X → X))
    (fun f l hne => cbcState f (bf (l.getLast hne)))
    (fun f l => decide (cbcGraphBad f bf l)) hne).trans
    (Dist.mass_congr _ fun f => by simp)

/-- **Game "not won ∧ output matches"**: the MAC agrees with `ȳ` on every query ∧ no bad
structure-graph event. -/
private theorem massYAfalse_cbcGraphGame (bf : M → List X) {i : ℕ}
    (ys : Vector X (i + 1)) (xs : Vector M (i + 1)) :
    CondEquiv.massYAfalse (cbcGraphGame bf) i ys xs
      = (Dist.uniform (X → X)).mass fun f =>
        (∀ k : Fin (i + 1), cbcState f (bf (xs.get k)) = ys.get k) ∧
          ¬ cbcGraphBad f bf xs.toList :=
  (massYAfalse_fTransform_lastQuery (Dist.uniform (X → X)) (fun f m => cbcState f (bf m))
    (fun f l => decide (cbcGraphBad f bf l))
    (fun f => cbcGraphBad_decide_monotone f bf) ys xs).trans
    (Dist.mass_congr _ fun f => and_congr Iff.rfl (by simp))

/-- **Conditional equivalence under the tolerant guard** — the eq. (6.2) analogue: conditioned
on no bad structure-graph event, CBC *is* the VIL-URF — in the presence of tolerated internal
accidents.  The engine is eq. (6.2)'s verbatim: the MBO supplies `cbcFresh` through its
terminal clause, is `cbcShift`-invariant by output-blindness, and the balanced-fiber count
closes the per-transcript identity.  The accident count never enters. -/
theorem cbcGraphGame_condEquiv [Nontrivial M] (bf : M → List X)
    (hbf_pf : PrefixFree bf) :
    cbcGraphGame bf |≡ Vn := by
  have hbf_ne : ∀ m, bf m ≠ [] := hbf_pf.ne_nil
  refine condEquiv_of_transcript_mass_reductions (cbcGraphGame bf) Vn
    (Dist.uniform (X → X)) (Dist.uniform (M → X))
    (fun f m => cbcState f (bf m)) (fun g m => g m) (fun f l => ¬ cbcGraphBad f bf l)
    (fun hne => massAfalse_cbcGraphGame bf hne) (fun ys xs => massY_Vn ys xs)
    (fun ys xs => massYAfalse_cbcGraphGame bf ys xs) (fun xs a => ?_)
  refine Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq _ _ _ ?_
  have hTle : xs.toList.toFinset.card ≤ Fintype.card M := Finset.card_le_univ _
  rw [Fintype.card_fun, Counting.card_function_fiber_finset,
    ← cbc_fiber_card bf hbf_ne hbf_pf _
      (fun f hf => cbcFresh_of_not_cbcGraphBad f bf hf)
      (fun δ f hf => not_cbcGraphBad_cbcShift f bf δ hbf_pf hbf_ne hf) a]
  conv_lhs => rw [← Nat.sub_add_cancel hTle]
  cr18_algebra

/-! ## The counting leg: the affine collision calculus

Every clause of `cbcGraphBad` is covered by **charged affine events** on call-site inputs:

* an input collision (`cbcInput = cbcInput`, distinct keys) is a pair event with constant `0`;
* a vertex collision `state_j(m) = state_{j'}(m')` is, one level up, the pair event
  `cbcInput(m,j) = cbcInput(m',j') + (b_j − b_{j'})` (`state = input − block`);
* a root hit `state_j(m) = 0` is the single-site event `cbcInput(m,j) = b_j`.

The probability engine is the guarded `pointShift` slice: conditioned on a suitable guard, the
top input of an event sweeps `X` freely, so each event costs `1/|X|` — and two
minimally-chosen events cost `1/|X|²` by slicing twice. -/

/-- A **charged affine event**: two call sites whose inputs differ by a constant, or a single
site whose input hits a constant.  The `pair` events are block-sorted (`j ≤ j'`, top `j'`). -/
inductive ChargedEvent (M X : Type u) : Type u where
  | pair (m : M) (j : ℕ) (m' : M) (j' : ℕ) (c : X)
  | single (m : M) (j : ℕ) (c : X)
  deriving DecidableEq

namespace ChargedEvent

variable {M X : Type u}

/-- The event's top block level — the level whose input the slice re-randomises. -/
def top : ChargedEvent M X → ℕ
  | pair _ _ _ j' _ => j'
  | single _ j _ => j

/-- The event's site messages. -/
def msgs : ChargedEvent M X → List M
  | pair m _ m' _ _ => [m, m']
  | single m _ _ => [m]

end ChargedEvent

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- The event holds for the round function `f`. -/
def ChargedEvent.holds (f : X → X) (bf : M → List X) : ChargedEvent M X → Prop
  | .pair m j m' j' c => cbcInput f (bf m) j = cbcInput f (bf m') j' + c
  | .single m j c => cbcInput f (bf m) j = c

/-- Structural validity of an event over the history `l`: memberships, in-range block levels,
sortedness, and non-degeneracy (`pair`: distinct keys — same keys make the sites the same
computation). -/
def ChargedEvent.valid (bf : M → List X) (l : List M) : ChargedEvent M X → Prop
  | .pair m j m' j' c => m ∈ l ∧ m' ∈ l ∧ j < (bf m).length ∧ j' < (bf m').length ∧
      j ≤ j' ∧ (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧
      (c = 0 ∨ (1 ≤ j ∧ c = (bf m).getD j 0 - (bf m').getD j' 0 ∧
        (bf m).take j ≠ (bf m').take j'))
  | .single m j c => m ∈ l ∧ j < (bf m).length ∧ 1 ≤ j ∧ c = (bf m).getD j 0

/-- The input values at the predecessors of the event's sites — the construction fingerprint
that separates events built from distinct collision witnesses. -/
def ChargedEvent.predInputs (f : X → X) (bf : M → List X) : ChargedEvent M X → Finset X
  | .pair m j m' j' _ => {cbcInput f (bf m) (j - 1), cbcInput f (bf m') (j' - 1)}
  | .single m j _ => {cbcInput f (bf m) (j - 1)}

/-- The event is a **terminal input collision**: a `c = 0` pair with one site at its message's
last block — the events the tolerant MBO's terminal clause generates. -/
def ChargedEvent.isTerminal (bf : M → List X) : ChargedEvent M X → Prop
  | .pair m j m' j' c => c = 0 ∧ (j + 1 = (bf m).length ∨ j' + 1 = (bf m').length)
  | .single _ _ _ => False

/-- **The charged guard**: no valid charged event with top level `< t` holds — the affine
generalization of `cbcBadLt`. -/
def chargedLt (f : X → X) (bf : M → List X) (l : List M) (t : ℕ) : Prop :=
  ∃ D : ChargedEvent M X, D.valid bf l ∧ D.top < t ∧ D.holds f bf

/-- **The internal vertex set is exactly root + image**: `V = insert 0 (f '' I)`. -/
theorem structVertices_eq (f : X → X) (ms : List (List X)) :
    structVertices f ms = insert 0 ((structInputs f ms).image f) := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases structVertices_eq_root_or_image f ms v hv with rfl | ⟨u, hu, rfl⟩
    · exact Finset.mem_insert_self 0 _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_insert_self 0 _
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact image_structInputs_subset f ms u hu

/-- Every member of `structInputs` is the input of an in-range internal call site. -/
theorem exists_site_of_mem_structInputs (f : X → X) (bf : M → List X) (l : List M)
    {u : X} (hu : u ∈ structInputs f (l.map bf)) :
    ∃ m ∈ l, ∃ j : ℕ, j + 1 < (bf m).length ∧ cbcInput f (bf m) j = u := by
  obtain ⟨bs, hbs, hj⟩ := Finset.mem_biUnion.mp hu
  rw [List.mem_toFinset] at hbs
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hbs
  obtain ⟨j, hjr, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hjr
  exact ⟨m, hm, j, by omega, rfl⟩

/-- **A vertex collision, one level up, is a charged pair event**: distinct input values with
equal `f`-images yield a valid, holding pair event (the state collision at the successor
level, with the block-difference constant). -/
theorem chargedEvent_of_image_collision (f : X → X) (bf : M → List X) (l : List M)
    {u u' : X} (hu : u ∈ structInputs f (l.map bf)) (hu' : u' ∈ structInputs f (l.map bf))
    (hne : u ≠ u') (himg : f u = f u') :
    ∃ D : ChargedEvent M X, D.valid bf l ∧ D.holds f bf ∧ 1 ≤ D.top ∧
      D.predInputs f bf = {u, u'} := by
  obtain ⟨m, hm, j, hj, hju⟩ := exists_site_of_mem_structInputs f bf l hu
  obtain ⟨m', hm', j', hj', hju'⟩ := exists_site_of_mem_structInputs f bf l hu'
  -- keys distinct at both the event level and the predecessor level: equal keys would make the
  -- sites the same computation, contradicting the distinct input values
  have hkey_gen : ∀ d : ℕ, 1 ≤ d → j + d ≤ (bf m).length → j' + d ≤ (bf m').length →
      (bf m).take (j + d) = (bf m').take (j' + d) → False := by
    intro d hd hdl hdl' heq
    apply hne
    rw [← hju, ← hju']
    have hjj : j = j' := by
      have hlen := congrArg List.length heq
      rw [List.length_take, List.length_take] at hlen
      omega
    subst hjj
    have : cbcInput f ((bf m).take (j + d)) j = cbcInput f ((bf m').take (j + d)) j := by
      rw [heq]
    rwa [cbcInput_take_of_lt f (bf m) (by omega), cbcInput_take_of_lt f (bf m') (by omega)]
      at this
  have hkey : (bf m).take (j + 1 + 1) ≠ (bf m').take (j' + 1 + 1) :=
    fun h => hkey_gen 2 (by omega) (by omega) (by omega) h
  have hpredkey : (bf m).take (j + 1) ≠ (bf m').take (j' + 1) :=
    fun h => hkey_gen 1 le_rfl (by omega) (by omega) h
  have hstate : cbcState f ((bf m).take (j + 1)) = cbcState f ((bf m').take (j' + 1)) := by
    rw [cbcState_take_succ_eq f (bf m) (t := j) (by omega),
      cbcState_take_succ_eq f (bf m') (t := j') (by omega), hju, hju', himg]
  have hholds : cbcInput f (bf m) (j + 1)
      = cbcInput f (bf m') (j' + 1) + ((bf m).getD (j + 1) 0 - (bf m').getD (j' + 1) 0) := by
    unfold cbcInput
    rw [hstate]
    abel
  rcases le_total (j + 1) (j' + 1) with hle | hle
  · refine ⟨.pair m (j + 1) m' (j' + 1) ((bf m).getD (j + 1) 0 - (bf m').getD (j' + 1) 0),
      ⟨hm, hm', by omega, by omega, hle, hkey, Or.inr ⟨by omega, rfl, by
        show (bf m).take (j + 1) ≠ (bf m').take (j' + 1); exact hpredkey⟩⟩, hholds, by
        show 1 ≤ j' + 1; omega, ?_⟩
    show ({cbcInput f (bf m) (j + 1 - 1), cbcInput f (bf m') (j' + 1 - 1)} : Finset X) = {u, u'}
    rw [show j + 1 - 1 = j from rfl, show j' + 1 - 1 = j' from rfl, hju, hju']
  · refine ⟨.pair m' (j' + 1) m (j + 1) ((bf m').getD (j' + 1) 0 - (bf m).getD (j + 1) 0),
      ⟨hm', hm, by omega, by omega, hle, fun hk => hkey hk.symm, Or.inr ⟨by omega, rfl, by
        show (bf m').take (j' + 1) ≠ (bf m).take (j + 1); exact fun h => hpredkey h.symm⟩⟩, ?_, by
        show 1 ≤ j + 1; omega, ?_⟩
    · show cbcInput f (bf m') (j' + 1) = cbcInput f (bf m) (j + 1) + _
      rw [hholds]
      abel
    · show ({cbcInput f (bf m') (j' + 1 - 1), cbcInput f (bf m) (j + 1 - 1)} : Finset X) = {u, u'}
      rw [show j + 1 - 1 = j from rfl, show j' + 1 - 1 = j' from rfl, hju, hju']
      exact Finset.pair_comm u' u

/-- **A root hit is a charged single event**: an input value sent to `0` by `f` yields a
valid, holding single event at the successor level. -/
theorem chargedEvent_of_root_hit (f : X → X) (bf : M → List X) (l : List M)
    {u : X} (hu : u ∈ structInputs f (l.map bf)) (hroot : f u = 0) :
    ∃ D : ChargedEvent M X, D.valid bf l ∧ D.holds f bf ∧ 1 ≤ D.top ∧
      D.predInputs f bf = {u} := by
  obtain ⟨m, hm, j, hj, hju⟩ := exists_site_of_mem_structInputs f bf l hu
  refine ⟨.single m (j + 1) ((bf m).getD (j + 1) 0), ⟨hm, by omega, by omega, rfl⟩, ?_, by
    show 1 ≤ j + 1; omega, ?_⟩
  · show cbcInput f (bf m) (j + 1) = (bf m).getD (j + 1) 0
    unfold cbcInput
    rw [cbcState_take_succ_eq f (bf m) (t := j) (by omega), hju, hroot, zero_add]
  · show ({cbcInput f (bf m) (j + 1 - 1)} : Finset X) = {u}
    rw [show j + 1 - 1 = j from rfl, hju]

/-- **The terminal clause is a charged pair event** (constant `0`). -/
theorem chargedEvent_of_terminal (f : X → X) (bf : M → List X) (l : List M)
    (hbf_ne : ∀ m, bf m ≠ [])
    {m m' : M} (hm : m ∈ l) (hm' : m' ∈ l) {j : ℕ} (hj : j < (bf m').length)
    (hkey : bf m ≠ (bf m').take (j + 1))
    (hval : cbcLastInput f bf m = cbcInput f (bf m') j) :
    ∃ D : ChargedEvent M X, D.valid bf l ∧ D.isTerminal bf ∧ D.holds f bf := by
  have hlen : 0 < (bf m).length := List.length_pos_of_ne_nil (hbf_ne m)
  have hkey' : (bf m).take ((bf m).length - 1 + 1) ≠ (bf m').take (j + 1) := by
    rwa [take_last_key (hbf_ne m)]
  rcases le_total ((bf m).length - 1) j with hle | hle
  · exact ⟨.pair m ((bf m).length - 1) m' j 0,
      ⟨hm, hm', by omega, hj, hle, hkey', Or.inl rfl⟩, ⟨rfl, Or.inl (by omega)⟩, by
        show cbcInput f (bf m) ((bf m).length - 1) = cbcInput f (bf m') j + 0
        rw [add_zero]; exact hval⟩
  · exact ⟨.pair m' j m ((bf m).length - 1) 0,
      ⟨hm', hm, hj, by omega, hle, fun hk => hkey' hk.symm, Or.inl rfl⟩,
      ⟨rfl, Or.inr (by omega)⟩, by
        show cbcInput f (bf m') j = cbcInput f (bf m) ((bf m).length - 1) + 0
        rw [add_zero]; exact hval.symm⟩

/-- **Two accidents yield two distinct charged events** — the image-deficiency extraction:
`V = insert 0 (f '' I)` exactly, so `acc ≥ 2` forces either two `f`-collisions on the internal
inputs, or one collision plus a root hit; the `predInputs` fingerprints separate the events. -/
theorem two_chargedEvents_of_accidents (f : X → X) (bf : M → List X) (l : List M)
    (hacc : 2 ≤ structAccidents f (l.map bf)) :
    ∃ D₁ D₂ : ChargedEvent M X, D₁.valid bf l ∧ D₁.holds f bf ∧ 1 ≤ D₁.top ∧
      D₂.valid bf l ∧ D₂.holds f bf ∧ 1 ≤ D₂.top ∧ D₁ ≠ D₂ := by
  classical
  set I := structInputs f (l.map bf) with hI
  have hVeq := structVertices_eq f (l.map bf)
  unfold structAccidents at hacc
  rw [hVeq, ← hI] at hacc
  have hmaps : ∀ x ∈ I, f x ∈ I.image f := fun x hx => Finset.mem_image_of_mem f hx
  by_cases h0 : (0 : X) ∈ I.image f
  · -- a root hit + at least one collision
    rw [Finset.insert_eq_self.mpr h0] at hacc
    have hdef : (I.image f).card < I.card := by
      have := Finset.card_image_le (s := I) (f := f)
      omega
    obtain ⟨u, hu, u', hu', hne, himg⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hdef hmaps
    obtain ⟨u₀, hu₀, hroot⟩ := Finset.mem_image.mp h0
    obtain ⟨D₁, hv₁, hh₁, ht₁, hp₁⟩ := chargedEvent_of_image_collision f bf l hu hu' hne himg
    obtain ⟨D₂, hv₂, hh₂, ht₂, hp₂⟩ := chargedEvent_of_root_hit f bf l hu₀ hroot
    refine ⟨D₁, D₂, hv₁, hh₁, ht₁, hv₂, hh₂, ht₂, fun hD => ?_⟩
    have : ({u, u'} : Finset X).card = ({u₀} : Finset X).card := by
      rw [← hp₁, ← hp₂, hD]
    rw [Finset.card_pair hne, Finset.card_singleton] at this
    omega
  · -- two collisions: pigeonhole, erase the redundant witness, pigeonhole again
    rw [Finset.card_insert_of_notMem h0] at hacc
    have hdef : (I.image f).card < I.card := by omega
    obtain ⟨u₁, hu₁, u₁', hu₁', hne₁, himg₁⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hdef hmaps
    set I' := I.erase u₁' with hI'
    have hI'sub : I' ⊆ I := Finset.erase_subset _ _
    have hI'img : I'.image f = I.image f := by
      apply Finset.Subset.antisymm (Finset.image_subset_image hI'sub)
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      by_cases h : u = u₁'
      · subst h
        exact Finset.mem_image.mpr ⟨u₁, Finset.mem_erase.mpr ⟨hne₁, hu₁⟩, himg₁⟩
      · exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨h, hu⟩, rfl⟩
    have hdef' : (I'.image f).card < I'.card := by
      rw [hI'img, Finset.card_erase_of_mem hu₁']
      omega
    obtain ⟨u₂, hu₂, u₂', hu₂', hne₂, himg₂⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hdef'
        (fun x hx => Finset.mem_image_of_mem f hx)
    have hu₂I : u₂ ∈ I := hI'sub hu₂
    have hu₂'I : u₂' ∈ I := hI'sub hu₂'
    have hu₂ne : u₂ ≠ u₁' := (Finset.mem_erase.mp hu₂).1
    have hu₂'ne : u₂' ≠ u₁' := (Finset.mem_erase.mp hu₂').1
    obtain ⟨D₁, hv₁, hh₁, ht₁, hp₁⟩ := chargedEvent_of_image_collision f bf l hu₁ hu₁' hne₁ himg₁
    obtain ⟨D₂, hv₂, hh₂, ht₂, hp₂⟩ := chargedEvent_of_image_collision f bf l hu₂I hu₂'I hne₂ himg₂
    refine ⟨D₁, D₂, hv₁, hh₁, ht₁, hv₂, hh₂, ht₂, fun hD => ?_⟩
    have hmem : u₁' ∈ ({u₂, u₂'} : Finset X) := by
      rw [← hp₂, ← hD, hp₁]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hu₂ne h.symm
    · exact hu₂'ne ((Finset.mem_singleton.mp h).symm)

/-- The charged guard is stronger than the input-collision guard: an input collision *is* a
charged (`c = 0`) event. -/
theorem not_cbcBadLt_of_not_chargedLt (f : X → X) (bf : M → List X) (l : List M) (t : ℕ)
    (h : ¬ chargedLt f bf l t) : ¬ cbcBadLt f bf l t := by
  rintro ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩
  rw [lt_min_iff] at hj hj'
  rcases le_total j j' with hle | hle
  · exact h ⟨.pair m j m' j' 0, ⟨hm, hm', hj.2, hj'.2, hle, hkey, Or.inl rfl⟩, hj'.1, by
      show cbcInput f (bf m) j = cbcInput f (bf m') j' + 0
      rw [add_zero]; exact hval⟩
  · exact h ⟨.pair m' j' m j 0, ⟨hm', hm, hj'.2, hj.2, hle, fun hk => hkey hk.symm,
      Or.inl rfl⟩, hj.1, by
      show cbcInput f (bf m') j' = cbcInput f (bf m) j + 0
      rw [add_zero]; exact hval.symm⟩

/-- The charged guard is preserved by a `pointShift` at a guarded block-`t` input: every event
below the shift level reads only invariant inputs. -/
theorem not_chargedLt_pointShift (f : X → X) (bf : M → List X) (l : List M)
    {m₂ : M} (hm₂ : m₂ ∈ l) {t : ℕ} (ht : t < (bf m₂).length)
    (hguard : ¬ chargedLt f bf l (t + 1)) (δ : X) :
    ¬ chargedLt (pointShift f (cbcInput f (bf m₂) t) δ) bf l (t + 1) := by
  have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hguard
  rintro ⟨D, hval, htop, hholds⟩
  refine hguard ⟨D, hval, htop, ?_⟩
  cases D with
  | pair m j m' j' c =>
      obtain ⟨hm, hm', hjl, hjl', hjj, -⟩ := hval
      have htop' : j' ≤ t := by simpa [ChargedEvent.top] using Nat.lt_succ_iff.mp htop
      show cbcInput f (bf m) j = cbcInput f (bf m') j' + c
      rw [← cbcInput_pointShift_of_le f bf l hm₂ ht hbadLt δ hm (by omega) hjl,
        ← cbcInput_pointShift_of_le f bf l hm₂ ht hbadLt δ hm' htop' hjl']
      exact hholds
  | single m j c =>
      obtain ⟨hm, hjl, -⟩ := hval
      have htop' : j ≤ t := by simpa [ChargedEvent.top] using Nat.lt_succ_iff.mp htop
      show cbcInput f (bf m) j = c
      rw [← cbcInput_pointShift_of_le f bf l hm₂ ht hbadLt δ hm htop' hjl]
      exact hholds

open Classical in
/-- **The affine leaf, card form**: the `holds ∧ guard` slice carries at most a `1/|X|`
fraction of the guard set — the top input sweeps `X` freely under the guarded `pointShift` at
its predecessor, for *every* target constant. -/
theorem card_chargedEvent_mul_le (bf : M → List X) (l : List M) (D : ChargedEvent M X)
    (hv : D.valid bf l) :
    (Finset.univ.filter fun f : X → X => D.holds f bf ∧ ¬ chargedLt f bf l D.top).card
        * Fintype.card X
      ≤ (Finset.univ.filter fun f : X → X => ¬ chargedLt f bf l D.top).card := by
  classical
  cases D with
  | single m j c =>
      obtain ⟨hm, hjl, hj1, hc⟩ := hv
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      have key := Counting.card_filter_shift_univ (A := X)
        (fun f => ¬ chargedLt f bf l (t + 1 : ℕ))
        (fun f => cbcInput f (bf m) (t + 1) - c)
        (fun δ f => pointShift f (cbcInput f (bf m) t) δ)
        (fun δ f hf => not_chargedLt_pointShift f bf l hm (by omega) hf δ)
        (fun δ f hf => by
          have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hf
          show cbcInput (pointShift f (cbcInput f (bf m) t) δ) (bf m) (t + 1) - c
            = cbcInput f (bf m) (t + 1) - c + δ
          rw [cbcInput_top_pointShift f bf l hm hjl hbadLt δ]
          abel)
        (fun δ δ' f hf => by
          have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hf
          show pointShift (pointShift f (cbcInput f (bf m) t) δ)
              (cbcInput (pointShift f (cbcInput f (bf m) t) δ) (bf m) t) δ' = _
          rw [cbcInput_pointShift_of_le f bf l hm (by omega) hbadLt δ hm le_rfl (by omega)]
          exact pointShift_pointShift f _ δ δ')
        (fun f _ => pointShift_zero f _) 0
      refine le_of_eq ?_
      rw [show (Finset.univ.filter fun f : X → X =>
          ChargedEvent.holds f bf (.single m (t+1) c) ∧ ¬ chargedLt f bf l
            (ChargedEvent.single m (t+1) c).top)
        = (Finset.univ.filter fun f : X → X =>
            cbcInput f (bf m) (t + 1) - c = 0 ∧ ¬ chargedLt f bf l (t + 1)) from
        Finset.filter_congr fun f _ => by
          show (cbcInput f (bf m) (t + 1) = c ∧ ¬ chargedLt f bf l (t + 1)) ↔ _
          rw [sub_eq_zero]]
      exact key
  | pair m j m' j' c =>
      obtain ⟨hm, hm', hjl, hjl', hjj, hkey, hcs⟩ := hv
      cases j' with
      | zero =>
        have hj0 : j = 0 := Nat.le_zero.mp hjj
        subst hj0
        have hc0 : c = 0 := by
          rcases hcs with h | ⟨h1, -⟩
          · exact h
          · omega
        subst hc0
        have hne : (bf m).getD 0 0 ≠ (bf m').getD 0 0 :=
          getD_ne_of_take_eq_of_take_succ_ne 0 rfl hkey hjl hjl'
        have hempty : (Finset.univ.filter fun f : X → X =>
            ChargedEvent.holds f bf (.pair m 0 m' 0 0) ∧ ¬ chargedLt f bf l
              (ChargedEvent.pair m 0 m' 0 (0:X)).top) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun f _ => ?_
          rintro ⟨h1, -⟩
          have h1' : cbcInput f (bf m) 0 = cbcInput f (bf m') 0 + 0 := h1
          exact hne (by simpa [cbcInput, cbcState, add_zero] using h1')
        rw [hempty]
        simp
      | succ t =>
        by_cases hpe : j = t + 1 ∧ (bf m).take (t + 1) = (bf m').take (t + 1)
        · obtain ⟨rfl, hpe⟩ := hpe
          have hc0 : c = 0 := by
            rcases hcs with h | ⟨-, -, hpred⟩
            · exact h
            · exact absurd hpe hpred
          subst hc0
          have hne : (bf m).getD (t + 1) 0 ≠ (bf m').getD (t + 1) 0 :=
            getD_ne_of_take_eq_of_take_succ_ne 0 hpe hkey hjl hjl'
          have hempty : (Finset.univ.filter fun f : X → X =>
              ChargedEvent.holds f bf (.pair m (t+1) m' (t+1) 0) ∧ ¬ chargedLt f bf l
                (ChargedEvent.pair m (t+1) m' (t+1) (0:X)).top) = ∅ := by
            refine Finset.filter_eq_empty_iff.mpr fun f _ => ?_
            rintro ⟨h1, -⟩
            have h1' : cbcInput f (bf m) (t + 1) = cbcInput f (bf m') (t + 1) + 0 := h1
            have hstate : cbcState f ((bf m).take (t + 1))
                = cbcState f ((bf m').take (t + 1)) := by rw [hpe]
            rw [add_zero] at h1'
            unfold cbcInput at h1'
            rw [hstate] at h1'
            exact hne (add_left_cancel h1')
          rw [hempty]
          simp
        · have hsplit : j ≤ t ∨ j = t + 1 ∧ (bf m).take (t + 1) ≠ (bf m').take (t + 1) := by
            grind
          have hu₁ : ∀ (δ : X), ∀ f, ¬ chargedLt f bf l (t + 1) →
              cbcInput (pointShift f (cbcInput f (bf m') t) δ) (bf m) j
                = cbcInput f (bf m) j := by
            intro δ f hf
            have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hf
            rcases hsplit with hle | ⟨rfl, hpne⟩
            · exact cbcInput_pointShift_of_le f bf l hm' (by omega) hbadLt δ hm hle hjl
            · exact cbcInput_top_pointShift_other f bf l hm hm' hjl (by omega) hpne hbadLt δ
          have key := Counting.card_filter_shift_univ (A := X)
            (fun f => ¬ chargedLt f bf l (t + 1 : ℕ))
            (fun f => cbcInput f (bf m') (t + 1) - cbcInput f (bf m) j)
            (fun δ f => pointShift f (cbcInput f (bf m') t) δ)
            (fun δ f hf => not_chargedLt_pointShift f bf l hm' (by omega) hf δ)
            (fun δ f hf => by
              have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hf
              show cbcInput (pointShift f (cbcInput f (bf m') t) δ) (bf m') (t + 1)
                  - cbcInput (pointShift f (cbcInput f (bf m') t) δ) (bf m) j
                = cbcInput f (bf m') (t + 1) - cbcInput f (bf m) j + δ
              rw [cbcInput_top_pointShift f bf l hm' hjl' hbadLt δ, hu₁ δ f hf]
              abel)
            (fun δ δ' f hf => by
              have hbadLt := not_cbcBadLt_of_not_chargedLt f bf l (t + 1) hf
              show pointShift (pointShift f (cbcInput f (bf m') t) δ)
                  (cbcInput (pointShift f (cbcInput f (bf m') t) δ) (bf m') t) δ' = _
              rw [cbcInput_pointShift_of_le f bf l hm' (by omega) hbadLt δ hm' le_rfl (by omega)]
              exact pointShift_pointShift f _ δ δ')
            (fun f _ => pointShift_zero f _) (-c)
          refine le_of_eq ?_
          rw [show (Finset.univ.filter fun f : X → X =>
              ChargedEvent.holds f bf (.pair m j m' (t+1) c) ∧ ¬ chargedLt f bf l
                (ChargedEvent.pair m j m' (t+1) c).top)
            = (Finset.univ.filter fun f : X → X =>
                cbcInput f (bf m') (t + 1) - cbcInput f (bf m) j = -c
                  ∧ ¬ chargedLt f bf l (t + 1)) from
            Finset.filter_congr fun f _ => by
              show (cbcInput f (bf m) j = cbcInput f (bf m') (t+1) + c
                  ∧ ¬ chargedLt f bf l (t + 1)) ↔ _
              exact and_congr_left' ⟨fun h => by rw [h]; abel, fun h => by
                rw [sub_eq_iff_eq_add] at h
                rw [h]; abel⟩]
          exact key

/-- **The affine leaf**: a valid charged event holds under its own charged guard with
probability at most `1/|X|`. -/
theorem mass_chargedEvent_le (bf : M → List X) (l : List M) (D : ChargedEvent M X)
    (hv : D.valid bf l) :
    (Dist.uniform (X → X)).mass (fun f => D.holds f bf ∧ ¬ chargedLt f bf l D.top)
      ≤ 1 / (Fintype.card X : NNReal) := by
  classical
  refine Dist.uniform_mass_le_inv_card_of_card_mul_le (B := X) _ ?_
  exact le_trans (card_chargedEvent_mul_le bf l D hv)
    (Finset.card_le_univ _)

/-- The event's sites. -/
def ChargedEvent.sites : ChargedEvent M X → List (M × ℕ)
  | .pair m j m' j' _ => [(m, j), (m', j')]
  | .single m j _ => [(m, j)]

/-- The event's top-site message. -/
def ChargedEvent.topMsg : ChargedEvent M X → M
  | .pair _ _ m' _ _ => m'
  | .single m _ _ => m

/-- **The uniqueness-driven avoidance engine**: under the uniqueness-below guard, a chain input
at level `p ≤ t` never equals the level-`t` input of `b₂` — such a revisit is a charged `c = 0`
event below `t + 1`, forced to be `D₁`, whose shape `hblock` excludes.  For `p < t` the key
distinctness is automatic (different take-lengths); at `p = t` the caller supplies it. -/
private theorem avoid_of_uniqueBelow (bf : M → List X) (l : List M) (D₁ : ChargedEvent M X)
    {b₂ : M} (hb₂ : b₂ ∈ l) {t : ℕ} (ht : t < (bf b₂).length)
    (hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i b₂ t 0)
    {f : X → X}
    (hu : ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 → D' = D₁)
    {x : M} (hx : x ∈ l) {p : ℕ} (hp : p ≤ t) (hplen : p < (bf x).length)
    (hkey : (bf x).take (p + 1) ≠ (bf b₂).take (t + 1)) :
    cbcInput f (bf x) p ≠ cbcInput f (bf b₂) t := by
  intro heq
  have hD : (ChargedEvent.pair x p b₂ t (0 : X)).valid bf l :=
    ⟨hx, hb₂, hplen, ht, hp, hkey, Or.inl rfl⟩
  have hDh : (ChargedEvent.pair x p b₂ t (0 : X)).holds f bf := by
    show cbcInput f (bf x) p = cbcInput f (bf b₂) t + 0
    rw [add_zero]; exact heq
  exact hblock x p (hu _ hD hDh (Nat.lt_succ_self t)).symm

/-- Keys at strictly different levels are automatically distinct (take-length arithmetic). -/
private theorem take_key_ne_of_level_lt (bf : M → List X) {x b₂ : M} {p t : ℕ}
    (hplen : p < (bf x).length) (ht : t < (bf b₂).length) (hlt : p < t) :
    (bf x).take (p + 1) ≠ (bf b₂).take (t + 1) := by
  intro h
  have := congrArg List.length h
  rw [List.length_take, List.length_take] at this
  omega

/-- **Input invariance under the `D₂`-top shift**: any site input at level `≤ t + 1` is fixed,
given the uniqueness guard, the shape exclusion, and (at level exactly `t + 1`) the pred-key
protection. -/
private theorem cbcInput_shift₂_invariant (bf : M → List X) (l : List M)
    (D₁ : ChargedEvent M X)
    {b₂ : M} (hb₂ : b₂ ∈ l) {t : ℕ} (ht : t < (bf b₂).length)
    (hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i b₂ t 0)
    {f : X → X}
    (hu : ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 → D' = D₁)
    (δ : X) {x : M} (hx : x ∈ l) {i : ℕ} (hi : i ≤ t + 1) (hilen : i < (bf x).length)
    (hspecial : i = t + 1 → (bf x).take (t + 1) ≠ (bf b₂).take (t + 1)) :
    cbcInput (pointShift f (cbcInput f (bf b₂) t) δ) (bf x) i = cbcInput f (bf x) i := by
  refine cbcInput_pointShift_of_avoid f bf _ δ fun p hp' => ?_
  have hpt : p ≤ t := by omega
  refine avoid_of_uniqueBelow bf l D₁ hb₂ ht hblock hu hx hpt (by omega) ?_
  rcases Nat.lt_or_ge p t with hlt | hge
  · exact take_key_ne_of_level_lt bf (by omega) ht hlt
  · have hpt' : p = t := by omega
    subst hpt'
    exact hspecial (by omega)

open Classical in
/-- **The double slice** (card form): with the uniqueness-below guard *in the base predicate*
(a random `f` is not shift-stable without it), the `D₂`-top input sweeps `X` freely — `D₁`'s
data and both guards read only invariant levels — so the joint slice carries a `1/|X|` fraction
of the guarded base.  Composed below with `card_chargedEvent_mul_le` this yields `1/|X|²`. -/
theorem card_two_chargedEvents_mul_le (bf : M → List X) (l : List M)
    (a₁ p₁ : M) (i₁ i₁' : ℕ) (c₁ : X) (m₂ m₂' : M) (j₂ t : ℕ) (c₂ : X)
    (hv₁ : (ChargedEvent.pair a₁ i₁ p₁ i₁' c₁).valid bf l) (hlow : i₁' ≤ t)
    (hm₂ : m₂ ∈ l) (hm₂' : m₂' ∈ l) (hj₂ : j₂ ≤ t + 1)
    (hj₂len : j₂ < (bf m₂).length) (htlen : t + 1 < (bf m₂').length)
    (hblock : ∀ (a : M) (i : ℕ), (ChargedEvent.pair a₁ i₁ p₁ i₁' c₁) ≠ .pair a i m₂' t 0)
    (hj₂special : j₂ = t + 1 → (bf m₂).take (t + 1) ≠ (bf m₂').take (t + 1)) :
    (Finset.univ.filter fun f : X → X =>
        (cbcInput f (bf a₁) i₁ = cbcInput f (bf p₁) i₁' + c₁ ∧
          ¬ chargedLt f bf l i₁' ∧
          (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
            D' = .pair a₁ i₁ p₁ i₁' c₁)) ∧
        cbcInput f (bf m₂) j₂ = cbcInput f (bf m₂') (t + 1) + c₂).card
        * Fintype.card X
      ≤ (Finset.univ.filter fun f : X → X =>
          cbcInput f (bf a₁) i₁ = cbcInput f (bf p₁) i₁' + c₁ ∧ ¬ chargedLt f bf l i₁').card := by
  obtain ⟨ha₁, hp₁, hi₁len, hi₁'len, hi₁le, hkey₁, -⟩ := hv₁
  set D₁ : ChargedEvent M X := .pair a₁ i₁ p₁ i₁' c₁ with hD₁
  set base : (X → X) → Prop := fun f => cbcInput f (bf a₁) i₁ = cbcInput f (bf p₁) i₁' + c₁ ∧
    ¬ chargedLt f bf l i₁' ∧
    (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 → D' = D₁) with hbase
  have huniq : ∀ f, base f → ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf →
      D'.top < t + 1 → D' = D₁ := fun f hf => hf.2.2
  set act : X → (X → X) → (X → X) := fun δ f => pointShift f (cbcInput f (bf m₂') t) δ with hact
  -- inputs at level `≤ t+1` of guarded chains are shift-invariant
  have hInv : ∀ (f : X → X), base f → ∀ (δ : X) {x : M}, x ∈ l → ∀ {i : ℕ}, i ≤ t + 1 →
        i < (bf x).length → (i = t + 1 → (bf x).take (t + 1) ≠ (bf m₂').take (t + 1)) →
        cbcInput (act δ f) (bf x) i = cbcInput f (bf x) i :=
    fun f hf δ x hx i hi hilen hspec =>
      cbcInput_shift₂_invariant bf l D₁ hm₂' (by omega) hblock (huniq f hf) δ hx hi hilen hspec
  -- events with top `< t+1` read only invariant inputs, so their truth is preserved
  have hev : ∀ (f : X → X), base f → ∀ (δ : X) (D' : ChargedEvent M X), D'.valid bf l →
      D'.top < t + 1 → (D'.holds (act δ f) bf ↔ D'.holds f bf) := by
    intro f hf δ D' hvD' htopD'
    cases D' with
    | pair a p a' p' c =>
        obtain ⟨hma, hma', hpl, hpl', hple, -⟩ := hvD'
        have htop' : p' < t + 1 := by simpa [ChargedEvent.top] using htopD'
        show (cbcInput (act δ f) (bf a) p = cbcInput (act δ f) (bf a') p' + c)
          ↔ (cbcInput f (bf a) p = cbcInput f (bf a') p' + c)
        rw [hInv f hf δ hma (by omega) hpl (by omega),
          hInv f hf δ hma' (le_of_lt htop') hpl' (by omega)]
    | single a p c =>
        obtain ⟨hma, hpl, -⟩ := hvD'
        have htop' : p < t + 1 := by simpa [ChargedEvent.top] using htopD'
        show (cbcInput (act δ f) (bf a) p = c) ↔ (cbcInput f (bf a) p = c)
        rw [hInv f hf δ hma (le_of_lt htop') hpl (by omega)]
  have hbaseInv : ∀ (δ : X) (f : X → X), base f → base (act δ f) := by
    intro δ f hf
    have hlt : i₁ ≤ t := le_trans hi₁le hlow
    have e₁ := hInv f hf δ ha₁ (by omega) hi₁len (by intro he; omega)
    have e₁' := hInv f hf δ hp₁ (by omega) hi₁'len (by intro he; omega)
    refine ⟨by rw [e₁, e₁']; exact hf.1, ?_, ?_⟩
    · intro ⟨D, hvD, htopD, hhD⟩
      exact hf.2.1 ⟨D, hvD, htopD, (hev f hf δ D hvD (by omega)).mp hhD⟩
    · intro D' hvD' hhD' htopD'
      exact huniq f hf D' hvD' ((hev f hf δ D' hvD' htopD').mp hhD') htopD'
  -- the `D₂`-top value shifts by `δ`; the base's own inputs and `D₂`'s low input are fixed
  have hj₂inv : ∀ (δ : X) (f : X → X), base f →
      cbcInput (act δ f) (bf m₂) j₂ = cbcInput f (bf m₂) j₂ :=
    fun δ f hf => hInv f hf δ hm₂ hj₂ hj₂len hj₂special
  have htopShift : ∀ (δ : X) (f : X → X), base f →
      cbcInput (act δ f) (bf m₂') (t + 1) = cbcInput f (bf m₂') (t + 1) + δ := by
    intro δ f hf
    refine cbcInput_top_pointShift_of_avoid f bf δ htlen fun p' hp' => ?_
    exact avoid_of_uniqueBelow bf l D₁ hm₂' (by omega) hblock (huniq f hf) hm₂' (le_of_lt hp')
      (by omega) (take_key_ne_of_level_lt bf (by omega) (by omega) hp')
  have key := Counting.card_filter_shift_univ (A := X) base
    (fun f => cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂))
    act hbaseInv
    (fun δ f hf => by
      show cbcInput (act δ f) (bf m₂') (t + 1) - (cbcInput (act δ f) (bf m₂) j₂ - c₂)
        = cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂) + δ
      rw [htopShift δ f hf, hj₂inv δ f hf]; abel)
    (fun δ δ' f hf => by
      show act δ' (act δ f) = act (δ + δ') f
      have hpred : cbcInput (act δ f) (bf m₂') t = cbcInput f (bf m₂') t :=
        hInv f hf δ hm₂' (by omega) (by omega) (by intro he; omega)
      show pointShift (act δ f) (cbcInput (act δ f) (bf m₂') t) δ' = _
      rw [hpred]
      exact pointShift_pointShift f _ δ δ')
    (fun f _ => pointShift_zero f _) (0 : X)
  -- `base ∧ value = 0` is exactly the four-way slice; drop uniqueness from `base` on the right
  calc (Finset.univ.filter fun f : X → X =>
          (cbcInput f (bf a₁) i₁ = cbcInput f (bf p₁) i₁' + c₁ ∧ ¬ chargedLt f bf l i₁' ∧
            (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 → D' = D₁))
          ∧ cbcInput f (bf m₂) j₂ = cbcInput f (bf m₂') (t + 1) + c₂).card * Fintype.card X
      = (Finset.univ.filter fun f : X → X =>
          cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂) = 0 ∧ base f).card
          * Fintype.card X := by
        congr 2
        refine Finset.filter_congr fun f _ => ?_
        constructor
        · rintro ⟨hb, h₂⟩; exact ⟨by rw [h₂]; abel, hb⟩
        · rintro ⟨h₂, hb⟩; refine ⟨hb, ?_⟩; rw [sub_eq_zero] at h₂; rw [h₂]; abel
    _ = (Finset.univ.filter fun f : X → X => base f).card := key
    _ ≤ (Finset.univ.filter fun f : X → X =>
          cbcInput f (bf a₁) i₁ = cbcInput f (bf p₁) i₁' + c₁ ∧ ¬ chargedLt f bf l i₁').card := by
        apply Finset.card_le_card
        intro f hf
        rw [Finset.mem_filter] at hf ⊢
        exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-- **First-event extraction**: a holding valid event yields one whose own top is fully
guarded. -/
theorem charged_exists_minimal (f : X → X) (bf : M → List X) (l : List M)
    (h : ∃ D : ChargedEvent M X, D.valid bf l ∧ D.holds f bf) :
    ∃ D : ChargedEvent M X, D.valid bf l ∧ D.holds f bf ∧ ¬ chargedLt f bf l D.top := by
  classical
  obtain ⟨D₀, hv₀, hh₀⟩ := h
  have hP : ∃ t, chargedLt f bf l t := ⟨D₀.top + 1, D₀, hv₀, Nat.lt_succ_self _, hh₀⟩
  obtain ⟨D, hv, htop, hh⟩ := Nat.find_spec hP
  exact ⟨D, hv, hh, fun hcl => Nat.find_min hP htop hcl⟩

/-- **Second-event extraction**: a holding valid event other than `D₁` yields one below whose
top every holding event *is* `D₁` — the uniqueness-below guard of the double charge. -/
theorem charged_exists_second_minimal (f : X → X) (bf : M → List X) (l : List M)
    (D₁ : ChargedEvent M X)
    (h : ∃ D : ChargedEvent M X, D ≠ D₁ ∧ D.valid bf l ∧ D.holds f bf) :
    ∃ D₂ : ChargedEvent M X, D₂ ≠ D₁ ∧ D₂.valid bf l ∧ D₂.holds f bf ∧
      ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top → D' = D₁ := by
  classical
  obtain ⟨D₀, hne₀, hv₀, hh₀⟩ := h
  have hP : ∃ t, ∃ D : ChargedEvent M X, D ≠ D₁ ∧ D.valid bf l ∧ D.top < t ∧ D.holds f bf :=
    ⟨D₀.top + 1, D₀, hne₀, hv₀, Nat.lt_succ_self _, hh₀⟩
  obtain ⟨D, hne, hv, htop, hh⟩ := Nat.find_spec hP
  refine ⟨D, hne, hv, hh, fun D' hv' hh' htop' => ?_⟩
  by_contra hne'
  exact Nat.find_min hP htop ⟨D', hne', hv', lt_of_lt_of_le htop' le_rfl, hh'⟩

/-- **The cover**: a bad structure-graph history is a fully-guarded terminal collision, or two
minimally-selected charged events with the layered guards. -/
theorem cbcGraphBad_cases (f : X → X) (bf : M → List X) (l : List M)
    (hbf_ne : ∀ m, bf m ≠ []) (hbad : cbcGraphBad f bf l) :
    (∃ D : ChargedEvent M X, D.valid bf l ∧ D.isTerminal bf ∧ D.holds f bf ∧
        ¬ chargedLt f bf l D.top) ∨
    (∃ D₁ D₂ : ChargedEvent M X, D₂ ≠ D₁ ∧ D₁.valid bf l ∧ D₁.holds f bf ∧
        D₂.valid bf l ∧ D₂.holds f bf ∧ D₁.top ≤ D₂.top ∧
        ¬ chargedLt f bf l D₁.top ∧
        (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top → D' = D₁)) := by
  classical
  have hinv : ∃ D : ChargedEvent M X, D.valid bf l ∧ D.holds f bf := by
    rcases hbad with hacc | ⟨m, hm, m', hm', j, hj, hkey, hval⟩
    · obtain ⟨Da, Db, hva, hha, -, -, -, -, -⟩ := two_chargedEvents_of_accidents f bf l hacc
      exact ⟨Da, hva, hha⟩
    · obtain ⟨D, hv, -, hh⟩ := chargedEvent_of_terminal f bf l hbf_ne hm hm' hj hkey hval
      exact ⟨D, hv, hh⟩
  obtain ⟨Dm, hvm, hhm, hguardm⟩ := charged_exists_minimal f bf l hinv
  by_cases hsecond : ∃ D : ChargedEvent M X, D ≠ Dm ∧ D.valid bf l ∧ D.holds f bf
  · right
    obtain ⟨D₂, hne₂, hv₂, hh₂, huniq⟩ := charged_exists_second_minimal f bf l Dm hsecond
    refine ⟨Dm, D₂, hne₂, hvm, hhm, hv₂, hh₂, ?_, hguardm, huniq⟩
    by_contra hlt
    push_neg at hlt
    exact hguardm ⟨D₂, hv₂, hlt, hh₂⟩
  · left
    push_neg at hsecond
    rcases hbad with hacc | ⟨m, hm, m', hm', j, hj, hkey, hval⟩
    · obtain ⟨Da, Db, hva, hha, -, hvb, hhb, -, hab⟩ :=
        two_chargedEvents_of_accidents f bf l hacc
      have ha : Da = Dm := by
        by_contra h
        exact (hsecond Da h hva) hha
      have hb : Db = Dm := by
        by_contra h
        exact (hsecond Db h hvb) hhb
      exact absurd (ha.trans hb.symm) hab
    · obtain ⟨D_T, hvT, hTterm, hhT⟩ :=
        chargedEvent_of_terminal f bf l hbf_ne hm hm' hj hkey hval
      have hTm : D_T = Dm := by
        by_contra h
        exact (hsecond D_T h hvT) hhT
      exact ⟨Dm, hvm, hTm ▸ hTterm, hhm, hguardm⟩

/-! ## The counting leg — the proven pieces

The union bound over descriptor pools.  The cover splits the bad mass into the terminal leg
`E₁` and the double-event leg `E₂` (`mass_cbcGraphBad_le_terminal_add_pairs`).  For `E₁` the
descriptors live in an explicit pool of `≤ 2q²L` elements — the terminal message contributes
its last block level only, the partner site is free, either side may be terminal — and each
costs `1/|X|` (`mass_chargedEvent_le`): this is the `ℓ`-linear headline term, proven in
`mass_terminal_chargedEvent_le`.  For `E₂`, `mass_two_chargedEvents_strictTop_le` settles the
generic configuration (`D₁.top < D₂.top`, pred-revisit shape excluded) at `1/|X|²` for all
four descriptor shapes; the equal-top and pred-revisit configurations — the corrected BPR05
Lemma 10 kernel — remain open. -/

/-- Finite union bound for `Dist.mass`, binary form. -/
private theorem mass_or_le {A : Type u} [Fintype A] [Nonempty A]
    (D : Dist A) (P Q : A → Prop) :
    D.mass (fun a => P a ∨ Q a) ≤ D.mass P + D.mass Q := by
  classical
  refine le_trans (mass_mono D (Q := fun a => ∃ b ∈ ({true, false} : Finset Bool),
      (if b then P a else Q a)) fun a h => ?_) (le_trans (mass_biUnion_le D _ _) ?_)
  · rcases h with h | h
    · exact ⟨true, by simp, by simpa⟩
    · exact ⟨false, by simp, by simpa⟩
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    exact add_le_add (le_of_eq (Dist.mass_congr _ fun a => by simp))
      (le_of_eq (Dist.mass_congr _ fun a => by simp))

/-- **The cover, mass form**: the bad mass splits into the guarded-terminal leg `E₁` and the
two-event leg `E₂`.  Together with `mass_terminal_chargedEvent_le` this pins the whole
remaining obligation of `mass_cbcGraphBad_le` on the `E₂` union. -/
theorem mass_cbcGraphBad_le_terminal_add_pairs (bf : M → List X) (l : List M)
    (hbf_ne : ∀ m, bf m ≠ []) :
    (Dist.uniform (X → X)).mass (fun f => cbcGraphBad f bf l)
      ≤ (Dist.uniform (X → X)).mass (fun f => ∃ D : ChargedEvent M X, D.valid bf l ∧
            D.isTerminal bf ∧ D.holds f bf ∧ ¬ chargedLt f bf l D.top)
        + (Dist.uniform (X → X)).mass (fun f => ∃ D₁ D₂ : ChargedEvent M X, D₂ ≠ D₁ ∧
            D₁.valid bf l ∧ D₁.holds f bf ∧ D₂.valid bf l ∧ D₂.holds f bf ∧
            D₁.top ≤ D₂.top ∧ ¬ chargedLt f bf l D₁.top ∧
            (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top →
              D' = D₁)) :=
  le_trans (mass_mono _ fun f hbad => cbcGraphBad_cases f bf l hbf_ne hbad)
    (mass_or_le _ _ _)

open Classical in
/-- **The terminal-descriptor pool**: an explicit `Finset` containing every valid terminal
charged event over the history `l` with block levels `< L` — the terminal side's level is
pinned to its message's last block, so the pool has at most `2q²L` elements, not `(qL)²`.
This is where the `ℓ`-linear win of the tolerant MBO is counted. -/
noncomputable def terminalEventPool (bf : M → List X) (l : List M) (L : ℕ) :
    Finset (ChargedEvent M X) :=
  ((((l.toFinset ×ˢ l.toFinset) ×ˢ Finset.range L).image fun x =>
      ChargedEvent.pair x.1.1 ((bf x.1.1).length - 1) x.1.2 x.2 0) ∪
    (((l.toFinset ×ˢ l.toFinset) ×ˢ Finset.range L).image fun x =>
      ChargedEvent.pair x.1.1 x.2 x.1.2 ((bf x.1.2).length - 1) 0)).filter
    fun D => D.valid bf l

omit [Fintype X] [Nonempty X] [Fintype M] in
/-- The terminal pool counts `2q²L`: terminal-involving site pairs number `q·qL` per side. -/
theorem card_terminalEventPool_le (bf : M → List X) (l : List M) (q L : ℕ)
    (hql : l.length ≤ q) :
    (terminalEventPool bf l L).card ≤ 2 * q ^ 2 * L := by
  classical
  have hq : l.toFinset.card ≤ q := le_trans l.toFinset_card_le hql
  have himg : ∀ g : (M × M) × ℕ → ChargedEvent M X,
      ((((l.toFinset ×ˢ l.toFinset) ×ˢ Finset.range L).image g)).card ≤ q ^ 2 * L := by
    intro g
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_product, Finset.card_range, sq]
    exact Nat.mul_le_mul (Nat.mul_le_mul hq hq) le_rfl
  refine le_trans (Finset.card_filter_le _ _) (le_trans (Finset.card_union_le _ _) ?_)
  calc ((((l.toFinset ×ˢ l.toFinset) ×ˢ Finset.range L).image fun x =>
          ChargedEvent.pair x.1.1 ((bf x.1.1).length - 1) x.1.2 x.2 0).card)
        + ((((l.toFinset ×ˢ l.toFinset) ×ˢ Finset.range L).image fun x =>
          ChargedEvent.pair x.1.1 x.2 x.1.2 ((bf x.1.2).length - 1) 0).card)
      ≤ q ^ 2 * L + q ^ 2 * L := Nat.add_le_add (himg _) (himg _)
    _ = 2 * q ^ 2 * L := by ring

omit [Fintype X] [Nonempty X] [Fintype M] in
/-- Every valid terminal descriptor lies in the pool. -/
theorem mem_terminalEventPool (bf : M → List X) (l : List M) (L : ℕ)
    (hbfL : ∀ m, (bf m).length ≤ L) {D : ChargedEvent M X}
    (hv : D.valid bf l) (hT : D.isTerminal bf) :
    D ∈ terminalEventPool bf l L := by
  classical
  cases D with
  | single m j c => exact hT.elim
  | pair m j m' j' c =>
      obtain ⟨hm, hm', hjl, hjl', -, -, -⟩ := id hv
      obtain ⟨rfl, hterm⟩ := hT
      refine Finset.mem_filter.mpr ⟨?_, hv⟩
      rcases hterm with h1 | h2
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨((m, m'), j'),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hm,
            List.mem_toFinset.mpr hm'⟩,
            Finset.mem_range.mpr (lt_of_lt_of_le hjl' (hbfL m'))⟩, ?_⟩)
        show ChargedEvent.pair m ((bf m).length - 1) m' j' 0 = ChargedEvent.pair m j m' j' 0
        rw [show (bf m).length - 1 = j from by omega]
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨((m, m'), j),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hm,
            List.mem_toFinset.mpr hm'⟩,
            Finset.mem_range.mpr (lt_of_lt_of_le hjl (hbfL m))⟩, ?_⟩)
        show ChargedEvent.pair m j m' ((bf m').length - 1) 0 = ChargedEvent.pair m j m' j' 0
        rw [show (bf m').length - 1 = j' from by omega]

/-- **The terminal leg `E₁` is proven**: a fully-guarded terminal collision costs at most
`2q²L/|X|` — the pool union bound at the `1/|X|` single-charge leaf
(`mass_chargedEvent_le`).  This is the linear-in-`L` headline term of
`mass_cbcGraphBad_le`, at exactly the stated constant. -/
theorem mass_terminal_chargedEvent_le (bf : M → List X) (l : List M) (q L : ℕ)
    (hql : l.length ≤ q) (hbfL : ∀ m, (bf m).length ≤ L) :
    (Dist.uniform (X → X)).mass (fun f => ∃ D : ChargedEvent M X, D.valid bf l ∧
        D.isTerminal bf ∧ D.holds f bf ∧ ¬ chargedLt f bf l D.top)
      ≤ (2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal) := by
  classical
  have hcover : ∀ f : X → X, (∃ D : ChargedEvent M X, D.valid bf l ∧ D.isTerminal bf ∧
      D.holds f bf ∧ ¬ chargedLt f bf l D.top) →
      ∃ D ∈ terminalEventPool bf l L, D.holds f bf ∧ ¬ chargedLt f bf l D.top := by
    rintro f ⟨D, hv, hT, hh, hg⟩
    exact ⟨D, mem_terminalEventPool bf l L hbfL hv hT, hh, hg⟩
  refine le_trans (mass_mono _ hcover) (le_trans (mass_biUnion_le _ _ _) ?_)
  calc ∑ D ∈ terminalEventPool bf l L,
        (Dist.uniform (X → X)).mass (fun f => D.holds f bf ∧ ¬ chargedLt f bf l D.top)
      ≤ ∑ _D ∈ terminalEventPool bf l L, 1 / (Fintype.card X : NNReal) :=
        Finset.sum_le_sum fun D hD =>
          mass_chargedEvent_le bf l D (Finset.mem_filter.mp hD).2
    _ = ((terminalEventPool bf l L).card : NNReal) / (Fintype.card X : NNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal) := by
        gcongr
        exact_mod_cast card_terminalEventPool_le bf l q L hql

/-- **Event truth below the shift level is preserved**: a valid charged event with top
`< t + 1` reads only inputs the guarded `D₂`-top shift fixes — `cbcInput_shift₂_invariant`
at each site.  Instantiated at `D₁` itself (base preservation) and at the guard events. -/
private theorem chargedEvent_holds_shift₂_iff (bf : M → List X) (l : List M)
    (D₁ : ChargedEvent M X) {b₂ : M} (hb₂ : b₂ ∈ l) {t : ℕ} (ht : t < (bf b₂).length)
    (hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i b₂ t 0) {f : X → X}
    (hu : ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 → D' = D₁)
    (δ : X) (D' : ChargedEvent M X) (hvD' : D'.valid bf l) (htopD' : D'.top < t + 1) :
    D'.holds (pointShift f (cbcInput f (bf b₂) t) δ) bf ↔ D'.holds f bf := by
  cases D' with
  | pair a p a' p' c =>
      obtain ⟨hma, hma', hpl, hpl', hple, -⟩ := hvD'
      have htop' : p' < t + 1 := by simpa [ChargedEvent.top] using htopD'
      show (cbcInput (pointShift f (cbcInput f (bf b₂) t) δ) (bf a) p
          = cbcInput (pointShift f (cbcInput f (bf b₂) t) δ) (bf a') p' + c)
        ↔ (cbcInput f (bf a) p = cbcInput f (bf a') p' + c)
      rw [cbcInput_shift₂_invariant bf l D₁ hb₂ ht hblock hu δ hma (by omega) hpl
          (by intro he; omega),
        cbcInput_shift₂_invariant bf l D₁ hb₂ ht hblock hu δ hma' (by omega) hpl'
          (by intro he; omega)]
  | single a p c =>
      obtain ⟨hma, hpl, -⟩ := hvD'
      have htop' : p < t + 1 := by simpa [ChargedEvent.top] using htopD'
      show (cbcInput (pointShift f (cbcInput f (bf b₂) t) δ) (bf a) p = c)
        ↔ (cbcInput f (bf a) p = c)
      rw [cbcInput_shift₂_invariant bf l D₁ hb₂ ht hblock hu δ hma (by omega) hpl
        (by intro he; omega)]

open Classical in
/-- **The double slice, descriptor form** (strict top order): for any two valid charged
events with `D₁.top < D₂.top` — all four shape combinations — provided `D₁` is not itself a
`c = 0` collision into the predecessor site of `D₂`'s top (`hblock`, the pred-revisit
configuration), the joint slice carries at most a `1/|X|` fraction of the guarded base
`D₁ ∧ guard`.  Generalizes `card_two_chargedEvents_mul_le` beyond pair/pair and discharges
the same-computation degeneracy of `D₂` internally (a same-take equal-level pair never
holds, by validity's key clause). -/
theorem card_two_chargedEvents_strictTop_mul_le (bf : M → List X) (l : List M)
    (D₁ D₂ : ChargedEvent M X) (hv₁ : D₁.valid bf l) (hv₂ : D₂.valid bf l)
    (hlt : D₁.top < D₂.top)
    (hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i D₂.topMsg (D₂.top - 1) 0) :
    (Finset.univ.filter fun f : X → X =>
        (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
          (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top →
            D' = D₁)) ∧ D₂.holds f bf).card * Fintype.card X
      ≤ (Finset.univ.filter fun f : X → X =>
          D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top).card := by
  cases D₂ with
  | single m₂ j₂ c₂ =>
      obtain ⟨hm₂, hj₂len, hj₂1, hc₂⟩ := hv₂
      obtain ⟨t, rfl⟩ : ∃ t, j₂ = t + 1 := ⟨j₂ - 1, by omega⟩
      -- definitional casts: `topMsg`/`top` of the constructor reduce by iota
      replace hlt : D₁.top < t + 1 := hlt
      replace hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i m₂ t 0 := hblock
      -- rewrite the two constructor spots of the goal; `D₁`/`D'` occurrences stay abstract
      simp only [show ∀ f : X → X, ChargedEvent.holds f bf (ChargedEvent.single m₂ (t + 1) c₂)
          = (cbcInput f (bf m₂) (t + 1) = c₂) from fun f => rfl,
        show (ChargedEvent.single m₂ (t + 1) c₂ : ChargedEvent M X).top = t + 1 from rfl]
      set base : (X → X) → Prop := fun f =>
        D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
          (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
            D' = D₁) with hbase
      have huniq : ∀ f, base f → ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf →
          D'.top < t + 1 → D' = D₁ := fun f hf => hf.2.2
      set act : X → (X → X) → (X → X) := fun δ f => pointShift f (cbcInput f (bf m₂) t) δ
        with hact
      have hbaseInv : ∀ (δ : X) (f : X → X), base f → base (act δ f) := by
        intro δ f hf
        refine ⟨(chargedEvent_holds_shift₂_iff bf l D₁ hm₂ (by omega) hblock
            (huniq f hf) δ D₁ hv₁ hlt).mpr hf.1, ?_, ?_⟩
        · rintro ⟨D, hvD, htopD, hhD⟩
          exact hf.2.1 ⟨D, hvD, htopD, (chargedEvent_holds_shift₂_iff bf l D₁ hm₂ (by omega)
            hblock (huniq f hf) δ D hvD (by omega)).mp hhD⟩
        · intro D' hvD' hhD' htopD'
          exact huniq f hf D' hvD' ((chargedEvent_holds_shift₂_iff bf l D₁ hm₂ (by omega)
            hblock (huniq f hf) δ D' hvD' htopD').mp hhD') htopD'
      have htopShift : ∀ (δ : X) (f : X → X), base f →
          cbcInput (act δ f) (bf m₂) (t + 1) = cbcInput f (bf m₂) (t + 1) + δ := by
        intro δ f hf
        refine cbcInput_top_pointShift_of_avoid f bf δ hj₂len fun p' hp' => ?_
        exact avoid_of_uniqueBelow bf l D₁ hm₂ (by omega) hblock (huniq f hf) hm₂
          (le_of_lt hp') (by omega) (take_key_ne_of_level_lt bf (by omega) (by omega) hp')
      have key := Counting.card_filter_shift_univ (A := X) base
        (fun f => cbcInput f (bf m₂) (t + 1) - c₂) act hbaseInv
        (fun δ f hf => by
          show cbcInput (act δ f) (bf m₂) (t + 1) - c₂
            = cbcInput f (bf m₂) (t + 1) - c₂ + δ
          rw [htopShift δ f hf]; abel)
        (fun δ δ' f hf => by
          show act δ' (act δ f) = act (δ + δ') f
          have hpred : cbcInput (act δ f) (bf m₂) t = cbcInput f (bf m₂) t :=
            cbcInput_shift₂_invariant bf l D₁ hm₂ (by omega) hblock (huniq f hf) δ hm₂
              (by omega) (by omega) (by intro he; omega)
          show pointShift (act δ f) (cbcInput (act δ f) (bf m₂) t) δ' = _
          rw [hpred]
          exact pointShift_pointShift f _ δ δ')
        (fun f _ => pointShift_zero f _) 0
      calc (Finset.univ.filter fun f : X → X =>
              (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
                (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
                  D' = D₁)) ∧ cbcInput f (bf m₂) (t + 1) = c₂).card * Fintype.card X
          = (Finset.univ.filter fun f : X → X =>
              cbcInput f (bf m₂) (t + 1) - c₂ = 0 ∧ base f).card * Fintype.card X := by
            congr 2
            refine Finset.filter_congr fun f _ => ?_
            constructor
            · rintro ⟨hb, h₂⟩
              exact ⟨by rw [h₂]; abel, hb⟩
            · rintro ⟨h₂, hb⟩
              refine ⟨hb, ?_⟩
              rwa [sub_eq_zero] at h₂
        _ = (Finset.univ.filter base).card := key
        _ ≤ (Finset.univ.filter fun f : X → X =>
              D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top).card := by
            apply Finset.card_le_card
            intro f hf
            rw [Finset.mem_filter] at hf ⊢
            exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  | pair m₂ j₂ m₂' j₂' c₂ =>
      obtain ⟨hm₂, hm₂', hj₂len, hj₂'len, hjle, hkey₂, hcs₂⟩ := hv₂
      have hj₂'pos : 0 < j₂' :=
        lt_of_le_of_lt (Nat.zero_le _) (by simpa [ChargedEvent.top] using hlt)
      obtain ⟨t, rfl⟩ : ∃ t, j₂' = t + 1 := ⟨j₂' - 1, by omega⟩
      -- definitional casts: `topMsg`/`top` of the constructor reduce by iota
      replace hlt : D₁.top < t + 1 := hlt
      replace hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i m₂' t 0 := hblock
      -- rewrite the two constructor spots of the goal; `D₁`/`D'` occurrences stay abstract
      simp only [show ∀ f : X → X, ChargedEvent.holds f bf (ChargedEvent.pair m₂ j₂ m₂' (t + 1) c₂)
          = (cbcInput f (bf m₂) j₂ = cbcInput f (bf m₂') (t + 1) + c₂) from fun f => rfl,
        show (ChargedEvent.pair m₂ j₂ m₂' (t + 1) c₂ : ChargedEvent M X).top = t + 1 from rfl]
      by_cases hpe : j₂ = t + 1 ∧ (bf m₂).take (t + 1) = (bf m₂').take (t + 1)
      · -- same-computation degeneracy: the event never holds (validity's key clause)
        obtain ⟨rfl, hpe⟩ := hpe
        have hc0 : c₂ = 0 := by
          rcases hcs₂ with h | ⟨-, -, hpred⟩
          · exact h
          · exact absurd hpe hpred
        subst hc0
        have hne : (bf m₂).getD (t + 1) 0 ≠ (bf m₂').getD (t + 1) 0 :=
          getD_ne_of_take_eq_of_take_succ_ne 0 hpe hkey₂ hj₂len hj₂'len
        have hempty : ∀ f : X → X, ¬ ((D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
            (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
              D' = D₁)) ∧
            cbcInput f (bf m₂) (t + 1) = cbcInput f (bf m₂') (t + 1) + 0) := by
          rintro f ⟨-, h₂⟩
          rw [add_zero] at h₂
          unfold cbcInput at h₂
          rw [show cbcState f ((bf m₂).take (t + 1)) = cbcState f ((bf m₂').take (t + 1))
            from by rw [hpe]] at h₂
          exact hne (add_left_cancel h₂)
        rw [Finset.filter_eq_empty_iff.mpr fun f _ => hempty f, Finset.card_empty,
          Nat.zero_mul]
        exact Nat.zero_le _
      · have hsplit : j₂ ≤ t ∨ j₂ = t + 1 ∧ (bf m₂).take (t + 1) ≠ (bf m₂').take (t + 1) := by
          grind
        set base : (X → X) → Prop := fun f =>
          D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
            (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
              D' = D₁) with hbase
        have huniq : ∀ f, base f → ∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf →
            D'.top < t + 1 → D' = D₁ := fun f hf => hf.2.2
        set act : X → (X → X) → (X → X) := fun δ f => pointShift f (cbcInput f (bf m₂') t) δ
          with hact
        have hbaseInv : ∀ (δ : X) (f : X → X), base f → base (act δ f) := by
          intro δ f hf
          refine ⟨(chargedEvent_holds_shift₂_iff bf l D₁ hm₂' (by omega) hblock
              (huniq f hf) δ D₁ hv₁ hlt).mpr hf.1, ?_, ?_⟩
          · rintro ⟨D, hvD, htopD, hhD⟩
            exact hf.2.1 ⟨D, hvD, htopD, (chargedEvent_holds_shift₂_iff bf l D₁ hm₂'
              (by omega) hblock (huniq f hf) δ D hvD (by omega)).mp hhD⟩
          · intro D' hvD' hhD' htopD'
            exact huniq f hf D' hvD' ((chargedEvent_holds_shift₂_iff bf l D₁ hm₂' (by omega)
              hblock (huniq f hf) δ D' hvD' htopD').mp hhD') htopD'
        have hj₂inv : ∀ (δ : X) (f : X → X), base f →
            cbcInput (act δ f) (bf m₂) j₂ = cbcInput f (bf m₂) j₂ := by
          intro δ f hf
          refine cbcInput_shift₂_invariant bf l D₁ hm₂' (by omega) hblock (huniq f hf) δ
            hm₂ hjle hj₂len ?_
          rcases hsplit with h | ⟨-, hne⟩
          · intro he; omega
          · intro _; exact hne
        have htopShift : ∀ (δ : X) (f : X → X), base f →
            cbcInput (act δ f) (bf m₂') (t + 1) = cbcInput f (bf m₂') (t + 1) + δ := by
          intro δ f hf
          refine cbcInput_top_pointShift_of_avoid f bf δ hj₂'len fun p' hp' => ?_
          exact avoid_of_uniqueBelow bf l D₁ hm₂' (by omega) hblock (huniq f hf) hm₂'
            (le_of_lt hp') (by omega) (take_key_ne_of_level_lt bf (by omega) (by omega) hp')
        have key := Counting.card_filter_shift_univ (A := X) base
          (fun f => cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂)) act hbaseInv
          (fun δ f hf => by
            show cbcInput (act δ f) (bf m₂') (t + 1)
                - (cbcInput (act δ f) (bf m₂) j₂ - c₂)
              = cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂) + δ
            rw [htopShift δ f hf, hj₂inv δ f hf]; abel)
          (fun δ δ' f hf => by
            show act δ' (act δ f) = act (δ + δ') f
            have hpred : cbcInput (act δ f) (bf m₂') t = cbcInput f (bf m₂') t :=
              cbcInput_shift₂_invariant bf l D₁ hm₂' (by omega) hblock (huniq f hf) δ hm₂'
                (by omega) (by omega) (by intro he; omega)
            show pointShift (act δ f) (cbcInput (act δ f) (bf m₂') t) δ' = _
            rw [hpred]
            exact pointShift_pointShift f _ δ δ')
          (fun f _ => pointShift_zero f _) 0
        calc (Finset.univ.filter fun f : X → X =>
                (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
                  (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < t + 1 →
                    D' = D₁)) ∧
                  cbcInput f (bf m₂) j₂ = cbcInput f (bf m₂') (t + 1) + c₂).card
                * Fintype.card X
            = (Finset.univ.filter fun f : X → X =>
                cbcInput f (bf m₂') (t + 1) - (cbcInput f (bf m₂) j₂ - c₂) = 0
                  ∧ base f).card * Fintype.card X := by
              congr 2
              refine Finset.filter_congr fun f _ => ?_
              constructor
              · rintro ⟨hb, h₂⟩
                exact ⟨by rw [h₂]; abel, hb⟩
              · rintro ⟨h₂, hb⟩
                refine ⟨hb, ?_⟩
                rw [sub_eq_zero] at h₂
                rw [h₂]
                abel
          _ = (Finset.univ.filter base).card := key
          _ ≤ (Finset.univ.filter fun f : X → X =>
                D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top).card := by
              apply Finset.card_le_card
              intro f hf
              rw [Finset.mem_filter] at hf ⊢
              exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-- **The strict-top double charge costs `1/|X|²`**: the two slices composed —
`card_two_chargedEvents_strictTop_mul_le` at the `D₂` top, then `card_chargedEvent_mul_le`
at the `D₁` top.  With `cbcGraphBad_cases` this settles every `E₂` configuration except
equal tops (`D₁.top = D₂.top`) and the pred-revisit shape (`hblock`) — the corrected BPR05
Lemma 10 kernel. -/
theorem mass_two_chargedEvents_strictTop_le (bf : M → List X) (l : List M)
    (D₁ D₂ : ChargedEvent M X) (hv₁ : D₁.valid bf l) (hv₂ : D₂.valid bf l)
    (hlt : D₁.top < D₂.top)
    (hblock : ∀ (a : M) (i : ℕ), D₁ ≠ .pair a i D₂.topMsg (D₂.top - 1) 0) :
    (Dist.uniform (X → X)).mass (fun f =>
        (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
          (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top →
            D' = D₁)) ∧ D₂.holds f bf)
      ≤ 1 / (Fintype.card X : NNReal) ^ 2 := by
  classical
  have hcard : (Finset.univ.filter fun f : X → X =>
      (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
        (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top →
          D' = D₁)) ∧ D₂.holds f bf).card * Fintype.card (X × X)
      ≤ Fintype.card (X → X) := by
    rw [Fintype.card_prod, ← Nat.mul_assoc]
    calc (Finset.univ.filter fun f : X → X =>
            (D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top ∧
              (∀ D' : ChargedEvent M X, D'.valid bf l → D'.holds f bf → D'.top < D₂.top →
                D' = D₁)) ∧ D₂.holds f bf).card * Fintype.card X * Fintype.card X
        ≤ (Finset.univ.filter fun f : X → X =>
            D₁.holds f bf ∧ ¬ chargedLt f bf l D₁.top).card * Fintype.card X :=
          Nat.mul_le_mul (card_two_chargedEvents_strictTop_mul_le bf l D₁ D₂ hv₁ hv₂
            hlt hblock) le_rfl
      _ ≤ (Finset.univ.filter fun f : X → X => ¬ chargedLt f bf l D₁.top).card :=
          card_chargedEvent_mul_le bf l D₁ hv₁
      _ ≤ Fintype.card (X → X) := Finset.card_le_univ _
  have h := Dist.uniform_mass_le_inv_card_of_card_mul_le (B := X × X) _ hcard
  rwa [show ((Fintype.card (X × X) : NNReal)) = (Fintype.card X : NNReal) ^ 2 from by
    rw [Fintype.card_prod, Nat.cast_mul, sq]] at h

/-! ## The counting leg and the headline (open — the JN combinatorics campaign) -/

/-- **The pure combinatorial counting bound** (JN16, corrected BPR05 Lemma 10): over a fixed
history of `≤ q` messages of `≤ L` blocks, the uniform round function provokes the tolerant
structure-graph event with probability `≤ 2q²L/|X| + (qL)⁴/|X|²`.

This is the sole remaining obligation of the beyond-birthday route.  The split and the `E₁`
leg are proven above at the stated constant: `mass_cbcGraphBad_le_terminal_add_pairs` (the
cover in mass form) and `mass_terminal_chargedEvent_le` (`E₁ ≤ 2q²L/|X|` via the
`terminalEventPool` union at the `mass_chargedEvent_le` leaf).  For `E₂`,
`mass_two_chargedEvents_strictTop_le` proves the `1/|X|²` per-pair bound for every
configuration with `D₁.top < D₂.top` outside the pred-revisit shape (`hblock`).  What
remains is (a) the equal-top configuration `D₁.top = D₂.top` (two events sharing their top
chain — the forced-difference rewrite) and the pred-revisit configuration (`D₁` a `c = 0`
collision into the predecessor of `D₂`'s top) — together the corrected Lemma-10 kernel,
including a sharpening of the cover that excludes forced-twin descriptor pairs (whose joint
event costs only `1/|X|`); and (b) the `E₂` descriptor-pair union itself.  **Caveat on the
stated constant**: the valid-descriptor pool has `q²L(L+1) + q(L−1) ≤ 2(qL)²` elements (two
constants per sorted site pair), so the pair union supports `4(qL)⁴`, not `(qL)⁴`; the
second term as stated is not reachable by the descriptor-pair union bound. -/
theorem mass_cbcGraphBad_le (bf : M → List X) (l : List M) (q L : ℕ)
    (hbf_ne : ∀ m, bf m ≠ []) (hql : l.length ≤ q) (hbfL : ∀ m, (bf m).length ≤ L) :
    (Dist.uniform (X → X)).mass (fun f => cbcGraphBad f bf l)
      ≤ (2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal)
        + ((q * L) ^ 4 : ℕ) / (Fintype.card X : NNReal) ^ 2 := by
  sorry

/-- **The counting leg** (JN16, the corrected BPR05 combinatorics): a blind winner provokes a
bad structure-graph event with probability `𝒪(q²L/|X|)` — terminal-involving pairs number
`q·qL`, not `(qL)²` — plus the two-accident tail `𝒪((qL)⁴/|X|²)`.  The blind-winner reduction
(Thm 4.17's `Γᵇ` shape) is the same as the birthday leg's; the per-schedule mass bound is the
combinatorial `mass_cbcGraphBad_le`. -/
theorem blindMaxWinProb_cbcGraphGame_le (bf : M → List X) (q L : ℕ)
    (hbf_ne : ∀ m, bf m ≠ []) (hL : ∀ m, (bf m).length ≤ L) :
    (Γᵇ (⌈q⌉ cbcGraphGame bf) : ℝ)
      ≤ ((2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal)
          + ((q * L) ^ 4 : ℕ) / (Fintype.card X : NNReal) ^ 2 : NNReal) := by
  rw [NNReal.coe_le_coe]
  exact blindMaxWinProb_filterQueries_monitored_le (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f => cbcGraphBad f bf)
    Dist.uniform_nonNeg (fun f => cbcGraphBad_monotone f bf) q _
    fun w _ => mass_cbcGraphBad_le bf (blindQueryList w q) q L hbf_ne
      (blindQueryList_length_le w q) hL

/-- **CBC-MAC beyond the birthday bound in `ℓ`** (Jha–Nandi via Maurer): the distinguishing
advantage is linear, not quadratic, in the block length.  Same two paper citations as
Theorem 6.1 — Thm 4.17 at the tolerant conditional equivalence, then the counting leg. -/
theorem cbc_mac_beyond_birthday [Nontrivial M] (bf : M → List X) (q L : ℕ)
    (hbf_pf : PrefixFree bf) (hL : ∀ m, (bf m).length ≤ L) :
    Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn)
      ≤ ((2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal)
          + ((q * L) ^ 4 : ℕ) / (Fintype.card X : NNReal) ^ 2 : NNReal) :=
  calc Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn)
      ≤ (Γᵇ (⌈q⌉ cbcGraphGame bf) : ℝ) :=
        maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv q (cbcGraphGame bf)
          (cbcGraphGame_condEquiv bf hbf_pf)
    _ ≤ ((2 * q ^ 2 * L : ℕ) / (Fintype.card X : NNReal)
          + ((q * L) ^ 4 : ℕ) / (Fintype.card X : NNReal) ^ 2 : NNReal) :=
        blindMaxWinProb_cbcGraphGame_le bf q L hbf_pf.ne_nil hL

end RandomSystems.CR18
