/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SwitchingLemma
import RandomSystems.FilterDomNormalization
import RandomSystems.AbsorbDPI
import RandomSystems.CompatibleMetric
import RandomSystems.StepRealization
import RandomSystems.SemanticRegistry
import RandomSystems.StrictContextSharedDomain

cc_diagram_labels cbcReal "CBC 𝖱", cbcRealP "CBC 𝖯", Vn "Vₙ", cbcGame "ĈBC 𝖱", cbcStep "CBC", PFunPDS.URF "𝖱", PFunPDS.URP "𝖯"

/-!
# CR18 §6.2.3 — the CBC-MAC as a randomness expander (Theorem 6.1)

Maurer's *simpler* CBC-MAC proof, carried out purely in the conditional-equivalence framework
(CR18 §4.11), following the exact skeleton of the URP–URF switching lemma (`urf_urp_switching`,
Lemma 4.19): conditional equivalence `ĈBC 𝖱 |≡ Vₙ` (eq. 6.2), then Theorem 4.17, then the birthday
bound (Lemma 4.18).

The proof's one engine (`Rerandomise` section): the chaining reads its round function only at its
own call-site inputs, so translating it at *fresh* points is a free, measure-preserving symmetry —
at the terminal inputs it makes eq. (6.2)'s MAC-fibers balanced, at a guarded predecessor input it
gives the per-pair birthday leaf.

* the base round function is a uniform `f : X → X` (the URF `Rₙ,ₙ`, `X = {0,1}ⁿ`);
* a message `m : M` is expanded by a prefix-free block former `bf : M → List X`;
* CBC **is a converter** (`cbcStep`, Def 3.8): `cbcReal = casc[CBC, 𝖱]` and `cbcRealP =
  casc[CBC, 𝖯]` are its Def 3.9 applications to the two resources; `Vn` is the ideal VIL-URF
  (CR18 Def 6.1).

The **block-cipher corollary** (`cbc_mac_randomness_expander_urp`, not tight): `casc[CBC, 𝖯]`
over the uniform round *permutation*, by a stepwise calculation — triangle through
`casc[CBC, 𝖱]`, the query-budgeted converter DPI (the same converter, two resources), the
`Δ`-swap, the switching lemma (Lemma 4.19), and Theorem 6.1.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

-- Standing `[Fintype _] [DecidableEq _]` section variables are shared by most but not all lemmas;
-- repo convention (`Dist.lean`, `HCTR2.lean`) silences the per-theorem inclusion lint.
set_option linter.unusedSectionVars false

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- **The CBC converter's chaining.** Digest the block sequence `bs` block by block, invoking the
round function `f` at each step: `y₀ = 0`, `yⱼ = f (y_{j-1} + bⱼ)`.  The CBC-MAC of `bs` is the final
chaining value.  The initial state is the fixed, public constant `0` (Maurer, CR18 §6.2.3: "the initial
value of the state is a fixed and known parameter"). -/
def cbcState (f : X → X) (bs : List X) : X :=
  bs.foldl (fun y b => f (y + b)) 0

/-- **The CBC protocol step** (CR18 Def 3.8, outer-memoryless): on outer query `m`, having
received the chaining values `ys` so far (`y₀ = 0`), issue the next round-function input
`y_c + b_c`; once the blocks are exhausted, answer the final chaining value.  This is `cbcState`
presented as a *converter* — `casc[CBC, ·]` below is its Def 3.9 application. -/
def cbcStep (bf : M → List X) (m : M) (ys : List X) : X ⊕ X :=
  if ys.length < (bf m).length
  then Sum.inl (ys.getLastD 0 + (bf m).getD ys.length 0)
  else Sum.inr (ys.getLastD 0)

/-- The CBC converter answers within `L` rounds (Def 3.8's round bound). -/
theorem cbcStep_answersWithin (bf : M → List X) {L : ℕ} (hL : ∀ m, (bf m).length ≤ L) :
    PFunConverter.DDC.AnswersWithin (cbcStep bf) L := by
  intro m ys hlen
  exact ⟨ys.getLastD 0, by unfold cbcStep; rw [if_neg (by have := hL m; omega)]⟩

/-- **The real system `casc[CBC, 𝖱]`** (Maurer's `CBC Rₙ,ₙ`): the CBC converter applied (Def 3.9)
to the uniform round *function*. -/
noncomputable def cbcReal (bf : M → List X) : PFunPDS M X :=
  PFunPDS.applyDDC (PFunConverter.DDC.ofStep (cbcStep bf)) (𝖱 X)

/-- **The real system `casc[CBC, 𝖯]`**: the *same* converter applied to the uniform round
*permutation* (the ideal-cipher instantiation) — only the resource changes. -/
noncomputable def cbcRealP (bf : M → List X) : PFunPDS M X :=
  PFunPDS.applyDDC (PFunConverter.DDC.ofStep (cbcStep bf)) (𝖯 X)

/-- **The ideal VIL-URF `Vₙ`** (CR18 Def 6.1): a uniform random function `M → X` — fresh uniform per
new message, consistent on repeats.

Finite-`M` caveat: the paper's `Vₙ` is the *behavior* of a `({0,1}*, {0,1}ⁿ)`-system (Def 3.18 /
Example 3.7) — footnote 2 notes it admits no PDS over the infinite message alphabet.  Here the
message space `M` is a standing finite type, so `Vₙ` is an honest PDS (Def 3.14): the Def 6.1
behavior restricted to `M`.  The theorems below are uniform in every finite `M`, with an
`|M|`-independent bound, which is how the VIL content is recovered (any `q`-query distinguisher
of the VIL system touches finitely many messages). -/
noncomputable def Vn : PFunPDS M X := PFunPDS.URF (X := M) (Y := X)

/-- A **prefix-free block former** — Maurer's standing assumption on the message encoding
(CR18 §6.2.3): distinct messages have incomparable block sequences. -/
def PrefixFree (bf : M → List X) : Prop :=
  ∀ m m', m ≠ m' → ¬ (bf m <+: bf m')

/-- With at least two messages, a prefix-free block former has no empty block sequence — the empty
word prefixes everything.  Maurer's single prefix-freeness assumption already carries
nonemptiness. -/
theorem PrefixFree.ne_nil [Nontrivial M] {bf : M → List X} (h : PrefixFree bf) (m : M) :
    bf m ≠ [] := by
  intro hnil
  obtain ⟨m', hm'⟩ := exists_ne m
  exact h m m' hm'.symm (by rw [hnil]; exact List.nil_prefix)

/-! ## Scheme-agnostic condition-C wrapper

The CBC proof below and Gaži's NMAC outer-call proof have the same CR18
spine.  A seed chooses a deterministic inner map `F`; a monotone predicate
`bad` records the first loss of condition C; conditional equivalence gives
the ideal system while `bad` is false; and a blind winner fixes one query
schedule, on which the remaining work is an ordinary seed-event bound.

This theorem is deliberately independent of CBC chaining.  It packages the
condition-equivalence and first-bad reduction once, leaving schemes only the
conditional-equivalence witness and their fixed-schedule collision count.
-/

/-! ## Step 1 — Maurer's MBO `Aᵢ`: a non-trivial collision at the round-function input

Maurer (CR18 §6.2.3): *"`Aᵢ = 1` iff, up to the evaluation of the `i`-th message, a non-trivial
collision has occurred at the input to `Rₙ,ₙ`. By non-trivial we mean that collisions do not count if
they hold because two messages have the same prefix."*

Processing a block sequence `bs` with round function `f` invokes `f` once per block: at block position
`j` (0-indexed) the input is `uⱼ = y_{j} + b_{j}` where `yⱼ = cbcState f (bs.take j)`.  Two invocations
are *the same computation* exactly when their identifying block-prefix `bs.take (j+1)` agrees (a shared
message prefix), so a **non-trivial** collision is two call sites with **distinct** keys but equal
inputs. -/

/-- The round-function input at block position `j` (0-indexed) of block sequence `bs`:
`uⱼ = cbcState f (bs.take j) + bⱼ` — the chaining value after the first `j` blocks, plus block `j`. -/
def cbcInput (f : X → X) (bs : List X) (j : ℕ) : X :=
  cbcState f (bs.take j) + bs.getD j 0

/-- **Maurer's MBO `Aᵢ`.** A non-trivial round-function-input collision in the history `l`: two call
sites `(m, j)`, `(m', j')` — message `m ∈ l`, block position `j < |bf m|` — whose *keys*
`(bf m).take (j+1)` differ (equal keys ⟺ shared block-prefix ⟺ literally the same call, the trivial
collisions Maurer discounts) but whose inputs to `Rₙ,ₙ` coincide. -/
def cbcBad (f : X → X) (bf : M → List X) (l : List M) : Prop :=
  ∃ m ∈ l, ∃ m' ∈ l, ∃ j < (bf m).length, ∃ j' < (bf m').length,
    (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧ cbcInput f (bf m) j = cbcInput f (bf m') j'

instance (f : X → X) (bf : M → List X) (l : List M) : Decidable (cbcBad f bf l) := by
  unfold cbcBad; infer_instance

/-- **The game `ĈBC 𝖱` per deterministic round function `f`** (Maurer's `ĈBC Rₙ,ₙ`): the
history-dependent system whose visible output on history `l` is the CBC-MAC of the last message,
tagged with the MBO bit `Aᵢ = cbcBad f bf l`. -/
noncomputable def cbcGameDDS (f : X → X) (bf : M → List X) : PFunDDS.DDS M (X × Bool) :=
  PFunDDS.historyEvaluator (fun l hne =>
    (cbcState f (bf (l.getLast hne)), decide (cbcBad f bf l)))

/-- **The game `ĈBC 𝖱`** as a probabilistic system: push the uniform round function `f : X → X`
through `cbcGameDDS`.  Its MBO-stripped system is `cbcReal` (`cbcGame_ignoreMBO`). -/
noncomputable def cbcGame (bf : M → List X) : PFunPDS M (X × Bool) :=
  seededConditionCGame (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f l => cbcBad f bf l)

/-- The shared condition-C presentation of `cbcGame` is definitionally the
original uniform mixture of the deterministic CBC games. -/
theorem cbcGame_eq_fTransform_cbcGameDDS (bf : M → List X) :
    cbcGame bf =
      Dist.fTransform (fun f : X → X => cbcGameDDS f bf) (Dist.uniform (X → X)) := by
  rfl

/-! ### Standing facts about the game (registered below for `cr18_standing` discharge) -/

/-- The CBC inner-collision bit is monotone in the query history: a witnessing pair of call sites is
never lost when the history grows. -/
theorem cbcBad_monotone (f : X → X) (bf : M → List X)
    {l₁ l₂ : List M} (hpre : l₁ <+: l₂) (h : cbcBad f bf l₁) : cbcBad f bf l₂ := by
  obtain ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩ := h
  exact ⟨m, hpre.subset hm, m', hpre.subset hm', j, hj, j', hj', hkey, hval⟩

-- Teach `grind` the MBO's monotonicity: any grind call in this development may chain it forward.
attribute [grind →] cbcBad_monotone

/-- `Aᵢ`'s monotonicity in `decide`d form — the shape the history-game laws consume. -/
private theorem cbcBad_decide_monotone (f : X → X) (bf : M → List X) :
    ∀ {l₁ l₂ : List M}, l₁ <+: l₂ →
      decide (cbcBad f bf l₁) = true → decide (cbcBad f bf l₂) = true := fun hpre hb => by
  simpa using cbcBad_monotone f bf hpre (by simpa using hb)

/-- The game's MBO is monotone — each realization is an MBO game (CR18 Def 3.22). -/
theorem cbcGame_monotoneMBO (bf : M → List X) : MonotoneMBO (cbcGame bf) :=
  seededConditionCGame_monotoneMBO (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f l => cbcBad f bf l)
    (fun f => cbcBad_monotone f bf)

/-- The game is a probability system (a deterministic pushforward of the uniform round function). -/
theorem cbcGame_isProbDist (bf : M → List X) : (cbcGame bf).isProbDist := by
  exact seededConditionCGame_isProbDist (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f l => cbcBad f bf l)
    Dist.uniform_isProbDist

/-- The game is total on nonempty histories (`historyEvaluator` accepts every nonempty list). -/
theorem cbcGame_totalOnNonempty (bf : M → List X) :
    CondEquiv.TotalOnNonempty (cbcGame bf) :=
  seededConditionCGame_totalOnNonempty (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f l => cbcBad f bf l)

/-- `Vₙ` is a probability system. -/
theorem Vn_isProbDist : (Vn (M := M) (X := X)).isProbDist :=
  PFunPDS.URF_isProbDist

/-- `Vₙ` is total on nonempty histories. -/
theorem Vn_totalOnNonempty : CondEquiv.TotalOnNonempty (Vn (M := M) (X := X)) :=
  PFunPDS.URF_totalOnNonempty

-- **The game's standing facts**, registered for automatic discharge (`cr18_standing`): a
-- monotone-MBO probability system, total on nonempty histories, whose stripped system is `CBC𝖱`;
-- `Vₙ` a total probability system.  Paper theorems then apply on their mathematical inputs alone.
attribute [cr18_standing] cbcGame_monotoneMBO cbcGame_isProbDist
  Vn_isProbDist cbcGame_totalOnNonempty Vn_totalOnNonempty
-- (`cbcGame_ignoreMBO` joins the standing facts after the realization section below.)

/-! ### The re-randomisation engine and the birthday decomposition (internal machinery)

The one engine behind both obligations: `cbcState f bs` reads `f` only at the call-site inputs
`cbcInput f bs j`.  So translating `f` at the *terminal* inputs (`cbcShift`) fixes every input —
hence `cbcBad` — while freely re-randomising the MAC.  Everything below is `private`. -/

section Rerandomise

/-- Appending one block is one more round-function call. -/
private theorem cbcState_concat (f : X → X) (bs : List X) (b : X) :
    cbcState f (bs ++ [b]) = f (cbcState f bs + b) := by
  simp only [cbcState, List.foldl_concat]

private theorem cbcInput_append_of_lt (f : X → X) (bs : List X) (b : X) {j : ℕ} (hj : j < bs.length) :
    cbcInput f (bs ++ [b]) j = cbcInput f bs j := by
  unfold cbcInput
  rw [List.take_append_of_le_length (Nat.le_of_lt hj), List.getD_append bs [b] 0 j hj]

private theorem cbcInput_append_length (f : X → X) (bs : List X) (b : X) :
    cbcInput f (bs ++ [b]) bs.length = cbcState f bs + b := by
  unfold cbcInput
  rw [List.take_left, List.getD_append_right bs [b] 0 bs.length (le_refl _)]; simp

/- **Chaining agreement.** `f`, `f'` agreeing at every call-site input of `bs` give equal chaining. -/
theorem cbcState_congr_of_agree_on_inputs (f f' : X → X) (bs : List X)
    (h : ∀ j < bs.length, f (cbcInput f bs j) = f' (cbcInput f bs j)) :
    cbcState f bs = cbcState f' bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs' b ih =>
    rw [cbcState_concat, cbcState_concat]
    have hstep : ∀ j < bs'.length, f (cbcInput f bs' j) = f' (cbcInput f bs' j) := by
      intro j hj
      have hj' : j < (bs' ++ [b]).length := by rw [List.length_append]; omega
      have := h j hj'
      rwa [cbcInput_append_of_lt f bs' b hj] at this
    have hbs' : cbcState f bs' = cbcState f' bs' := ih hstep
    have hlast : f (cbcInput f (bs' ++ [b]) bs'.length) = f' (cbcInput f (bs' ++ [b]) bs'.length) :=
      h bs'.length (by rw [List.length_append]; simp)
    rw [cbcInput_append_length] at hlast
    rw [hlast, hbs']

/-- The MAC of `bs` is `f` at the terminal input `cbcInput f bs (|bs|-1)`. -/
theorem cbcState_eq_f_lastInput (f : X → X) (bs : List X) (hbs : bs ≠ []) :
    cbcState f bs = f (cbcInput f bs (bs.length - 1)) := by
  rcases bs.eq_nil_or_concat with h | ⟨bs', b, rfl⟩
  · exact absurd h hbs
  · rw [List.concat_eq_append, cbcState_concat]
    congr 1
    have hlen : (bs' ++ [b]).length - 1 = bs'.length := by simp
    rw [hlen, cbcInput_append_length]

/-- `¬cbcBad`: distinct keys force distinct inputs (contrapositive of the MBO). -/
theorem not_cbcBad_inputs_ne (f : X → X) (bf : M → List X) {l : List M}
    (h : ¬ cbcBad f bf l) {m m' : M} (hm : m ∈ l) (hm' : m' ∈ l) {j j' : ℕ}
    (hj : j < (bf m).length) (hj' : j' < (bf m').length)
    (hkey : (bf m).take (j + 1) ≠ (bf m').take (j' + 1)) :
    cbcInput f (bf m) j ≠ cbcInput f (bf m') j' :=
  fun hval => h ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩

/-- The terminal input of `m`: the round-function input at its last block. -/
def cbcLastInput (f : X → X) (bf : M → List X) (m : M) : X :=
  cbcInput f (bf m) ((bf m).length - 1)

/-- The terminal key is the full block sequence: `bs.take ((|bs|-1)+1) = bs`. -/
theorem take_last_key {bs : List X} (hne : bs ≠ []) : bs.take (bs.length - 1 + 1) = bs := by
  rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil hne)]
  exact List.take_length

/-- **The freshness interface of the re-randomisation engine**: every terminal input avoids every
call site carrying a distinct key.  This is all the engine ever consumes from an MBO: `¬cbcBad`
provides it because *any* nontrivial collision is banned; the structure-graph MBO
(`CBCStructureGraph.lean`) provides it through its terminal clause alone, while *tolerating*
internal collisions. -/
def cbcFresh (f : X → X) (bf : M → List X) (l : List M) : Prop :=
  ∀ m ∈ l, ∀ m' ∈ l, ∀ j' < (bf m').length,
    bf m ≠ (bf m').take (j' + 1) → cbcLastInput f bf m ≠ cbcInput f (bf m') j'

/-- `¬cbcBad` provides the engine's freshness interface. -/
theorem cbcFresh_of_not_cbcBad (f : X → X) (bf : M → List X) {l : List M}
    (hbf_ne : ∀ m, bf m ≠ []) (h : ¬ cbcBad f bf l) : cbcFresh f bf l := by
  intro m hm m' hm' j' hj' hkey
  refine not_cbcBad_inputs_ne f bf h hm hm'
    (by have := List.length_pos_of_ne_nil (hbf_ne m); omega) hj' ?_
  rw [take_last_key (hbf_ne m)]
  exact hkey

/-- Distinct messages have distinct terminal keys `bf m`, hence (under freshness) distinct
terminal inputs. -/
private theorem cbcLastInput_injOn (f : X → X) (bf : M → List X) {l : List M}
    (hbf_ne : ∀ m, bf m ≠ []) (hbf_pf : PrefixFree bf)
    (hfresh : cbcFresh f bf l) : Set.InjOn (cbcLastInput f bf) {m | m ∈ l} := by
  intro m hm m' hm' heq
  by_contra hmm
  have hkey : bf m ≠ (bf m').take ((bf m').length - 1 + 1) := by
    rw [take_last_key (hbf_ne m')]
    exact fun h => hbf_pf m m' hmm (h ▸ List.prefix_refl (bf m))
  exact hfresh m hm m' hm' _
    (by have := List.length_pos_of_ne_nil (hbf_ne m'); omega) hkey heq

theorem cbcInput_take_of_lt (f : X → X) (bs : List X) {i j : ℕ} (hij : i < j) :
    cbcInput f (bs.take j) i = cbcInput f bs i := by
  unfold cbcInput
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hij]

/-- **The atomic congruence engine**: if `f'` agrees with `f` at the inputs of all blocks `< p`, the
input at block `p` is unchanged.  Every invariance fact below is an instance of this. -/
theorem cbcInput_congr_of_agree_below (f f' : X → X) (bs : List X) {p : ℕ}
    (h : ∀ p' < p, f' (cbcInput f bs p') = f (cbcInput f bs p')) :
    cbcInput f' bs p = cbcInput f bs p := by
  unfold cbcInput
  congr 1
  refine (cbcState_congr_of_agree_on_inputs f f' (bs.take p) ?_).symm
  intro i hi_len
  have hip : i < p := by rw [List.length_take] at hi_len; omega
  rw [cbcInput_take_of_lt f bs hip]
  exact (h i hip).symm

/-- The chaining value after `t+1` blocks is `f` at the block-`t` input. -/
theorem cbcState_take_succ_eq (f : X → X) (bs : List X) {t : ℕ} (ht : t < bs.length) :
    cbcState f (bs.take (t + 1)) = f (cbcInput f bs t) := by
  have hne : bs.take (t + 1) ≠ [] := by
    rw [← List.length_pos_iff_ne_nil, List.length_take]; omega
  rw [cbcState_eq_f_lastInput f _ hne]
  congr 1
  have hlen : (bs.take (t + 1)).length - 1 = t := by rw [List.length_take]; omega
  rw [hlen, cbcInput_take_of_lt f bs (Nat.lt_succ_self t)]

/-- The one-step recurrence of the chaining inputs. -/
private theorem cbcInput_succ (f : X → X) (bs : List X) {t : ℕ} (ht : t < bs.length) :
    cbcInput f bs (t + 1) = f (cbcInput f bs t) + bs.getD (t + 1) 0 := by
  show cbcState f (bs.take (t + 1)) + bs.getD (t + 1) 0 = _
  rw [cbcState_take_succ_eq f bs ht]

/-- Single-point shift: translate `f` by `δ` at the point `w` only. -/
def pointShift (f : X → X) (w δ : X) : X → X :=
  fun x => if x = w then f x + δ else f x

theorem pointShift_apply_self (f : X → X) (w δ : X) :
    pointShift f w δ w = f w + δ := if_pos rfl

theorem pointShift_apply_ne (f : X → X) (w δ : X) {x : X} (h : x ≠ w) :
    pointShift f w δ x = f x := if_neg h

theorem pointShift_pointShift (f : X → X) (w δ δ' : X) :
    pointShift (pointShift f w δ) w δ' = pointShift f w (δ + δ') := by
  funext x
  unfold pointShift
  grind

theorem pointShift_zero (f : X → X) (w : X) : pointShift f w 0 = f := by
  funext x
  unfold pointShift
  grind

/- **The CBC grind theory.**  The structural equations of the chaining (append/take/terminal laws)
and the shift's defining equations, registered as `grind` E-matching rules: routine call-site
reasoning is dispatched by `grind`/`cr18_routine` instead of hand `rw`-chains. -/
attribute [grind =] cbcState_concat cbcInput_append_of_lt cbcInput_append_length
  cbcInput_take_of_lt cbcState_take_succ_eq cbcInput_succ cbcState_eq_f_lastInput
  pointShift_apply_self pointShift_apply_ne pointShift_pointShift pointShift_zero
attribute [grind →] not_cbcBad_inputs_ne

/-- The disjointness that makes the re-randomisation invisible: a proper-prefix call-site input
(`i + 1 < |bf m|`) is never a terminal input (distinct keys via prefix-freeness + `¬cbcBad`). -/
private theorem cbcInput_ne_lastInput (f : X → X) (bf : M → List X) {l : List M}
    (hbf_pf : PrefixFree bf) (hfresh : cbcFresh f bf l)
    {m : M} (hm : m ∈ l) {i : ℕ} (hi : i + 1 < (bf m).length)
    {s : M} (hs : s ∈ l) (_hne_s : bf s ≠ []) :
    cbcInput f (bf m) i ≠ cbcLastInput f bf s := by
  have hkey : bf s ≠ (bf m).take (i + 1) := by
    intro h
    have hpre : bf s <+: bf m := h ▸ List.take_prefix (i + 1) (bf m)
    by_cases hsm : s = m
    · subst hsm; have hh := congrArg List.length h; rw [List.length_take] at hh; omega
    · exact hbf_pf s m hsm hpre
  exact (hfresh s hs m hm i (by omega) hkey).symm

/-- Translate `f` by `δ s` at the terminal input of each distinct queried message `s` — the generic
multi-point shift `Counting.multiShift` at the terminal-input site family. -/
noncomputable def cbcShift (f : X → X) (bf : M → List X) (l : List M)
    (δ : ↥l.toFinset → X) : X → X :=
  Counting.multiShift (fun s : ↥l.toFinset => cbcLastInput f bf s.1) δ f

private theorem cbcShift_eq_of_not_terminal (f : X → X) (bf : M → List X) (l : List M)
    (δ : ↥l.toFinset → X) {x : X} (h : ∀ s ∈ l.toFinset, cbcLastInput f bf s ≠ x) :
    cbcShift f bf l δ x = f x :=
  Counting.multiShift_apply_of_ne δ f fun s => h s.1 s.2

private theorem cbcShift_lastInput (f : X → X) (bf : M → List X) (l : List M) (δ : ↥l.toFinset → X)
    (hinj : Set.InjOn (cbcLastInput f bf) {m | m ∈ l}) (s₀ : ↥l.toFinset) :
    cbcShift f bf l δ (cbcLastInput f bf s₀.1) = f (cbcLastInput f bf s₀.1) + δ s₀ :=
  Counting.multiShift_apply_site δ f
    (fun a b hab =>
      Subtype.ext (hinj (List.mem_toFinset.mp a.2) (List.mem_toFinset.mp b.2) hab)) s₀

/-- **P3 — inputs are invariant under `cbcShift`** (it touches only terminal inputs). -/
theorem cbcInput_cbcShift (f : X → X) (bf : M → List X) {l : List M} (δ : ↥l.toFinset → X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) {m : M} (hm : m ∈ l) {j : ℕ} (hj : j < (bf m).length) :
    cbcInput (cbcShift f bf l δ) (bf m) j = cbcInput f (bf m) j := by
  refine cbcInput_congr_of_agree_below f _ (bf m) fun i hip => ?_
  refine cbcShift_eq_of_not_terminal f bf l δ fun s hs => ?_
  exact (cbcInput_ne_lastInput f bf hbf_pf hfresh hm (by omega) (List.mem_toFinset.mp hs)
    (hbf_ne s)).symm

/-- **P4 — `cbcShift` preserves `¬cbcBad`** (it fixes every call-site input). -/
private theorem not_cbcBad_cbcShift (f : X → X) (bf : M → List X) {l : List M} (δ : ↥l.toFinset → X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hbad : ¬ cbcBad f bf l) :
    ¬ cbcBad (cbcShift f bf l δ) bf l := by
  have hfresh := cbcFresh_of_not_cbcBad f bf hbf_ne hbad
  rintro ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩
  rw [cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm hj,
    cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hm' hj'] at hval
  exact hbad ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩

/-- **P5 — the MAC of each queried message shifts by exactly `δ`.** -/
private theorem cbcState_cbcShift (f : X → X) (bf : M → List X) {l : List M} (δ : ↥l.toFinset → X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) {s : M} (hs : s ∈ l.toFinset) :
    cbcState (cbcShift f bf l δ) (bf s) = cbcState f (bf s) + δ ⟨s, hs⟩ := by
  have hinj := cbcLastInput_injOn f bf hbf_ne hbf_pf hfresh
  have hsl : s ∈ l := List.mem_toFinset.mp hs
  have hpos : 0 < (bf s).length := List.length_pos_of_ne_nil (hbf_ne s)
  have hshift := cbcShift_lastInput f bf l δ hinj ⟨s, hs⟩
  rw [cbcState_eq_f_lastInput (cbcShift f bf l δ) (bf s) (hbf_ne s),
    cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh hsl (by omega),
    show cbcInput f (bf s) ((bf s).length - 1) = cbcLastInput f bf s from rfl, hshift]
  congr 1
  exact (cbcState_eq_f_lastInput f (bf s) (hbf_ne s)).symm

private theorem cbcShift_zero (f : X → X) (bf : M → List X) (l : List M) :
    cbcShift f bf l 0 = f :=
  Counting.multiShift_zero _ f

/-- Shifts compose additively — under `¬cbcBad` the shifted `f` has the *same* terminal-input sites,
so `Counting.multiShift_multiShift` applies verbatim. -/
private theorem cbcShift_cbcShift (f : X → X) (bf : M → List X) {l : List M} (δ δ' : ↥l.toFinset → X)
    (hbf_pf : PrefixFree bf) (hbf_ne : ∀ m, bf m ≠ [])
    (hfresh : cbcFresh f bf l) :
    cbcShift (cbcShift f bf l δ) bf l δ' = cbcShift f bf l (δ + δ') := by
  have hsites : (fun s : ↥l.toFinset => cbcLastInput (cbcShift f bf l δ) bf s.1)
      = fun s : ↥l.toFinset => cbcLastInput f bf s.1 := funext fun s =>
    cbcInput_cbcShift f bf δ hbf_pf hbf_ne hfresh (List.mem_toFinset.mp s.2)
      (by have := List.length_pos_of_ne_nil (hbf_ne s.1); omega)
  show Counting.multiShift (fun s : ↥l.toFinset => cbcLastInput (cbcShift f bf l δ) bf s.1) δ'
      (cbcShift f bf l δ) = _
  rw [hsites]
  exact Counting.multiShift_multiShift _ δ δ' f

/-- **Balanced MAC-fibers** (the heart of eq. 6.2): conditioned on `¬cbcBad`, the `|T|` distinct-message
MACs are jointly uniform — `cbcShift` is a free `Xᵀ`-action on `{¬cbcBad}` translating the MAC map
(`Counting.card_filter_shift`). -/
theorem cbc_fiber_card (bf : M → List X) {l : List M}
    (hbf_ne : ∀ m, bf m ≠ []) (hbf_pf : PrefixFree bf)
    (P : (X → X) → Prop) [DecidablePred P]
    (hPfresh : ∀ f, P f → cbcFresh f bf l)
    (hPshift : ∀ (δ : ↥l.toFinset → X) (f : X → X), P f → P (cbcShift f bf l δ))
    (a : ↥l.toFinset → X) :
    (Finset.univ.filter (fun f : X → X =>
        (∀ s : ↥l.toFinset, cbcState f (bf s.1) = a s) ∧ P f)).card
      * Fintype.card X ^ l.toFinset.card
      = (Finset.univ.filter (fun f : X → X => P f)).card := by
  classical
  have key := Counting.card_filter_shift_univ (A := ↥l.toFinset → X)
    P
    (fun f s => cbcState f (bf s.1)) (fun δ f => cbcShift f bf l δ)
    (fun δ f hf => hPshift δ f hf)
    (fun δ f hf => funext fun s => by
      show cbcState (cbcShift f bf l δ) (bf s.1) = cbcState f (bf s.1) + δ s
      rw [cbcState_cbcShift f bf δ hbf_pf hbf_ne (hPfresh f hf) s.2])
    (fun δ δ' f hf => cbcShift_cbcShift f bf δ δ' hbf_pf hbf_ne (hPfresh f hf))
    (fun f _ => cbcShift_zero f bf l) a
  rw [Fintype.card_fun, Fintype.card_coe] at key
  rw [← key]
  congr 2
  ext f
  simp [funext_iff, and_comm]

/-! #### The birthday leaf — per-pair collision probability `≤ 1/|X|`

`cbcBadLt … t` truncates the MBO to call sites of block index `< t`.  A collision is decomposed by
its *level-minimal* pair (no collision strictly below the top block); conditioned on that guard, a
`pointShift` at the top site's predecessor input freely re-randomises the top input while fixing the
other, so each pair collides with probability exactly `1/|X|` (`card_filter_shift` again). -/

/-- The level-`t` truncation of the MBO: a non-trivial collision among sites of block index `< t`. -/
def cbcBadLt (f : X → X) (bf : M → List X) (l : List M) (t : ℕ) : Prop :=
  ∃ m ∈ l, ∃ m' ∈ l, ∃ j < min t (bf m).length, ∃ j' < min t (bf m').length,
    (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧ cbcInput f (bf m) j = cbcInput f (bf m') j'

instance (f : X → X) (bf : M → List X) (l : List M) (t : ℕ) :
    Decidable (cbcBadLt f bf l t) := by
  unfold cbcBadLt; infer_instance

/-- **First-collision extraction**: a collision yields a *level-minimal* colliding pair —
block-sorted (`j ≤ j'`) with no collision strictly below the top block `j'`. -/
theorem cbcBad_exists_minimal (f : X → X) (bf : M → List X) (l : List M)
    (h : cbcBad f bf l) : ∃ m ∈ l, ∃ m' ∈ l, ∃ j < (bf m).length, ∃ j' < (bf m').length,
      j ≤ j' ∧ (bf m).take (j + 1) ≠ (bf m').take (j' + 1) ∧
      cbcInput f (bf m) j = cbcInput f (bf m') j' ∧ ¬ cbcBadLt f bf l j' := by
  classical
  obtain ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩ := h
  have hP : ∃ t, cbcBadLt f bf l t :=
    ⟨max j j' + 1, m, hm, m', hm', j, lt_min (by omega) hj, j', lt_min (by omega) hj', hkey, hval⟩
  obtain ⟨a, ha, a', ha', i, hi, i', hi', hikey, hival⟩ := Nat.find_spec hP
  rcases le_total i i' with hii | hii
  · exact ⟨a, ha, a', ha', i, (lt_min_iff.mp hi).2, i', (lt_min_iff.mp hi').2, hii, hikey, hival,
      Nat.find_min hP (lt_min_iff.mp hi').1⟩
  · exact ⟨a', ha', a, ha, i', (lt_min_iff.mp hi').2, i, (lt_min_iff.mp hi).2, hii,
      Ne.symm hikey, hival.symm, Nat.find_min hP (lt_min_iff.mp hi).1⟩

/-- Under the level-`t+1` guard, the inputs of blocks `≤ t` never equal the block-`t` input `w` of a
guarded chain — their keys are shorter — so a `pointShift` at `w` leaves all of them unchanged. -/
theorem cbcInput_pointShift_of_le (f : X → X) (bf : M → List X) (l : List M)
    {m₂ : M} (hm₂ : m₂ ∈ l) {t : ℕ} (ht : t < (bf m₂).length)
    (hguard : ¬ cbcBadLt f bf l (t + 1)) (δ : X)
    {m : M} (hm : m ∈ l) {p : ℕ} (hp : p ≤ t) (hplen : p < (bf m).length) :
    cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m) p = cbcInput f (bf m) p := by
  refine cbcInput_congr_of_agree_below f _ (bf m) fun p' hp' => ?_
  refine pointShift_apply_ne f _ δ fun hcontra => ?_
  refine hguard ⟨m, hm, m₂, hm₂, p', lt_min (by omega) (by omega), t, lt_min (by omega) ht,
    fun hkeys => ?_, hcontra⟩
  have := congrArg List.length hkeys
  rw [List.length_take, List.length_take] at this
  omega

/-- The level-`t+1` guard is preserved by a `pointShift` at a guarded block-`t` input. -/
theorem not_cbcBadLt_pointShift (f : X → X) (bf : M → List X) (l : List M)
    {m₂ : M} (hm₂ : m₂ ∈ l) {t : ℕ} (ht : t < (bf m₂).length)
    (hguard : ¬ cbcBadLt f bf l (t + 1)) (δ : X) :
    ¬ cbcBadLt (pointShift f (cbcInput f (bf m₂) t) δ) bf l (t + 1) := by
  rintro ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩
  rw [cbcInput_pointShift_of_le f bf l hm₂ ht hguard δ hm (by omega) (by omega),
    cbcInput_pointShift_of_le f bf l hm₂ ht hguard δ hm' (by omega) (by omega)] at hval
  exact hguard ⟨m, hm, m', hm', j, hj, j', hj', hkey, hval⟩

/-- The block-`t+1` input of the guarded chain shifts by exactly `δ` under the `pointShift` at its
predecessor input. -/
theorem cbcInput_top_pointShift (f : X → X) (bf : M → List X) (l : List M)
    {m₂ : M} (hm₂ : m₂ ∈ l) {t : ℕ} (ht : t + 1 < (bf m₂).length)
    (hguard : ¬ cbcBadLt f bf l (t + 1)) (δ : X) :
    cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₂) (t + 1)
      = cbcInput f (bf m₂) (t + 1) + δ := by
  rw [cbcInput_succ _ (bf m₂) (by omega), cbcInput_succ f (bf m₂) (by omega),
    cbcInput_pointShift_of_le f bf l hm₂ (by omega) hguard δ hm₂ le_rfl (by omega),
    pointShift_apply_self]
  abel

/-- A *different* block-`t+1` input (distinct predecessor keys) is untouched by that `pointShift`. -/
theorem cbcInput_top_pointShift_other (f : X → X) (bf : M → List X) (l : List M)
    {m₁ m₂ : M} (hm₁ : m₁ ∈ l) (hm₂ : m₂ ∈ l) {t : ℕ}
    (h₁ : t + 1 < (bf m₁).length) (ht : t < (bf m₂).length)
    (hpred : (bf m₁).take (t + 1) ≠ (bf m₂).take (t + 1))
    (hguard : ¬ cbcBadLt f bf l (t + 1)) (δ : X) :
    cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₁) (t + 1)
      = cbcInput f (bf m₁) (t + 1) := by
  rw [cbcInput_succ _ (bf m₁) (by omega), cbcInput_succ f (bf m₁) (by omega),
    cbcInput_pointShift_of_le f bf l hm₂ ht hguard δ hm₁ le_rfl (by omega),
    pointShift_apply_ne f _ δ fun hcontra => hguard
      ⟨m₁, hm₁, m₂, hm₂, t, lt_min (by omega) (by omega), t, lt_min (by omega) ht,
        hpred, hcontra⟩]

/-- **Avoidance core** — input invariance under a `pointShift` from raw chain avoidance: if the
chain of `m` below block `p` never queries `w`, the block-`p` input is unchanged.  (The guard-based
`cbcInput_pointShift_of_le` is the `¬cbcBadLt` instance; the structure-graph double charge needs
this raw form, its guard being uniqueness-below rather than collision-freeness.) -/
theorem cbcInput_pointShift_of_avoid (f : X → X) (bf : M → List X) (w δ : X)
    {m : M} {p : ℕ}
    (hav : ∀ p' < p, cbcInput f (bf m) p' ≠ w) :
    cbcInput (pointShift f w δ) (bf m) p = cbcInput f (bf m) p := by
  refine cbcInput_congr_of_agree_below f _ (bf m) fun p' hp' => ?_
  exact pointShift_apply_ne f _ δ fun hcontra => hav p' hp' hcontra

/-- **Avoidance core, translation** — the block-`t+1` input shifts by exactly `δ` under the
`pointShift` at the block-`t` input, from raw avoidance of the chain below `t`. -/
theorem cbcInput_top_pointShift_of_avoid (f : X → X) (bf : M → List X) (δ : X)
    {m : M} {t : ℕ} (ht : t + 1 < (bf m).length)
    (hav : ∀ p' < t, cbcInput f (bf m) p' ≠ cbcInput f (bf m) t) :
    cbcInput (pointShift f (cbcInput f (bf m) t) δ) (bf m) (t + 1)
      = cbcInput f (bf m) (t + 1) + δ := by
  rw [cbcInput_succ _ (bf m) (by omega), cbcInput_succ f (bf m) (by omega),
    cbcInput_pointShift_of_avoid f bf _ δ hav, pointShift_apply_self]
  abel

/-- **The per-pair collision bound**: two call-site coordinates with distinct keys collide, with no
collision strictly below the top block, with probability at most `1/|X|`.  Block-0 pairs and
equal-predecessor pairs are impossible; otherwise the `pointShift` at the top predecessor input is a
free `X`-action fixing one input and translating the other (`card_filter_shift`). -/
theorem mass_pairColl_le (bf : M → List X) (l : List M)
    {m₁ m₂ : M} (hm₁ : m₁ ∈ l) (hm₂ : m₂ ∈ l) {j₁ j₂ : ℕ}
    (hj₁ : j₁ < (bf m₁).length) (hj₂ : j₂ < (bf m₂).length) (hj : j₁ ≤ j₂)
    (hkey : (bf m₁).take (j₁ + 1) ≠ (bf m₂).take (j₂ + 1)) :
    (Dist.uniform (X → X)).mass (fun f =>
        cbcInput f (bf m₁) j₁ = cbcInput f (bf m₂) j₂ ∧ ¬ cbcBadLt f bf l j₂)
      ≤ 1 / (Fintype.card X : NNReal) := by
  classical
  cases j₂ with
  | zero =>
    -- block-0 pair: both inputs are the constant first blocks, distinct because the keys differ
    have hj₁0 : j₁ = 0 := Nat.le_zero.mp hj
    subst hj₁0
    have hne : (bf m₁).getD 0 0 ≠ (bf m₂).getD 0 0 :=
      getD_ne_of_take_eq_of_take_succ_ne 0 rfl hkey hj₁ hj₂
    have hnone : ∀ f : X → X,
        ¬ (cbcInput f (bf m₁) 0 = cbcInput f (bf m₂) 0 ∧ ¬ cbcBadLt f bf l 0) := by
      intro f hf
      exact hne (by simpa [cbcInput, cbcState] using hf.1)
    exact Dist.mass_le_of_forall_not _ hnone
      (one_div_nonneg.mpr (NNReal.coe_nonneg _))
  | succ t =>
    by_cases hpe : j₁ = t + 1 ∧ (bf m₁).take (t + 1) = (bf m₂).take (t + 1)
    · -- same predecessor computation: the top blocks differ, so the inputs never collide
      obtain ⟨rfl, hpe⟩ := hpe
      have hne : (bf m₁).getD (t + 1) 0 ≠ (bf m₂).getD (t + 1) 0 :=
        getD_ne_of_take_eq_of_take_succ_ne 0 hpe hkey hj₁ hj₂
      have hnone : ∀ f : X → X,
          ¬ (cbcInput f (bf m₁) (t + 1) = cbcInput f (bf m₂) (t + 1)
            ∧ ¬ cbcBadLt f bf l (t + 1)) := by
        intro f hf
        have hstate : cbcState f ((bf m₁).take (t + 1)) = cbcState f ((bf m₂).take (t + 1)) := by
          rw [hpe]
        have := hf.1
        unfold cbcInput at this
        rw [hstate] at this
        exact hne (add_left_cancel this)
      exact Dist.mass_le_of_forall_not _ hnone
        (one_div_nonneg.mpr (NNReal.coe_nonneg _))
    · -- the genuine case: free single-point re-randomisation at the top predecessor input
      have hsplit : j₁ ≤ t ∨ j₁ = t + 1 ∧ (bf m₁).take (t + 1) ≠ (bf m₂).take (t + 1) := by
        grind
      have hu₁ : ∀ (δ : X), ∀ f, ¬ cbcBadLt f bf l (t + 1) →
          cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₁) j₁
            = cbcInput f (bf m₁) j₁ := by
        intro δ f hf
        rcases hsplit with hle | ⟨rfl, hpne⟩
        · exact cbcInput_pointShift_of_le f bf l hm₂ (by omega) hf δ hm₁ hle hj₁
        · exact cbcInput_top_pointShift_other f bf l hm₁ hm₂ hj₁ (by omega) hpne hf δ
      -- the guarded pointShift is a free `X`-action fixing input `j₁`, translating the top input
      have key := Counting.card_filter_shift_univ (A := X)
        (fun f => ¬ cbcBadLt f bf l (t + 1))
        (fun f => cbcInput f (bf m₂) (t + 1) - cbcInput f (bf m₁) j₁)
        (fun δ f => pointShift f (cbcInput f (bf m₂) t) δ)
        (fun δ f hf => not_cbcBadLt_pointShift f bf l hm₂ (by omega) hf δ)
        (fun δ f hf => by
          show cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₂) (t + 1)
              - cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₁) j₁
            = cbcInput f (bf m₂) (t + 1) - cbcInput f (bf m₁) j₁ + δ
          rw [cbcInput_top_pointShift f bf l hm₂ hj₂ hf δ, hu₁ δ f hf]
          abel)
        (fun δ δ' f hf => by
          show pointShift (pointShift f (cbcInput f (bf m₂) t) δ)
              (cbcInput (pointShift f (cbcInput f (bf m₂) t) δ) (bf m₂) t) δ' = _
          rw [cbcInput_pointShift_of_le f bf l hm₂ (by omega) hf δ hm₂ le_rfl (by omega)]
          exact pointShift_pointShift f _ δ δ')
        (fun f _ => pointShift_zero f _) 0
      rw [Dist.mass_congr _ (fun f => show
        (cbcInput f (bf m₁) j₁ = cbcInput f (bf m₂) (t + 1) ∧ ¬ cbcBadLt f bf l (t + 1))
          ↔ (cbcInput f (bf m₂) (t + 1) - cbcInput f (bf m₁) j₁ = 0 ∧ ¬ cbcBadLt f bf l (t + 1))
        from by rw [sub_eq_zero]; exact and_congr_left' eq_comm)]
      refine Dist.uniform_mass_le_inv_card_of_card_mul_le (B := X) _ ?_
      rw [key]
      exact Finset.card_le_univ _

/-- **The MBO birthday bound**: over the uniform round function, a fixed history of at most `q`
messages of at most `L` blocks each provokes the MBO with probability at most the pair-union bound
at `q·L` sites — the first-collision decomposition and the per-pair `1/|X|` leaf. -/
theorem mass_cbcBad_le (bf : M → List X) (l : List M) (q L : ℕ)
    (hql : l.length ≤ q) (hbfL : ∀ m, (bf m).length ≤ L) :
    (Dist.uniform (X → X)).mass (fun f => cbcBad f bf l)
      ≤ pairCollisionUnionBound X (q * L) := by
  classical
  by_cases hl : l = []
  · have hnone : ∀ f : X → X, ¬ cbcBad f bf l := by
      rintro f ⟨m, hm, -⟩
      simp [hl] at hm
    exact Dist.mass_le_of_forall_not _ hnone (NNReal.coe_nonneg _)
  · have hq : 0 < q := lt_of_lt_of_le (List.length_pos_of_ne_nil hl) hql
    have hidxq : ∀ s : ↥l.toFinset, l.idxOf s.1 < q := fun s =>
      lt_of_lt_of_le (List.idxOf_lt_length_of_mem (List.mem_toFinset.mp s.2)) hql
    -- Descriptors: two call-site coordinates `(message, block)`, block-major sorted (ties broken by
    -- first-occurrence index), in range, with distinct keys.  The event stays in these native
    -- coordinates; the block-major site code embeds the descriptors into the strict query pairs.
    refine mass_le_pairCollisionUnionBound_of_cover_injOn X (Dist.uniform (X → X))
      Dist.uniform_nonNeg (q * L)
      (Finset.univ.filter fun p : (↥l.toFinset × Fin L) × (↥l.toFinset × Fin L) =>
        (p.1.2.1 < p.2.2.1 ∨ p.1.2.1 = p.2.2.1 ∧ l.idxOf p.1.1.1 < l.idxOf p.2.1.1) ∧
        p.1.2.1 < (bf p.1.1.1).length ∧ p.2.2.1 < (bf p.2.1.1).length ∧
        (bf p.1.1.1).take (p.1.2.1 + 1) ≠ (bf p.2.1.1).take (p.2.2.1 + 1))
      (fun p f => cbcInput f (bf p.1.1.1) p.1.2.1 = cbcInput f (bf p.2.1.1) p.2.2.1
        ∧ ¬ cbcBadLt f bf l p.2.2.1) _
      (fun p => (⟨p.1.2.1 * q + l.idxOf p.1.1.1, Counting.siteCode_lt (hidxq p.1.1) p.1.2.2⟩,
        ⟨p.2.2.1 * q + l.idxOf p.2.1.1, Counting.siteCode_lt (hidxq p.2.1) p.2.2.2⟩))
      ?_ ?_ ?_ ?_
    · -- cover: the level-minimal colliding pair, block-major canonicalized
      intro f hf
      obtain ⟨m, hm, m', hm', j, hjlen, j', hjlen', hjj, hkey, hval, hguard⟩ :=
        cbcBad_exists_minimal f bf l hf
      have hjL : j < L := lt_of_lt_of_le hjlen (hbfL m)
      have hjL' : j' < L := lt_of_lt_of_le hjlen' (hbfL m')
      rcases Nat.lt_or_ge j j' with hlt | hge
      · exact ⟨((⟨m, List.mem_toFinset.mpr hm⟩, ⟨j, hjL⟩),
          (⟨m', List.mem_toFinset.mpr hm'⟩, ⟨j', hjL'⟩)),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt, hjlen, hjlen', hkey⟩,
          hval, hguard⟩
      · have hj' : j = j' := le_antisymm hjj hge
        subst hj'
        -- equal blocks: break the tie by first-occurrence index; equal indices force `m = m'`,
        -- contradicting the distinct keys — otherwise swap (the event is symmetric at equal levels)
        rcases Nat.lt_trichotomy (l.idxOf m) (l.idxOf m') with hi | hi | hi
        · exact ⟨((⟨m, List.mem_toFinset.mpr hm⟩, ⟨j, hjL⟩),
            (⟨m', List.mem_toFinset.mpr hm'⟩, ⟨j, hjL'⟩)),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨rfl, hi⟩, hjlen, hjlen', hkey⟩,
            hval, hguard⟩
        · exact absurd (by rw [(List.idxOf_inj hm).mp hi]) hkey
        · exact ⟨((⟨m', List.mem_toFinset.mpr hm'⟩, ⟨j, hjL'⟩),
            (⟨m, List.mem_toFinset.mpr hm⟩, ⟨j, hjL⟩)),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨rfl, hi⟩, hjlen', hjlen,
              Ne.symm hkey⟩,
            hval.symm, hguard⟩
    · -- leaf: exactly the per-pair bound at the descriptor's coordinates
      rintro ⟨⟨s₁, j₁⟩, s₂, j₂⟩ hp
      obtain ⟨-, horder, hlen₁, hlen₂, hkey⟩ := Finset.mem_filter.mp hp
      exact mass_pairColl_le bf l (List.mem_toFinset.mp s₁.2) (List.mem_toFinset.mp s₂.2)
        hlen₁ hlen₂ (by omega) hkey
    · -- the block-major site code of a sorted descriptor pair is a strict query pair
      rintro ⟨⟨s₁, j₁⟩, s₂, j₂⟩ hp
      obtain ⟨-, horder, -⟩ := Finset.mem_filter.mp hp
      rw [queryPairSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Fin.mk_lt_mk.mpr (Counting.siteCode_strictMono (hidxq s₁) horder)⟩
    · -- the site code decodes: `siteCode_fst/snd` recover index and block, `idxOf` is injective
      refine Function.Injective.injOn ?_
      have hdec : ∀ (s s' : ↥l.toFinset) (t t' : Fin L),
          t.1 * q + l.idxOf s.1 = t'.1 * q + l.idxOf s'.1 → s = s' ∧ t = t' := by
        intro s s' t t' h
        have hj : t.1 = t'.1 := by
          have h2 : (t.1 * q + l.idxOf s.1) / q = (t'.1 * q + l.idxOf s'.1) / q := by rw [h]
          rwa [Counting.siteCode_snd (hidxq s) hq, Counting.siteCode_snd (hidxq s') hq] at h2
        have hi : l.idxOf s.1 = l.idxOf s'.1 := by
          have h2 : (t.1 * q + l.idxOf s.1) % q = (t'.1 * q + l.idxOf s'.1) % q := by rw [h]
          rwa [Counting.siteCode_fst (hidxq s), Counting.siteCode_fst (hidxq s')] at h2
        exact ⟨Subtype.ext ((List.idxOf_inj (List.mem_toFinset.mp s.2)).mp hi), Fin.ext hj⟩
      rintro ⟨⟨s₁, j₁⟩, s₂, j₂⟩ ⟨⟨s₁', j₁'⟩, s₂', j₂'⟩ heq
      simp only [Prod.mk.injEq, Fin.mk.injEq] at heq
      obtain ⟨hs₁, hj₁⟩ := hdec _ _ _ _ heq.1
      obtain ⟨hs₂, hj₂⟩ := hdec _ _ _ _ heq.2
      rw [hs₁, hj₁, hs₂, hj₂]

/-- **The MBO birthday bound at the history's actual block count.**
Unlike the rectangular `q · L` bound above, this charges one site for each
block occurring in the queried messages and therefore applies directly to
Maurer's total-block restriction `θ_r`. -/
theorem mass_cbcBad_le_total (bf : M → List X) (l : List M) (r : ℕ)
    (hr : (l.map fun m => (bf m).length).sum ≤ r) :
    (Dist.uniform (X → X)).mass (fun f => cbcBad f bf l)
      ≤ pairCollisionUnionBound X r := by
  classical
  have hsumToFinset :
      ∀ messages : List M,
        ∑ m ∈ messages.toFinset, (bf m).length ≤
          (messages.map fun m => (bf m).length).sum := by
    intro messages
    induction messages with
    | nil =>
        simp
    | cons m messages ih =>
        simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
        by_cases hm : m ∈ messages
        · rw [Finset.insert_eq_of_mem (by simpa using hm)]
          omega
        · rw [Finset.sum_insert (by simpa using hm)]
          omega
  let Site :=
    Σ m : ↥l.toFinset, Fin (bf m.1).length
  have hsiteCard :
      Fintype.card Site ≤ r := by
    dsimp only [Site]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← l.toFinset.attach_eq_univ,
      Finset.sum_attach l.toFinset (fun m => (bf m).length)]
    exact (hsumToFinset l).trans hr
  let code : Site ↪ Fin r :=
    (Function.Embedding.nonempty_of_card_le
      (by simpa using hsiteCard)).some
  let descriptors : Finset (Site × Site) :=
    Finset.univ.filter fun p =>
      code p.1 < code p.2 ∧
        (bf p.1.1.1).take (p.1.2.1 + 1) ≠
          (bf p.2.1.1).take (p.2.2.1 + 1)
  refine mass_le_pairCollisionUnionBound_of_cover_injOn X
    (Dist.uniform (X → X)) Dist.uniform_nonNeg r descriptors
    (fun p f =>
      cbcInput f (bf p.1.1.1) p.1.2.1 =
          cbcInput f (bf p.2.1.1) p.2.2.1 ∧
        ¬ cbcBadLt f bf l (max p.1.2.1 p.2.2.1))
    (fun f => cbcBad f bf l)
    (fun p => (code p.1, code p.2))
    ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨m, hm, m', hm', j, hj, j', hj', hjj,
      hkey, hcollision, hminimal⟩ :=
      cbcBad_exists_minimal f bf l hf
    let s : Site :=
      ⟨⟨m, List.mem_toFinset.mpr hm⟩, ⟨j, hj⟩⟩
    let s' : Site :=
      ⟨⟨m', List.mem_toFinset.mpr hm'⟩, ⟨j', hj'⟩⟩
    have hsites : s ≠ s' := by
      intro heq
      exact hkey (congrArg
        (fun t : Site =>
          (bf t.1.1).take (t.2.1 + 1)) heq)
    have hcode : code s ≠ code s' :=
      fun heq => hsites (code.injective heq)
    rcases lt_or_gt_of_ne hcode with hlt | hgt
    · refine ⟨(s, s'), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hlt, hkey⟩
      · simpa [s, s', Nat.max_eq_right hjj] using
          And.intro hcollision hminimal
    · refine ⟨(s', s), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgt, Ne.symm hkey⟩
      · simpa [s, s', Nat.max_eq_left hjj] using
          And.intro hcollision.symm hminimal
  · rintro ⟨⟨m₁, j₁⟩, ⟨m₂, j₂⟩⟩ hp
    obtain ⟨_, _horder, hkey⟩ :=
      Finset.mem_filter.mp hp
    rcases le_total j₁.1 j₂.1 with hj | hj
    · simpa [Nat.max_eq_right hj] using
        mass_pairColl_le bf l
          (List.mem_toFinset.mp m₁.2)
          (List.mem_toFinset.mp m₂.2)
          j₁.2 j₂.2 hj hkey
    · simpa [Nat.max_eq_left hj, eq_comm] using
        mass_pairColl_le bf l
          (List.mem_toFinset.mp m₂.2)
          (List.mem_toFinset.mp m₁.2)
          j₂.2 j₁.2 hj (Ne.symm hkey)
  · intro p hp
    rw [queryPairSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      Fin.mk_lt_mk.mpr (Finset.mem_filter.mp hp).2.1⟩
  · intro p _ q _ hpq
    apply Prod.ext
    · exact code.injective (congrArg Prod.fst hpq)
    · exact code.injective (congrArg Prod.snd hpq)

/-- **`Γᵇ` of the filtered CBC game is bounded by the pair-union birthday expression at `q·L`**: the
generic monitored-game bound (`blindMaxWinProb_filterQueries_monitored_le`) reduces it to the MBO
mass leaf `mass_cbcBad_le` at each blind winner's fixed schedule. -/
theorem blindMaxWinProb_cbcGame_le (bf : M → List X) (q L : ℕ)
    (hbfL : ∀ m, (bf m).length ≤ L) :
    (Γᵇ (⌈q⌉ cbcGame bf) : ℝ) ≤ (pairCollisionUnionBound X (q * L) : ℝ) := by
  exact blindMaxWinProb_filterQueries_monitored_le (Dist.uniform (X → X))
    (fun f m => cbcState f (bf m)) (fun f => cbcBad f bf) Dist.uniform_nonNeg
    (fun f => cbcBad_monotone f bf) q _
    fun w _ => mass_cbcBad_le bf (blindQueryList w q) q L (blindQueryList_length_le w q) hbfL

end Rerandomise

/-! ### Step 3 (CR18 eq. 6.2) — the three mass reductions, then the counting identity

Mirroring the switching lemma's per-mass reduction lemmas (`massAfalse_filterURF_…` etc.), each of
eq. (6.2)'s masses is read off the game as a uniform-function count, already indexed over the
transcript vector. -/

/-- **Game "not won"**: the `Aᵢ = 0` mass is the uniform probability of no non-trivial collision
(the seed-event law `massAfalse_fTransform_historyEvaluator` at the CBC game). -/
private theorem massAfalse_cbcGame (bf : M → List X) {xs : List M} (hne : xs ≠ []) :
    CondEquiv.massAfalse (cbcGame bf) xs
      = (Dist.uniform (X → X)).mass fun f => ¬ cbcBad f bf xs :=
  (CondEquiv.massAfalse_fTransform_historyEvaluator (Dist.uniform (X → X))
    (fun f l hne => cbcState f (bf (l.getLast hne))) (fun f l => decide (cbcBad f bf l))
    hne).trans (Dist.mass_congr _ fun f => by simp)

/-- **Ideal side**: the `Vₙ` transcript law is a uniform `M → X` agreeing with `ȳ` on the queries
(the transcript law `massY_fTransform_historyEvaluator` at the URF). -/
theorem massY_Vn {i : ℕ} (ys : Vector X (i + 1)) (xs : Vector M (i + 1)) :
    CondEquiv.massY (Vn (M := M) (X := X)) i ys xs
      = (Dist.uniform (M → X)).mass fun g => ∀ k : Fin (i + 1), g (xs.get k) = ys.get k :=
  massY_fTransform_lastQuery (Dist.uniform (M → X)) (fun g m => g m) ys xs

/-- **Game "not won ∧ output matches"**: the MAC agrees with `ȳ` on every query ∧ no non-trivial
collision (the joint law `massYAfalse_fTransform_historyEvaluator`; `Aᵢ`'s monotonicity collapses the
per-prefix bits to the final one). -/
private theorem massYAfalse_cbcGame (bf : M → List X) {i : ℕ}
    (ys : Vector X (i + 1)) (xs : Vector M (i + 1)) :
    CondEquiv.massYAfalse (cbcGame bf) i ys xs
      = (Dist.uniform (X → X)).mass fun f =>
        (∀ k : Fin (i + 1), cbcState f (bf (xs.get k)) = ys.get k) ∧ ¬ cbcBad f bf xs.toList :=
  (massYAfalse_fTransform_lastQuery (Dist.uniform (X → X)) (fun f m => cbcState f (bf m))
    (fun f l => decide (cbcBad f bf l)) (fun f => cbcBad_decide_monotone f bf) ys xs).trans
    (Dist.mass_congr _ fun f => and_congr Iff.rfl (by simp))

/-- **CR18 eq. (6.2)** — `ĈBC 𝖱 |≡ Vₙ`. The CBC-MAC over a uniform round function, conditioned on the
MBO `Aᵢ = 0` (no non-trivial round-function-input collision), is the VIL-URF `Vₙ`.  Prefix-freeness
makes the last-block inputs of distinct messages distinct (`cbcLastInput_injOn`), so conditioned on
`Aᵢ = 0` every
fresh message hits a fresh uniform round-function output — a fresh uniform MAC.

Cross-multiplied (thesis Def 2.1 / Notation 2.34, weights cancel): the eq. (4.38) template
(`condEquiv_of_transcript_mass_reductions`) on the three mass reductions, closed by the
balanced-fiber count `cbc_fiber_card`. -/
theorem cbc_condEquiv [Nontrivial M] (bf : M → List X) (hbf_pf : PrefixFree bf) :
    cbcGame bf |≡ Vn := by
  have hbf_ne : ∀ m, bf m ≠ [] := hbf_pf.ne_nil
  -- The eq. (4.38) template on the three mass reductions; what is left is CBC's one mathematical
  -- fact — per distinct-message assignment, the balanced-fiber count `cbc_fiber_card`, read off as
  -- a mass product (`uniform_mass_eq_mass_mul_mass_…`).
  refine condEquiv_of_transcript_mass_reductions (cbcGame bf) Vn
    (Dist.uniform (X → X)) (Dist.uniform (M → X))
    (fun f m => cbcState f (bf m)) (fun g m => g m) (fun f l => ¬ cbcBad f bf l)
    (fun hne => massAfalse_cbcGame bf hne) (fun ys xs => massY_Vn ys xs)
    (fun ys xs => massYAfalse_cbcGame bf ys xs) (fun xs a => ?_)
  refine Dist.uniform_mass_eq_mass_mul_mass_of_card_mul_eq _ _ _ ?_
  have hTle : xs.toList.toFinset.card ≤ Fintype.card M := Finset.card_le_univ _
  rw [Fintype.card_fun, Counting.card_function_fiber_finset,
    ← cbc_fiber_card bf hbf_ne hbf_pf _
      (fun f hf => cbcFresh_of_not_cbcBad f bf hbf_ne hf)
      (fun δ f hf => not_cbcBad_cbcShift f bf δ hbf_pf hbf_ne hf) a]
  conv_lhs => rw [← Nat.sub_add_cancel hTle]
  cr18_algebra

/-! ## The realization equation

`casc[CBC, ·]` really is the chaining: the one-round loop lemma feeds the packaged realization
law (`apply_ofStep_functionEvaluator_of_round`), identifying `cbcReal` with the pushforward
evaluator of `cbcState · ∘ bf` — which yields the MBO-strip standing fact (`cbcGame_ignoreMBO`).
The block-cipher corollary is then the paper one-liner: triangle through `casc[CBC, 𝖱]`,
converter monotonicity into the query budget (`cbc_urp_substitution`, at most `L` round-function
calls per message), `Δ`-symmetry, and the switching lemma (Lemma 4.19) — twice the birthday,
`(qL)²/|X|`. -/

/-- The converter's answer history after `c` rounds reads back the chaining value. -/
private theorem cbc_answers_getLastD (f : X → X) (bs : List X) (c : ℕ) :
    ((List.range c).map fun j => cbcState f (bs.take (j + 1))).getLastD 0
      = cbcState f (bs.take c) := by
  cases c with
  | zero => rfl
  | succ c => rw [List.range_succ, List.map_append]; simp

/-- **The CBC round loop** against the `f`-evaluator, closed form: from `c` answered blocks the
drive completes the remaining `k`, issuing exactly the chain inputs `cbcInput f (bf m) j`,
`c ≤ j` — the protocol''s one genuine realization computation. -/
private theorem driveG_cbcStep_loop (bf : M → List X) (f : X → X) (m : M) :
    ∀ (k c : ℕ), c + k = (bf m).length → ∀ (n : ℕ) (xs : List X),
      CausalApply.driveG (cbcStep bf m) (PFunDDS.functionEvaluator f).1 (n + k + 1) xs
          ((List.range c).map fun j => cbcState f ((bf m).take (j + 1)))
        = Part.some (cbcState f (bf m),
            xs ++ (List.range' c k).map (cbcInput f (bf m))) := by
  intro k
  induction k with
  | zero =>
      intro c hc n xs
      obtain rfl : c = (bf m).length := by omega
      have hstep : cbcStep bf m
          ((List.range (bf m).length).map fun j => cbcState f ((bf m).take (j + 1)))
          = Sum.inr (cbcState f (bf m)) := by
        unfold cbcStep
        rw [if_neg (by simp), cbc_answers_getLastD, List.take_length]
      simp only [CausalApply.driveG, hstep, List.range'_zero, List.map_nil, List.append_nil]
  | succ k ih =>
      intro c hc n xs
      have hclt : c < (bf m).length := by omega
      have hstep : cbcStep bf m
          ((List.range c).map fun j => cbcState f ((bf m).take (j + 1)))
          = Sum.inl (cbcInput f (bf m) c) := by
        unfold cbcStep
        rw [if_pos (by simpa using hclt), cbc_answers_getLastD]
        simp only [List.length_map, List.length_range]
        rfl
      have hans : f (cbcInput f (bf m) c) = cbcState f ((bf m).take (c + 1)) :=
        (cbcState_take_succ_eq f (bf m) hclt).symm
      have hih := ih (c + 1) (by omega) n (xs ++ [cbcInput f (bf m) c])
      have h1 : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
      rw [h1]
      generalize n + k + 1 = f' at hih ⊢
      simp only [CausalApply.driveG, hstep, CausalApply.functionEvaluator_raw_append,
        Part.bind_some, hans]
      rw [show ((List.range c).map fun j => cbcState f ((bf m).take (j + 1))) ++
            [cbcState f ((bf m).take (c + 1))]
          = (List.range (c + 1)).map fun j => cbcState f ((bf m).take (j + 1)) from by
        rw [List.range_succ, List.map_append]; rfl]
      rw [hih]
      simp [List.range'_succ]

/-- One full CBC round: output `cbcState f (bf m)`, calls `cbcInput f (bf m) '' [0, |bf m|)`. -/
private theorem driveG_cbcStep_round (bf : M → List X) (f : X → X) (m : M) (n : ℕ)
    (xs : List X) :
    CausalApply.driveG (cbcStep bf m) (PFunDDS.functionEvaluator f).1 (n + (bf m).length + 1) xs []
      = Part.some (cbcState f (bf m),
          xs ++ (List.range (bf m).length).map (cbcInput f (bf m))) := by
  have h := driveG_cbcStep_loop bf f m (bf m).length 0 (by omega) n xs
  simpa [List.range_eq_range'] using h

/-- **The realization equation** (Def 3.9 surface): the CBC converter applied to the evaluator of
`f` *is* the evaluator of `casc[CBC, f] = cbcState f ∘ bf` — one citation of the packaged
round-driven law. -/
private theorem apply_ofStep_cbcStep (bf : M → List X) (f : X → X) :
    PFunConverter.DDC.apply (PFunConverter.DDC.ofStep (cbcStep bf))
        (PFunDDS.functionEvaluator f)
      = PFunDDS.functionEvaluator (fun m => cbcState f (bf m)) :=
  PFunConverter.DDC.apply_ofStep_functionEvaluator_of_round (cbcStep bf) f
    (fun m => cbcState f (bf m)) (fun m => (List.range (bf m).length).map (cbcInput f (bf m)))
    (fun m => (bf m).length)
    (fun m => Finset.le_sup (f := fun m => (bf m).length) (Finset.mem_univ m))
    (driveG_cbcStep_round bf f)

/-- **Law level**: `casc[CBC, 𝖱]` *is* the pushforward evaluator of the chaining — the
transport of the realization equation. -/
private theorem cbcReal_eq_ofFunDist (bf : M → List X) :
    cbcReal bf = PFunPDS.ofFunDist (Dist.fTransform
      (fun f : X → X => fun m => cbcState f (bf m)) (Dist.uniform (X → X))) := by
  unfold cbcReal PFunPDS.URF
  exact PFunPDS.applyDDC_ofFunDist _ (apply_ofStep_cbcStep bf) _

/-- Stripping the MBO from the game returns the real system: `ĈBC 𝖱⁻ = casc[CBC,𝖱]`
(the `historyEvaluator` last-query output is `functionEvaluator`, through the realization
equation).  Mirrors `hctr2Hat_stripMBO`. -/
theorem cbcGame_ignoreMBO (bf : M → List X) :
    PFunPDS.ignoreMBO (cbcGame bf) = cbcReal bf := by
  rw [cbcReal_eq_ofFunDist]
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO cbcGame seededConditionCGame
    PFunPDS.ofFunDist
  simp only [dist_simp]
  rw [show (PFunDDS.stripMBO ∘ fun f : X → X =>
        PFunDDS.historyEvaluator fun l h =>
          (cbcState f (bf (l.getLast h)), decide (cbcBad f bf l))) =
      (fun f : X → X => PFunDDS.functionEvaluator (fun m => cbcState f (bf m))) from by
    funext f; rfl]
  rfl

attribute [cr18_standing] cbcGame_ignoreMBO

/-- **Finite-message rectangle corollary to CR18 Theorem 6.1.** For a
prefix-free block former, CBC-MAC over a uniform round function is
indistinguishable from the VIL-URF `Vₙ` up to the birthday bound
`½ (q·L)² / |X|`, for at most `q` message queries whose encodings contain at
most `L` blocks each.

Relation to the printed theorem: the budget here is the *rectangle*
`τ_{q,L}` (the filter of CR18 §6.2.7: at most `q`
queries, each of at most `L` blocks — the `⌈q⌉` filter plus the `hL` hypothesis), not `θ_r`'s
total-block count.  Every `(q, L)`-adversary is a `θ_{qL}`-adversary, and on the paper's optimal
schedule (one message of `r` blocks, `q = 1`, `L = r`) the two bounds coincide at `½r²/|X|`; for
mixed schedules the rectangle bound is looser.  The tight `θ_r` form is future work (generalize
`mass_cbcBad_le` from the `q·L` pair-rectangle to the schedule's total block count). -/
@[rs_rule "rs.cbc.randomness_expander" distance_bound random_systems]
theorem cbc_mac_randomness_expander [Nontrivial M] (bf : M → List X) (q L : ℕ)
    (hbf_pf : PrefixFree bf) (hL : ∀ m, (bf m).length ≤ L) :
    Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) ≤
      (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
  -- The shared condition-C endpoint packages Theorem 4.17 and the blind
  -- fixed-schedule reduction; Lemma 4.18 closes the arithmetic birthday step.
  calc Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn)
      = Δ(⌈q⌉ PFunPDS.ignoreMBO (cbcGame bf), ⌈q⌉ Vn) := by
        rw [cbcGame_ignoreMBO]
    _ ≤ (pairCollisionUnionBound X (q * L) : ℝ) := by
      exact maxAdvantage_filterQueries_seededConditionCGame_le
        (Dist.uniform (X → X)) (fun f m => cbcState f (bf m))
        (fun f l => cbcBad f bf l) (fun f => cbcBad_monotone f bf)
        q Vn (pairCollisionUnionBound X (q * L)) (cbc_condEquiv bf hbf_pf)
        Dist.uniform_isProbDist Vn_isProbDist Vn_totalOnNonempty
        (fun w _ => mass_cbcBad_le bf (blindQueryList w q) q L
          (blindQueryList_length_le w q) hL)
    _ ≤ (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
        pairCollisionUnionBound_le_birthday X (q * L)


/-- **CBC over a URP is a randomness expander** (the block-cipher corollary of Theorem 6.1, not
tight): triangle through `casc[CBC, 𝖱]`; the substitution hop is converter monotonicity (CBC makes
at most `L` round-function calls per message) into the switching lemma (CR18 Lemma 4.19); the
`𝖱`-leg is Theorem 6.1.  The two birthday terms add up to `(qL)²/|X|`. -/
@[rs_rule "rs.cbc.randomness_expander_urp" distance_bound random_systems]
theorem cbc_mac_randomness_expander_urp [Nontrivial M] (bf : M → List X) (q L : ℕ)
    (hbf_pf : PrefixFree bf) (hL : ∀ m, (bf m).length ≤ L) :
    Δ(⌈q⌉ cbcRealP bf, ⌈q⌉ Vn) ≤ ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
  calc Δ(⌈q⌉ cbcRealP bf, ⌈q⌉ Vn)
      ≤ Δ(⌈q⌉ cbcRealP bf, ⌈q⌉ cbcReal bf) + Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) :=
        maxAdvantage_triangle _ _ _
    _ ≤ Δ(⌈q * L⌉ 𝖯 X, ⌈q * L⌉ 𝖱 X) + Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) :=
        -- Converter monotonicity, with query accounting.  The two systems are the SAME
        -- converter on the two resources, and each of the distinguisher's `q` queries drives
        -- the chaining through at most `L` round-function calls (`cbcStep_answersWithin`, the
        -- Def 3.8 round bound `R := L`).  So the induced distinguisher of `𝖯` vs `𝖱` asks at
        -- most `q·L` inner queries — the DPI's budget `q·R`.
        add_le_add_left
          (maxAdvantage_filterQueries_applyDDC_le (cbcStep bf) (cbcStep_answersWithin bf hL)
            q _ _ (PFunPDS.URP_isRandomFunction X) PFunPDS.URF_isRandomFunction) _
    _ ≤ (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) +
        Δ(⌈q⌉ cbcReal bf, ⌈q⌉ Vn) :=
        -- `Δ`-symmetry, then the switching lemma (CR18 Lemma 4.19)
        add_le_add_left
          ((maxAdvantage_filterQueries_swap_le (q * L) (𝖱 X) (𝖯 X)
              PFunPDS.URF_totalOnNonempty (PFunPDS.URP_totalOnNonempty X)
              (by rw [PFunPDS.URF_isProbDist.weight_eq,
                (PFunPDS.URP_isProbDist X).weight_eq])).trans
            (urf_urp_switching X (q * L))) _
    _ ≤   (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ)
        + (1 / 2 : ℝ) * ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
        -- Theorem 6.1 on the `𝖱`-leg
        add_le_add_right (cbc_mac_randomness_expander bf q L hbf_pf hL) _
    _ = ((q * L : ℕ) : ℝ) ^ 2 / (Fintype.card X : ℝ) := by ring

end RandomSystems.CR18
namespace RandomSystems.CR18

open scoped PFunDDS
open scoped RandomSystems.CR18 RandomSystems.CR18.CondEquiv

universe u

variable {X : Type u} [AddCommGroup X] {M : Type u}

/-- **The CBC converter** (Maurer's `CBC`), a function of the block
former, in the protocol-function carrier: at outer messages `ms` and
cumulative inner answers `ys` (in the `Y ∪ {⊥}` alphabet of CR18
Def 3.8), the current round is the last message, its chaining segment
is the answers left after discounting the `Σ (bf mᵢ).length` consumed
by the previous rounds, and the move is `cbcStep` on the sequenced
segment — the converter is silent unless every consumed answer is
proper (`List.mapM id` sequences the segment).  Definitionally the
outer-memoryless step converter `PFunConverter.ProtocolFn.ofStep` at
`cbcStep`, with the block former's lengths as the round budgets. -/
@[rs_rule "rs.cbc.protocol" rs_protocol random_systems]
def CBC (bf : M → List X) : PFunConverter.ProtocolFn M X X X :=
  PFunConverter.ProtocolFn.ofStep (cbcStep bf) fun m => (bf m).length

/-- The CBC round boundary (CR18 Def 3.8's inner-call bound): `cbcStep`
issues an inner query exactly while the block former's blocks last. -/
theorem cbc_step_issues_query_iff (bf : M → List X) (m : M) (ys : List X) :
    (∃ x, cbcStep bf m ys = Sum.inl x) ↔ ys.length < (bf m).length := by
  unfold cbcStep
  split_ifs with h <;> simp [h]

/-- `CBC` is in the outer-memoryless class (`IsOfStep`), witnessed by
its own definition.  (Predicate-first naming per Mathlib's `even_two`
pattern; the file's other lemmas are subject-first — flagged for
arbitration.) -/
theorem cbc_is_step_converter (bf : M → List X) :
    PFunConverter.ProtocolFn.IsOfStep (CBC bf) :=
  ⟨cbcStep bf, _, cbc_step_issues_query_iff bf, rfl⟩

/-- **The restriction converter `θ bf r`** (Maurer's `θr`, CR18 §6.2.3:
"for each message θr determines the number of blocks the block-former
outputs … and keeps track of the total number of such blocks resulting
for all messages seen so far.  When this number exceeds `r`, then θr
stops replying to queries"), in the protocol-function carrier — the
weighted `queryLimitFn`. -/
@[rs_rule "rs.cbc.restriction" rs_protocol random_systems]
def θ {Y : Type u} (bf : M → List X) (r : ℕ) :
    PFunConverter.ProtocolFn M Y M Y := fun p =>
  if h : p.1.length = p.2.length + 1 ∧
      (p.1.map fun m => (bf m).length).sum ≤ r then
    Part.some (Sum.inl (p.1.getLast (by
      apply List.ne_nil_of_length_pos; omega)))
  else if h' : p.1.length = p.2.length ∧ 0 < p.2.length ∧
      (p.1.map fun m => (bf m).length).sum ≤ r then
    match p.2.getLast (List.ne_nil_of_length_pos h'.2.1) with
    | some y => Part.some (Sum.inr y)
    | none => Part.none
  else Part.none

/-- Maurer's `θr` is the general identity restriction at the accumulated
block-count predicate. -/
lemma theta_eq_restrictionFn {Y : Type u} (bf : M → List X) (r : ℕ) :
    θ (Y := Y) bf r = PFunConverter.restrictionFn (Y := Y)
      (fun messages => (messages.map fun m => (bf m).length).sum ≤ r) := by
  rfl

/-- Theorem 4.17 after applying Maurer's common weighted restriction `θr`.
All domain normalization is inherited from the general restriction theorem;
the caller supplies only the conditional equivalence. -/
theorem theta_advantage_le_blind_game_of_cond_equiv
    {Y : Type u} [Nonempty M]
    (bf : M → List X) (r : ℕ)
    (Shat : PFunPDS M (Y × Bool)) (T : PFunPDS M Y)
    (hCE : Shat |≡ T)
    (hmono : MonotoneMBO Shat := by cr18_standing)
    (hShat : Shat.isProbDist := by cr18_standing)
    (hT : T.isProbDist := by cr18_standing)
    (hShatTot : CondEquiv.TotalOnNonempty Shat := by cr18_standing)
    (hTTot : CondEquiv.TotalOnNonempty T := by cr18_standing) :
    Δ(PFunPDS.apply (θ bf r) (PFunPDS.ignoreMBO Shat),
        PFunPDS.apply (θ bf r) T) ≤
      (Γᵇ (PFunPDS.apply (θ bf r) Shat) : ℝ) := by
  simpa only [theta_eq_restrictionFn] using
    restrict_advantage_le_blind_game_of_cond_equiv
      (fun m => (bf m).length) r Shat T hCE
      hmono hShat hT hShatTot hTTot

/-- The blind winning probability of Maurer's `θr`-restricted CBC game is
bounded by the birthday expression at the total number `r` of admitted
blocks. -/
theorem blindMaxWinProb_theta_cbcGame_le
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M]
    (bf : M → List X) (r : ℕ) :
    Γᵇ (StrictContext.applyLaw (θ bf r) (cbcGame bf))
      ≤ pairCollisionUnionBound X r := by
  classical
  let P : List M → Prop :=
    fun messages =>
      (messages.map fun m => (bf m).length).sum ≤ r
  have hP : PrefixClosed P := by
    rintro messages _ ⟨tail, rfl⟩ h
    simp only [P, List.map_append, List.sum_append] at h ⊢
    omega
  rw [theta_eq_restrictionFn,
    StrictContext.apply_law_restrictionFn P hP]
  unfold PFunPDS.filterDom
  rw [cbcGame_eq_fTransform_cbcGameDDS, Dist.fTransform_comp]
  refine blindMaxWinProb_fTransform_le _ _ _ fun w hblind => ?_
  let queries : ℕ → List M :=
    fun n =>
      ((List.range n).map fun k =>
        w (List.replicate k (none : Option X))).reduceOption
  have queries_prefix :
      ∀ {n N : ℕ}, n ≤ N → queries n <+: queries N := by
    intro n N hnN
    have hrange : List.range n <+: List.range N := by
      refine ⟨(List.range N).drop n, ?_⟩
      conv_rhs =>
        rw [← List.take_append_drop n (List.range N)]
      rw [List.take_range, Nat.min_eq_left hnN]
    exact (hrange.map fun k =>
      w (List.replicate k (none : Option X))).reduceOption
  let accepted : Finset M :=
    Finset.univ.filter fun m =>
      ∃ n, m ∈ PFunDDS.keepAdmitted P (queries n)
  have finite_cover :
      ∀ s : Finset M,
        (∀ m ∈ s, ∃ n,
          m ∈ PFunDDS.keepAdmitted P (queries n)) →
        ∃ N, ∀ m ∈ s,
          m ∈ PFunDDS.keepAdmitted P (queries N) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, by simp⟩
    | @insert m s hm ih =>
        obtain ⟨n, hn⟩ := hs m (Finset.mem_insert_self m s)
        obtain ⟨N, hN⟩ := ih fun m' hm' =>
          hs m' (Finset.mem_insert_of_mem hm')
        refine ⟨max n N, ?_⟩
        intro m' hm'
        rw [Finset.mem_insert] at hm'
        rcases hm' with rfl | hm'
        · exact (PFunDDS.keepAdmitted_prefix P
            (queries_prefix (le_max_left n N))).subset hn
        · exact (PFunDDS.keepAdmitted_prefix P
            (queries_prefix (le_max_right n N))).subset (hN m' hm')
  obtain ⟨N, hN⟩ := finite_cover accepted (by
    intro m hm
    simpa only [accepted, Finset.mem_filter, Finset.mem_univ,
      true_and] using hm)
  have sum_toFinset_le :
      ∀ messages : List M,
        ∑ m ∈ messages.toFinset, (bf m).length ≤
          (messages.map fun m => (bf m).length).sum := by
    intro messages
    induction messages with
    | nil =>
        simp
    | cons m messages ih =>
        simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
        by_cases hm : m ∈ messages
        · rw [Finset.insert_eq_of_mem (by simpa using hm)]
          omega
        · rw [Finset.sum_insert (by simpa using hm)]
          omega
  have accepted_cost :
      ∑ m ∈ accepted, (bf m).length ≤ r := by
    have hsubset :
        accepted ⊆
          (PFunDDS.keepAdmitted P (queries N)).toFinset := by
      intro m hm
      exact List.mem_toFinset.mpr (hN m hm)
    calc
      ∑ m ∈ accepted, (bf m).length
          ≤ ∑ m ∈ (PFunDDS.keepAdmitted P
              (queries N)).toFinset, (bf m).length :=
        Finset.sum_le_sum_of_subset hsubset
      _ ≤ ((PFunDDS.keepAdmitted P
              (queries N)).map fun m => (bf m).length).sum :=
        sum_toFinset_le _
      _ ≤ r := by
        exact PFunDDS.keepAdmitted_satisfies P (by simp [P]) _
  refine (mass_mono Dist.uniform_nonNeg fun f hwin => ?_).trans
    (mass_cbcBad_le_total bf accepted.toList r (by
      simpa using accepted_cost))
  obtain ⟨n, y, hmem⟩ := hwin
  obtain ⟨m, x, hquery, hxs, hbit⟩ :=
    PFunDDS.true_output_mem_exists_query_output_true
      (PFunDDS.filterDom P hP (cbcGameDDS f bf)) w n y hmem
  let t :=
    PFunDDS.transcript
      (PFunDDS.filterDom P hP (cbcGameDDS f bf))
      (PFunDDS.winnerView w) m
  let raw := PFunDDS.transcriptInputs t
  let xs :=
    PFunDDS.keptPrefix
      (PFunDDS.filterDom P hP (cbcGameDDS f bf)) raw ++ [x]
  change
    PFunDDS.winnerView w
      (PFunDDS.transcript
        (PFunDDS.filterDom P hP (cbcGameDDS f bf))
        (PFunDDS.winnerView w) m)↓ᵧ = some x at hquery
  change xs ∈
    PFunDDS.dom (PFunDDS.filterDom P hP (cbcGameDDS f bf)) at hxs
  change
    (PFunDDS.output
      (PFunDDS.filterDom P hP (cbcGameDDS f bf)) xs hxs).2 =
        true at hbit
  have hbad : cbcBad f bf xs := by
    simpa only [PFunDDS.output_filterDom, cbcGameDDS,
      PFunDDS.historyEvaluator_output, decide_eq_true_eq] using hbit
  have htlen : t.length = m := by
    exact PFunDDS.transcript_length_eq_of_fire
      (PFunDDS.filterDom P hP (cbcGameDDS f bf))
      (PFunDDS.winnerView w) hquery
  have hrawlen : raw.length = m := by
    simp only [raw, PFunDDS.transcriptInputs, List.length_map, htlen]
  have hscheduled :
      ∀ k : Fin raw.length,
        w (List.replicate k.1 (none : Option X)) =
          some (raw.get k) := by
    intro k
    have hget : raw[k.1]? = some (raw.get k) :=
      List.getElem?_eq_getElem k.2
    have hactual :=
      PFunDDS.transcript_input_get?_eq_env
        (PFunDDS.filterDom P hP (cbcGameDDS f bf))
        (PFunDDS.winnerView w) m k.1 hget
    have hactual' :
        w ((PFunDDS.transcriptOutputs (t.take k.1)).map
          (Option.map Prod.fst)) = some (raw.get k) := by
      simpa only [PFunDDS.winnerView, t, raw] using hactual
    have hlength :
        ((PFunDDS.transcriptOutputs (t.take k.1)).map
          (Option.map Prod.fst)).length =
            (List.replicate k.1 (none : Option X)).length := by
      simp only [List.length_map, PFunDDS.transcriptOutputs,
        List.length_take, List.length_replicate]
      rw [Nat.min_eq_left]
      omega
    rw [← hblind
      ((PFunDDS.transcriptOutputs (t.take k.1)).map
        (Option.map Prod.fst))
      (List.replicate k.1 (none : Option X)) hlength]
    exact hactual'
  have hmap :
      (List.range m).map
          (fun k => w (List.replicate k (none : Option X))) =
        raw.map some := by
    apply List.ext_getElem
    · simp [hrawlen]
    · intro k hk₁ hk₂
      simp only [List.getElem_map, List.getElem_range]
      exact hscheduled ⟨k, by simpa [hrawlen] using hk₂⟩
  have reduceOption_map_some :
      ∀ messages : List M, (messages.map some).reduceOption = messages := by
    intro messages
    induction messages with
    | nil =>
        rfl
    | cons m messages ih =>
        change m :: (messages.map some).reduceOption = m :: messages
        rw [ih]
  have hqueries : queries m = raw := by
    simp only [queries, hmap]
    exact reduceOption_map_some raw
  have hfinal :
      w (List.replicate m (none : Option X)) = some x := by
    have hlength :
        ((PFunDDS.transcriptOutputs t).map
          (Option.map Prod.fst)).length =
            (List.replicate m (none : Option X)).length := by
      simp only [List.length_map, PFunDDS.transcriptOutputs,
        List.length_replicate, htlen]
    rw [← hblind
      ((PFunDDS.transcriptOutputs t).map (Option.map Prod.fst))
      (List.replicate m (none : Option X)) hlength]
    simpa only [PFunDDS.winnerView, t] using hquery
  have hqueries_succ : queries (m + 1) = raw ++ [x] := by
    simp only [queries, List.range_succ, List.map_append,
      List.map_singleton, List.reduceOption_append, hmap, hfinal]
    rw [reduceOption_map_some]
    simp
  have htotal :
      ∀ messages : List M, messages ≠ [] →
        messages ∈ PFunDDS.dom (cbcGameDDS f bf) := by
    intro messages hmessages
    simpa only [cbcGameDDS, PFunDDS.dom_historyEvaluator,
      Set.mem_setOf_eq] using hmessages
  have hkept :
      PFunDDS.keptPrefix
          (PFunDDS.filterDom P hP (cbcGameDDS f bf)) raw =
        PFunDDS.keepAdmitted P raw :=
    PFunDDS.keptPrefix_filterDom_eq_keepAdmitted_of_total
      P hP (cbcGameDDS f bf) htotal raw
  have hadmit :
      P (PFunDDS.keepAdmitted P raw ++ [x]) := by
    simpa only [xs, hkept] using hxs.2
  have hxsKeep :
      xs = PFunDDS.keepAdmitted P (queries (m + 1)) := by
    rw [hqueries_succ, PFunDDS.keepAdmitted_append, if_pos hadmit]
    simp only [xs, hkept]
  obtain ⟨m₁, hm₁, m₂, hm₂, j₁, hj₁, j₂, hj₂,
    hkey, hcollision⟩ := hbad
  refine ⟨m₁, ?_, m₂, ?_, j₁, hj₁, j₂, hj₂,
    hkey, hcollision⟩
  · simp only [Finset.mem_toList, accepted, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨m + 1, by simpa [hxsKeep] using hm₁⟩
  · simp only [Finset.mem_toList, accepted, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨m + 1, by simpa [hxsKeep] using hm₂⟩

/-- **`θ` is genuinely outside the outer-memoryless class** — the
type/representative test: no step function and round budget present it,
in *any* syntax (membership in `IsOfStep` is extensional).  Engine: over
the block budget `θ` goes *silent* (`Part.none`), while an `ofStep`
converter always moves at an all-proper history
(`PFunConverter.ProtocolFn.ofStep_dom`) — the budget-style stop has no
step-style presentation.  Nondegeneracy `∃ m, 0 < (bf m).length`: some
message must carry a block, so that enough repetitions of it exceed the
budget `r`. -/
theorem theta_is_not_step_converter (bf : M → List X) (r : ℕ)
    (h : ∃ m, 0 < (bf m).length) :
    ¬ PFunConverter.ProtocolFn.IsOfStep (θ (Y := X) bf r) := by
  rintro ⟨step, cnt, -, heq⟩
  obtain ⟨m, hpos⟩ := h
  have hdom : (θ bf r (List.replicate r m ++ [m],
      (List.replicate r (0 : X)).map some)).Dom := by
    rw [heq]
    exact PFunConverter.ProtocolFn.ofStep_dom step cnt (by simp) _
  have hnone : θ bf r (List.replicate r m ++ [m],
      (List.replicate r (0 : X)).map some) = Part.none := by
    have hsum : ¬ (((List.replicate r m ++ [m]).map
        fun m' => (bf m').length).sum ≤ r) := by
      intro hle
      have hler : r ≤ r * (bf m).length := Nat.le_mul_of_pos_right r hpos
      simp only [List.map_append, List.sum_append, List.map_replicate,
        List.sum_replicate, smul_eq_mul, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil] at hle
      omega
    unfold θ
    split_ifs with h1 h2
    · exact absurd h1.2 hsum
    · exact absurd h2.1 (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons, List.length_nil, List.length_map]
        omega)
    · rfl
  rw [hnone] at hdom
  exact Part.not_none_dom hdom

/-! ### eq. (6.1): the θ-gate instantiation

The equation is the gate congruence (`comp_congr_right_of_gate`) at the
filter exchange (`comp_ofStep_queryLimitFn_apply`): θ's budget gate
keeps every consulted inner pair replay-consistent and within the
weight budget — θ *is* its own weight filter — and there the
`[r]`-filtered composite has exactly `CBC`'s moves.  The invariants: in
α-mode all completed rounds consumed their exact block count and every
consumed answer is proper; in β-mode the current round is open on a
consistent offset. -/

section ThetaCBCQueryLimit

variable {bf : M → List X} {r : ℕ}

omit [AddCommGroup X] in
/-- Move inversion for `θ`, query branch. -/
private theorem theta_query_move_implies_shape
    {ws : List M} {vs : List (Option X)} {u : M}
    (h : Sum.inl u ∈ θ bf r (ws, vs)) :
    ws.length = vs.length + 1 ∧ (ws.map fun m => (bf m).length).sum ≤ r ∧
      ∃ hne : ws ≠ [], u = ws.getLast hne := by
  simp only [θ] at h
  split_ifs at h with h1 h2
  · simp only [Part.mem_some_iff, Sum.inl.injEq] at h
    exact ⟨h1.1, h1.2, List.ne_nil_of_length_pos (by omega), h⟩
  · split at h <;> simp at h
  · simp at h

omit [AddCommGroup X] in
/-- Move inversion for `θ`, answer branch. -/
private theorem theta_answer_move_implies_shape
    {ws : List M} {vs : List (Option X)} {z : X}
    (h : Sum.inr z ∈ θ bf r (ws, vs)) :
    ws.length = vs.length ∧ (ws.map fun m => (bf m).length).sum ≤ r ∧
      ∃ h0 : 0 < vs.length,
        vs.getLast (List.ne_nil_of_length_pos h0) = some z := by
  simp only [θ] at h
  split_ifs at h with h1 h2
  · simp at h
  · split at h
    · rename_i y hy
      simp only [Part.mem_some_iff, Sum.inr.injEq] at h
      exact ⟨h2.1, h2.2.2, h2.2.1, by rw [hy, h]⟩
    · simp at h
  · simp at h

omit [AddCommGroup X] in
/-- On `θ`'s tree a `⊥` answer is always the last event: the strict
relay never extends past it. -/
private theorem theta_reachable_none_is_terminal
    {p : List M × List (Option X)}
    (hr : PFunConverter.Reach (θ bf r) p) (hn : none ∈ p.2) :
    p.1.length = p.2.length ∧
      ∃ hne : p.2 ≠ [], p.2.getLast hne = none := by
  induction hr with
  | first u => simp at hn
  | answer hrp hx y ih =>
      rename_i us ys x
      obtain ⟨hl1, -, -⟩ := theta_query_move_implies_shape hx
      rcases List.mem_append.mp hn with hn' | hn'
      · exfalso
        obtain ⟨hlen, -⟩ := ih hn'
        have hlen' : us.length = ys.length := hlen
        omega
      · have hy : y = none := (List.mem_singleton.mp hn').symm
        subst hy
        refine ⟨?_, by simp, List.getLast_append_singleton _⟩
        show us.length = (ys ++ [none]).length
        simp only [List.length_append, List.length_singleton]
        omega
  | next hrp hv u ih =>
      rename_i us ys v
      obtain ⟨-, hne', hlast⟩ := ih hn
      obtain ⟨-, -, h0, hgl⟩ := theta_answer_move_implies_shape hv
      exfalso
      have h1 : ys.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

omit [AddCommGroup X] in
/-- `θ` is silent past a `⊥` (Def 3.8's input-alphabet clause). -/
private theorem theta_answers_in_output_alphabet :
    PFunConverter.AnswersInY (θ (Y := X) bf r) := by
  rintro ⟨ws, vs⟩ hr hn hd
  obtain ⟨hlen, hne', hlast⟩ := theta_reachable_none_is_terminal hr hn
  have hlen' : ws.length = vs.length := hlen
  rw [Part.dom_iff_mem] at hd
  obtain ⟨m, hm⟩ := hd
  cases m with
  | inl u =>
      obtain ⟨h1, -, -⟩ := theta_query_move_implies_shape hm
      omega
  | inr z =>
      obtain ⟨-, -, h0, hgl⟩ := theta_answer_move_implies_shape hm
      have h1 : vs.getLast (List.ne_nil_of_length_pos h0) = none := hlast
      rw [h1] at hgl
      simp at hgl

omit [AddCommGroup X] in
/-- `θ` is a value-subfunction of the identity-routing simple converter:
the budget guard only ever restricts. -/
private theorem theta_move_mem_simple_converter
    {p : List M × List (Option X)} {mv : M ⊕ X}
    (h : mv ∈ θ bf r p) : mv ∈ PFunConverter.simpleFn id id p := by
  simp only [θ] at h
  simp only [PFunConverter.simpleFn]
  split_ifs at h with h1 h2
  · rw [dif_pos h1.1]
    simpa using h
  · rw [dif_neg (by omega), dif_pos ⟨h2.1, h2.2.1⟩]
    exact h
  · simp at h

omit [AddCommGroup X] in
/-- `θ` closes every round it opens (§6.2.3's "stops replying" only
ever silences *between* rounds): the answer branch's budget guard is
implied by the query branch's, over the same outer history. -/
private theorem theta_stops_replying :
    PFunConverter.StopsReplying (θ (Y := X) bf r) := by
  intro us ys x y _ hx
  obtain ⟨hl1, hbud, -⟩ := theta_query_move_implies_shape hx
  simp only [θ]
  rw [dif_neg (by
      simp only [List.length_append, List.length_singleton]
      omega),
    dif_pos ⟨by
      simp only [List.length_append, List.length_singleton]
      omega, by
      simp only [List.length_append, List.length_singleton]
      omega, hbud⟩]
  rw [show (ys ++ [some y]).getLast (List.ne_nil_of_length_pos (by
      simp only [List.length_append, List.length_singleton]
      omega)) = some y from List.getLast_append_singleton _]
  trivial

omit [AddCommGroup X] in
/-- `θ` never opens a streak of two queries. -/
private theorem theta_answers_within_two :
    PFunConverter.AnswersWithin (θ (Y := X) bf r) 2 := by
  intro p _ ext hlen hall
  obtain ⟨u0, hx0⟩ := hall 0 (by omega)
  obtain ⟨u1, hx1⟩ := hall 1 (by omega)
  obtain ⟨h0, -, -⟩ := theta_query_move_implies_shape hx0
  obtain ⟨h1, -, -⟩ := theta_query_move_implies_shape hx1
  simp only [List.length_append, List.length_take] at h0 h1
  omega

end ThetaCBCQueryLimit

omit [AddCommGroup X] in
/-- **`θ` is a DDC** (CR18 Def 3.8) — membership in the class. -/
theorem theta_is_deterministic_discrete_converter
    {Y : Type u} (bf : M → List X) (r : ℕ) :
    PFunConverter.IsDDC (θ (Y := Y) bf r) := by
  have hle :
      ∀ p mv, mv ∈ θ (Y := Y) bf r p →
        mv ∈ PFunConverter.simpleFn id id p := by
    rintro p mv h
    simp only [θ] at h
    simp only [PFunConverter.simpleFn]
    split_ifs at h with hquery hanswer
    · rw [dif_pos hquery.1]
      simpa using h
    · rw [dif_neg (by omega), dif_pos ⟨hanswer.1, hanswer.2.1⟩]
      exact h
    · simp at h
  exact
    ⟨PFunConverter.answersInY_of_le_simpleFn hle, 2,
      PFunConverter.answersWithin_of_le_simpleFn hle⟩

omit [AddCommGroup X] in
/-- **`θ` is emulable** (MauRen11 Def 16 — the chosen Σ class of the
discrete-systems algebra): the budget-guarded identity-routing shape
delivers the two bounds, and θ closes every round it opens. -/
theorem theta_is_emulable (bf : M → List X) (r : ℕ) :
    PFunConverter.Emulable (θ (Y := X) bf r) :=
  PFunConverter.emulable_of_stopsReplying _
    (PFunConverter.answersWithin_of_le_simpleFn fun _ _ h =>
      theta_move_mem_simple_converter h)
    (PFunConverter.answersInY_of_le_simpleFn fun _ _ h =>
      theta_move_mem_simple_converter h)
    theta_stops_replying

/-- **`CBC` is a DDC** (CR18 Def 3.8) under a uniform block bound: the
generic `isDDC_ofStep` at the CBC boundary.  Def 3.8's finite-bound
clause *forces* the bound on VIL CBC — an unbounded block former has
unbounded query streaks — and the bound is free for the `Fintype`
message space of Theorem 6.1. -/
theorem cbc_is_deterministic_discrete_converter
    (bf : M → List X) (hbf : ∃ L, ∀ m, (bf m).length ≤ L) :
    PFunConverter.IsDDC (CBC bf) :=
  PFunConverter.ProtocolFn.isDDC_ofStep (cbcStep bf) _
    (cbc_step_issues_query_iff bf) hbf

/-- **CR18 eq. (6.1)**: `θr ĈBC = θr ĈBC[r]` — "the filter `[r]` is
irrelevant because the restriction implied by `θr` guarantees that at
most `r` queries are made to `Rₙ,ₙ`."  An equation *between
converters*: serial composition is `comp`, `[r]` is the
inner-interface query filter `queryLimitFn r`, and the two composites —
concrete partial functions — are equal outright.  The proof is the
algebra: gate congruence at the filter exchange. -/
@[rs_rule "rs.cbc.filter_exchange" equivalence random_systems]
theorem theta_comp_cbc_eq_theta_comp_query_limited_cbc
    (bf : M → List X) (r : ℕ) :
    PFunConverter.comp (θ bf r) (CBC bf) =
      PFunConverter.comp (θ bf r)
        (PFunConverter.comp (CBC bf) (PFunConverter.queryLimitFn r)) := by
  refine PFunConverter.comp_congr_right_of_gate
    (Pα := fun wsAct vs us ysDone =>
      ((wsAct = us ∧ vs.length = us.length) ∨
        (∃ w, wsAct = us ++ [w] ∧ vs.length = us.length)) ∧
      ysDone.length = (us.map fun m => (bf m).length).sum ∧
      ∃ ysX : List X, ysDone = ysX.map some)
    (Pβ := fun wsAct vs us ysDone =>
      us ≠ [] ∧ wsAct = us ∧ vs.length + 1 = us.length ∧
      (us.map fun m => (bf m).length).sum ≤ r ∧
      (us.dropLast.map fun m => (bf m).length).sum ≤ ysDone.length ∧
      ysDone.length ≤ (us.map fun m => (bf m).length).sum ∧
      ∃ preX : List X, ysDone.take
        ((us.dropLast.map fun m => (bf m).length).sum) = preX.map some)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- agreement under the gate: the filter exchange
    rintro wsAct vs us ysDone ⟨hMne, -, -, hbud, hoffβ, hupβ, hprop⟩
    exact (PFunConverter.ProtocolFn.comp_ofStep_queryLimitFn_apply
      (cbcStep bf) _ (cbc_step_issues_query_iff bf) hMne hoffβ hupβ hbud
        hprop).symm
  · -- θ forwards a message: the delivered round opens consistently
    rintro wsAct vs us ysDone u ⟨hphase, hlen, ysX, hproper⟩ hmθ
    obtain ⟨hl1, hbud, hne1, hval⟩ := theta_query_move_implies_shape hmθ
    rcases hphase with ⟨hws, hlv⟩ | ⟨w, hws, hlv⟩
    · exfalso
      rw [hws] at hl1
      omega
    · subst hws
      rw [List.getLast_append_singleton] at hval
      subst hval
      refine ⟨by simp, rfl, ?_, hbud, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at hl1 ⊢
        omega
      · rw [List.dropLast_concat]
        omega
      · rw [List.map_append, List.sum_append]
        omega
      · exact ⟨ysX.take (((us ++ [u]).dropLast.map
            fun m => (bf m).length).sum), by
          rw [hproper, ← List.map_take]⟩
  · -- θ answers: the next outer input arrives
    rintro wsAct vs us ysDone z ⟨hphase, hlen, ysX, hproper⟩ hmθ w
    obtain ⟨hl1, -, hpos, -⟩ := theta_answer_move_implies_shape hmθ
    rcases hphase with ⟨hws, hlv⟩ | ⟨w', hws, hlv⟩
    · exact ⟨Or.inr ⟨w, by rw [hws], hlv⟩, hlen, ysX, hproper⟩
    · exfalso
      rw [hws, List.length_append] at hl1
      simp only [List.length_singleton] at hl1
      omega
  · -- `CBC` answers: the round closed on its exact block count, proper
    rintro wsAct vs us ysDone v ⟨hMne, hws, hlv, hbud, hoffβ, hupβ, preX,
      hpreP⟩ hmβ
    obtain ⟨segX, hdropP, hvalP⟩ :=
      (PFunConverter.ProtocolFn.mem_ofStep_iff (cbcStep bf) _ hMne
        ysDone _).mp hmβ
    have hgeP : ¬ segX.length < (bf (us.getLast hMne)).length :=
      PFunConverter.ProtocolFn.not_lt_cnt_of_eq_inr
        (cbc_step_issues_query_iff bf)
        hvalP.symm
    have hsplitM : (us.map fun m => (bf m).length).sum
        = (us.dropLast.map fun m => (bf m).length).sum
          + (bf (us.getLast hMne)).length :=
      sum_map_dropLast_getLast _ hMne
    have hseglenP : segX.length = ysDone.length
        - (us.dropLast.map fun m => (bf m).length).sum := by
      have hl := congrArg List.length hdropP
      simp only [List.length_drop, List.length_map] at hl
      omega
    refine ⟨Or.inl ⟨hws, by
        simp only [List.length_append, List.length_singleton]
        omega⟩, by omega, preX ++ segX, ?_⟩
    conv_lhs => rw [← List.take_append_drop
      ((us.dropLast.map fun m => (bf m).length).sum) ysDone]
    rw [hpreP, hdropP, List.map_append]
  · -- `CBC` queries: the round stays open, the segment consistent
    rintro wsAct vs us ysDone x ⟨hMne, hws, hlv, hbud, hoffβ, hupβ, preX,
      hpreP⟩ hmβ y
    obtain ⟨segX, hdropP, hvalP⟩ :=
      (PFunConverter.ProtocolFn.mem_ofStep_iff (cbcStep bf) _ hMne
        ysDone _).mp hmβ
    have hltP : segX.length < (bf (us.getLast hMne)).length :=
      (cbc_step_issues_query_iff bf _ _).mp ⟨x, hvalP.symm⟩
    have hsplitM : (us.map fun m => (bf m).length).sum
        = (us.dropLast.map fun m => (bf m).length).sum
          + (bf (us.getLast hMne)).length :=
      sum_map_dropLast_getLast _ hMne
    have hseglenP : segX.length = ysDone.length
        - (us.dropLast.map fun m => (bf m).length).sum := by
      have hl := congrArg List.length hdropP
      simp only [List.length_drop, List.length_map] at hl
      omega
    refine ⟨hMne, hws, hlv, hbud, ?_, ?_, preX, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton]
      omega
    · rw [List.take_append_of_le_length hoffβ]
      exact hpreP
  · -- the initial gate state
    intro w
    exact ⟨Or.inr ⟨w, rfl, rfl⟩, by simp, [], rfl⟩

/-! ### The deterministic CBC coherence: `apply (CBC bf) = applyG (cbcStep bf)`

`CBC` is the outer-memoryless step converter
`PFunConverter.ProtocolFn.ofStep (cbcStep bf)` with round budgets the block
former's lengths, so the coherence is the generic step-converter
realization `apply_ofStep_eq_applyG` (StepRealization.lean) instantiated
at the CBC round boundary `cbc_step_issues_query_iff`. -/

/-- **The deterministic CBC coherence**: the protocol-function `CBC`,
applied by the transcript equations, is the `applyG`-application of
`cbcStep` to the system's raw function — against every system. -/
theorem apply_cbc_eq_step_application
    (bf : M → List X) (S : PFunDDS.DDS X X) :
    PFunConverter.apply (CBC bf) S = CausalApply.applyG (cbcStep bf) S.1 :=
  PFunConverter.ProtocolFn.apply_ofStep_eq_applyG (cbcStep bf) _
    (cbc_step_issues_query_iff bf) S

variable {M X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X] [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
/-- Coherence of the two presentations of the CBC converter: the
protocol-function `CBC`, applied by `apply`, computes the same random
system as the `ofStep` application through which `cbcReal` is defined
(the `queryLimit`/`queryLimitFn` precedent: apply-equal representatives
of the same converter). -/
theorem apply_cbc_to_uniform_random_function_eq_real_system (bf : M → List X) :
    PFunPDS.apply (CBC bf) (PFunPDS.URF (X := X) (Y := X)) =
      cbcReal bf := by
  unfold cbcReal PFunPDS.apply PFunPDS.applyDDC
  congr 1
  funext s
  rw [apply_cbc_eq_step_application bf s]
  exact (PFunConverter.DDC.apply_ofStep (cbcStep bf) s).symm

/-! ### No metric slack in the headline statements

Both sides of each headline comparison are same-predicate restrictions of
total laws (`θ_r` accumulates public block counts, `⌈q⌉` counts queries),
so they live on the shared-domain subcarrier where the strict contextual
metric *equals* `ENNReal.ofReal Δ`
(`StrictContextSharedDomain.maxEDist_filterDom_eq_ofReal_maxAdvantage`).
The `Δ`-stated radii of `cbc_mac_randomness_expander` and Theorem 6.1 therefore bound
the strict metric with no loss: CR18's costless rejection is invisible
when the stall pattern is a public function of the query history. -/

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
  [Fintype M] [DecidableEq M] in
/-- `θ_r`'s accumulated-block-count predicate is prefix-closed. -/
theorem thetaPredicate_prefixClosed (bf : M → List X) (r : ℕ) :
    PrefixClosed (fun messages : List M =>
      (messages.map fun m => (bf m).length).sum ≤ r) := by
  rintro messages _ ⟨tail, rfl⟩ h
  simp only [List.map_append, List.sum_append] at h ⊢
  omega

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype M] [DecidableEq M] in
/-- Applying `θ_r` to a law is the block-count domain restriction. -/
theorem theta_apply_eq_filterDom {Y : Type u} (bf : M → List X) (r : ℕ)
    (law : PFunPDS M Y) :
    PFunPDS.apply (θ bf r) law =
      PFunPDS.filterDom
        (fun messages => (messages.map fun m => (bf m).length).sum ≤ r)
        (thetaPredicate_prefixClosed bf r) law := by
  rw [theta_eq_restrictionFn]
  exact StrictContext.apply_law_restrictionFn _ _ law

/-- The real side is a probability system (the MBO strip of the game). -/
theorem cbcReal_isProbDist (bf : M → List X) : (cbcReal bf).isProbDist := by
  rw [← cbcGame_ignoreMBO]
  exact isProbDist_ignoreMBO (cbcGame_isProbDist bf)

/-- The real side is total on nonempty histories (the MBO strip of the
total game). -/
theorem cbcReal_totalOnNonempty (bf : M → List X) :
    CondEquiv.TotalOnNonempty (cbcReal bf) := by
  rw [← cbcGame_ignoreMBO]
  exact totalOnNonempty_ignoreMBO (cbcGame_totalOnNonempty bf)

/-- **Theorem 6.1's pair carries no metric slack**: on the
`θ_r`-restricted headline pair the strict contextual metric equals
`ENNReal.ofReal Δ`, so the birthday radius bounds the strict metric
exactly as it bounds `Δ`. -/
theorem maxEDist_theta_cbcReal_Vn_eq_ofReal_maxAdvantage
    (bf : M → List X) (r : ℕ) :
    StrictContext.maxEDist
        (PFunPDS.apply (θ bf r) (cbcReal bf))
        (PFunPDS.apply (θ bf r) (Vn (M := M) (X := X))) =
      ENNReal.ofReal
        Δ(PFunPDS.apply (θ bf r) (cbcReal bf),
          PFunPDS.apply (θ bf r) (Vn (M := M) (X := X))) := by
  rw [theta_apply_eq_filterDom, theta_apply_eq_filterDom]
  exact StrictContextSharedDomain.maxEDist_filterDom_eq_ofReal_maxAdvantage
    _ (thetaPredicate_prefixClosed bf r) (cbcReal bf) Vn
    (cbcReal_isProbDist bf) Vn_isProbDist
    (cbcReal_totalOnNonempty bf) Vn_totalOnNonempty

/-- **`cbc_mac_randomness_expander`'s pair carries no metric slack**: same receipt for
the query-budgeted comparison. -/
theorem maxEDist_filterQueries_cbcReal_Vn_eq_ofReal_maxAdvantage
    (bf : M → List X) (q : ℕ) :
    StrictContext.maxEDist
        (PFunPDS.filterQueries q (cbcReal bf))
        (PFunPDS.filterQueries q (Vn (M := M) (X := X))) =
      ENNReal.ofReal
        Δ(PFunPDS.filterQueries q (cbcReal bf),
          PFunPDS.filterQueries q (Vn (M := M) (X := X))) := by
  rw [PFunPDS.filterQueries_eq_filterDom, PFunPDS.filterQueries_eq_filterDom]
  exact StrictContextSharedDomain.maxEDist_filterDom_eq_ofReal_maxAdvantage
    _ (prefixClosed_length_le q) (cbcReal bf) Vn
    (cbcReal_isProbDist bf) Vn_isProbDist
    (cbcReal_totalOnNonempty bf) Vn_totalOnNonempty

end RandomSystems.CR18
