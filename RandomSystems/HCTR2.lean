/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.BitVecFacts
import RandomSystems.HTechnique.Derivation
import RandomSystems.HTechnique.StrongPRP
import RandomSystems.HTechnique.TweakablePRP

/-!
# HCTR2 — the paper's H-technique proof (ePrint 2021/1441), consolidated

The security proof of HCTR2 (Crowley–Huckleberry–Biggers, *Length-preserving encryption with
HCTR2*), formalized **as the paper proves it** (§3.4–3.5): the H-technique with extended
transcripts, in one file, over the paper's true bit-level message space
`M = ⋃ {0,1}^{≥n}` (a message is a head block, up to `L − 1` whole tail blocks, and `r < n`
leftover bits, over `F = GF(2ⁿ)`).

The theorem surface mirrors the paper 1:1:

* `hctr2Bit_security` — the paper's information-theoretic bound for the paper's adversary
  class (no pointless queries, `Σ_s dˢ ≤ σ` accounting via `bitNPB`):

      Adv±p̃rp ≤ (3σ² + 2qσ + 7σ + 2) / 2ⁿ⁺¹ + C(q,2) / 2ⁿ,   σ = σB;

* `hctr2Bit_security_unrestricted` — the reduction from arbitrary adversaries (the paper's
  §3.4 standing assumption discharged; beyond the paper);
* `hctr2Bit_main_lemma` (§3.4) and the generic `TweakablePRP.tprp_rnd` (§3.5, instantiated
  as `bit_tprp_rnd`) — the two lemmas the paper's proof combines;
* the p. 17 theorem over GF(2¹²⁸)+POLYVAL with the computational term is
  `hctr2_paper_theorem` in `HTechnique/HCTR2Paper.lean`.

(An earlier block-aligned shadow model was deleted 2026-07-11 once the paper chain moved to
the bit model; only its shared interface — `BinEnc`, `HashFamily`, `capRank`, `pickFresh` —
remains.)

Proof skeleton (the two `calc` citations of the headline):

1. **Main lemma** (§3.4) — `Adv(HCTR2[Perm F], ±rnd) ≤ (3σ²+2qσ+7σ+2)/2ⁿ⁺¹`, by the
   extended-transcript H-technique at ε = 0: reveal `(h̄, L) = (π(bin 0), π(bin 1))` after all
   queries, infer every block-cipher input/output from the transcript (p. 10), let `Bad` be a
   repeat in the inferred input multiset `D` or output multiset `R`; on good transcripts the
   real density `1/(N)_{σ_m}` dominates the ideal `N^{−σ_m}`, and `Pr_ideal[Bad]` is a
   pair-union bound whose 22 Fig-4/5 cells reduce to four shapes (uniform `1/N`, impossible,
   hash `d/N` via Properties 1/3, hash-XOR `d/N` via Property 2).
2. **PRP-RND** (§3.5, [HR03] App. C Lemma 6) — `Adv(±rnd, ±p̃rp) ≤ C(q,2)/2ⁿ`, per-class
   without-replacement vs. fresh-uniform counting.

This file consolidated and superseded the proofs of the former `HTechnique/HCTR2.lean`
and `HTechnique/HCTR2Bit.lean` (retired 2026-07-11; their consumers
`HCTR2Computational`/`Instance`/`Spec`/`Paper` now build on this file).  The generic
PRP-RND leg and reveal-collapse spine live in `HTechnique/TweakablePRP.lean` (`TweakablePRP.*`).
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.CR18.HCTR2

open RandomSystems.CR18 RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique (QueryDir)
open RandomSystems.HTechnique.HashThenPRF (choose2)

-- Standing `[Fintype _]`-style section variables are shared by most but not all lemmas;
-- repo convention silences the per-theorem inclusion lint.
set_option linter.unusedSectionVars false

/-! ### Characteristic-2 dischargers

XOR algebra is swept under the rug in the paper; these three macros do the same in Lean. -/

/-- `linear_combination` normalizer for char 2: `ring_nf`, then kill the `2 = 0` residue. -/
macro "char2_norm" : tactic => `(tactic| (ring_nf; simp [CharTwo.two_eq_zero]))

/-- Closes any char-2 ring identity (`a+b+b=a`, XOR rearrangements). -/
macro "char2" : tactic =>
  `(tactic| (ring_nf; simp only [CharTwo.two_eq_zero, mul_zero, zero_mul,
      add_zero, zero_add, mul_comm]))

/-- Closes `a = b ↔ a' = b'` when the sides are char-2 linear rearrangements of each other. -/
macro "char2_iff" : tactic =>
  `(tactic| (constructor <;> intro h <;> linear_combination (norm := char2_norm) h))

/-- The decidable-case-grid residual closer (STATUS §7.2's blessed shape): split the
`ite`s, then close each branch by `rfl`, cast-and-ring, or arithmetic contradiction. -/
macro "hctr2_ite_arith" : tactic =>
  `(tactic| (split_ifs <;> first | rfl | (push_cast; ring1) | (exfalso; omega)))

/-! ## Shared interface — hash bundle, union-bound rank, WLOG helper

`F` is the block field (`GF(2ⁿ)`, `⊕ = +`), `T` the tweak space, `L` a block-length cap.
`BinEnc`/`HashFamily` are the paper's §3.2 objects (POLYVAL realizes them —
`HTechnique/HCTR2Paper.lean`); `capRank` is the fixed-cap linear rank ordering the
union-bound pairs (used below at cap `Fin (L + 2)`); `pickFresh` feeds the
pointless-query WLOG padding. -/

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable (T : Type) [Fintype T] [DecidableEq T]

/-- The paper's `bin`: block encoding of small integers, carried as data with its injectivity
on the used range `0..L+1`. -/
structure BinEnc (L : ℕ) where
  bin : ℕ → F
  bin_inj : ∀ i j, i ≤ L + 1 → j ≤ L + 1 → bin i = bin j → i = j

/-- **The paper's structured hash tail** (§3.2): the message minus its head block, kept
structured — `ℓ` full tail blocks `N` over `F`, and an optional partial block (`none` =
block-aligned message, no leftover bits; `some b` = one `10*`-padded partial block for the
unaligned case).  This is the honest hash input: the polynomial map's INJECTIVITY (App. A)
and its per-query degree `dˢ = 1 + ⌈|T|/n⌉ + ⌈|N|/n⌉` are stated over these structured
inputs — with the alignment (`none`/`some`) fixed by the tweak-length/mode block
`bin(2|T|+2/3)` in the POLYVAL realization, NOT by an invented encoding block. -/
abbrev BitTailS (F : Type) [Field F] : Type := Σ ℓ, (Fin ℓ → F) × Option F

/-- The paper's per-query cipher/degree granularity `mˢ` of a structured tail: the head
block, `ℓ` full tail blocks, and (if unaligned) the one partial block —
`mˢ = 1 + ℓ + (partial ? 1 : 0)`.  The honest hash degree is `dˢ = mˢ + ⌈|T|/n⌉` (p. 9,
`degB t mˢ`); `⌈|N|/n⌉ = mˢ − 1`, and the leading `bin` block supplies the `+1`. -/
def bitTailDegLen {F : Type} [Field F] (m : BitTailS F) : ℕ :=
  1 + m.1 + (if m.2.2.isSome then 1 else 0)

/-- The keyed hash of §3.2 (POLYVAL in the spec) over the **structured tail** `BitTailS`,
with the paper's three properties at a single degree bound `d` for every tail within the
cap. -/
structure HashFamily (F T : Type) [Field F] [Fintype F] (L : ℕ) where
  /-- `H_h̄(tweak, tail)` on a structured tail (`ℓ` full blocks + optional partial). -/
  hash : F → T → BitTailS F → F
  /-- Degree bound `d = 1 + ⌈|T|/n⌉ + ⌈|P|/n⌉` (uniform over lengths ≤ cap). -/
  d : ℕ
  /-- Property 1: almost uniformity. -/
  prop1 : ∀ (t : T) (m : BitTailS F), m.1 ≤ L → ∀ (g : F),
    (Dist.uniform F).mass (fun h => hash h t m = g) ≤ (d : NNReal) / Fintype.card F
  /-- Property 2: almost-XOR-universality, over DISTINCT `(tweak, structured tail)` pairs. -/
  prop2 : ∀ (t₁ : T) (m₁ : BitTailS F), m₁.1 ≤ L → ∀ (t₂ : T) (m₂ : BitTailS F), m₂.1 ≤ L →
    ∀ (g : F), (t₁, m₁) ≠ (t₂, m₂) →
    (Dist.uniform F).mass (fun h => hash h t₁ m₁ + hash h t₂ m₂ = g) ≤
      (d : NNReal) / Fintype.card F
  /-- Property 3: key-offset almost uniformity. -/
  prop3 : ∀ (t : T) (m : BitTailS F), m.1 ≤ L → ∀ (g : F),
    (Dist.uniform F).mass (fun h => hash h t m + h = g) ≤ (d : NNReal) / Fintype.card F

variable {F T} {L : ℕ}
variable {q : ℕ}

/-- Lexicographic rank on `Fin q × Fin L` (the `inr`-part of `capRank`). -/
def pairRank {q : ℕ} (x : Fin q × Fin L) : ℕ := x.1.val * L + x.2.val

theorem pairRank_injective {q : ℕ} : Function.Injective (pairRank (L := L) (q := q)) := by
  have key : ∀ (x y : Fin q) (u v : Fin L), x.val < y.val →
      x.val * L + u.val < y.val * L + v.val := by
    intro x y u v hxy
    have hu := u.isLt
    have h2 : (x.val + 1) * L ≤ y.val * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hxy)
    rw [Nat.add_one_mul] at h2
    omega
  rintro ⟨s, j⟩ ⟨s', j'⟩ h
  simp only [pairRank] at h
  rcases lt_trichotomy s.val s'.val with hs | hs | hs
  · exact absurd h (Nat.ne_of_lt (key s s' j j' hs))
  · obtain rfl : s = s' := Fin.ext hs
    exact congrArg (fun z : Fin L => (s, z)) (Fin.ext (by omega))
  · exact absurd h (Nat.ne_of_gt (key s' s j' j hs))

/-- Linear rank on the fixed cap — orders the union-bound pairs so each *unordered* collision
is counted once (the ordered-pair sum would overshoot the §3.4 budget by the paper's
`C(σ_m,2)`-vs-ordered factor). -/
def capRank {q : ℕ} : (Bool ⊕ Fin q × Fin L) → ℕ
  | Sum.inl false => 0
  | Sum.inl true => 1
  | Sum.inr x => 2 + pairRank x

theorem capRank_injective {q : ℕ} : Function.Injective (capRank (L := L) (q := q)) := by
  rintro ((_ | _) | x) ((_ | _) | y) h <;> simp only [capRank] at h <;>
    first
    | rfl
    | omega
    | exact congrArg Sum.inr (pairRank_injective (Nat.add_left_cancel h))

/-! Cap reduction pack: constructor-shape reductions for `capRank`, used by name
(`rw`/`simp only`) in the cell dispatch and leaf lemmas; `capRank_inl_false/true` stay
`@[simp]` for the rank-order side goals of the fiber counts. -/

@[simp] theorem capRank_inl_false {q : ℕ} :
    capRank (L := L) (q := q) (Sum.inl false) = 0 := rfl
@[simp] theorem capRank_inl_true {q : ℕ} :
    capRank (L := L) (q := q) (Sum.inl true) = 1 := rfl
theorem capRank_inr {q : ℕ} (s : Fin q) (j : Fin L) :
    capRank (Sum.inr (s, j)) = 2 + s.val * L + j.val := (Nat.add_assoc 2 _ _).symm

/-! #### Sorted-guard characterization

The `h̄`/`L` rows sort before every `inr` cell; on `inr`–`inr` cells the sorted guard is
exactly the lexicographic order — the paper's "later query `s`" convention. -/

/-- The `h̄`/`L` rows sort before every `inr` cell. -/
theorem capRank_inl_lt_inr {q : ℕ} (b : Bool) (s : Fin q) (j : Fin L) :
    capRank (L := L) (q := q) (Sum.inl b) < capRank (Sum.inr (s, j)) := by
  cases b <;>
    simp only [capRank_inl_false, capRank_inl_true, capRank_inr] <;>
    omega

/-- Sorted `inr`–`inr` rank inversion: the lex rank order gives the paper's
"later query" convention. -/
theorem capRank_lt_inr_inr {q : ℕ} {r s : Fin q} {i j : Fin L}
    (h : capRank (L := L) (Sum.inr (r, i)) < capRank (Sum.inr (s, j))) :
    r < s ∨ (r = s ∧ i.val < j.val) := by
  rcases lt_trichotomy r s with h' | h' | h'
  · exact Or.inl h'
  · refine Or.inr ⟨h', ?_⟩
    subst h'
    simp only [capRank, pairRank] at h
    omega
  · exfalso
    simp only [capRank, pairRank] at h
    have hi := i.isLt
    have h2 : (s.val + 1) * L ≤ r.val * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt h')
    rw [Nat.add_one_mul] at h2
    omega

/-- Converse direction of `capRank_lt_inr_inr`: the sorted guard on `inr`–`inr` cells is
exactly the lexicographic order. -/
theorem capRank_lt_inr_inr_iff {q : ℕ} {r s : Fin q} {i j : Fin L} :
    capRank (L := L) (Sum.inr (r, i)) < capRank (Sum.inr (s, j))
      ↔ r < s ∨ (r = s ∧ i.val < j.val) := by
  refine ⟨capRank_lt_inr_inr, ?_⟩
  rintro (hrs | ⟨rfl, hij⟩)
  · simp only [capRank_inr]
    have hi := i.isLt
    have h2 : (r.val + 1) * L ≤ s.val * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hrs)
    rw [Nat.add_one_mul] at h2
    omega
  · simp only [capRank_inr]
    omega

/-! ### The pointless-query WLOG helper

The paper *assumes* the adversary never makes a pointless query (§3.4); the reduction from
unrestricted adversaries (`hctr2Bit_security_unrestricted`) self-answers checkably-pointless
queries and pads with head-fresh forward queries once the environment halts — `pickFresh`
supplies the fresh head block. -/

/-- Pick a field element outside `s` (junk when `s` is everything). -/
private def pickFresh (s : Finset F) : F :=
  if h : (Finset.univ \ s).Nonempty then h.choose else 0

private theorem pickFresh_notMem {s : Finset F} (hs : s.card < Fintype.card F) :
    pickFresh s ∉ s := by
  have hne : (Finset.univ \ s).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
    omega
  rw [pickFresh, dif_pos hne]
  have hmem := hne.choose_spec
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2

/-! ## Part 2 — bit-level HCTR2

The paper's true message space `M = ⋃_{ℓ ≥ n} {0,1}^ℓ`: a message of length class
`(ℓ, r) : Fin L × Fin n` is a head block, `ℓ` whole tail blocks over `F`, and `r` leftover
bits, so the last XCTR keystream block is consumed only partially (the paper's `Dˢ`
bookkeeping, §3.4).  Modeling decisions (paper-faithful, cf. p. 7):

* **Block↔bits bridge.**  Blocks live in `F = GF(2ⁿ)` for the hash/field algebra; the
  partial-block operations are XORs on `BitVec`.  `BlockBits` bundles an additive bijection
  `F ≃ BitVec n` carrying `+` to `^^^` — the only extra hypothesis over Part 1.
* **Structured tail shape.**  The hash is evaluated on the paper's honest **structured**
  tail `BitTailS` (`hashTailB`): the `ℓ` full blocks `N` and, only when unaligned
  (`r > 0`), one `10*`-padded partial block (`none`/`some`) — the paper's `H(T, N)` input.
  Injectivity (App. A) and the per-query degree `dˢ = degB t mˢ = mˢ + ⌈|T|/n⌉`
  (`mˢ = 1 + ℓ + (r ≠ 0 ? 1 : 0)`, `bitTailDegLen`) are stated over these structured inputs;
  the tweak-length mode block `bin(2|T|+2/3)` (which fixes the alignment) lives in the
  POLYVAL realization (`HTechnique/HCTR2Paper.lean`), NOT an invented encoding block.
* **σ accounting.**  The paper's per-query budget `dˢ = mˢ + ⌈|Tˢ|/n⌉` (p. 9) is carried
  honestly: `twBlocks : T → ℕ` supplies the tweak block count, `HashFamilyS.degB … mˢ` the
  per-query hash degree `dˢ` (the green Fig-4/5 cells pay exactly this at every query, both
  `r = 0` and `r > 0`), and the adversary class `bitNPB` is the paper's — no pointless
  queries AND within the block budget `Σ_s dˢ ≤ σB`.  XCTR still always issues the
  `(ℓ+1)`-th call (`mBlocksBit = ℓ + 2 ≥ 2`, the reveal's fork-free cipher count, keeping
  `bit_count_core`'s `2 ≤ mˢ` minimum); the σ cap `q·(L+τ+1)` and the per-`r>0`-query
  charge are paper-exact. -/

/-- **Block↔bits bridge**: an additive bijection between the block field `F` (`= GF(2ⁿ)`)
and `n`-bit vectors, carrying field addition to XOR.  Abstract — instantiable for a
concrete `GaloisField`. -/
structure BlockBits (F : Type) [Field F] (n : ℕ) where
  /-- The block↔bits bijection. -/
  toBits : F ≃ BitVec n
  /-- Field addition is bit XOR. -/
  toBits_add : ∀ a b : F, toBits (a + b) = toBits a ^^^ toBits b

/-- Bit message fiber at length class `(ℓ, r)`: a head block, an `ℓ`-block full tail, and
`r` leftover bits. -/
abbrev bitMsg (F : Type) [Field F] (ℓ r : ℕ) : Type := F × (Fin ℓ → F) × BitVec r

variable {n : ℕ}

/-- Split a flattened length index into `(ℓ, r) : Fin L × Fin n`. -/
def splitIdx (k : Fin (L * n)) : Fin L × Fin n :=
  (finProdFinEquiv (m := L) (n := n)).symm k

/-- The bit message family, flattened over the single length index `Fin (L * n)` (the
`Sigma`-carrier interface takes one `Fin`; `L = 0` or `n = 0` gives an empty domain and
vacuous statements, so no positivity guard is carried). -/
def bitMsgL : Fin (L * n) → Type :=
  fun k => bitMsg F (splitIdx k).1.val (splitIdx k).2.val

/-- The bit-level query and response carriers (twins of `HQ`/`HM`); every oracle below is
length-class-preserving. -/
local notation:max "HQB" => QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))
local notation:max "HMB" => Sigma (bitMsgL (F := F) (L := L) (n := n))

-- Named per-fiber instances (mirror of the Part-1 block): the Sigma/Pi `Fintype`/
-- `DecidableEq` builders resolve the coin spaces; the bit transcript space is finite and
-- (classically) discrete.
instance bitMsgL_fintype (k : Fin (L * n)) : Fintype (bitMsgL (F := F) k) := by
  unfold bitMsgL bitMsg; infer_instance
instance bitMsgL_decEq (k : Fin (L * n)) : DecidableEq (bitMsgL (F := F) k) := by
  unfold bitMsgL bitMsg; infer_instance
instance bitMsgL_nonempty (k : Fin (L * n)) : Nonempty (bitMsgL (F := F) k) := by
  unfold bitMsgL bitMsg; infer_instance
instance bitTranscript_discrete : DiscreteTranscriptSpace HQB HMB q := Classical.decEq _
instance bitTranscript_finite : FiniteTranscriptSpace HQB HMB q := inferInstance

/-! ### The hash input (paper p. 7) -/

/-- The `10*` (set-marker) pad of the `r` low bits into an `n`-bit block: the `r` payload
bits, a marker `1` at bit `r`, zeros above — the leftover count `r` is recoverable. -/
def padBlockBits (n r : ℕ) (p : BitVec r) : BitVec n :=
  p.setWidth n ||| BitVec.twoPow n r

/-- Pad the `r` leftover bits into a full block of `F` — the paper's `pad(M‖1)`. -/
def padBlock (bb : BlockBits F n) (r : ℕ) (part : BitVec r) : F :=
  bb.toBits.symm (padBlockBits n r part)

/-- The paper's **structured** hashed tail at length class `(ℓ, r)`: the `ℓ` full blocks `N`,
plus an optional `10*`-padded partial block (`none` when `r = 0`, block-aligned; `some`
`pad(P‖1)` when `r > 0`).  NO invented length/alignment block — alignment is the `none`/`some`
tag, and the tweak-length/mode block `bin(2|T|+2/3)` (App. A) lives in the POLYVAL
realization.  Injectivity flows through `padBlock`'s `10*` marker (`padBlock_r_inj`). -/
def hashTailB (bb : BlockBits F n) (ℓ : Fin L) (r : Fin n)
    (N : Fin ℓ.val → F) (P : BitVec r.val) : BitTailS F :=
  ⟨ℓ.val, N, if r.val = 0 then none else some (padBlock bb r.val P)⟩

/-! ### The σ-accounted hash bundle -/

/-- The σ-accounted hash bundle (paper p. 9–10): `HashFamily` plus the per-`(tweak, tail)`
honest degree bound `degB`, applied at the paper's granularity `bitTailDegLen = mˢ`, with
sharp Properties 1'/2'/3'.  The paper's `dˢ = degB t mˢ = mˢ + ⌈|T|/n⌉` is BOTH a query's
block count and its hash polynomial degree, and each green Fig-4/5 cell costs `dˢ/2ⁿ`, so
the uniform `d` alone cannot reach the σ-accounted constant.  `degB` is tweak-sensitive
(`T → ℕ → ℕ`): a tail-only bound could only carry the worst-case tweak and overshoots
`σ = Σ_s dˢ` when tweak lengths vary.  POLYVAL realizes `degB t k = ⌈|T|/n⌉ + k` (the
leading `bin` block is absorbed into `mˢ`'s head), so `degB t mˢ = mˢ + ⌈|T|/n⌉ = dˢ`. -/
structure HashFamilyS (F T : Type) [Field F] [Fintype F] (L : ℕ)
    extends HashFamily F T L where
  /-- Per-`(tweak, mˢ)` honest degree bound (the paper's `dˢ = degB t mˢ`, p. 9). -/
  degB : T → ℕ → ℕ
  /-- `degB t` is monotone in `mˢ`. -/
  degB_mono : ∀ t : T, Monotone (degB t)
  /-- Within the cap, the per-length bound is under the uniform `d`. -/
  degB_le : ∀ (t : T) {k : ℕ}, k ≤ L → degB t k ≤ d
  /-- Property 1, sharp: `prop1` at `degB t mˢ`. -/
  prop1' : ∀ (t : T) (m : BitTailS F), m.1 ≤ L → ∀ (g : F),
    (Dist.uniform F).mass (fun h => hash h t m = g) ≤
      (degB t (bitTailDegLen m) : NNReal) / Fintype.card F
  /-- Property 2, sharp: the paper's honest `max (dʳ, dˢ)` (Figs 4–5). -/
  prop2' : ∀ (t₁ : T) (m₁ : BitTailS F), m₁.1 ≤ L → ∀ (t₂ : T) (m₂ : BitTailS F), m₂.1 ≤ L →
    ∀ (g : F), (t₁, m₁) ≠ (t₂, m₂) →
    (Dist.uniform F).mass (fun h => hash h t₁ m₁ + hash h t₂ m₂ = g) ≤
      (max (degB t₁ (bitTailDegLen m₁)) (degB t₂ (bitTailDegLen m₂)) : NNReal) / Fintype.card F
  /-- Property 3, sharp: `prop3` at `degB t mˢ`. -/
  prop3' : ∀ (t : T) (m : BitTailS F), m.1 ≤ L → ∀ (g : F),
    (Dist.uniform F).mass (fun h => hash h t m + h = g) ≤
      (degB t (bitTailDegLen m) : NNReal) / Fintype.card F

/-! ### The construction (paper Figures 2–3, bit domain) -/

/-- HCTR2 encryption at length class `(ℓ, r)` (Figure 2, bit domain): hash over the padded
tail, one XCTR pass over the `ℓ` full blocks and the always-present `(ℓ+1)`-th call,
consumed to `r` bits. -/
def bitEncCore (bb : BlockBits F n) (be : BinEnc F L) (Hfb : HashFamily F T (L + 2))
    (π : Equiv.Perm F) (t : T) (ℓ : Fin L) (r : Fin n)
    (p : bitMsg F ℓ.val r.val) : bitMsg F ℓ.val r.val :=
  let m := p.1
  let nn := p.2.1
  let np := p.2.2
  let hk := π (be.bin 0)
  let mm := m + Hfb.hash hk t (hashTailB bb ℓ r nn np)
  let uu := π mm
  let s := mm + uu + π (be.bin 1)
  let v := fun i : Fin ℓ.val => nn i + π (s + be.bin (i.val + 1))
  let ksLast := π (s + be.bin (ℓ.val + 1))
  let vp := np ^^^ (bb.toBits ksLast).setWidth r.val
  (uu + Hfb.hash hk t (hashTailB bb ℓ r v vp), v, vp)

/-- HCTR2 decryption at length class `(ℓ, r)` (Figure 3, bit domain): the inverse pass. -/
def bitDecCore (bb : BlockBits F n) (be : BinEnc F L) (Hfb : HashFamily F T (L + 2))
    (π : Equiv.Perm F) (t : T) (ℓ : Fin L) (r : Fin n)
    (c : bitMsg F ℓ.val r.val) : bitMsg F ℓ.val r.val :=
  let u := c.1
  let vv := c.2.1
  let vp := c.2.2
  let hk := π (be.bin 0)
  let uu := u + Hfb.hash hk t (hashTailB bb ℓ r vv vp)
  let mm := π.symm uu
  let s := mm + uu + π (be.bin 1)
  let nn := fun i : Fin ℓ.val => vv i + π (s + be.bin (i.val + 1))
  let np := vp ^^^ (bb.toBits (π (s + be.bin (ℓ.val + 1)))).setWidth r.val
  (mm + Hfb.hash hk t (hashTailB bb ℓ r nn np), nn, np)

/-- Correctness (§2.4), bit domain: `Dec ∘ Enc = id` at every length class — field XOR
cancellation for the head and full blocks, `BitVec` XOR cancellation for the partial last
block. -/
theorem bitDecCore_bitEncCore (bb : BlockBits F n) (be : BinEnc F L)
    (Hfb : HashFamily F T (L + 2)) (π : Equiv.Perm F) (t : T) (ℓ : Fin L) (r : Fin n)
    (p : bitMsg F ℓ.val r.val) :
    bitDecCore bb be Hfb π t ℓ r (bitEncCore bb be Hfb π t ℓ r p) = p := by
  obtain ⟨m, nn, np⟩ := p
  have hself : ∀ a b : F, a + b + b = a := fun a b => by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hbit : ∀ {w : ℕ} (a b : BitVec w), (a ^^^ b) ^^^ b = a := fun a b => by
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  set hk := π (be.bin 0) with hhk
  set mm := m + Hfb.hash hk t (hashTailB bb ℓ r nn np) with hmm
  set s := mm + π mm + π (be.bin 1) with hs
  set v : Fin ℓ.val → F := fun i => nn i + π (s + be.bin (i.val + 1)) with hv
  set vp := np ^^^ (bb.toBits (π (s + be.bin (ℓ.val + 1)))).setWidth r.val with hvp
  simp only [bitEncCore, bitDecCore, ← hhk, ← hmm]
  rw [show (π mm + Hfb.hash hk t (hashTailB bb ℓ r v vp))
        + Hfb.hash hk t (hashTailB bb ℓ r v vp) = π mm from hself _ _,
    Equiv.symm_apply_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- head block `M`
    show mm + Hfb.hash hk t
        (hashTailB bb ℓ r (fun i : Fin ℓ.val => v i + π (s + be.bin (i.val + 1)))
          (vp ^^^ (bb.toBits (π (s + be.bin (ℓ.val + 1)))).setWidth r.val))
        = m
    rw [show (fun i : Fin ℓ.val => v i + π (s + be.bin (i.val + 1))) = nn from
        funext fun i => hself _ _,
      show vp ^^^ (bb.toBits (π (s + be.bin (ℓ.val + 1)))).setWidth r.val = np by
        rw [hvp]; exact hbit _ _]
    exact hself _ _
  · -- full tail `N`
    funext i; exact hself _ _
  · -- partial last block
    show vp ^^^ (bb.toBits (π (s + be.bin (ℓ.val + 1)))).setWidth r.val = np
    rw [hvp]; exact hbit np _

/-- The two-directional bit-level HCTR2 oracle: length class preserved, direction routed to
the encryption or decryption core. -/
def hctr2BitFun (bb : BlockBits F n) (be : BinEnc F L) (Hfb : HashFamily F T (L + 2))
    (π : Equiv.Perm F) : HQB → HMB :=
  fun x =>
    ⟨x.2.2.1, match x.1 with
      | QueryDir.fwd => bitEncCore bb be Hfb π x.2.1
          (splitIdx x.2.2.1).1 (splitIdx x.2.2.1).2 x.2.2.2
      | QueryDir.inv => bitDecCore bb be Hfb π x.2.1
          (splitIdx x.2.2.1).1 (splitIdx x.2.2.1).2 x.2.2.2⟩

/-- **World X, bit domain** — `HCTR2[Perm F]`: one uniform `π` drives the construction
across all bit length classes. -/
def hctr2BitReal (bb : BlockBits F n) (be : BinEnc F L) (Hfb : HashFamily F T (L + 2)) :
    ProbPDS HQB HMB :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (Equiv.Perm F), Dist.uniform_isProbDist⟩
    (fun π => hctr2BitFun bb be Hfb π)

theorem hctr2BitReal_KStepTotal (bb : BlockBits F n) (be : BinEnc F L)
    (Hfb : HashFamily F T (L + 2)) :
    (hctr2BitReal bb be Hfb).KStepTotal q := functionEvaluatorProb_KStepTotal _ _ q

/-! ### σ accounting and the paper's per-transcript budget (p. 10)

`dˢ = mˢ + ⌈|Tˢ|/n⌉`: `mˢ = ℓˢ + 2` block-cipher calls (head, `ℓˢ` full XCTR blocks, the
always-present partial call), plus the tweak's hash-block count, supplied abstractly as
`twBlocks : T → ℕ`.  The per-transcript budget is `Σ_s dˢ`. -/

/-- The plaintext of query `s`: input on `enc`, response on `dec` (twin of `plain`). -/
def bitPlain (t : TranscriptPrefix HQB HMB q) (s : Fin q) : HMB :=
  match (t.1.get s).1 with
  | QueryDir.fwd => (t.1.get s).2.2
  | QueryDir.inv => t.2.get s

/-- The tweak of query `s` (twin of `tweak`). -/
def bitTweak (t : TranscriptPrefix HQB HMB q) (s : Fin q) : T := (t.1.get s).2.1

/-- Block-cipher call count of query `s`: `mˢ = ℓˢ + 2`. -/
def mBlocksBit (t : TranscriptPrefix HQB HMB q) (s : Fin q) : ℕ :=
  (splitIdx (bitPlain t s).1).1.val + 2

/-- **Per-query block budget `dˢ`** (paper p. 10): `dˢ = mˢ + ⌈|Tˢ|/n⌉`. -/
def bitD (twBlocks : T → ℕ) (t : TranscriptPrefix HQB HMB q) (s : Fin q) : ℕ :=
  mBlocksBit t s + twBlocks (bitTweak t s)

/-- The transcript's total block budget `Σ_s dˢ` (the paper's `σ ≥ Σ_s dˢ`, p. 10). -/
def sigmaDBit (twBlocks : T → ℕ) (t : TranscriptPrefix HQB HMB q) : ℕ :=
  ∑ s : Fin q, bitD twBlocks t s

/-- **The paper's bit-level adversary class**: no pointless queries (the generic `TweakablePRP.NP`
filter at the bit fibers) AND within the per-transcript block budget `Σ_s dˢ ≤ σB` (the
paper's "at most σ blocks of total work", p. 17). -/
def bitNPB (twBlocks : T → ℕ) (σB : ℕ) (t : TranscriptPrefix HQB HMB q) : Prop :=
  TweakablePRP.NP t ∧ sigmaDBit twBlocks t ≤ σB

/-! ### The bit PRP-RND leg (paper §3.5, free instantiation of the generic leg)

`N_min = |F|`, realized by the shortest, `(ℓ, r) = (0, 0)` class:
`|bitMsg F ℓ r| = |F|^{ℓ+1}·2^r ≥ |F|` via the head-block injection. -/

/-- `N_min = |F|`: every bit fiber embeds `F` through its head block. -/
private theorem card_le_bitMsg_card (k : Fin (L * n)) :
    Fintype.card F ≤ Fintype.card (bitMsgL (F := F) (L := L) (n := n) k) :=
  Fintype.card_le_of_injective
    (fun x : F => ((x, fun _ => 0, 0) : bitMsgL (F := F) (L := L) (n := n) k))
    (fun _ _ h => (Prod.ext_iff.mp h).1)

/-- **PRP-RND, bit fibers** (paper §3.5 / [HR03] App. C Lemma 6): `±rnd` is
`C(q,2)/2ⁿ`-close to `±p̃rp` over the bit fibers against non-pointless adversaries — the
`N_min = |F|` instance of the generic leg endpoint `TweakablePRP.tprp_rnd`. -/
theorem bit_tprp_rnd :
    filteredAdaptiveTranscriptAdvantage (q := q) TweakablePRP.NP
      (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) TweakablePRP.rnd ≤
      ((choose2 q : NNReal) / Fintype.card F : ℝ) :=
  TweakablePRP.tprp_rnd (Fintype.card F) Fintype.card_pos card_le_bitMsg_card

/-! ### BitVec support: cardinalities, zero-extension, and the `10*` pad

The leftover-bit toolkit of the inference and reveal layers: fiber cardinalities for the
σ⁺ counting, injectivity of zero-extension, and recoverability of `(r, P)` from the
paper's `pad(M‖1)` set marker. -/

/-- Fiber cardinality `|bitMsg (ℓ, r)| = N^{ℓ+1}·2^r`. -/
theorem bitMsgL_card (k : Fin (L * n)) :
    Fintype.card (bitMsgL (F := F) (L := L) (n := n) k)
      = Fintype.card F ^ ((splitIdx k).1.val + 1) * 2 ^ (splitIdx k).2.val := by
  show Fintype.card
      (F × (Fin (splitIdx k).1.val → F) × BitVec (splitIdx k).2.val) = _
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    card_bitVec, pow_succ]
  ring

private theorem padBlockBits_self (n r : ℕ) (hr : r < n) (p : BitVec r) :
    (padBlockBits n r p).getLsbD r = true := by
  unfold padBlockBits
  rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_twoPow,
    BitVec.getLsbD_of_ge p r (le_refl r)]
  simp [hr]

private theorem padBlockBits_gt (n r : ℕ) (p : BitVec r) (j : ℕ) (hj : r < j) :
    (padBlockBits n r p).getLsbD j = false := by
  unfold padBlockBits
  rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_twoPow,
    BitVec.getLsbD_of_ge p j (by omega)]
  simp [Nat.ne_of_lt hj]

/-- The `10*` marker position separates the pad widths. -/
theorem padBlockBits_r_inj (n r1 r2 : ℕ) (hr1 : r1 < n) (hr2 : r2 < n)
    (p1 : BitVec r1) (p2 : BitVec r2)
    (h : padBlockBits n r1 p1 = padBlockBits n r2 p2) : r1 = r2 := by
  by_contra hne
  rcases Nat.lt_trichotomy r1 r2 with hlt | heq | hgt
  · have hh := congrArg (fun b => b.getLsbD r2) h
    simp only at hh
    rw [padBlockBits_gt n r1 p1 r2 hlt, padBlockBits_self n r2 hr2 p2] at hh
    exact absurd hh (by simp)
  · exact hne heq
  · have hh := congrArg (fun b => b.getLsbD r1) h
    simp only at hh
    rw [padBlockBits_self n r1 hr1 p1, padBlockBits_gt n r2 p2 r1 hgt] at hh
    exact absurd hh (by simp)

/-- Truncation under the marker recovers the payload bits. -/
theorem padBlockBits_setWidth (n r : ℕ) (hr : r < n) (p : BitVec r) :
    (padBlockBits n r p).setWidth r = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth]
  unfold padBlockBits
  rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_twoPow]
  have h1 : decide (i < r) = true := by simp [hi]
  have h2 : decide (i < n) = true := by simp; omega
  have h3 : decide (r = i) = false := by simp; omega
  rw [h1, h2, h3]; simp

/-- `padBlock` recovers the leftover-bit count `r` from the `10*` marker. -/
theorem padBlock_r_inj (bb : BlockBits F n) (r1 r2 : ℕ) (hr1 : r1 < n) (hr2 : r2 < n)
    (p1 : BitVec r1) (p2 : BitVec r2)
    (h : padBlock bb r1 p1 = padBlock bb r2 p2) : r1 = r2 :=
  padBlockBits_r_inj n r1 r2 hr1 hr2 p1 p2 (bb.toBits.symm.injective h)

/-- `padBlock` recovers the partial bits `P` (given the count `r`). -/
theorem padBlock_setWidth (bb : BlockBits F n) (r : ℕ) (hr : r < n) (p : BitVec r) :
    (bb.toBits (padBlock bb r p)).setWidth r = p := by
  unfold padBlock
  rw [Equiv.apply_symm_apply, padBlockBits_setWidth n r hr]

/-! ### The inferred block-cipher I/O, bit level (paper §3.4.1, p. 10)

Twin of Part 1's extraction at the bit fibers.  Given the reveal
`Z = (h̄, L, per-query full last keystream block)`, the paper's inference table reads every
block-cipher input/output off the transcript; the partial last block adds the
always-present `(ℓˢ+1)`-th call, whose *output* is read from the reveal — the paper's `Dˢ`
bookkeeping. -/

/-- The ciphertext of query `s`: response on `enc`, input on `dec` (twin of `cipher`). -/
def bitCipher (t : TranscriptPrefix HQB HMB q) (s : Fin q) : HMB :=
  match (t.1.get s).1 with
  | QueryDir.fwd => t.2.get s
  | QueryDir.inv => (t.1.get s).2.2

/-- The paper's structured hashed tail of an extracted message, at the message's own length
class: `N` and (if unaligned) `pad(M‖1)`. -/
def msgHashTail (bb : BlockBits F n) (m : HMB) : BitTailS F :=
  hashTailB bb (splitIdx m.1).1 (splitIdx m.1).2 m.2.2.1 m.2.2.2

/-- Hash-masked head block of an extracted message (`MM`/`UU` unified) — the bit `hashBlk`
twin over the padded tail. -/
def hashBlkB (bb : BlockBits F n) (Hf : HashFamily F T (L + 2))
    (z : F × F × (Fin q → F)) (tw : T) (m : HMB) : F :=
  m.2.1 + Hf.hash z.1 tw (msgHashTail bb m)

/-- `MMˢ = Mˢ + H_h̄(Tˢ, tail(Nˢ))` — the first inferred block-cipher input. -/
def MMvB (bb : BlockBits F n) (Hf : HashFamily F T (L + 2)) (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) : F :=
  hashBlkB bb Hf z (bitTweak t s) (bitPlain t s)

/-- `UUˢ = Uˢ + H_h̄(Tˢ, tail(Vˢ))` — the first inferred block-cipher output. -/
def UUvB (bb : BlockBits F n) (Hf : HashFamily F T (L + 2)) (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) : F :=
  hashBlkB bb Hf z (bitTweak t s) (bitCipher t s)

/-- `Sˢ = MMˢ + UUˢ + L` — the XCTR start block. -/
def SvB (bb : BlockBits F n) (Hf : HashFamily F T (L + 2)) (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) : F :=
  MMvB bb Hf z t s + UUvB bb Hf z t s + z.2.1

/-- `Sⱼˢ = Sˢ + bin(j)` — the `j`-th XCTR block-cipher input (`1 ≤ j ≤ ℓˢ+1`). -/
def SjvB (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))
    (z : F × F × (Fin q → F)) (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : ℕ) : F :=
  SvB bb Hf z t s + be.bin j

/-- Plaintext full-tail block `Nⱼˢ` as a total `ℕ → F` (`dite`-free; twin of `tailN`). -/
def bitTailN (t : TranscriptPrefix HQB HMB q) (s : Fin q) : ℕ → F := fun j =>
  (List.ofFn (bitPlain t s).2.2.1).getD j 0

/-- Ciphertext full-tail block `Vⱼˢ` as a total `ℕ → F` (twin of `tailV`). -/
def bitTailV (t : TranscriptPrefix HQB HMB q) (s : Fin q) : ℕ → F := fun j =>
  (List.ofFn (bitCipher t s).2.2.1).getD j 0

/-- `Yⱼˢ = Nⱼˢ + Vⱼˢ` — the `j`-th inferred XCTR output for a **full** block. -/
def YjvB (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : ℕ) : F :=
  bitTailN t s j + bitTailV t s j

section BitExtraction
-- Section variables must NOT be typed via the local notation (silent-failure trap);
-- spell the carrier out here.
variable (t : TranscriptPrefix (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))
    (Sigma (bitMsgL (F := F) (L := L) (n := n))) q) (s : Fin q)

theorem bitPlain_fwd (h : (t.1.get s).1 = QueryDir.fwd) :
    bitPlain t s = (t.1.get s).2.2 := by unfold bitPlain; rw [h]
theorem bitPlain_inv (h : (t.1.get s).1 = QueryDir.inv) :
    bitPlain t s = t.2.get s := by unfold bitPlain; rw [h]
theorem bitCipher_fwd (h : (t.1.get s).1 = QueryDir.fwd) :
    bitCipher t s = t.2.get s := by unfold bitCipher; rw [h]
theorem bitCipher_inv (h : (t.1.get s).1 = QueryDir.inv) :
    bitCipher t s = (t.1.get s).2.2 := by unfold bitCipher; rw [h]

/-- With a length-matched response, the plaintext lives in the query's length class. -/
theorem bitPlain_fst (hm : (t.2.get s).1 = (t.1.get s).2.2.1) :
    (bitPlain t s).1 = (t.1.get s).2.2.1 := by
  unfold bitPlain; rcases (t.1.get s).1 <;> first | rfl | exact hm

/-- With a length-matched response, the ciphertext lives in the query's length class. -/
theorem bitCipher_fst (hm : (t.2.get s).1 = (t.1.get s).2.2.1) :
    (bitCipher t s).1 = (t.1.get s).2.2.1 := by
  unfold bitCipher; rcases (t.1.get s).1 <;> first | rfl | exact hm

end BitExtraction

/-- `MMvB` respects `(tweak, plaintext)` sharing. -/
theorem MMvB_congr (bb : BlockBits F n) (Hf : HashFamily F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F)) {s s' : Fin q}
    (hT : bitTweak t s = bitTweak t s') (hP : bitPlain t s = bitPlain t s') :
    MMvB bb Hf z t s = MMvB bb Hf z t s' := by
  unfold MMvB; rw [hT, hP]

/-- `UUvB` respects `(tweak, ciphertext)` sharing. -/
theorem UUvB_congr (bb : BlockBits F n) (Hf : HashFamily F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F)) {s s' : Fin q}
    (hT : bitTweak t s = bitTweak t s') (hC : bitCipher t s = bitCipher t s') :
    UUvB bb Hf z t s = UUvB bb Hf z t s' := by
  unfold UUvB; rw [hT, hC]

/-! ### Inferred multisets `D`, `R` and the bad event, bit level (paper §3.4.1)

Per query `s` there are `mˢ = ℓˢ + 2` block-cipher indices: block `0` is the head
(`MM`/`UU`), blocks `1..ℓˢ` the full XCTR blocks, block `ℓˢ+1` the always-present partial
call.  `D`'s last entry is the inferred input `S_{ℓˢ+1}ˢ`; `R`'s last entry reads the
**reveal** (the revealed full last keystream block `z.2.2 s`), not the transcript. -/

/-- Index of the inferred multisets (twin of `DRIdx`, at `mˢ = ℓˢ + 2`). -/
abbrev DRIdxBit (t : TranscriptPrefix HQB HMB q) : Type :=
  Bool ⊕ (Σ s : Fin q, Fin (mBlocksBit t s))

/-- Entry of the inferred **input** multiset `D`: `bin(0)`, `bin(1)`, and per query `MMˢ`
(block 0) / `Sⱼˢ` (block `j ≥ 1`, including the last call). -/
def DfullB (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))
    (z : F × F × (Fin q → F)) (t : TranscriptPrefix HQB HMB q) :
    DRIdxBit (L := L) (n := n) t → F
  | Sum.inl false => be.bin 0
  | Sum.inl true => be.bin 1
  | Sum.inr ⟨s, j⟩ => if j.val = 0 then MMvB bb Hf z t s else SjvB bb be Hf z t s j.val

/-- Entry of the inferred **output** multiset `R`: `h̄`, `L`, and per query `UUˢ` (block 0)
/ `Yⱼˢ` (full block `1 ≤ j ≤ ℓˢ`) / the **revealed** full last keystream block (block
`ℓˢ+1`). -/
def RfullB (bb : BlockBits F n) (Hf : HashFamily F T (L + 2))
    (z : F × F × (Fin q → F)) (t : TranscriptPrefix HQB HMB q) :
    DRIdxBit (L := L) (n := n) t → F
  | Sum.inl false => z.1
  | Sum.inl true => z.2.1
  | Sum.inr ⟨s, j⟩ =>
      if j.val = 0 then UUvB bb Hf z t s
      else if j.val ≤ (splitIdx (bitPlain t s).1).1.val then YjvB t s (j.val - 1)
      else z.2.2 s

/-- **The bad event** (paper §3.4.1): an entry of `D` or of `R` has multiplicity > 1. -/
def bitBad (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))
    (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) : Prop :=
  (∃ a b : DRIdxBit (L := L) (n := n) tz.1, a ≠ b ∧
      DfullB bb be Hf tz.2 tz.1 a = DfullB bb be Hf tz.2 tz.1 b) ∨
  (∃ a b : DRIdxBit (L := L) (n := n) tz.1, a ≠ b ∧
      RfullB bb Hf tz.2 tz.1 a = RfullB bb Hf tz.2 tz.1 b)

/-- `mˢ = ℓˢ + 2 > 0`. -/
theorem mBlocksBit_pos (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    0 < mBlocksBit t s := Nat.succ_pos _

/-- Total inferred block count `σ_m = 2 + Σₛ mˢ` (twin of `sigmaM`, at `mˢ = ℓˢ + 2`). -/
def sigmaMBit (t : TranscriptPrefix HQB HMB q) : ℕ := 2 + ∑ s : Fin q, mBlocksBit t s

/-- The inferred multiset index has exactly `σ_m` entries. -/
theorem card_DRIdxBit (t : TranscriptPrefix HQB HMB q) :
    Fintype.card (DRIdxBit (L := L) (n := n) t) = sigmaMBit t := by
  simp only [DRIdxBit, sigmaMBit, Fintype.card_sum, Fintype.card_bool,
    Fintype.card_sigma, Fintype.card_fin]

/-- `σ_m` in `|F|`-exponent form: `σ_m = 2 + q + Σₛ (ℓˢ + 1)` — the ideal mass's
`N`-exponent (the ideal coins are `N^{2+q}` reveal dummies times `N^{1+ℓˢ}·2^{rˢ}` per
fiber, and the `2^{rˢ}` cancel against the hybrid point mass). -/
theorem sigmaMBit_eq (t : TranscriptPrefix HQB HMB q) :
    sigmaMBit t = 2 + q + ∑ s : Fin q, ((splitIdx (bitPlain t s).1).1.val + 1) := by
  have h : ∑ s : Fin q, mBlocksBit t s
      = (∑ s : Fin q, ((splitIdx (bitPlain t s).1).1.val + 1)) + ∑ _s : Fin q, 1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => rfl
  simp only [sigmaMBit, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  omega

section BitReductionPack

variable (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))
  (z : F × F × (Fin q → F))
  (t : TranscriptPrefix (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))
    (Sigma (bitMsgL (F := F) (L := L) (n := n))) q) (s : Fin q)

set_option maxHeartbeats 1000000 in
/-- Block-0 inferred input is `MMˢ`. -/
theorem DfullB_inr_zero (h : (0 : ℕ) < mBlocksBit t s) :
    DfullB bb be Hf z t (Sum.inr ⟨s, ⟨0, h⟩⟩) = MMvB bb Hf z t s := rfl

set_option maxHeartbeats 1000000 in
/-- Block-0 inferred output is `UUˢ`. -/
theorem RfullB_inr_zero (h : (0 : ℕ) < mBlocksBit t s) :
    RfullB bb Hf z t (Sum.inr ⟨s, ⟨0, h⟩⟩) = UUvB bb Hf z t s := rfl

set_option maxHeartbeats 1000000 in
/-- Block `i+1 ≥ 1` inferred input is the XCTR input `Sⱼˢ` (incl. the last call). -/
theorem DfullB_inr_succ (i : ℕ) (h : i + 1 < mBlocksBit t s) :
    DfullB bb be Hf z t (Sum.inr ⟨s, ⟨i + 1, h⟩⟩) = SjvB bb be Hf z t s (i + 1) := rfl

set_option maxHeartbeats 1000000 in
/-- Full block `1 ≤ i+1 ≤ ℓˢ` inferred output is the XCTR output `Yⱼˢ`. -/
theorem RfullB_inr_succ_of_le (i : ℕ) (h : i + 1 < mBlocksBit t s)
    (hle : i + 1 ≤ (splitIdx (bitPlain t s).1).1.val) :
    RfullB bb Hf z t (Sum.inr ⟨s, ⟨i + 1, h⟩⟩) = YjvB t s i := by
  have h0 : i + 1 ≠ 0 := Nat.succ_ne_zero i
  simp only [RfullB]
  rw [if_neg h0, if_pos hle, Nat.add_sub_cancel]

set_option maxHeartbeats 1000000 in
/-- The last block `ℓˢ+1` inferred output is the **revealed** full last keystream block. -/
theorem RfullB_inr_last (h : (splitIdx (bitPlain t s).1).1.val + 1 < mBlocksBit t s) :
    RfullB bb Hf z t (Sum.inr ⟨s, ⟨(splitIdx (bitPlain t s).1).1.val + 1, h⟩⟩)
      = z.2.2 s := by
  simp only [RfullB]
  rw [if_neg (Nat.succ_ne_zero _), if_neg (by omega)]

end BitReductionPack

/-! ### The representative extension (reveal `(h̄, L, last blocks)` after all queries)

The extended σ⁺ H-technique compares distributions over `(transcript, reveal)` with
`Z = F × F × (Fin q → F)`: the real world reveals `(π(bin 0), π(bin 1))` and per query the
full last keystream block `π(Sˢ + bin(ℓˢ+1))` (⊇ the paper's leftover `Dˢ`); the ideal
world samples a uniform dummy triple alongside the `±rnd` coins and reveals it through the
transcript-indexed **hybrid** map below. -/

/-- Real sampler: a uniform permutation of `F` (twin of `realP`). -/
abbrev bitRealP : Dist.ProbDist (Equiv.Perm F) :=
  ⟨Dist.uniform (Equiv.Perm F), Dist.uniform_isProbDist⟩

/-- Real sampled system: bit-level HCTR2 driven by `π` (twin of `realF`). -/
abbrev bitRealF (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2)) :
    PFunPDS.RV (Equiv.Perm F) HQB HMB :=
  functionEvaluatorRV (fun π => hctr2BitFun bb be Hf π)

/-- Real reveal: `h̄ = π(bin 0)`, `L = π(bin 1)`, and per query the full last keystream
block `π(Sˢ + bin(ℓˢ+1))`, inferred from the sample `π` and the transcript exactly as the
collision analysis reads it (`UUˢ` is `π(MMˢ)` here, not the transcript's ciphertext —
they agree exactly on the transcripts `π` realizes). -/
def bitRealAug (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2)) :
    Equiv.Perm F → TranscriptPrefix HQB HMB q → (F × F × (Fin q → F)) :=
  fun π t =>
    (π (be.bin 0), π (be.bin 1), fun s =>
      let mm := (bitPlain t s).2.1
        + Hf.hash (π (be.bin 0)) (bitTweak t s) (msgHashTail bb (bitPlain t s))
      π (mm + π mm + π (be.bin 1) + be.bin ((splitIdx (bitPlain t s).1).1.val + 1)))

/-- Ideal sampler: a uniform dummy reveal triple alongside the `±rnd` coins (twin of
`idealP`; the product structure is what factors the extended law). -/
abbrev bitIdealP : Dist.ProbDist ((F × F × (Fin q → F)) ×
    (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) :=
  Dist.prodProbDist
    ⟨Dist.uniform (F × F × (Fin q → F)), Dist.uniform_isProbDist⟩
    ⟨Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1),
      Dist.uniform_isProbDist⟩

/-- Ideal sampled system: `±rnd` over the bit fibers, the dummy ignored (twin of
`idealF`). -/
abbrev bitIdealF :
    PFunPDS.RV ((F × F × (Fin q → F)) ×
      (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) HQB HMB :=
  functionEvaluatorRV (fun p => TweakablePRP.rndFun p.2)

/-! ### The hybrid ideal reveal (the paper's `Dˢ` bookkeeping, §3.4)

The real reveal's third component is *partially transcript-determined*: its low `rˢ` bits
always equal `npˢ ⊕ vpˢ`, so on good but reveal-inconsistent `(t, z)` the real extended
mass is `0` while a naive dummy reveal would spread positive ideal mass there — the
unconditional σ⁺ ratio is FALSE for the dummy design.  The fix: keep the sampler, read the
dummy through the transcript-indexed hybrid `Φ_t` — low `rˢ` bits computed from the
transcript, high bits from the dummy.  On length-consistent transcripts the image of `Φ_t`
is exactly the consistent slice (the ideal mass now vanishes where the real one does), and
`Φ_t` is `2^{Σrˢ}`-to-1, so the hybrid point mass `≤ 2^{Σrˢ}/N^{2+q}` exactly cancels the
`2^{−Σrˢ}` of the per-fiber URF coins, closing the ratio at `N^{−σ_m}`.

The low/high split is pure XOR algebra — `lowFill r v` zeroes the bits `≥ r`, and
`hybridBits r a k = k ⊕ lowFill r k ⊕ a↑` replaces the low `r` bits of `k` by `a` — so no
bit-indexing is ever needed. -/

/-- Zero the bits `≥ r` of `v` (truncate, then zero-extend back). -/
def lowFill (r : ℕ) (v : BitVec n) : BitVec n := (v.setWidth r).setWidth n

/-- `lowFill` is the identity on values below `2^r`. -/
private theorem lowFill_eq_self_of_lt {r : ℕ} (x : BitVec n) (hx : x.toNat < 2 ^ r) :
    lowFill (n := n) r x = x := by
  apply BitVec.toNat_inj.mp
  unfold lowFill
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt x.isLt]

private theorem bitvec_xor_cancel_right {w : ℕ} {x y c : BitVec w}
    (h : x ^^^ c = y ^^^ c) : x = y := by
  have h2 : x ^^^ c ^^^ c = y ^^^ c ^^^ c := by rw [h]
  rwa [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero] at h2

/-- **Hybrid block**: replace the low `r` bits of `k` by `a`, keep the high bits of `k`. -/
def hybridBits (r : ℕ) (a : BitVec r) (k : BitVec n) : BitVec n :=
  k ^^^ lowFill r k ^^^ a.setWidth n

/-- The low `r` bits of a hybrid are the prescribed `a` (`r ≤ n`). -/
theorem setWidth_hybridBits {r : ℕ} (h : r ≤ n) (a : BitVec r) (k : BitVec n) :
    (hybridBits (n := n) r a k).setWidth r = a := by
  unfold hybridBits lowFill
  rw [BitVec.setWidth_xor, BitVec.setWidth_xor, setWidth_setWidth_of_le h,
    setWidth_setWidth_of_le h, BitVec.xor_self, BitVec.zero_xor]

/-- Hybrids with the same low part and equal values have equal high sources, given equal
recorded low bits of the sources. -/
theorem hybridBits_high_inj {r : ℕ} (a : BitVec r) {k k' : BitVec n}
    (hh : hybridBits (n := n) r a k = hybridBits (n := n) r a k')
    (hl : k.setWidth r = k'.setWidth r) : k = k' := by
  unfold hybridBits lowFill at hh
  rw [hl] at hh
  exact bitvec_xor_cancel_right (bitvec_xor_cancel_right hh)

/-- Transcript-determined low bits of query `s`'s last keystream block: `npˢ ⊕ vpˢ`, read
off at the *query's* leftover width `rˢ` (well-defined on every transcript; equals the
partial-block XOR on length-consistent ones). -/
def bitLowBits (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    BitVec (splitIdx (t.1.get s).2.2.1).2.val :=
  ((bitPlain t s).2.2.2.setWidth n ^^^ (bitCipher t s).2.2.2.setWidth n).setWidth
    (splitIdx (t.1.get s).2.2.1).2.val

/-- **Hybrid last keystream block** of query `s`: transcript low bits, dummy high bits. -/
def bitHybridBlock (bb : BlockBits F n) (t : TranscriptPrefix HQB HMB q) (s : Fin q)
    (w : F) : F :=
  bb.toBits.symm (hybridBits (splitIdx (t.1.get s).2.2.1).2.val
    (bitLowBits t s) (bb.toBits w))

/-- **The hybrid reveal map** `Φ_t : Z → Z`: keep `(h̄, L)`, hybridize each last block. -/
def bitHybrid (bb : BlockBits F n) (t : TranscriptPrefix HQB HMB q)
    (d : F × F × (Fin q → F)) : F × F × (Fin q → F) :=
  (d.1, d.2.1, fun s => bitHybridBlock bb t s (d.2.2 s))

/-- **Ideal reveal — the hybrid** (twin of `idealAug` through `Φ_t`): read the dummy
triple through the transcript-indexed hybridization.  Load-bearing: a naive dummy reveal
(`fun p _ => p.1`) is PROVABLY wrong here (see the section header). -/
def bitIdealAugH (bb : BlockBits F n) : ((F × F × (Fin q → F)) ×
      (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) →
    TranscriptPrefix HQB HMB q → (F × F × (Fin q → F)) :=
  fun p t => bitHybrid bb t p.1

/-- Real representative marginal = `hctr2BitReal` (definitional; twin of `pmf_real_eq`). -/
theorem pmf_bitReal_eq (bb : BlockBits F n) (be : BinEnc F L)
    (Hf : HashFamily F T (L + 2)) :
    (Dist.PMF (bitRealP (F := F)) (bitRealF bb be Hf) : ProbPDS HQB HMB)
      = hctr2BitReal bb be Hf := rfl

/-- Ideal representative marginal = `±rnd` over the bit fibers: the dummy triple sums out
(twin of `pmf_ideal_eq`). -/
theorem pmf_bitIdeal_eq :
    (Dist.PMF (bitIdealP (F := F) (T := T) (L := L) (n := n) (q := q))
        (bitIdealF (F := F) (T := T) (L := L) (n := n) (q := q)) : ProbPDS HQB HMB)
      = TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T) := by
  refine Subtype.ext ?_
  show Dist.fTransform (bitIdealF (F := F) (T := T) (L := L) (n := n) (q := q))
      (bitIdealP (F := F) (T := T) (L := L) (n := n) (q := q)).val =
    Dist.fTransform (functionEvaluatorRV (fun g => TweakablePRP.rndFun g)) _
  rw [show (bitIdealF (F := F) (T := T) (L := L) (n := n) (q := q)) =
      (functionEvaluatorRV (fun g => TweakablePRP.rndFun g)) ∘ Prod.snd from rfl,
    ← Dist.fTransform_comp]
  congr 1
  refine Finsupp.ext fun g => ?_
  rw [Dist.fTransform_apply_eq_mass]
  refine ((mass_prod_snd_pred (Dist.uniform (F × F × (Fin q → F))) _
    (fun g' => g' = g)).trans ?_)
  rw [show (Dist.uniform (F × F × (Fin q → F))).weight = 1 from
      Dist.uniform_isProbDist.weight_eq,
    one_mul, Dist.mass_eq_sum]
  refine (Finset.sum_eq_single g (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ g) h)).trans (if_pos rfl)

/-! ### The good ratio, bit level (paper §3.4.1, ε = 0)

On a good (collision-free) extended transcript the hybrid ideal σ⁺ is at most `N^{−σ_m}`
(dummy point mass `2^{Σrˢ}/N^{2+q}` × URF coins `∏ₛ (N^{1+ℓˢ}·2^{rˢ})⁻¹`, the `2^{Σrˢ}`
cancelling) and the real σ⁺ is at least `N^{−σ_m}` (a uniform permutation consistent with
`σ_m` distinct inferred pairs). -/

section BitGoodRatio

variable (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))

/-- **Distinct queries on good transcripts** (twin of `query_inj`): a repeat forces an
`MMˢ` (fwd) or `UUˢ` (inv) block-0 collision. -/
theorem bit_query_inj (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (h_good : ¬ bitBad bb be Hf tz) : Function.Injective tz.1.1.get := by
  intro s s' hss
  by_contra hne
  have hidx : (Sum.inr ⟨s, ⟨0, mBlocksBit_pos tz.1 s⟩⟩ :
        DRIdxBit (L := L) (n := n) tz.1)
      ≠ Sum.inr ⟨s', ⟨0, mBlocksBit_pos tz.1 s'⟩⟩ := by
    simp only [ne_eq, Sum.inr.injEq, Sigma.mk.injEq, not_and]
    exact fun h => absurd h hne
  have hT : bitTweak tz.1 s = bitTweak tz.1 s' := by unfold bitTweak; rw [hss]
  refine h_good ?_
  rcases hd : (tz.1.1.get s).1 with _ | _
  · have hd' : (tz.1.1.get s').1 = QueryDir.fwd := by rw [← hss]; exact hd
    refine Or.inl ⟨_, _, hidx, ?_⟩
    rw [DfullB_inr_zero bb be Hf tz.2 tz.1 s (mBlocksBit_pos tz.1 s),
      DfullB_inr_zero bb be Hf tz.2 tz.1 s' (mBlocksBit_pos tz.1 s')]
    exact MMvB_congr bb Hf tz.1 tz.2 hT (by
      rw [bitPlain_fwd tz.1 s hd, bitPlain_fwd tz.1 s' hd', hss])
  · have hd' : (tz.1.1.get s').1 = QueryDir.inv := by rw [← hss]; exact hd
    refine Or.inr ⟨_, _, hidx, ?_⟩
    rw [RfullB_inr_zero bb Hf tz.2 tz.1 s (mBlocksBit_pos tz.1 s),
      RfullB_inr_zero bb Hf tz.2 tz.1 s' (mBlocksBit_pos tz.1 s')]
    exact UUvB_congr bb Hf tz.1 tz.2 hT (by
      rw [bitCipher_inv tz.1 s hd, bitCipher_inv tz.1 s' hd', hss])

/-- **Hybrid reveal-factoring** (twin of `extSysFactor_ideal_eq` through `Φ_t`): the ideal
extended factor splits as (hybridized dummy hits `tz.2`) × (URF realizes the transcript) —
the URF factor is reveal-independent, which is what collapses the bad bound to
per-transcript reveal bounds. -/
theorem bitExtSysFactorH_eq (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) :
    extSysFactorRep bitIdealP bitIdealF (bitIdealAugH bb) tz =
      (Dist.uniform (F × F × (Fin q → F))).mass (fun d => bitHybrid bb tz.1 d = tz.2) *
        (Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)).mass
          (fun g => ∀ i, TweakablePRP.rndFun g (tz.1.1.get i) = tz.1.2.get i) := by
  have hpred : (fun p : (F × F × (Fin q → F)) ×
        (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) =>
      PFunPDE.transcriptSystemEvent bitIdealF tz.1.1 tz.1.2 p ∧
        bitIdealAugH bb p tz.1 = tz.2)
      = (fun p => (fun d => bitHybrid bb tz.1 d = tz.2) p.1 ∧
          (fun g => ∀ i, TweakablePRP.rndFun g (tz.1.1.get i) = tz.1.2.get i) p.2) := by
    funext p
    simp only [eq_iff_iff]
    rw [transcriptSystemEvent_functionEvaluatorRV_iff]
    exact and_comm
  unfold extSysFactorRep
  rw [hpred, show (bitIdealP (F := F) (T := T) (L := L) (n := n) (q := q)).val
    = Dist.prod (Dist.uniform (F × F × (Fin q → F))) (Dist.uniform
        (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) from rfl]
  exact Dist.mass_prod_and _ _ (fun d => bitHybrid bb tz.1 d = tz.2)
    (fun g => ∀ i, TweakablePRP.rndFun g (tz.1.1.get i) = tz.1.2.get i)

/-- **Ideal σ⁺ vanishes off length-support** (twin of `ideal_zero`; the augmentation is
irrelevant — the URF event already fails). -/
theorem bitIdeal_zero (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (s : Fin q) (hne : (tz.1.2.get s).1 ≠ (tz.1.1.get s).2.2.1) :
    extSysFactorRep bitIdealP bitIdealF (bitIdealAugH bb) tz = 0 := by
  classical
  have hfalse : ∀ p, ¬ (PFunPDE.transcriptSystemEvent bitIdealF tz.1.1 tz.1.2 p ∧
      bitIdealAugH bb p tz.1 = tz.2) := by
    rintro p ⟨hev, -⟩
    rw [transcriptSystemEvent_functionEvaluatorRV_iff] at hev
    exact hne (by simpa [TweakablePRP.rndFun] using (congrArg Sigma.fst (hev s)).symm)
  unfold extSysFactorRep
  rw [Dist.mass_congr _ (fun p => iff_of_false (hfalse p) not_false), Dist.mass_eq_sum]
  simp

/-- **Reveal-consistency of an extended transcript**: per query, the revealed full last
keystream block truncates (on the used `rˢ` bits) to `npˢ ⊕ vpˢ` — stated at width `n`
(zero-extended) to avoid dependent-length transport.  Always true in the real world; the
hybrid makes it true by construction in the ideal world. -/
def bitRevealConsistent (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) : Prop :=
  ∀ s : Fin q,
    ((bb.toBits (tz.2.2.2 s)).setWidth (splitIdx (tz.1.1.get s).2.2.1).2.val).setWidth n
      = (bitPlain tz.1 s).2.2.2.setWidth n ^^^ (bitCipher tz.1 s).2.2.2.setWidth n

/-- On length-consistent transcripts the hybrid reveal is **always** reveal-consistent:
the low `rˢ` bits are `npˢ ⊕ vpˢ` by construction. -/
theorem bitHybrid_revealConsistent (t : TranscriptPrefix HQB HMB q)
    (hlen : ∀ s : Fin q, (t.2.get s).1 = (t.1.get s).2.2.1)
    (d : F × F × (Fin q → F)) :
    bitRevealConsistent bb (t, bitHybrid bb t d) := by
  intro s
  show ((bb.toBits ((bitHybrid bb t d).2.2 s)).setWidth
      (splitIdx (t.1.get s).2.2.1).2.val).setWidth n = _
  have hrw : bb.toBits ((bitHybrid bb t d).2.2 s)
      = hybridBits (splitIdx (t.1.get s).2.2.1).2.val (bitLowBits t s)
          (bb.toBits (d.2.2 s)) := by
    show bb.toBits (bb.toBits.symm _) = _
    rw [Equiv.apply_symm_apply]
  rw [hrw, setWidth_hybridBits (splitIdx (t.1.get s).2.2.1).2.isLt.le]
  -- goal: `lowFill r (npˢ↑ ⊕ vpˢ↑) = npˢ↑ ⊕ vpˢ↑`
  show lowFill (splitIdx (t.1.get s).2.2.1).2.val
      ((bitPlain t s).2.2.2.setWidth n ^^^ (bitCipher t s).2.2.2.setWidth n) = _
  refine lowFill_eq_self_of_lt _ ?_
  have hp : (bitPlain t s).2.2.2.toNat < 2 ^ (splitIdx (t.1.get s).2.2.1).2.val :=
    lt_of_lt_of_le (bitPlain t s).2.2.2.isLt (le_of_eq (congrArg (2 ^ ·)
      (congrArg (fun k : Fin (L * n) => (splitIdx k).2.val)
        (bitPlain_fst t s (hlen s)))))
  have hc : (bitCipher t s).2.2.2.toNat < 2 ^ (splitIdx (t.1.get s).2.2.1).2.val :=
    lt_of_lt_of_le (bitCipher t s).2.2.2.isLt (le_of_eq (congrArg (2 ^ ·)
      (congrArg (fun k : Fin (L * n) => (splitIdx k).2.val)
        (bitCipher_fst t s (hlen s)))))
  rw [BitVec.toNat_xor,
    BitVec.toNat_setWidth_of_le (splitIdx (bitPlain t s).1).2.isLt.le,
    BitVec.toNat_setWidth_of_le (splitIdx (bitCipher t s).1).2.isLt.le]
  exact Nat.xor_lt_two_pow hp hc

/-- **Ideal σ⁺ vanishes on reveal-inconsistent extended transcripts** (the hybrid's
raison d'être): the hybrid image is contained in the consistent slice, where the real
mass also lives. -/
theorem bitIdeal_zero_of_inconsistent
    (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (hlen : ∀ s : Fin q, (tz.1.2.get s).1 = (tz.1.1.get s).2.2.1)
    (hcons : ¬ bitRevealConsistent bb tz) :
    extSysFactorRep bitIdealP bitIdealF (bitIdealAugH bb) tz = 0 := by
  rw [bitExtSysFactorH_eq]
  rw [mass_eq_zero_of_forall _ (fun d hd => (hcons (by
      have h := bitHybrid_revealConsistent bb tz.1 hlen d
      rw [hd] at h
      exact h)).elim), zero_mul]

/-- **Hybrid point mass** `≤ 2^{Σrˢ}/N^{2+q}`: each `Φ_t`-fiber injects into the recorded
per-query dummy low bits (`2^{Σrˢ}` many). -/
theorem bitHybrid_pt_mass_le (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F)) :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun d => bitHybrid bb t d = z)
      ≤ (2 ^ ∑ s : Fin q, (splitIdx (t.1.get s).2.2.1).2.val : ℝ) /
          ((Fintype.card F : ℝ) ^ (2 + q)) := by
  classical
  rw [Dist.uniform_mass_eq_card_filter]
  have hZ : ((Fintype.card (F × F × (Fin q → F)) : ℕ) : ℝ)
      = (Fintype.card F : ℝ) ^ (2 + q) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hZ]
  gcongr
  -- numerator: inject each fiber into the recorded per-query dummy low bits
  have hinj : (Finset.univ.filter (fun d : F × F × (Fin q → F) =>
        bitHybrid bb t d = z)).card
      ≤ Fintype.card (∀ s : Fin q, BitVec (splitIdx (t.1.get s).2.2.1).2.val) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun d => fun s => (bb.toBits (d.2.2 s)).setWidth
        (splitIdx (t.1.get s).2.2.1).2.val)
      (fun _ _ => Finset.mem_univ _) ?_
    intro d hd d' hd' hrec
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      at hd hd'
    have hzz := hd.trans hd'.symm
    simp only [bitHybrid, Prod.mk.injEq] at hzz
    obtain ⟨h1, h2, h3⟩ := hzz
    refine Prod.ext h1 (Prod.ext h2 (funext fun s => ?_))
    have h4 : hybridBits (splitIdx (t.1.get s).2.2.1).2.val (bitLowBits t s)
          (bb.toBits (d.2.2 s))
        = hybridBits (splitIdx (t.1.get s).2.2.1).2.val (bitLowBits t s)
          (bb.toBits (d'.2.2 s)) :=
      bb.toBits.symm.injective (congrFun h3 s)
    exact bb.toBits.injective (hybridBits_high_inj _ h4 (congrFun hrec s))
  refine le_trans (Nat.cast_le.mpr hinj) (le_of_eq ?_)
  rw [Fintype.card_pi,
    Finset.prod_congr rfl (fun s _ => card_bitVec ((splitIdx (t.1.get s).2.2.1).2.val))]
  push_cast
  rw [Finset.prod_pow_eq_pow_sum]

/-- **Ideal σ⁺ upper bound** (paper §3.4.1 with the `Dˢ` truncation factor cancelled; twin
of `ideal_le` at the hybrid reveal): on a good, length-consistent extended transcript the
ideal extended factor is at most `N^{−σ_m}` — the point-mass `2^{Σrˢ}` exactly absorbs the
fiber-cardinality `2^{−Σrˢ}` of the URF coins over the distinct queries. -/
theorem bitIdeal_le (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (h_good : ¬ bitBad bb be Hf tz)
    (hlen : ∀ s : Fin q, (tz.1.2.get s).1 = (tz.1.1.get s).2.2.1) :
    extSysFactorRep bitIdealP bitIdealF (bitIdealAugH bb) tz ≤
      ((Fintype.card F : ℝ) ^ sigmaMBit tz.1)⁻¹ := by
  classical
  have hinj := bit_query_inj bb be Hf tz h_good
  rw [bitExtSysFactorH_eq]
  refine le_trans (mul_le_mul (bitHybrid_pt_mass_le bb tz.1 tz.2)
    (TweakablePRP.rnd_output_le tz.1.1.get tz.1.2.get)
    (Dist.uniform_nonNeg.mass_nonneg _) (by positivity)) ?_
  rw [Finset.prod_image (fun a _ b _ h => hinj h)]
  have hprod : ∀ s : Fin q,
      (Fintype.card (bitMsgL (F := F) (L := L) (n := n)
          (tz.1.1.get s).2.2.1) : ℝ)⁻¹
        = ((Fintype.card F : ℝ) ^ ((splitIdx (tz.1.1.get s).2.2.1).1.val + 1)
            * 2 ^ (splitIdx (tz.1.1.get s).2.2.1).2.val)⁻¹ := by
    intro s
    rw [bitMsgL_card]
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun s _ => hprod s), Finset.prod_inv_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have hσ : sigmaMBit tz.1
      = (2 + q) + ∑ s : Fin q, ((splitIdx (tz.1.1.get s).2.2.1).1.val + 1) := by
    have hsum : ∑ s : Fin q, ((splitIdx (bitPlain tz.1 s).1).1.val + 1)
        = ∑ s : Fin q, ((splitIdx (tz.1.1.get s).2.2.1).1.val + 1) :=
      Finset.sum_congr rfl fun s _ => by rw [bitPlain_fst tz.1 s (hlen s)]
    rw [sigmaMBit_eq, hsum]
  refine le_of_eq ?_
  set A := ∑ s : Fin q, (splitIdx (tz.1.1.get s).2.2.1).2.val with hA
  set B := ∑ s : Fin q, ((splitIdx (tz.1.1.get s).2.2.1).1.val + 1) with hB
  have h2 : ((2 : ℝ) ^ A) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hstep : (2 : ℝ) ^ A / (Fintype.card F : ℝ) ^ (2 + q)
        * ((Fintype.card F : ℝ) ^ B * 2 ^ A)⁻¹
      = ((Fintype.card F : ℝ) ^ (2 + q))⁻¹
        * ((Fintype.card F : ℝ) ^ B)⁻¹ * ((2 : ℝ) ^ A / 2 ^ A) := by
    rw [mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hstep, div_self h2, mul_one, ← mul_inv, ← pow_add, hσ]

/-- **Per-query reconstruction, forward** (clean `bitEncCore` level; twin of
`enc_reconstruct` plus the partial-block equation): if `π` maps the inferred head block
correctly (`hMM`), every full XCTR block correctly (`hS`), the last call to the revealed
block `w` (`hw`), and the transcript's partial block is consistent with `w` (`hvp`), the
encryption core outputs exactly `(U, V, vp)`. -/
theorem bitEnc_reconstruct (π : Equiv.Perm F) (τ : T) (ℓ : Fin L) (r : Fin n)
    (M : F) (N : Fin ℓ.val → F) (np : BitVec r.val)
    (U : F) (V : Fin ℓ.val → F) (vp : BitVec r.val) (w : F)
    (hMM : π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
        = U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
    (hS : ∀ j : Fin ℓ.val,
      π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
          + (U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
          + π (be.bin 1) + be.bin (j.val + 1)) = N j + V j)
    (hw : π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
          + (U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
          + π (be.bin 1) + be.bin (ℓ.val + 1)) = w)
    (hvp : vp = np ^^^ (bb.toBits w).setWidth r.val) :
    bitEncCore bb be Hf π τ ℓ r (M, N, np) = (U, V, vp) := by
  have hV : (fun i : Fin ℓ.val =>
      N i + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
        + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
        + π (be.bin 1) + be.bin (i.val + 1))) = V := by
    funext i
    rw [hMM, hS i]
    char2
  have hLast : π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
      + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
      + π (be.bin 1) + be.bin (ℓ.val + 1)) = w := by
    rw [hMM]; exact hw
  simp only [bitEncCore]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
        + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r _ _) = U
    rw [hV, hLast, ← hvp, hMM]
    char2
  · show (fun i : Fin ℓ.val =>
        N i + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
          + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
          + π (be.bin 1) + be.bin (i.val + 1))) = V
    exact hV
  · show np ^^^ (bb.toBits (π (M + Hf.hash (π (be.bin 0)) τ
        (hashTailB bb ℓ r N np)
        + π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
        + π (be.bin 1) + be.bin (ℓ.val + 1)))).setWidth r.val = vp
    rw [hLast, ← hvp]

/-- **Per-query reconstruction, inverse** (via correctness). -/
theorem bitDec_reconstruct (π : Equiv.Perm F) (τ : T) (ℓ : Fin L) (r : Fin n)
    (M : F) (N : Fin ℓ.val → F) (np : BitVec r.val)
    (U : F) (V : Fin ℓ.val → F) (vp : BitVec r.val) (w : F)
    (hMM : π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np))
        = U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
    (hS : ∀ j : Fin ℓ.val,
      π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
          + (U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
          + π (be.bin 1) + be.bin (j.val + 1)) = N j + V j)
    (hw : π (M + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r N np)
          + (U + Hf.hash (π (be.bin 0)) τ (hashTailB bb ℓ r V vp))
          + π (be.bin 1) + be.bin (ℓ.val + 1)) = w)
    (hvp : vp = np ^^^ (bb.toBits w).setWidth r.val) :
    bitDecCore bb be Hf π τ ℓ r (U, V, vp) = (M, N, np) := by
  rw [← bitEnc_reconstruct bb be Hf π τ ℓ r M N np U V vp w hMM hS hw hvp,
    bitDecCore_bitEncCore]

/-- **Inference lemma, reconstruction direction** (twin of `reconstruct`): if the reveal
holds, the head block, all full XCTR blocks, and the last call map correctly under `π`,
and the reveal is consistent with the transcript's partial block, then `π` realizes query
`s`. -/
theorem bit_reconstruct (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F))
    (π : Equiv.Perm F) (s : Fin q)
    (hlen : (t.2.get s).1 = (t.1.get s).2.2.1)
    (hr1 : π (be.bin 0) = z.1) (hr2 : π (be.bin 1) = z.2.1)
    (hMM : π (MMvB bb Hf z t s) = UUvB bb Hf z t s)
    (hS : ∀ i : ℕ, i < (splitIdx (bitPlain t s).1).1.val →
        π (SjvB bb be Hf z t s (i + 1)) = YjvB t s i)
    (hw : π (SjvB bb be Hf z t s ((splitIdx (bitPlain t s).1).1.val + 1)) = z.2.2 s)
    (hcons : ((bb.toBits (z.2.2 s)).setWidth
          (splitIdx (t.1.get s).2.2.1).2.val).setWidth n
        = (bitPlain t s).2.2.2.setWidth n ^^^ (bitCipher t s).2.2.2.setWidth n) :
    hctr2BitFun bb be Hf π (t.1.get s) = t.2.get s := by
  simp only [hctr2BitFun, MMvB, UUvB, SjvB, SvB, YjvB, bitTailN, bitTailV,
    bitPlain, bitCipher, bitTweak, hashBlkB, msgHashTail] at hMM hS hw hcons ⊢
  revert hlen hMM hS hw hcons
  obtain ⟨dir, τ, k, M, N, np⟩ := t.1.get s
  obtain ⟨ρ, U, V, vp⟩ := t.2.get s
  intro hlen hMM hS hw hcons
  cases dir
  · -- fwd: query = plaintext (M, N, np), response = ciphertext (U, V, vp)
    dsimp only at hlen hMM hS hw hcons ⊢
    have hlen' : k = ρ := hlen.symm
    subst hlen'
    refine Sigma.ext rfl (heq_of_eq ?_)
    have hrle : (splitIdx k).2.val ≤ n := (splitIdx k).2.isLt.le
    have hx : (bb.toBits (z.2.2 s)).setWidth (splitIdx k).2.val = np ^^^ vp :=
      setWidth_injective hrle
        (hcons.trans (setWidth_xor_of_le hrle np vp).symm)
    have hvp : vp = np ^^^ (bb.toBits (z.2.2 s)).setWidth (splitIdx k).2.val := by
      rw [hx, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [← hr1] at hMM
    refine bitEnc_reconstruct bb be Hf π τ (splitIdx k).1 (splitIdx k).2
      M N np U V vp (z.2.2 s) hMM (fun j => ?_) ?_ hvp
    · have h := hS j.val j.isLt
      rw [← hr1, ← hr2] at h
      simpa using h
    · have h := hw
      rw [← hr1, ← hr2] at h
      exact h
  · -- inv: query = ciphertext (M, N, np), response = plaintext (U, V, vp)
    dsimp only at hlen hMM hS hw hcons ⊢
    have hlen' : k = ρ := hlen.symm
    subst hlen'
    refine Sigma.ext rfl (heq_of_eq ?_)
    have hrle : (splitIdx k).2.val ≤ n := (splitIdx k).2.isLt.le
    have hx : (bb.toBits (z.2.2 s)).setWidth (splitIdx k).2.val = vp ^^^ np :=
      setWidth_injective hrle
        (hcons.trans (setWidth_xor_of_le hrle vp np).symm)
    have hvp : np = vp ^^^ (bb.toBits (z.2.2 s)).setWidth (splitIdx k).2.val := by
      rw [hx, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [← hr1] at hMM
    refine bitDec_reconstruct bb be Hf π τ (splitIdx k).1 (splitIdx k).2
      U V vp M N np (z.2.2 s) hMM (fun j => ?_) ?_ hvp
    · have h := hS j.val j.isLt
      rw [← hr1, ← hr2] at h
      simpa using h
    · have h := hw
      rw [← hr1, ← hr2] at h
      exact h

/-- **Real σ⁺ lower bound** (paper §3.4.1; twin of `real_ge`): on a good,
length-consistent, reveal-consistent extended transcript the real extended factor is at
least `N^{−σ_m}` — `¬Bad` makes `DfullB`/`RfullB` injective, the reconstruction turns the
point constraints into "π realizes transcript + reveal", and the perm-consistency engine
counts the completions. -/
theorem bitReal_ge (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (h_good : ¬ bitBad bb be Hf tz)
    (hlen : ∀ s : Fin q, (tz.1.2.get s).1 = (tz.1.1.get s).2.2.1)
    (hcons : bitRevealConsistent bb tz) :
    ((Fintype.card F : ℝ) ^ sigmaMBit tz.1)⁻¹ ≤
      extSysFactorRep bitRealP (bitRealF bb be Hf) (bitRealAug bb be Hf) tz := by
  classical
  have hDinj : Function.Injective (DfullB bb be Hf tz.2 tz.1) := fun a b hab => by
    by_contra hne; exact h_good (Or.inl ⟨a, b, hne, hab⟩)
  have hRinj : Function.Injective (RfullB bb Hf tz.2 tz.1) := fun a b hab => by
    by_contra hne; exact h_good (Or.inr ⟨a, b, hne, hab⟩)
  have himpl : ∀ π : Equiv.Perm F,
      (∀ k, π (DfullB bb be Hf tz.2 tz.1 k) = RfullB bb Hf tz.2 tz.1 k) →
      (PFunPDE.transcriptSystemEvent (bitRealF bb be Hf) tz.1.1 tz.1.2 π ∧
        bitRealAug bb be Hf π tz.1 = tz.2) := by
    intro π hconsπ
    have hr1 : π (be.bin 0) = tz.2.1 := hconsπ (Sum.inl false)
    have hr2 : π (be.bin 1) = tz.2.2.1 := hconsπ (Sum.inl true)
    have hMM : ∀ s, π (MMvB bb Hf tz.2 tz.1 s) = UUvB bb Hf tz.2 tz.1 s := fun s => by
      have h := hconsπ (Sum.inr ⟨s, ⟨0, mBlocksBit_pos tz.1 s⟩⟩)
      rwa [DfullB_inr_zero, RfullB_inr_zero] at h
    have hSS : ∀ s (i : ℕ), i < (splitIdx (bitPlain tz.1 s).1).1.val →
        π (SjvB bb be Hf tz.2 tz.1 s (i + 1)) = YjvB tz.1 s i := fun s i hi => by
      have hik : i + 1 < mBlocksBit tz.1 s := by unfold mBlocksBit; omega
      have h := hconsπ (Sum.inr ⟨s, ⟨i + 1, hik⟩⟩)
      rwa [DfullB_inr_succ, RfullB_inr_succ_of_le bb Hf tz.2 tz.1 s i hik hi] at h
    have hW : ∀ s, π (SjvB bb be Hf tz.2 tz.1 s
          ((splitIdx (bitPlain tz.1 s).1).1.val + 1)) = tz.2.2.2 s := fun s => by
      have hik : (splitIdx (bitPlain tz.1 s).1).1.val + 1 < mBlocksBit tz.1 s := by
        unfold mBlocksBit; omega
      have h := hconsπ (Sum.inr ⟨s, ⟨(splitIdx (bitPlain tz.1 s).1).1.val + 1, hik⟩⟩)
      rwa [DfullB_inr_succ, RfullB_inr_last] at h
    refine ⟨(transcriptSystemEvent_functionEvaluatorRV_iff _ _ _ _).mpr (fun s =>
      bit_reconstruct bb be Hf tz.1 tz.2 π s (hlen s) hr1 hr2 (hMM s) (hSS s)
        (hW s) (hcons s)), ?_⟩
    refine Prod.ext hr1 (Prod.ext hr2 ?_)
    funext s
    show π ((bitPlain tz.1 s).2.1
        + Hf.hash (π (be.bin 0)) (bitTweak tz.1 s) (msgHashTail bb (bitPlain tz.1 s))
        + π ((bitPlain tz.1 s).2.1
          + Hf.hash (π (be.bin 0)) (bitTweak tz.1 s)
              (msgHashTail bb (bitPlain tz.1 s)))
        + π (be.bin 1)
        + be.bin ((splitIdx (bitPlain tz.1 s).1).1.val + 1)) = tz.2.2.2 s
    rw [hr1, hr2]
    rw [show (bitPlain tz.1 s).2.1
        + Hf.hash tz.2.1 (bitTweak tz.1 s) (msgHashTail bb (bitPlain tz.1 s))
        = MMvB bb Hf tz.2 tz.1 s from rfl, hMM s]
    exact hW s
  refine le_trans ?_ (CR18.mass_mono Dist.uniform_nonNeg himpl)
  have himg : (Finset.univ.image (DfullB bb be Hf tz.2 tz.1)).card = sigmaMBit tz.1 := by
    rw [Finset.card_image_of_injective _ hDinj, Finset.card_univ, card_DRIdxBit]
  have hle : (Finset.univ.image (DfullB bb be Hf tz.2 tz.1)).card ≤ Fintype.card F := by
    rw [himg, ← card_DRIdxBit tz.1]
    exact Fintype.card_le_of_injective _ hDinj
  have hmass := uniform_perm_consistent_mass_ge_finset
    (DfullB bb be Hf tz.2 tz.1) (RfullB bb Hf tz.2 tz.1)
    (fun i j h => congrArg _ (hDinj h)) (fun i j h => congrArg _ (hRinj h)) hle
  rw [himg] at hmass
  exact hmass

/-- **The ε = 0 σ⁺ ratio, bit level** (Layer-3 deliverable; twin of `sigma_ratio`, made
UNCONDITIONAL by the hybrid reveal): on any good extended transcript, ideal ≤ real —
length-mismatched: ideal `= 0` (`bitIdeal_zero`); reveal-inconsistent: ideal `= 0`
(`bitIdeal_zero_of_inconsistent`, the hybrid's fix — for a naive dummy reveal this case
has positive ideal mass and zero real mass, so the ratio would be FALSE); otherwise
`ideal ≤ N^{−σ_m} ≤ real` (`bitIdeal_le` + `bitReal_ge`). -/
theorem bitSigma_ratio (xs : Fin q → HQB)
    (tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (h_good : ¬ bitBad bb be Hf tz) :
    extFixedQueryTranscriptDistRep bitIdealP bitIdealF (bitIdealAugH bb) xs tz ≤
      extFixedQueryTranscriptDistRep bitRealP (bitRealF bb be Hf)
        (bitRealAug bb be Hf) xs tz := by
  simp only [extFixedQueryTranscriptDistRep]
  rw [extendedTranscriptDistRep_apply, extendedTranscriptDistRep_apply]
  refine mul_le_mul_of_nonneg_right ?_ (envFactor_nonneg _ _)
  by_cases hlen : ∀ s : Fin q, (tz.1.2.get s).1 = (tz.1.1.get s).2.2.1
  · by_cases hcons : bitRevealConsistent bb tz
    · exact le_trans (bitIdeal_le bb be Hf tz h_good hlen)
        (bitReal_ge bb be Hf tz h_good hlen hcons)
    · rw [bitIdeal_zero_of_inconsistent bb tz hlen hcons]
      exact extSysFactorRep_nonneg _ _ _ _
  · rw [not_forall] at hlen
    obtain ⟨s, hs⟩ := hlen
    rw [bitIdeal_zero bb tz s hs]
    exact extSysFactorRep_nonneg _ _ _ _

end BitGoodRatio

/-! ### Part-2 support: generic engines for the triple reveal and the bit pins

Faithful ports from the oracle `HTechnique/HCTR2Bit.lean`, same names (each docstring cites
its oracle declaration): the triple-reveal uniform-mass engines, the dependent-codomain and
fused-product self-locating pins with their slice twins, and the conditional/weighted fiber
engines (`expectW`).  All are carrier-generic; the bit collapse/pin layers below instantiate
them. -/

/-! ### PHASE P1b3.C1 — the weighted-mass functional `expectW`

The σ-accounted bad-bound charges each transcript `t` a *per-transcript* weight
(the green cells pay the sharp `bitMsgDeg/N` and the u-cells pay `1/N`, both
gated by the pair's cap-validity at `t`).  `expectW D w = Σ_a D a · w a` is the
expectation of that weight under the extended ideal law `D`; the conditional
cells (C1) bound each event's mass by `expectW D (cellWeight · [valid])`, C1's
sum-swap collects them into a single `expectW D (Σ_p cellWeight)`, and C2 bounds
the inner `Σ_p cellWeight t ≤ bitW t` pointwise, so monotonicity + the support
bound (`bitW_le` on the `bitNPB σB` support) closes to `bitBadBudgetSigma`. -/

/-! ### The dummy-aug bit collapse layer (instances of the generic reveal-collapse spine)

The dummy ideal extension at the bit carriers is the generic `TweakablePRP.idealPZ`/`idealFZ`/
`idealAugZ` at `MsgK := bitMsgL`, `Z := F × F × (Fin q → F)` — `bitIdealP`/`bitIdealF` are
definitionally the generic sampler/system, and admissibility is `TweakablePRP.admissible` itself.
The oracle's stage-3 collapse layer survives as `bitIdealExt_apply` plus the conditional
ω-slice `bit_omega_slice_cond_le` (a faithful port with its own proof); the remaining
plain instances retired with their consumers — hybrid-layer users call the `TweakablePRP.*` spine
and the `_cond_wexp` bridges directly. -/

/-- Ideal reveal — the dummy (instance of `TweakablePRP.idealAugZ`.  Oracle: `bitIdealAug`). -/
abbrev bitIdealAug : ((F × F × (Fin q → F)) ×
      (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) →
    TranscriptPrefix HQB HMB q → (F × F × (Fin q → F)) :=
  TweakablePRP.idealAugZ

/-- **Ideal product factorization**, dummy aug (instance of `TweakablePRP.idealExtZ_apply`.  Oracle:
`bitIdealExt_apply`). -/
theorem bitIdealExt_apply (E : PFunDDS.DDE HQB HMB)
    (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F)) :
    extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E (t, z)
      = Dist.uniform (F × F × (Fin q → F)) z *
        (tr[q](TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T), E)) t :=
  TweakablePRP.idealExtZ_apply E t z

/-- **Conditional ω-slice collapse**, dummy aug (the `_cond` twin of `bit_omega_slice_le`):
a per-dummy-`z` conditional ω-bound `mass (P(run, ·)) ≤ c · mass (S ∘ run)` lifts to the
dummy ideal extended mass with the transcript-only slice `S` riding through as a
conditional weight.  (Oracle: `bit_omega_slice_cond_le`.) -/
theorem bit_omega_slice_cond_le (E : QQueryEnvironment HQB HMB q)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop) (c : NNReal)
    (hb : ∀ z : F × F × (Fin q → F),
      (Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)).mass
        (fun g => P (envRun E (TweakablePRP.rndFun g), z))
      ≤ c * (Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)).mass
        (fun g => S (envRun E (TweakablePRP.rndFun g)))) :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass P
      ≤ c * (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass
          (fun td => S td.1) := by
  classical
  refine mass_le_of_fiber_fst_cond _ _ _ (fun t z => bitIdealExt_apply E.1 t z)
    (fun z => Dist.uniform_nonNeg z) ?_ S P c
    (fun z _ => ?_)
  · rw [← Dist.weight_eq_sum, Dist.weight_uniform]
  · unfold TweakablePRP.rnd
    rw [deterministicTranscriptDist_functionEvaluator_eq_fTransform _
        (fun g => TweakablePRP.rndFun g) E,
      Dist.mass_fTransform, Dist.mass_fTransform]
    exact hb z


/-! ### Hybrid → dummy reduction (Layer E″, the stage-5/Part-B interface)

The hybrid extended distribution is the **pushforward** of the dummy one under
`(t, d) ↦ (t, Φ_t d)` (`bitIdealExtH_mass`); every dummy-layer collapse bridge lifts by
composing the predicate with the hybridization.  Faithful ports of the oracle's hybrid
collapse machinery (`HTechnique/HCTR2Bit.lean` §"Hybrid collapse machinery"). -/

section BitHybridCollapse

variable (bb : BlockBits F n)

/-- Local shorthand for the hybrid ideal extended transcript distribution. -/
local notation:max "bitExtHD" E:max =>
  extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb) E

/-- Local shorthand for the dummy ideal extended transcript distribution. -/
local notation:max "bitExtD" E:max =>
  extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E

/-- **Hybrid factorization** (the transcript-dependent-aug variant of
`bitIdealExt_apply`): the hybrid extension factors as
`(Φ_t)⋆uniform × ±rnd transcript mass`.  (Oracle: `bitIdealExtH_apply`.) -/
theorem bitIdealExtH_apply (E : PFunDDS.DDE HQB HMB)
    (t : TranscriptPrefix HQB HMB q) (z : F × F × (Fin q → F)) :
    (bitExtHD E) (t, z)
      = (Dist.uniform (F × F × (Fin q → F))).mass (fun d => bitHybrid bb t d = z) *
        (tr[q](TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T), E)) t := by
  unfold TweakablePRP.rnd
  rw [extendedTranscriptDistRep_apply, bitExtSysFactorH_eq,
    deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_functionEvaluator, mul_assoc]

/-- **Pushforward transport**: hybrid extended mass = dummy extended mass of
the hybridized predicate.  Every hybrid bound reduces to a stage-3 bound.  (Oracle: `bitIdealExtH_mass`.) -/
theorem bitIdealExtH_mass (E : PFunDDS.DDE HQB HMB)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop) :
    (bitExtHD E).mass P
      = (bitExtD E).mass (fun td => P (td.1, bitHybrid bb td.1 td.2)) := by
  classical
  rw [Dist.mass_eq_sum, Dist.mass_eq_sum]
  rw [show (∑ tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)),
        if P tz then (bitExtHD E) tz else 0)
      = ∑ t : TranscriptPrefix HQB HMB q, ∑ z : F × F × (Fin q → F),
          if P (t, z) then (bitExtHD E) (t, z) else 0 from
      Fintype.sum_prod_type _,
    show (∑ td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)),
        if P (td.1, bitHybrid bb td.1 td.2) then (bitExtD E) td else 0)
      = ∑ t : TranscriptPrefix HQB HMB q, ∑ d : F × F × (Fin q → F),
          if P (t, bitHybrid bb t d) then (bitExtD E) (t, d) else 0 from
      Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun t _ => ?_
  set C := (tr[q](TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T), E)) t with hC
  have h1 : (∑ z : F × F × (Fin q → F),
        if P (t, z) then (bitExtHD E) (t, z) else 0)
      = (Dist.fTransform (bitHybrid bb t)
          (Dist.uniform (F × F × (Fin q → F)))).mass (fun z => P (t, z)) * C := by
    rw [Dist.mass_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hp : P (t, z)
    · rw [if_pos hp, if_pos hp, bitIdealExtH_apply, Dist.fTransform_apply_eq_mass]
    · rw [if_neg hp, if_neg hp, zero_mul]
  have h3 : (Dist.uniform (F × F × (Fin q → F))).mass
        (fun d => P (t, bitHybrid bb t d)) * C
      = ∑ d : F × F × (Fin q → F),
          if P (t, bitHybrid bb t d) then (bitExtD E) (t, d) else 0 := by
    rw [Dist.mass_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hp : P (t, bitHybrid bb t d)
    · rw [if_pos hp, if_pos hp, bitIdealExt_apply]
    · rw [if_neg hp, if_neg hp, zero_mul]
  rw [h1, Dist.mass_fTransform, h3]

/-- **Weighted conditional hybrid reveal-collapse** (PHASE P1b3.C1, the `_wexp`
twin of `bitRevealCollapseH_cond_le`): the per-admissible-`V` bound may vary with
the transcript (`bnd : t ↦ …`), so the conclusion is the weighted mass
`expectW (bitExtD E.1) (t ↦ [V t]·bnd t)` (over the dummy extension, whose
`t`-marginal agrees with the hybrid one) rather than `bnd · mass (V∘fst)`.  (Oracle: `bitRevealCollapseH_cond_wexp_le`.) -/
theorem bitRevealCollapseH_cond_wexp_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (V : TranscriptPrefix HQB HMB q → Prop) [DecidablePred V]
    (bnd : TranscriptPrefix HQB HMB q → NNReal)
    (hVP : ∀ t d, P (t, bitHybrid bb t d) → V t)
    (hb : ∀ t, TweakablePRP.admissible E t → V t →
      (Dist.uniform (F × F × (Fin q → F))).mass
        (fun d => P (t, bitHybrid bb t d)) ≤ bnd t) :
    (bitExtHD E.1).mass P
      ≤ expectW (bitExtD E.1) (fun td => if V td.1 then bnd td.1 else 0) := by
  rw [bitIdealExtH_mass bb E.1 P]
  exact mass_le_of_fiber_snd_cond_wexp _ _ _ (bitIdealExt_apply E.1)
    (deterministicTranscriptDist_nonNeg _ E.1)
    Dist.weight_uniform _ V bnd (fun t d hp => hVP t d hp)
    (fun t hfne hVt => hb t
      (Classical.byContradiction fun hadm => hfne (TweakablePRP.idealTr_vanish E hE t hadm)) hVt)

/-- **Weighted conditional hybrid reveal-lift** (PHASE P1b3.C1): the `_wexp` twin
of `bitPairMassH_cond_le_of_reveal`, threading a `t`-dependent uniform-dummy
bound `bnd` (the sharp green weight `bitMsgDeg …/N` at fixed `t`).  (Oracle: `bitPairMassH_cond_wexp_le_of_reveal`.) -/
theorem bitPairMassH_cond_wexp_le_of_reveal
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (G : TranscriptPrefix HQB HMB q → (F × F × (Fin q → F)) → Prop)
    (V : TranscriptPrefix HQB HMB q → Prop) [DecidablePred V]
    (bnd : TranscriptPrefix HQB HMB q → NNReal)
    (hVP : ∀ t d, P (t, bitHybrid bb t d) → V t)
    (hG : ∀ t, TweakablePRP.admissible E t → V t →
      (Dist.uniform (F × F × (Fin q → F))).mass (G t) ≤ bnd t)
    (himp : ∀ t d, P (t, bitHybrid bb t d) → G t d) :
    (bitExtHD E.1).mass P
      ≤ expectW (bitExtD E.1) (fun td => if V td.1 then bnd td.1 else 0) :=
  bitRevealCollapseH_cond_wexp_le bb E hE P V bnd hVP (fun t hadm hVt =>
    le_trans (CR18.mass_mono Dist.uniform_nonNeg (himp t)) (hG t hadm hVt))

end BitHybridCollapse

/-! ### Bit reveal-shape collision leaves (paper §3.4.2, bit level)

Faithful ports of the oracle's `RevealShapes` section (`HTechnique/HCTR2Bit.lean`), restated
through the file's `hashBlkB` (the oracle's `bitHashBlk`) and the tweak extractor `bitTweak`
(the oracle's `msgTweak` collapses to it).  Every collision cell over the uniform triple
reveal `Z = h̄ × L × (Fin q → F)` reduces to: **prop2** (head vs head, `≤ d/N`), **prop1**
(head vs constant, `≤ d/N`), **prop3** (`h̄` vs head, `≤ d/N`), **functional-in-`L`**
(`Sⱼ`-shapes, `≤ 1/N`), or a **third-component pin** (`revealLastB_*`, the paper's `Dˢ`
cells, `≤ 1/N`) — plus the `_sharp` (`degB`-weighted) twins at the `HashFamilyS` props. -/

section BitRevealShapes

variable (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))

/-- `UUvB` is the ciphertext `hashBlkB` instance.  (Oracle: `UUvB_eq_bitHashBlk`.) -/
theorem UUvB_eq_hashBlkB (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    UUvB bb Hf z t s
      = hashBlkB bb Hf z (bitTweak t s) (bitCipher t s) := rfl

/-- **S4 reduction** (head-block collision, feeds `prop2`).  (Oracle: `bitHashBlk_eq_iff`.) -/
theorem hashBlkB_eq_iff (z : F × F × (Fin q → F))
    (tw1 tw2 : T) (m1 m2 : HMB) :
    hashBlkB bb Hf z tw1 m1 = hashBlkB bb Hf z tw2 m2 ↔
      Hf.hash z.1 tw1 (msgHashTail bb m1) + Hf.hash z.1 tw2 (msgHashTail bb m2)
        = m1.2.1 + m2.2.1 := by
  unfold hashBlkB
  char2_iff

/-- **Head-block constant reduction** (feeds `prop1`).  (Oracle: `bitHashBlk_eq_const_iff`.) -/
theorem hashBlkB_eq_const_iff (z : F × F × (Fin q → F))
    (tw : T) (m : HMB) (c : F) :
    hashBlkB bb Hf z tw m = c ↔
      Hf.hash z.1 tw (msgHashTail bb m) = c + m.2.1 := by
  unfold hashBlkB
  char2_iff

/-- **S3 reduction** (`h̄ = UUˢ`, feeds `prop3`).  (Oracle: `hbar_eq_UUvB_iff`.) -/
theorem hbar_eq_UUvB_iff (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    z.1 = UUvB bb Hf z t s ↔
      Hf.hash z.1 (bitTweak t s) (msgHashTail bb (bitCipher t s))
        + z.1 = (bitCipher t s).2.1 := by
  unfold UUvB hashBlkB
  char2_iff

/-- **S1 reduction** (`Sⁱʳ = MMˢ` solves for `L = reveal.2.1`).  (Oracle: `SjvB_eq_MMvB_iff`.) -/
theorem SjvB_eq_MMvB_iff (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q) (i : ℕ) :
    SjvB bb be Hf z t r i = MMvB bb Hf z t s ↔
      z.2.1 = MMvB bb Hf z t s + MMvB bb Hf z t r + UUvB bb Hf z t r + be.bin i := by
  unfold SjvB SvB
  char2_iff

/-- `Sⱼˢ = c` solves for `L = reveal.2.1` (functional in `L`).  (Oracle: `SjvB_eq_const_iff`.) -/
theorem SjvB_eq_const_iff (z : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (i : ℕ) (c : F) :
    SjvB bb be Hf z t s i = c ↔
      z.2.1 = c + MMvB bb Hf z t s + UUvB bb Hf z t s + be.bin i := by
  unfold SjvB SvB
  char2_iff

/-- **Hash-tail injectivity (P2b crux helper)**: two `hashTailB` tails packaged
as `Σ`-length-with-function are equal only if their length classes, full blocks
and partial blocks agree.  The length `ℓ` is read from the `Σ`-index `= ℓ + 2`
(so equal indices ⟹ equal `ℓ`); `r` and the partial bits `P` are read from the
`10*`-padded last block (`padBlock_r_inj` / `padBlock_setWidth`); the full
blocks `N` from the middle `Fin.cons`/`Fin.snoc` entries.  This is the Fin-tail
analogue of HCTR2Spec `specH_input_inj`.  (Oracle: `hashTailB_sigma_inj`.) -/
theorem hashTailB_sigma_inj {ℓ₁ ℓ₂ : Fin L} {r₁ r₂ : Fin n}
    {N₁ : Fin ℓ₁.val → F} {P₁ : BitVec r₁.val} {N₂ : Fin ℓ₂.val → F} {P₂ : BitVec r₂.val}
    (h : hashTailB bb ℓ₁ r₁ N₁ P₁ = hashTailB bb ℓ₂ r₂ N₂ P₂) :
    ∃ (_ : ℓ₁ = ℓ₂) (_ : r₁ = r₂), HEq N₁ N₂ ∧ HEq P₁ P₂ := by
  unfold hashTailB at h
  have hval : ℓ₁.val = ℓ₂.val := congrArg Sigma.fst h
  have hℓ : ℓ₁ = ℓ₂ := Fin.ext hval
  subst hℓ
  rw [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨_, hN, hopt⟩ := h
  have hr : r₁ = r₂ := by
    by_cases h1 : r₁.val = 0 <;> by_cases h2 : r₂.val = 0
    · exact Fin.ext (by omega)
    · rw [if_pos h1, if_neg h2] at hopt; exact absurd hopt (by simp)
    · rw [if_neg h1, if_pos h2] at hopt; exact absurd hopt (by simp)
    · rw [if_neg h1, if_neg h2, Option.some.injEq] at hopt
      exact Fin.ext (padBlock_r_inj bb r₁.val r₂.val r₁.isLt r₂.isLt P₁ P₂ hopt)
  subst hr
  have hP : P₁ = P₂ := by
    split_ifs at hopt with h1
    · have hpow : (2 : ℕ) ^ r₁.val = 1 := by rw [h1]; rfl
      have a := P₁.isLt
      have b := P₂.isLt
      rw [hpow] at a b
      exact BitVec.toNat_injective (by omega)
    · rw [Option.some.injEq] at hopt
      have h2 : (bb.toBits (padBlock bb r₁.val P₁)).setWidth r₁.val
          = (bb.toBits (padBlock bb r₁.val P₂)).setWidth r₁.val := by rw [hopt]
      rwa [padBlock_setWidth bb r₁.val r₁.isLt, padBlock_setWidth bb r₁.val r₁.isLt] at h2
  exact ⟨rfl, rfl, heq_of_eq hN, heq_of_eq hP⟩

/-- **No-share reduction** (mirror `revealHashBlk_of_no_share`, parameterized over the
off-diagonal bound): if `r` and `s` do not share their full `(hash tweak, extracted
message)` pair, the head-block collision mass is whatever the `Σ`-distinct collision bound
`hcoll` gives — on the diagonal the collision forces the full share (mass `0`; the length
class is no longer in the tweak: `hashTailB` coincidence forces `ℓ` via the `Σ`-index and
`(r, P)` via the `10*` pad — `hashTailB_sigma_inj`).  Both the uniform (`prop2`, `d/N`) and
sharp (`prop2'`, `max dʳ dˢ/N`) `of_no_share` bounds are instances. -/
theorem revealBitHashBlk_of_no_share_le (Hf' : HashFamily F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q) (X : Fin q → HMB)
    (b : ℝ) (hb : 0 ≤ b)
    (hshare : bitTweak t r = bitTweak t s → X r = X s → False)
    (hcoll : ((bitTweak t r, msgHashTail bb (X r)) : T × BitTailS F)
        ≠ (bitTweak t s, msgHashTail bb (X s)) →
      (Dist.uniform (F × F × (Fin q → F))).mass
          (fun z => hashBlkB bb Hf' z (bitTweak t r) (X r)
            = hashBlkB bb Hf' z (bitTweak t s) (X s)) ≤ b) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => hashBlkB bb Hf' z (bitTweak t r) (X r)
          = hashBlkB bb Hf' z (bitTweak t s) (X s))
      ≤ b := by
  by_cases hdiff : ((bitTweak t r, msgHashTail bb (X r)) : T × BitTailS F)
      = (bitTweak t s, msgHashTail bb (X s))
  · -- hash inputs coincide ⟹ the collision forces the full share
    refine le_trans (le_of_eq (mass_eq_zero_of_forall _ (fun z heq => ?_))) hb
    have hh := congrArg
      (fun x : T × BitTailS F => Hf'.hash z.1 x.1 x.2) hdiff
    dsimp only at hh
    simp only [hashBlkB] at heq
    rw [hh] at heq
    have hM : (X r).2.1 = (X s).2.1 := add_right_cancel heq
    have hT : bitTweak t r = bitTweak t s := (Prod.ext_iff.mp hdiff).1
    have htail : msgHashTail bb (X r) = msgHashTail bb (X s) := (Prod.ext_iff.mp hdiff).2
    have hX : X r = X s := by
      obtain ⟨kr, Mr, Nr, Pr, h₁⟩ : ∃ k M N P, X r = ⟨k, (M, N, P)⟩ := ⟨_, _, _, _, rfl⟩
      obtain ⟨ks, Ms, Ns, Ps, h₂⟩ : ∃ k M N P, X s = ⟨k, (M, N, P)⟩ := ⟨_, _, _, _, rfl⟩
      rw [h₁, h₂] at htail hM ⊢
      simp only [msgHashTail] at htail
      obtain ⟨hℓ, hr, hN, hP⟩ := hashTailB_sigma_inj bb htail
      have hidx : kr = ks :=
        (finProdFinEquiv (m := L) (n := n)).symm.injective (Prod.ext hℓ hr)
      subst hidx
      have hMe : Mr = Ms := hM
      have hNe : Nr = Ns := eq_of_heq hN
      have hPe : Pr = Ps := eq_of_heq hP
      rw [hMe, hNe, hPe]
    exact (hshare hT hX).elim
  · exact hcoll hdiff

/-! ### PHASE P1b2.S3 — sharp (`degB`-weighted) reveal bounds

The green D/R cells of `bit_cell_D_le`/`bit_cell_R_le` route the block-`0`
`MM`/`UU` head columns to `Hf.d/N` (the *uniform* multiplicity).  These `_sharp`
variants take the per-length bundle `HashFamilyS` and rebound the SAME masses by
the per-query degree `degB tw mˢ` (`bitMsgDeg`), the paper's `dˢ` granularity
(Fig 4/5).  The cell dispatch routes through these plus the `bit_degB_le_bitD`
bridge (the uniform-multiplicity twins retired with the plain leaf generation).
Everything runs over `Hfs.toHashFamily`, so the reduction iff-lemmas
(`hashBlkB_eq_*`, `hbar_eq_UUvB_iff`) and the no-share reduction
(`revealBitHashBlk_of_no_share_le`) are shared; only the property invoked
changes `prop_ ↦ prop_'`. -/

/-- The per-query hash degree at a message `m` under tweak `tw`: `degB tw` of the
padded tail length `mˢ = ℓ + 2` (`= (splitIdx m.1).1.val + 2`, the length of
`msgHashTail bb m`).  This is the sharp weight the green cells pay.  (Oracle: `bitMsgDeg`.) -/
def bitMsgDeg (Hfs : HashFamilyS F T (L + 2)) (tw : T) (m : HMB) : ℕ :=
  Hfs.degB tw (1 + (splitIdx m.1).1.val + (if (splitIdx m.1).2.val = 0 then 0 else 1))

/-- `bitTailDegLen (msgHashTail bb m) = mˢ = 1 + ℓ + (r ≠ 0 ? 1 : 0)`: the honest per-query
degree granularity, computed from the length class `(ℓ, r) = splitIdx m.1` only (so
`bitMsgDeg` needs no `bb`). -/
theorem bitTailDegLen_msgHashTail (m : HMB) :
    bitTailDegLen (msgHashTail bb m)
      = 1 + (splitIdx m.1).1.val + (if (splitIdx m.1).2.val = 0 then 0 else 1) := by
  simp only [bitTailDegLen, msgHashTail, hashTailB]
  by_cases hr : (splitIdx m.1).2.val = 0 <;> simp [hr]

/-- `bitMsgDeg` in `bitTailDegLen`-of-`msgHashTail` form, for feeding `prop_'`. -/
theorem bitMsgDeg_eq (Hfs : HashFamilyS F T (L + 2)) (tw : T) (m : HMB) :
    bitMsgDeg Hfs tw m = Hfs.degB tw (bitTailDegLen (msgHashTail bb m)) := by
  rw [bitMsgDeg, bitTailDegLen_msgHashTail]

/-- The structured-tail cap `(splitIdx m.1).1.val ≤ L + 2` (the `HashFamilyS`/`HashFamily`
cap `L + 2` from the message length class `Fin L`). -/
theorem msgHashTail_fst_le (m : HMB) : (msgHashTail bb m).1 ≤ L + 2 :=
  (splitIdx m.1).1.isLt.le.trans (Nat.le_add_right L 2)

/-- **Sharp head-block constant bound** (`prop1'`): `≤ degB tw mˢ / N`.  (Oracle: `revealBitHashBlk_const_le_sharp`.) -/
theorem revealBitHashBlk_const_le_sharp (Hfs : HashFamilyS F T (L + 2))
    (tw : T) (m : HMB) (c : F) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => hashBlkB bb Hfs.toHashFamily z tw m = c)
      ≤ (bitMsgDeg Hfs tw m : NNReal) / Fintype.card F := by
  rw [bitMsgDeg_eq bb Hfs tw m]
  exact uniform_prod_fst_marginal_le
    (fun z => hashBlkB_eq_const_iff bb Hfs.toHashFamily z tw m c)
    (Hfs.prop1' tw (msgHashTail bb m) (msgHashTail_fst_le bb m) (c + m.2.1))

/-- `MMˢ = c` (sharp): `≤ degB (bitTweak t s) mˢ / N`.  (Oracle: `revealMMvB_const_le_sharp`.) -/
theorem revealMMvB_const_le_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (c : F) :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun z => MMvB bb Hfs.toHashFamily z t s = c)
      ≤ (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s) : NNReal) / Fintype.card F :=
  revealBitHashBlk_const_le_sharp bb Hfs _ _ _

/-- `UUˢ = Yⱼʳ` (sharp): `≤ degB (bitTweak t s) mˢ / N`.  (Oracle: `revealUUvB_YjvB_le_sharp`.) -/
theorem revealUUvB_YjvB_le_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (s r : Fin q) (j : ℕ) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => UUvB bb Hfs.toHashFamily z t s = YjvB t r j)
      ≤ (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F :=
  revealBitHashBlk_const_le_sharp bb Hfs _ _ _

/-- **Sharp S3 bound** (`h̄ = UUˢ`, `prop3'`): `≤ degB (bitTweak t s) mˢ / N`.  (Oracle: `revealhbarB_UUvB_le_sharp`.) -/
theorem revealhbarB_UUvB_le_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun z => z.1 = UUvB bb Hfs.toHashFamily z t s)
      ≤ (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F := by
  rw [bitMsgDeg_eq bb Hfs (bitTweak t s) (bitCipher t s)]
  exact uniform_prod_fst_marginal_le (fun z => hbar_eq_UUvB_iff bb Hfs.toHashFamily z t s)
    (Hfs.prop3' (bitTweak t s) (msgHashTail bb (bitCipher t s))
      (msgHashTail_fst_le bb (bitCipher t s)) (bitCipher t s).2.1)

/-- **Sharp head-block collision bound** (`prop2'`): `≤ max (dʳ, dˢ)/N`, the
paper's honest Fig 5 off-diagonal max (restored from the frozen `prop2`'s
`max d d = d`).  (Oracle: `revealBitHashBlk_collision_le_sharp`.) -/
theorem revealBitHashBlk_collision_le_sharp (Hfs : HashFamilyS F T (L + 2))
    (tw1 tw2 : T) (m1 m2 : HMB)
    (hdiff : ((tw1, msgHashTail bb m1) : T × BitTailS F)
        ≠ (tw2, msgHashTail bb m2)) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => hashBlkB bb Hfs.toHashFamily z tw1 m1
          = hashBlkB bb Hfs.toHashFamily z tw2 m2)
      ≤ (max (bitMsgDeg Hfs tw1 m1) (bitMsgDeg Hfs tw2 m2) : NNReal) / Fintype.card F := by
  rw [bitMsgDeg_eq bb Hfs tw1 m1, bitMsgDeg_eq bb Hfs tw2 m2]
  exact uniform_prod_fst_marginal_le
    (fun z => hashBlkB_eq_iff bb Hfs.toHashFamily z tw1 tw2 m1 m2)
    (Hfs.prop2' tw1 (msgHashTail bb m1) (msgHashTail_fst_le bb m1)
      tw2 (msgHashTail bb m2) (msgHashTail_fst_le bb m2)
      (m1.2.1 + m2.2.1) hdiff)

/-- **Sharp no-share head-block bound** (`prop2'`): distinct queries with no
shared `(tweak, message)` give `≤ max (dʳ, dˢ)/N`; coinciding hash inputs force
the full share (mass `0`).  (Oracle: `revealBitHashBlk_of_no_share_sharp`.) -/
theorem revealBitHashBlk_of_no_share_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q) (X : Fin q → HMB)
    (hshare : bitTweak t r = bitTweak t s → X r = X s → False) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => hashBlkB bb Hfs.toHashFamily z (bitTweak t r) (X r)
          = hashBlkB bb Hfs.toHashFamily z (bitTweak t s) (X s))
      ≤ (max (bitMsgDeg Hfs (bitTweak t r) (X r))
          (bitMsgDeg Hfs (bitTweak t s) (X s)) : NNReal) / Fintype.card F :=
  revealBitHashBlk_of_no_share_le bb Hfs.toHashFamily t r s X _ (by positivity)
    hshare
    (fun hdiff => revealBitHashBlk_collision_le_sharp bb Hfs _ _ _ _ hdiff)

/-- `MM` collision, share-free form (sharp): `≤ max (dʳ, dˢ)/N`.  (Oracle: `revealMMvB_of_no_share_sharp`.) -/
theorem revealMMvB_of_no_share_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q)
    (hshare : bitTweak t r = bitTweak t s →
      bitPlain t r = bitPlain t s → False) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => MMvB bb Hfs.toHashFamily z t r = MMvB bb Hfs.toHashFamily z t s)
      ≤ (max (bitMsgDeg Hfs (bitTweak t r) (bitPlain t r))
          (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s)) : NNReal) / Fintype.card F :=
  revealBitHashBlk_of_no_share_sharp bb Hfs t r s (bitPlain t) hshare

/-- `UU` collision, share-free form (sharp): `≤ max (dʳ, dˢ)/N`.  (Oracle: `revealUUvB_of_no_share_sharp`.) -/
theorem revealUUvB_of_no_share_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q)
    (hshare : bitTweak t r = bitTweak t s →
      bitCipher t r = bitCipher t s → False) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => UUvB bb Hfs.toHashFamily z t r = UUvB bb Hfs.toHashFamily z t s)
      ≤ (max (bitMsgDeg Hfs (bitTweak t r) (bitCipher t r))
          (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s)) : NNReal) / Fintype.card F :=
  revealBitHashBlk_of_no_share_sharp bb Hfs t r s (bitCipher t) hshare

/-- **S1 reveal bound** (`Sⁱʳ = MMˢ`): `≤ 1/N` — `SjvB_eq_MMvB_iff` pins `L`
given `h̄` (the triple-middle functional engine).  (Oracle: `revealSjvB_MMvB_le`.) -/
theorem revealSjvB_MMvB_le (t : TranscriptPrefix HQB HMB q) (r s : Fin q) (i : ℕ) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => SjvB bb be Hf z t r i = MMvB bb Hf z t s)
      ≤ (Fintype.card F : NNReal)⁻¹ := by
  rw [Dist.mass_congr _ (fun z => SjvB_eq_MMvB_iff bb be Hf z t r s i)]
  refine uniform_triple_middle_functional _ (fun a b b' c h1 h2 => ?_)
  have hconst : MMvB bb Hf (a, b, c) t s + MMvB bb Hf (a, b, c) t r
        + UUvB bb Hf (a, b, c) t r + be.bin i
      = MMvB bb Hf (a, b', c) t s + MMvB bb Hf (a, b', c) t r
        + UUvB bb Hf (a, b', c) t r + be.bin i := rfl
  exact h1.trans (hconst.trans h2.symm)

/-- **S1 reveal bound** (`Sⱼˢ = c`, `c` reveal-independent): `≤ 1/N`.  Covers
the `bin(k) = Sⱼˢ` D-cells and `Sⱼˢ` vs transcript-determined targets.  (Oracle: `revealSjvB_const_le`.) -/
theorem revealSjvB_const_le (t : TranscriptPrefix HQB HMB q) (s : Fin q)
    (i : ℕ) (c : F) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => SjvB bb be Hf z t s i = c)
      ≤ (Fintype.card F : NNReal)⁻¹ := by
  rw [Dist.mass_congr _ (fun z => SjvB_eq_const_iff bb be Hf z t s i c)]
  refine uniform_triple_middle_functional _ (fun a b b' c' h1 h2 => ?_)
  have hconst : c + MMvB bb Hf (a, b, c') t s + UUvB bb Hf (a, b, c') t s + be.bin i
      = c + MMvB bb Hf (a, b', c') t s + UUvB bb Hf (a, b', c') t s + be.bin i := rfl
  exact h1.trans (hconst.trans h2.symm)

/-! ### The NEW family: reveal-third-component cells (paper `Dˢ` bookkeeping)

`R`'s last entry per query is the revealed full last keystream block
`reveal.2.2 s`; against anything determined by the transcript and the rest of
the reveal it is a uniform coordinate hit, `≤ 1/N`. -/

end BitRevealShapes

/-! ### The bit response-pin engines (stage 4, Part B)

Faithful ports of the oracle's `ResponsePin` section (`HTechnique/HCTR2Bit.lean`).  The
bit-level ω is `∀ x : HQB, bitMsg-fiber x`; per query it splits into the head block, the
`ℓₓ` full tail blocks (all `F`), and the **partial** block (`BitVec rₓ`).  Two engines are
assembled from the generic self-locating pins:

* `bit_respPin_cond_le` (+ solved form): pins an `F`-block of the response to a
  self-located later query, with the whole dummy triple `d` a fixed spectator (via
  `bit_omega_slice_cond_le`) — the classic engine, the heterogeneous coordinate handled
  by `uniform_pi_selfloc_slice_le` and the agreement package extended by the partial
  block (`partSW`);
* `bit_virtualPin_le` (+ solved/`_cond` forms): pins the **virtual last block** of query
  `s` — the hybrid reveal entry `z₃ˢ` — jointly over the partial-response coordinate and
  the dummy coordinate `d₃ˢ` (via `bit_joint_slice_eq` + `uniform_pi_prod_selfloc_fused_le`
  with the explicit fused equivalence `bitFuseEquiv`), giving the paper's clean `1/N` for
  every last-block cell. -/

section BitResponsePin

variable (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))

/-! ### Block view of a bit message -/

/-- Full-block view of a bit message: block `0` is the head, block `b ≥ 1` is
tail entry `b − 1` (`0` out of range).  (Oracle: `totBlockB`.) -/
def totBlockB (m : HMB) : ℕ → F := fun b => (m.2.1 :: List.ofFn m.2.2.1).getD b 0

/-- The zero-extended partial block of a bit message (width-`n` normal form,
matching `padBlock`'s reading).  (Oracle: `partSW`.) -/
def partSW (m : HMB) : BitVec n := m.2.2.2.setWidth n

/-- Block `0` is the head.  (Oracle: `totBlockB_zero`.) -/
theorem totBlockB_zero (m : HMB) : totBlockB m 0 = m.2.1 := rfl

/-- Block `k + 1` is tail entry `k`.  (Oracle: `totBlockB_succ`.) -/
theorem totBlockB_succ (m : HMB) (k : Fin (splitIdx m.1).1.val) :
    totBlockB m (k.val + 1) = m.2.2.1 k := by
  unfold totBlockB
  rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]

/-- In-range blocks are the `Fin.cons` of head and tail.  (Oracle: `totBlockB_eq_cons`.) -/
theorem totBlockB_eq_cons (m : HMB) (b : Fin ((splitIdx m.1).1.val + 1)) :
    totBlockB m b.val = Fin.cons (α := fun _ => F) m.2.1 m.2.2.1 b := by
  induction b using Fin.cases with
  | zero => rfl
  | succ i =>
    rw [Fin.cons_succ]
    exact totBlockB_succ m i

/-- Out-of-range blocks are the padding `0`.  (Oracle: `totBlockB_of_ge`.) -/
theorem totBlockB_of_ge (m : HMB) (b : ℕ) (hb : (splitIdx m.1).1.val + 1 ≤ b) :
    totBlockB m b = 0 := by
  unfold totBlockB
  exact List.getD_eq_default _ _ (by simpa using hb)

/-- **Hash-tail congruence**: same length index, equal nonzero blocks, and
equal zero-extended partials give equal keyed hashes of the padded tail.  (Oracle: `bitHashTail_congr`.) -/
theorem bitHashTail_congr (h : F) (tw : T) {m m' : HMB}
    (hlen : m.1 = m'.1)
    (hb : ∀ b : ℕ, b ≠ 0 → totBlockB m b = totBlockB m' b)
    (hp : partSW (F := F) (L := L) (n := n) m = partSW m') :
    Hf.hash h tw (msgHashTail bb m) = Hf.hash h tw (msgHashTail bb m') := by
  obtain ⟨k, M, N, Pp⟩ := m
  obtain ⟨k', M', N', Pp'⟩ := m'
  simp only at hlen
  subst hlen
  have hN : N = N' := funext fun j => by
    have h1 := hb (j.val + 1) (Nat.succ_ne_zero _)
    rwa [totBlockB_succ ⟨k, (M, N, Pp)⟩ j, totBlockB_succ ⟨k, (M', N', Pp')⟩ j] at h1
  have hP : Pp = Pp' := setWidth_injective (splitIdx k).2.isLt.le hp
  rw [show msgHashTail bb (⟨k, (M, N, Pp)⟩ : HMB)
      = msgHashTail bb (⟨k, (M', N', Pp')⟩ : HMB) by
    unfold msgHashTail
    rw [hN, hP]]

/-- **Head-pin context pack** (mirror `respPin_head_ctx`): with the queries at
`s` matching and the nonzero response blocks and partials agreeing, the
response lengths, composite tweaks, and padded-tail hashes at `s` agree.  (Oracle: `respPinB_head_ctx`.) -/
theorem respPinB_head_ctx {E : QQueryEnvironment HQB HMB q}
    {t t' : TranscriptPrefix HQB HMB q}
    (hadm : TweakablePRP.admissible E t) (hadm' : TweakablePRP.admissible E t') {s : Fin q}
    (hqs : t.1.get s = t'.1.get s)
    (hblocks : ∀ b : ℕ, b ≠ 0 → totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b)
    (hpart : partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s))
    (h : F) :
    (t.2.get s).1 = (t'.2.get s).1 ∧
      bitTweak t s = bitTweak t' s ∧
      Hf.hash h (bitTweak t s) (msgHashTail bb (t.2.get s))
        = Hf.hash h (bitTweak t' s) (msgHashTail bb (t'.2.get s)) := by
  have hlen : (t.2.get s).1 = (t'.2.get s).1 := by
    rw [hadm.2.2 s, hadm'.2.2 s, hqs]
  have htw : bitTweak t s = bitTweak t' s := by
    unfold bitTweak
    rw [hqs]
  refine ⟨hlen, htw, ?_⟩
  rw [htw]
  exact bitHashTail_congr bb Hf h _ hlen hblocks hpart

/-! ### The block-coordinate view of the ideal ω -/

/-- Block-coordinate index of the bit fiber at query `x`: `ℓₓ + 1` full
`F`-slots (head + tail) plus the partial slot.  (Oracle: `BitBlockIdx`.) -/
abbrev BitBlockIdx (x : HQB) : Type :=
  Fin ((splitIdx x.2.2.1).1.val + 1) ⊕ Unit

/-- Coordinate type: `F` at full-block slots, `BitVec rₓ` at the partial
slot.  (Oracle: `bitCoord`.) -/
def bitCoord : (Σ x : HQB, BitBlockIdx (F := F) (T := T) (L := L) (n := n) x) → Type
  | ⟨_, Sum.inl _⟩ => F
  | ⟨x, Sum.inr _⟩ => BitVec (splitIdx x.2.2.1).2.val

instance bitCoord_fintype :
    ∀ p : Σ x : HQB, BitBlockIdx (F := F) (T := T) (L := L) (n := n) x,
      Fintype (bitCoord p)
  | ⟨_, Sum.inl _⟩ => inferInstanceAs (Fintype F)
  | ⟨_, Sum.inr _⟩ => inferInstanceAs (Fintype (BitVec _))

instance bitCoord_decEq :
    ∀ p : Σ x : HQB, BitBlockIdx (F := F) (T := T) (L := L) (n := n) x,
      DecidableEq (bitCoord p)
  | ⟨_, Sum.inl _⟩ => inferInstanceAs (DecidableEq F)
  | ⟨_, Sum.inr _⟩ => inferInstanceAs (DecidableEq (BitVec _))

instance bitCoord_nonempty :
    ∀ p : Σ x : HQB, BitBlockIdx (F := F) (T := T) (L := L) (n := n) x,
      Nonempty (bitCoord p)
  | ⟨_, Sum.inl _⟩ => inferInstanceAs (Nonempty F)
  | ⟨_, Sum.inr _⟩ => inferInstanceAs (Nonempty (BitVec _))

/-- The block-indexed view of the ideal ω (mirror `hctrOmegaEquiv`, plus the
partial slot).  (Oracle: `bitOmegaEquiv`.) -/
def bitOmegaEquiv :
    (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) ≃
      (∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) where
  toFun g p := match p with
    | ⟨x, Sum.inl b⟩ => Fin.cons (α := fun _ => F) (g x).1 (g x).2.1 b
    | ⟨x, Sum.inr _⟩ => (g x).2.2
  invFun ω x :=
    (ω ⟨x, Sum.inl 0⟩, fun i => ω ⟨x, Sum.inl i.succ⟩, ω ⟨x, Sum.inr ()⟩)
  left_inv g := by
    funext x
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show Fin.cons (α := fun _ => F) (g x).1 (g x).2.1 0 = (g x).1
      exact Fin.cons_zero _ _
    · funext i
      show Fin.cons (α := fun _ => F) (g x).1 (g x).2.1 i.succ = (g x).2.1 i
      exact Fin.cons_succ _ _ _
    · rfl
  right_inv ω := by
    funext p
    obtain ⟨x, b | u⟩ := p
    · induction b using Fin.cases with
      | zero =>
        show Fin.cons (α := fun _ => F) (ω ⟨x, Sum.inl 0⟩)
          (fun i => ω ⟨x, Sum.inl i.succ⟩) 0 = ω ⟨x, Sum.inl 0⟩
        exact Fin.cons_zero _ _
      | succ i =>
        show Fin.cons (α := fun _ => F) (ω ⟨x, Sum.inl 0⟩)
          (fun i => ω ⟨x, Sum.inl i.succ⟩) i.succ = ω ⟨x, Sum.inl i.succ⟩
        exact Fin.cons_succ _ _ _
    · rfl

/-- The dummy triple as a homogeneous `F`-indexed family (`h̄`, `L`, and the
per-slot dummy blocks).  (Oracle: `zPackEquiv`.) -/
def zPackEquiv : (F × F × (Fin q → F)) ≃ ((Bool ⊕ Fin q) → F) where
  toFun d := fun j => match j with
    | Sum.inl false => d.1
    | Sum.inl true => d.2.1
    | Sum.inr s => d.2.2 s
  invFun w := (w (Sum.inl false), w (Sum.inl true), fun s => w (Sum.inr s))
  left_inv d := rfl
  right_inv w := by
    funext j
    rcases j with (_ | _) | s <;> rfl

/-! ### Run plumbing -/

/-- The run's transcripts are admissible (mirror `envRun_admissible`).  (Oracle: `bit_envRun_admissible`.) -/
theorem bit_envRun_admissible (E : QQueryEnvironment HQB HMB q)
    (hE : EnvRespects TweakablePRP.NP E)
    (g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) :
    TweakablePRP.admissible E (envRun E (TweakablePRP.rndFun g)) := by
  refine ⟨hE _ (envRun_consistent E _), envRun_consistent E _, fun i => ?_⟩
  have hresp : (envRun E (TweakablePRP.rndFun g)).2.get i
      = TweakablePRP.rndFun g ((envRun E (TweakablePRP.rndFun g)).1.get i) :=
    (((envRun_eq_iff E (TweakablePRP.rndFun g) _).mp rfl).2 i).symm
  rw [hresp]
  rfl

/-- The run's response at `s` is the oracle's value at the run's query.  (Oracle: `bit_envRun_resp`.) -/
theorem bit_envRun_resp (E : QQueryEnvironment HQB HMB q)
    (g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) (s : Fin q) :
    (envRun E (TweakablePRP.rndFun g)).2.get s
      = TweakablePRP.rndFun g ((envRun E (TweakablePRP.rndFun g)).1.get s) :=
  (((envRun_eq_iff E (TweakablePRP.rndFun g) _).mp rfl).2 s).symm

/-- Full blocks of the run's response at `s` are the fiber's `Fin.cons`
coordinates.  (Oracle: `bit_envRun_totBlock`.) -/
theorem bit_envRun_totBlock (E : QQueryEnvironment HQB HMB q)
    (g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) (s : Fin q)
    (b : Fin ((splitIdx ((envRun E (TweakablePRP.rndFun g)).1.get s).2.2.1).1.val + 1)) :
    totBlockB ((envRun E (TweakablePRP.rndFun g)).2.get s) b.val
      = Fin.cons (α := fun _ => F) (g ((envRun E (TweakablePRP.rndFun g)).1.get s)).1
          (g ((envRun E (TweakablePRP.rndFun g)).1.get s)).2.1 b := by
  rw [bit_envRun_resp E g s]
  exact totBlockB_eq_cons (TweakablePRP.rndFun g ((envRun E (TweakablePRP.rndFun g)).1.get s)) b

/-- The zero-extended partial of the run's response at `s` is the fiber's
partial coordinate.  (Oracle: `bit_envRun_part`.) -/
theorem bit_envRun_part (E : QQueryEnvironment HQB HMB q)
    (g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) (s : Fin q) :
    partSW (F := F) (L := L) (n := n) ((envRun E (TweakablePRP.rndFun g)).2.get s)
      = ((g ((envRun E (TweakablePRP.rndFun g)).1.get s)).2.2).setWidth n := by
  rw [bit_envRun_resp E g s]
  rfl

/-! ### The classic response-pin engine (`F`-block pins, spectator reveal) -/

/-- **Conditional bit response-pin bound** (PHASE P1b4a; the slice twin of
`bit_respPin_le`): the same located-coordinate pin, but restricted to a
transcript-only validity slice `S` (an off-located cylinder of the run, `hSoff`)
that contains the event (`hVP`).  The conclusion is the conditional
`mass P ≤ (1/N) · mass (S∘fst)` over the dummy ideal extension — the slice rides
through as the conditioning weight (`uniform_pi_selfloc_slice_le`).  (Oracle: `bit_respPin_cond_le`.) -/
theorem bit_respPin_cond_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (jbf : HQB → ℕ)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop)
    (hVP : ∀ t z, P (t, z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hrange : ∀ z t, TweakablePRP.admissible E t → P (t, z) →
      jbf (t.1.get s) < (splitIdx (t.1.get s).2.2.1).1.val + 1)
    (hpin : ∀ z t t', TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, b ≠ jbf (t.1.get s) →
        totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s) →
      P (t, z) → P (t', z) →
      totBlockB (t.2.get s) (jbf (t.1.get s))
        = totBlockB (t'.2.get s) (jbf (t.1.get s))) :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass P
      ≤ (Fintype.card F : NNReal)⁻¹ *
        (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass
          (fun td => S td.1) := by
  classical
  refine bit_omega_slice_cond_le E P S _ (fun z => ?_)
  rw [Dist.mass_congr _ (fun g => iff_self_and.mpr
      (fun hp => hVP (envRun E (TweakablePRP.rndFun g)) z hp)),
    uniform_mass_equiv (bitOmegaEquiv (F := F) (T := T) (L := L) (n := n))
      (fun g => P (envRun E (TweakablePRP.rndFun g), z) ∧ S (envRun E (TweakablePRP.rndFun g))),
    uniform_mass_equiv (bitOmegaEquiv (F := F) (T := T) (L := L) (n := n))
      (fun g => S (envRun E (TweakablePRP.rndFun g)))]
  set run : (∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) →
      TranscriptPrefix HQB HMB q :=
    fun ω => envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)) with hrundef
  set loc : (∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) →
      Σ x : HQB, BitBlockIdx x :=
    fun ω => ⟨(run ω).1.get s, Sum.inl
      (if h : jbf ((run ω).1.get s) < (splitIdx ((run ω).1.get s).2.2.1).1.val + 1
        then ⟨jbf ((run ω).1.get s), h⟩ else ⟨0, Nat.succ_pos _⟩)⟩ with hlocdef
  have loc_congr : ∀ (x x' : HQB), x = x' →
      (⟨x, Sum.inl (if h : jbf x < (splitIdx x.2.2.1).1.val + 1
          then ⟨jbf x, h⟩ else ⟨0, Nat.succ_pos _⟩)⟩ : Σ x : HQB, BitBlockIdx x)
      = ⟨x', Sum.inl (if h : jbf x' < (splitIdx x'.2.2.1).1.val + 1
          then ⟨jbf x', h⟩ else ⟨0, Nat.succ_pos _⟩)⟩ := by
    rintro x x' rfl
    rfl
  have hagree_of : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      (∀ i, i ≠ p → ω i = ω' i) →
      ∀ x, x ≠ p.1 → TweakablePRP.rndFun (bitOmegaEquiv.symm ω) x
        = TweakablePRP.rndFun (bitOmegaEquiv.symm ω') x := by
    intro ω ω' p hoff x hx
    have hgx : bitOmegaEquiv.symm ω x = bitOmegaEquiv.symm ω' x := by
      show ((ω ⟨x, Sum.inl 0⟩, fun i => ω ⟨x, Sum.inl i.succ⟩, ω ⟨x, Sum.inr ()⟩) :
            bitMsgL (F := F) (L := L) (n := n) x.2.2.1)
          = (ω' ⟨x, Sum.inl 0⟩, fun i => ω' ⟨x, Sum.inl i.succ⟩, ω' ⟨x, Sum.inr ()⟩)
      refine Prod.ext (hoff _ (fun h => hx (congrArg Sigma.fst h)))
        (Prod.ext ?_ ?_)
      · funext i
        exact hoff _ (fun h => hx (congrArg Sigma.fst h))
      · exact hoff _ (fun h => hx (congrArg Sigma.fst h))
    unfold TweakablePRP.rndFun
    rw [hgx]
  have hstab : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (run ω).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (∀ k : Fin q, k ≤ s → (run ω').1.get k = (run ω).1.get k) ∧
      (∀ k : Fin q, k < s → (run ω').2.get k = (run ω).2.get k) := by
    intro ω ω' p hp hoff
    refine envRun_prefix_congr E _ _ s (hE _ (envRun_consistent E _)).1 ?_
    intro x hx
    exact hagree_of ω ω' p hoff x (fun h => hx (by rw [← hp]; exact h))
  have hloc_stable : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω := by
    intro ω v
    have h1 := (hstab ω (Function.update ω (loc ω) v) (loc ω) rfl
      (fun i hi => (Function.update_of_ne hi _ _).symm)).1 s le_rfl
    simp only [hlocdef]
    exact loc_congr _ _ h1
  refine uniform_pi_selfloc_slice_le (fun ω => P (run ω, z)) (fun ω => S (run ω)) loc
    (fun p => Classical.arbitrary _) (Fintype.card F) Fintype.card_pos
    (fun ω _ _ => le_of_eq rfl) hloc_stable
    (fun ω v => hSoff ω (Function.update ω (loc ω) v) (loc ω) rfl
      (fun i hi => (Function.update_of_ne hi _ _).symm)) ?_
  intro ω ω' _ hoff hPω hPω' _ _
  have hadm : TweakablePRP.admissible E (run ω) := bit_envRun_admissible E hE _
  have hadm' : TweakablePRP.admissible E (run ω') := bit_envRun_admissible E hE _
  have hstab' := hstab ω ω' (loc ω) rfl hoff
  have hxs : (run ω').1.get s = (run ω).1.get s := hstab'.1 s le_rfl
  have hjb : jbf ((run ω).1.get s)
      < (splitIdx ((run ω).1.get s).2.2.1).1.val + 1 :=
    hrange z (run ω) hadm hPω
  have hlocval : loc ω
      = ⟨(run ω).1.get s, Sum.inl ⟨jbf ((run ω).1.get s), hjb⟩⟩ := by
    simp only [hlocdef]
    rw [dif_pos hjb]
  have hblock : ∀ (ω₀ : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (x : HQB) (b : Fin ((splitIdx x.2.2.1).1.val + 1)),
      (run ω₀).1.get s = x →
      totBlockB ((run ω₀).2.get s) b.val = ω₀ ⟨x, Sum.inl b⟩ := by
    intro ω₀ x b hp
    subst hp
    exact (bit_envRun_totBlock E (bitOmegaEquiv.symm ω₀) s b).trans
      (congrFun (bitOmegaEquiv.apply_symm_apply ω₀) ⟨(run ω₀).1.get s, Sum.inl b⟩)
  have hpartblock : ∀ (ω₀ : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (x : HQB), (run ω₀).1.get s = x →
      partSW (F := F) (L := L) (n := n) ((run ω₀).2.get s)
        = (ω₀ ⟨x, Sum.inr ()⟩ : BitVec (splitIdx x.2.2.1).2.val).setWidth n := by
    intro ω₀ x hp
    subst hp
    rw [bit_envRun_part E (bitOmegaEquiv.symm ω₀) s]
    exact congrArg (BitVec.setWidth n)
      (congrFun (bitOmegaEquiv.apply_symm_apply ω₀) ⟨(run ω₀).1.get s, Sum.inr ()⟩)
  have hoff_blocks : ∀ b : ℕ, b ≠ jbf ((run ω).1.get s) →
      totBlockB ((run ω).2.get s) b = totBlockB ((run ω').2.get s) b := by
    intro b hb
    by_cases hlt : b < (splitIdx ((run ω).1.get s).2.2.1).1.val + 1
    · rw [hblock ω ((run ω).1.get s) ⟨b, hlt⟩ rfl,
        hblock ω' ((run ω).1.get s) ⟨b, hlt⟩ hxs]
      refine hoff _ (fun h => hb ?_)
      rw [hlocval] at h
      have hsnd := sigma_mk_injective h
      exact congrArg Fin.val (Sum.inl.inj hsnd)
    · have hout : (splitIdx ((run ω).2.get s).1).1.val + 1 ≤ b := by
        have hlen := hadm.2.2 s
        rw [hlen]
        omega
      have hout' : (splitIdx ((run ω').2.get s).1).1.val + 1 ≤ b := by
        have hlen' := hadm'.2.2 s
        rw [hlen', hxs]
        omega
      rw [totBlockB_of_ge _ _ hout, totBlockB_of_ge _ _ hout']
  have hoff_part : partSW (F := F) (L := L) (n := n) ((run ω).2.get s)
      = partSW ((run ω').2.get s) := by
    rw [hpartblock ω ((run ω).1.get s) rfl, hpartblock ω' ((run ω).1.get s) hxs]
    congr 1
    refine hoff _ (fun h => ?_)
    rw [hlocval] at h
    have hsnd : (Sum.inr () : BitBlockIdx ((run ω).1.get s))
        = Sum.inl ⟨jbf ((run ω).1.get s), hjb⟩ :=
      eq_of_heq (Sigma.mk.inj h).2
    simp at hsnd
  have hfin := hpin z (run ω) (run ω') hadm hadm'
    (fun k hk => (hstab'.1 k hk).symm) (fun k hk => (hstab'.2 k hk).symm)
    hoff_blocks hoff_part hPω hPω'
  rw [hlocval]
  rw [← hblock ω ((run ω).1.get s) ⟨jbf ((run ω).1.get s), hjb⟩ rfl,
    ← hblock ω' ((run ω).1.get s) ⟨jbf ((run ω).1.get s), hjb⟩ hxs]
  exact hfin

/-- **Solved-form conditional bit response-pin** (PHASE P1b4a; slice twin of
`bit_respPin_solved_le`): the solved-expression interface, restricted to the
validity slice `S`.  (Oracle: `bit_respPin_cond_solved_le`.) -/
theorem bit_respPin_cond_solved_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (jbf : HQB → ℕ)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop)
    (rhs : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hVP : ∀ t z, P (t, z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hrange : ∀ z t, TweakablePRP.admissible E t → P (t, z) →
      jbf (t.1.get s) < (splitIdx (t.1.get s).2.2.1).1.val + 1)
    (hsolve : ∀ z t, TweakablePRP.admissible E t → P (t, z) →
      totBlockB (t.2.get s) (jbf (t.1.get s)) = rhs z t)
    (hcongr : ∀ z t t', TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, b ≠ jbf (t.1.get s) →
        totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s) →
      rhs z t = rhs z t') :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass P
      ≤ (Fintype.card F : NNReal)⁻¹ *
        (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass
          (fun td => S td.1) := by
  refine bit_respPin_cond_le E hE s jbf P S hVP hSoff hrange ?_
  intro z t t' hadm hadm' hq hr hblocks hpart hP hP'
  rw [hsolve z t hadm hP, hq s le_rfl, hsolve z t' hadm' hP']
  exact hcongr z t t' hadm hadm' hq hr hblocks hpart

/-! ### PHASE P1a.E3 — pin-update slice invariance

The validity slice `V_p` that P1b threads through `uniform_pi_selfloc_slice_le`'s
`hS` slot is invariant under the classic pin's located-coordinate update.  The
core is the `envRun_prefix_congr`-based stability of the run's queries `≤ s` (and
responses `< s`) — extracted verbatim from `bit_respPin_le`'s internal `hstab`.
Because `mBlocksBit t s'` reads only the *plain length* of query `s'`, and under
admissibility (`bitPlain_fst`) that length is the query's stated length field,
`bitCapValid` at any cap index whose query `≤ s` is invariant.  P1b instantiates
`ω' := Function.update ω (loc ω) v` and `p := loc ω` (so `p.1 = (run ω).1.get s`
holds by the classic pin's `loc`), giving the `hS` cylinder property. -/

/-- **Run prefix stability under an off-point update** (PHASE P1a.E3 core;
`bit_respPin_le`'s `hstab`, extracted): if `ω, ω'` agree off a point `p` whose
query is the run's `s`-th query, the runs' queries `≤ s` and responses `< s`
coincide.  (Oracle: `bit_run_prefix_congr_off`.) -/
theorem bit_run_prefix_congr_off
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i) :
    (∀ k : Fin q, k ≤ s →
        (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))).1.get k
          = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get k) ∧
    (∀ k : Fin q, k < s →
        (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))).2.get k
          = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).2.get k) := by
  refine envRun_prefix_congr E _ _ s (hE _ (envRun_consistent E _)).1 ?_
  intro x hx
  have hx' : x ≠ p.1 := fun h => hx (by rw [← hp]; exact h)
  have hgx : bitOmegaEquiv.symm ω x = bitOmegaEquiv.symm ω' x := by
    show ((ω ⟨x, Sum.inl 0⟩, fun i => ω ⟨x, Sum.inl i.succ⟩, ω ⟨x, Sum.inr ()⟩) :
          bitMsgL (F := F) (L := L) (n := n) x.2.2.1)
        = (ω' ⟨x, Sum.inl 0⟩, fun i => ω' ⟨x, Sum.inl i.succ⟩, ω' ⟨x, Sum.inr ()⟩)
    refine Prod.ext (hoff _ (fun h => hx' (congrArg Sigma.fst h))) (Prod.ext ?_ ?_)
    · funext i; exact hoff _ (fun h => hx' (congrArg Sigma.fst h))
    · exact hoff _ (fun h => hx' (congrArg Sigma.fst h))
  unfold TweakablePRP.rndFun
  rw [hgx]

/-- **Block-count invariance under the pin update** (PHASE P1a.E3): for a query
`s' ≤ s`, the run's `mBlocksBit` is invariant under an off-`p` update
(`p.1 = (run ω).1.get s`).  `mBlocksBit s'` reads only query `s'`'s plain length,
which admissibility (`bitPlain_fst`) ties to the query `(run _).1.get s'`; that
query is stable by `bit_run_prefix_congr_off`.  (`bitCapValid` is defined below;
its slice invariance `bitCapValid_run_stable_of_off` wraps this.)  (Oracle: `mBlocksBit_run_stable_of_off`.) -/
theorem mBlocksBit_run_stable_of_off
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i)
    (s' : Fin q) (hs' : s' ≤ s) :
    mBlocksBit (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))) s'
      = mBlocksBit (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))) s' := by
  have hpref := (bit_run_prefix_congr_off E hE s ω ω' p hp hoff).1 s' hs'
  have hmb : ∀ ω₀ : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p,
      mBlocksBit (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω₀))) s'
        = (splitIdx ((envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω₀))).1.get s').2.2.1).1.val
            + 2 := by
    intro ω₀
    unfold mBlocksBit
    rw [bitPlain_fst _ s' ((bit_envRun_admissible E hE _).2.2 s')]
  rw [hmb ω', hmb ω, hpref]

/-! ### The virtual-last-block pin engine

The hybrid reveal entry `z₃ˢ` fuses the partial-response coordinate
(`BitVec rˢ`, part of ω) with the dummy coordinate `d₃ˢ` (`F`): jointly they
are one uniform `BitVec n` (the virtual block) plus a `BitVec rˢ` remainder
(the dummy's discarded low bits) — the explicit equivalence `bitFuseEquiv`.
`bit_joint_slice_eq` exposes the joint `(d, ω)` sampler under the dummy
extension; `uniform_pi_prod_selfloc_fused_le` then pins the virtual block. -/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 512

/-- Restoring a block's own low bits to any hybrid of it recovers the block.  (Oracle: `hybridBits_restore`.) -/
theorem hybridBits_restore {r : ℕ} (h : r ≤ n) (a : BitVec r) (k : BitVec n) :
    hybridBits (n := n) r (k.setWidth r) (hybridBits (n := n) r a k) = k := by
  have hcancel : ∀ y c : BitVec n, y ^^^ c ^^^ c = y := fun y c => by
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  show hybridBits (n := n) r a k ^^^ lowFill r (hybridBits (n := n) r a k)
      ^^^ (k.setWidth r).setWidth n = k
  rw [show lowFill (n := n) r (hybridBits (n := n) r a k) = a.setWidth n by
    unfold lowFill
    rw [setWidth_hybridBits h]]
  show ((k ^^^ lowFill r k ^^^ a.setWidth n) ^^^ a.setWidth n)
      ^^^ (k.setWidth r).setWidth n = k
  rw [hcancel (k ^^^ lowFill r k) (a.setWidth n)]
  exact hcancel k (lowFill r k)

/-- The query-side partial bits of `x` (`npˢ` on forward, `vpˢ` on inverse
queries — the reveal's low bits are their XOR with the response side).  (Oracle: `queryPart`.) -/
def queryPart (x : HQB) : BitVec (splitIdx x.2.2.1).2.val := x.2.2.2.2.2

/-- Remainder type of the fused coordinate: the dummy's discarded low bits at
the partial slot; a spectator copy of `F` elsewhere.  (Oracle: `bitRem`.) -/
def bitRem : (Σ x : HQB, BitBlockIdx (F := F) (T := T) (L := L) (n := n) x) → Type
  | ⟨_, Sum.inl _⟩ => F
  | ⟨x, Sum.inr _⟩ => BitVec (splitIdx x.2.2.1).2.val

/-- **The fused coordinate equivalence**: at the partial slot of `x`, the pair
(partial-response bits, dummy block) is equivalent to (virtual last block,
discarded dummy low bits); at full-block slots, a spectator reshuffle.  (Oracle: `bitFuseEquiv`.) -/
def bitFuseEquiv (bb : BlockBits F n) :
    ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p × F ≃ BitVec n × bitRem p
  | ⟨_, Sum.inl _⟩ =>
    ({ toFun := fun pk => (bb.toBits pk.1, pk.2)
       invFun := fun vr => (bb.toBits.symm vr.1, vr.2)
       left_inv := fun pk => Prod.ext (Equiv.symm_apply_apply _ _) rfl
       right_inv := fun vr => Prod.ext (Equiv.apply_symm_apply _ _) rfl } :
      F × F ≃ BitVec n × F)
  | ⟨x, Sum.inr _⟩ =>
    ({ toFun := fun pk =>
         (hybridBits (splitIdx x.2.2.1).2.val (queryPart x ^^^ pk.1) (bb.toBits pk.2),
          (bb.toBits pk.2).setWidth (splitIdx x.2.2.1).2.val)
       invFun := fun vr =>
         (queryPart x ^^^ vr.1.setWidth (splitIdx x.2.2.1).2.val,
          bb.toBits.symm (hybridBits (splitIdx x.2.2.1).2.val vr.2 vr.1))
       left_inv := fun pk => by
         obtain ⟨p, k⟩ := pk
         refine Prod.ext ?_ ?_
         · show queryPart x ^^^ (hybridBits (splitIdx x.2.2.1).2.val
               (queryPart x ^^^ p) (bb.toBits k)).setWidth (splitIdx x.2.2.1).2.val = p
           rw [setWidth_hybridBits (splitIdx x.2.2.1).2.isLt.le, ← BitVec.xor_assoc,
             BitVec.xor_self, BitVec.zero_xor]
         · show bb.toBits.symm (hybridBits (splitIdx x.2.2.1).2.val
               ((bb.toBits k).setWidth (splitIdx x.2.2.1).2.val)
               (hybridBits (splitIdx x.2.2.1).2.val (queryPart x ^^^ p) (bb.toBits k))) = k
           rw [hybridBits_restore (splitIdx x.2.2.1).2.isLt.le, Equiv.symm_apply_apply]
       right_inv := fun vr => by
         obtain ⟨v, ρ⟩ := vr
         refine Prod.ext ?_ ?_
         · show hybridBits (splitIdx x.2.2.1).2.val
               (queryPart x ^^^ (queryPart x ^^^ v.setWidth (splitIdx x.2.2.1).2.val))
               (bb.toBits (bb.toBits.symm
                 (hybridBits (splitIdx x.2.2.1).2.val ρ v))) = v
           rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor,
             Equiv.apply_symm_apply]
           exact hybridBits_restore (splitIdx x.2.2.1).2.isLt.le ρ v
         · show (bb.toBits (bb.toBits.symm
               (hybridBits (splitIdx x.2.2.1).2.val ρ v))).setWidth
                 (splitIdx x.2.2.1).2.val = ρ
           rw [Equiv.apply_symm_apply,
             setWidth_hybridBits (splitIdx x.2.2.1).2.isLt.le] } :
      BitVec (splitIdx x.2.2.1).2.val × F
        ≃ BitVec n × BitVec (splitIdx x.2.2.1).2.val)

/-- `bitFuseEquiv` at the partial slot, `V`-component (definitional).  (Oracle: `bitFuseEquiv_inr_fst`.) -/
theorem bitFuseEquiv_inr_fst (bb : BlockBits F n) (x : HQB)
    (p : BitVec (splitIdx x.2.2.1).2.val) (k : F) :
    (bitFuseEquiv bb ⟨x, Sum.inr ()⟩ (p, k)).1
      = hybridBits (splitIdx x.2.2.1).2.val (queryPart x ^^^ p) (bb.toBits k) := rfl

/-- **Joint-sampler exposure** (the collapse behind the virtual pin): the
dummy ideal extended mass is exactly the joint `(d, ω)` uniform mass of the
run-composed predicate.  (Oracle: `bit_joint_slice_eq`.) -/
theorem bit_joint_slice_eq (E : QQueryEnvironment HQB HMB q)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop) :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E.1).mass P
      = (Dist.uniform ((F × F × (Fin q → F)) ×
          (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1))).mass
          (fun p => P (envRun E (TweakablePRP.rndFun p.2), p.1)) := by
  classical
  rw [Dist.mass_eq_sum, Dist.mass_eq_sum]
  rw [show (∑ tz : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)),
        if P tz then (extendedTranscriptDistRep (q := q)
          bitIdealP bitIdealF bitIdealAug E.1) tz else 0)
      = ∑ t : TranscriptPrefix HQB HMB q, ∑ z : F × F × (Fin q → F),
          if P (t, z) then (extendedTranscriptDistRep (q := q)
            bitIdealP bitIdealF bitIdealAug E.1) (t, z) else 0 from
      Fintype.sum_prod_type _,
    show (∑ p : (F × F × (Fin q → F)) ×
          (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1),
        if P (envRun E (TweakablePRP.rndFun p.2), p.1) then
          Dist.uniform ((F × F × (Fin q → F)) ×
            (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) p else 0)
      = ∑ z : F × F × (Fin q → F),
          ∑ g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1,
            if P (envRun E (TweakablePRP.rndFun g), z) then
              Dist.uniform ((F × F × (Fin q → F)) ×
                (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) (z, g) else 0
      from Fintype.sum_prod_type _,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have htr : tr[q](TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T), E.1)
      = Dist.fTransform (fun g => envRun E (TweakablePRP.rndFun g))
          (Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)) :=
    deterministicTranscriptDist_functionEvaluator_eq_fTransform
      (⟨Dist.uniform (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1),
        Dist.uniform_isProbDist⟩ : Dist.ProbDist _) (fun g => TweakablePRP.rndFun g) E
  have h1 : (∑ t : TranscriptPrefix HQB HMB q,
        if P (t, z) then (extendedTranscriptDistRep (q := q)
          bitIdealP bitIdealF bitIdealAug E.1) (t, z) else 0)
      = Dist.uniform (F × F × (Fin q → F)) z *
        (Dist.fTransform (fun g => envRun E (TweakablePRP.rndFun g))
          (Dist.uniform (∀ x : HQB,
            bitMsgL (F := F) (L := L) (n := n) x.2.2.1))).mass
          (fun t => P (t, z)) := by
    rw [Dist.mass_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hp : P (t, z)
    · rw [if_pos hp, if_pos hp, bitIdealExt_apply, htr]
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [h1, Dist.mass_fTransform, Dist.mass_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hp : P (envRun E (TweakablePRP.rndFun g), z)
  · rw [if_pos hp, if_pos hp, Dist.uniform_apply, Dist.uniform_apply,
      Dist.uniform_apply, one_div_mul_one_div]
    have hc : Fintype.card ((F × F × (Fin q → F)) ×
          (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1))
        = Fintype.card (F × F × (Fin q → F)) *
          Fintype.card (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) :=
      Fintype.card_prod _ _
    rw [hc, Nat.cast_mul]
  · rw [if_neg hp, if_neg hp, mul_zero]

/-- Oracles agree away from the fiber of a coordinate.  (Oracle: `bit_oracle_agree_off`.) -/
theorem bit_oracle_agree_off
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hoff : ∀ i, i ≠ p → ω i = ω' i) :
    ∀ x : HQB, x ≠ p.1 → TweakablePRP.rndFun (bitOmegaEquiv.symm ω) x
      = TweakablePRP.rndFun (bitOmegaEquiv.symm ω') x := by
  intro x hx
  have hgx : bitOmegaEquiv.symm ω x = bitOmegaEquiv.symm ω' x := by
    show ((ω ⟨x, Sum.inl 0⟩, fun i => ω ⟨x, Sum.inl i.succ⟩, ω ⟨x, Sum.inr ()⟩) :
          bitMsgL (F := F) (L := L) (n := n) x.2.2.1)
        = (ω' ⟨x, Sum.inl 0⟩, fun i => ω' ⟨x, Sum.inl i.succ⟩, ω' ⟨x, Sum.inr ()⟩)
    refine Prod.ext (hoff _ (fun h => hx (congrArg Sigma.fst h)))
      (Prod.ext ?_ ?_)
    · funext i
      exact hoff _ (fun h => hx (congrArg Sigma.fst h))
    · exact hoff _ (fun h => hx (congrArg Sigma.fst h))
  unfold TweakablePRP.rndFun
  rw [hgx]

/-- Run-prefix stability under agreement away from a coordinate over the
run's `s`-th query.  (Oracle: `bit_run_prefix_congr`.) -/
theorem bit_run_prefix_congr (E : QQueryEnvironment HQB HMB q)
    (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i) :
    (∀ k : Fin q, k ≤ s →
      (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))).1.get k
        = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get k) ∧
    (∀ k : Fin q, k < s →
      (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))).2.get k
        = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).2.get k) := by
  refine envRun_prefix_congr E _ _ s (hE _ (envRun_consistent E _)).1 ?_
  intro x hx
  exact bit_oracle_agree_off ω ω' p hoff x (fun h => hx (by rw [← hp]; exact h))

/-- Response full blocks of the run are ω-coordinates (standalone form).  (Oracle: `bit_run_totBlock_coord`.) -/
theorem bit_run_totBlock_coord (E : QQueryEnvironment HQB HMB q) (s : Fin q)
    (ω₀ : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) (x : HQB)
    (b : Fin ((splitIdx x.2.2.1).1.val + 1))
    (hp : (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω₀))).1.get s = x) :
    totBlockB ((envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω₀))).2.get s) b.val
      = ω₀ ⟨x, Sum.inl b⟩ := by
  subst hp
  exact (bit_envRun_totBlock E (bitOmegaEquiv.symm ω₀) s b).trans
    (congrFun (bitOmegaEquiv.apply_symm_apply ω₀)
      ⟨(envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω₀))).1.get s, Sum.inl b⟩)

/-- The transcript-determined low bits of the run's `s`-th last block:
query-side partial XOR the partial ω-coordinate of the run's query.  (Oracle: `bitLowBits_run`.) -/
theorem bitLowBits_run (E : QQueryEnvironment HQB HMB q)
    (g : ∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1) (s : Fin q) :
    bitLowBits (envRun E (TweakablePRP.rndFun g)) s
      = queryPart ((envRun E (TweakablePRP.rndFun g)).1.get s)
        ^^^ (g ((envRun E (TweakablePRP.rndFun g)).1.get s)).2.2 := by
  have hresp := bit_envRun_resp E g s
  have hr : (splitIdx ((envRun E (TweakablePRP.rndFun g)).1.get s).2.2.1).2.val ≤ n :=
    (splitIdx ((envRun E (TweakablePRP.rndFun g)).1.get s).2.2.1).2.isLt.le
  unfold bitLowBits
  rcases hd : ((envRun E (TweakablePRP.rndFun g)).1.get s).1 with _ | _
  · rw [bitPlain_fwd _ s hd, bitCipher_fwd _ s hd, hresp]
    show ((queryPart ((envRun E (TweakablePRP.rndFun g)).1.get s)).setWidth n
        ^^^ ((g ((envRun E (TweakablePRP.rndFun g)).1.get s)).2.2).setWidth n).setWidth _ = _
    rw [← setWidth_xor_of_le hr, setWidth_setWidth_of_le hr]
  · rw [bitPlain_inv _ s hd, bitCipher_inv _ s hd, hresp]
    show (((g ((envRun E (TweakablePRP.rndFun g)).1.get s)).2.2).setWidth n
        ^^^ (queryPart ((envRun E (TweakablePRP.rndFun g)).1.get s)).setWidth n).setWidth _ = _
    rw [← setWidth_xor_of_le hr, setWidth_setWidth_of_le hr, BitVec.xor_comm]

/-- **Conditional virtual-last-block pin bound** (PHASE P1b4b V2; the slice twin
of `bit_virtualPin_le`): the same fused pin of the hybrid reveal entry `z₃ˢ`, but
restricted to a transcript-only validity slice `S` (an off-located cylinder of
the run, `hSoff`) containing the event (`hVP`).  The conclusion is the
conditional `mass P ≤ (1/N) · mass (S∘fst)` over the hybrid ideal extension — the
slice rides through as the conditioning weight.  Unlike the classic
`bit_respPin_cond_le`, the pin runs on the FUSED `(ω, dummy)` sampler via
`bit_joint_slice_eq`, so the slice is served by the genuine fused slice engine
`uniform_pi_prod_selfloc_fused_slice_le`; the slice's dummy-coordinate invariance
is automatic (the run reads `ω` only).  (Oracle: `bit_virtualPin_cond_le`.) -/
theorem bit_virtualPin_cond_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop)
    (hVP : ∀ t z, P (t, z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hpin : ∀ (d d' : F × F × (Fin q → F)) t t',
      TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      d.1 = d'.1 → d.2.1 = d'.2.1 → (∀ r : Fin q, r ≠ s → d.2.2 r = d'.2.2 r) →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      P (t, bitHybrid bb t d) → P (t', bitHybrid bb t' d') →
      (bitHybrid bb t d).2.2 s = (bitHybrid bb t' d').2.2 s) :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb)
        E.1).mass P
      ≤ (Fintype.card F : NNReal)⁻¹ *
        (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb)
          E.1).mass (fun td => S td.1) := by
  classical
  rw [Dist.mass_congr _ (fun tz => iff_self_and.mpr (fun hp => hVP tz.1 tz.2 hp))]
  rw [bitIdealExtH_mass bb E.1 (fun tz => P tz ∧ S tz.1),
    bitIdealExtH_mass bb E.1 (fun td => S td.1),
    bit_joint_slice_eq E _, bit_joint_slice_eq E _]
  rw [uniform_mass_equiv
      ((Equiv.prodComm (F × F × (Fin q → F))
          (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)).trans
        (Equiv.prodCongr (bitOmegaEquiv (F := F) (T := T) (L := L) (n := n))
          (zPackEquiv (F := F) (q := q)))) _,
    uniform_mass_equiv
      ((Equiv.prodComm (F × F × (Fin q → F))
          (∀ x : HQB, bitMsgL (F := F) (L := L) (n := n) x.2.2.1)).trans
        (Equiv.prodCongr (bitOmegaEquiv (F := F) (T := T) (L := L) (n := n))
          (zPackEquiv (F := F) (q := q)))) _]
  have hcard : (Fintype.card F : NNReal)⁻¹ = (Fintype.card (BitVec n) : NNReal)⁻¹ := by
    rw [Fintype.card_congr bb.toBits]
  rw [hcard]
  set run : (∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) →
      TranscriptPrefix HQB HMB q :=
    fun ω => envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)) with hrundef
  set loc : (∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p) →
      Σ x : HQB, BitBlockIdx x :=
    fun ω => ⟨(run ω).1.get s, Sum.inr ()⟩ with hlocdef
  have hloc_stable : ∀ ω v, loc (Function.update ω (loc ω) v) = loc ω := by
    intro ω v
    have h1 := (bit_run_prefix_congr E hE s ω (Function.update ω (loc ω) v)
      (loc ω) rfl (fun i hi => (Function.update_of_ne hi _ _).symm)).1 s le_rfl
    simp only [hlocdef]
    rw [show (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm
        (Function.update ω (loc ω) v)))).1.get s = (run ω).1.get s from h1]
  have hvirt : ∀ (ω : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (w : (Bool ⊕ Fin q) → F),
      bb.toBits ((bitHybrid bb (run ω) (zPackEquiv.symm w)).2.2 s)
        = (bitFuseEquiv bb (loc ω) (ω (loc ω), w (Sum.inr s))).1 := by
    intro ω w
    show bb.toBits (bitHybridBlock bb (run ω) s ((zPackEquiv.symm w).2.2 s)) = _
    rw [bitHybridBlock, Equiv.apply_symm_apply]
    show hybridBits (splitIdx ((run ω).1.get s).2.2.1).2.val
        (bitLowBits (run ω) s) (bb.toBits (w (Sum.inr s))) = _
    rw [bitLowBits_run E (bitOmegaEquiv.symm ω) s,
      bitFuseEquiv_inr_fst bb ((run ω).1.get s)]
    rfl
  refine uniform_pi_prod_selfloc_fused_slice_le
    (W := fun _ : Bool ⊕ Fin q => F) _ _ loc (Sum.inr s) (bitFuseEquiv bb)
    (Classical.arbitrary _) hloc_stable ?_ ?_
  · -- (a) the slice is a cylinder in the fused pair's coordinates: it reads only
    -- the run of `ω`, invariant under the located update (`hSoff`); the dummy
    -- coordinate is irrelevant (the run does not read it)
    intro p a b
    exact hSoff p.1 (Function.update p.1 (loc p.1) a) (loc p.1) rfl
      (fun i hi => (Function.update_of_ne hi _ _).symm)
  · -- (b) the event pins the virtual block (identical to the base lemma; the
    -- slice hypotheses are spectators)
    intro ω w ω' w' hli hoffω hoffw hPω hPω' _ _
    have hadm : TweakablePRP.admissible E (run ω) := bit_envRun_admissible E hE _
    have hadm' : TweakablePRP.admissible E (run ω') := bit_envRun_admissible E hE _
    have hstab' := bit_run_prefix_congr E hE s ω ω' (loc ω) rfl hoffω
    have hxs : (run ω').1.get s = (run ω).1.get s := hstab'.1 s le_rfl
    have hblocks : ∀ b : ℕ, totBlockB ((run ω).2.get s) b
        = totBlockB ((run ω').2.get s) b := by
      intro b
      by_cases hlt : b < (splitIdx ((run ω).1.get s).2.2.1).1.val + 1
      · rw [bit_run_totBlock_coord E s ω ((run ω).1.get s) ⟨b, hlt⟩ rfl,
          bit_run_totBlock_coord E s ω' ((run ω).1.get s) ⟨b, hlt⟩ hxs]
        refine hoffω _ (fun h => ?_)
        have hsnd : (Sum.inl (⟨b, hlt⟩ : Fin _) :
            BitBlockIdx ((run ω).1.get s)) = Sum.inr () :=
          eq_of_heq (Sigma.mk.inj h).2
        simp at hsnd
      · have hout : (splitIdx ((run ω).2.get s).1).1.val + 1 ≤ b := by
          have hlen := hadm.2.2 s
          rw [hlen]
          omega
        have hout' : (splitIdx ((run ω').2.get s).1).1.val + 1 ≤ b := by
          have hlen' := hadm'.2.2 s
          rw [hlen', hxs]
          omega
        rw [totBlockB_of_ge _ _ hout, totBlockB_of_ge _ _ hout']
    have hd1 : (zPackEquiv.symm w).1 = ((zPackEquiv (F := F) (q := q)).symm w').1 :=
      hoffw (Sum.inl false) (by simp)
    have hd2 : (zPackEquiv.symm w).2.1 = ((zPackEquiv (F := F) (q := q)).symm w').2.1 :=
      hoffw (Sum.inl true) (by simp)
    have hd3 : ∀ r : Fin q, r ≠ s →
        (zPackEquiv.symm w).2.2 r = ((zPackEquiv (F := F) (q := q)).symm w').2.2 r :=
      fun r hr => hoffw (Sum.inr r) (by simp [hr])
    have hz := hpin (zPackEquiv.symm w) (zPackEquiv.symm w') (run ω) (run ω')
      hadm hadm' hd1 hd2 hd3
      (fun k hk => (hstab'.1 k hk).symm) (fun k hk => (hstab'.2 k hk).symm)
      hblocks hPω hPω'
    calc (bitFuseEquiv bb (loc ω) (ω (loc ω), w (Sum.inr s))).1
        = bb.toBits ((bitHybrid bb (run ω) (zPackEquiv.symm w)).2.2 s) :=
          (hvirt ω w).symm
      _ = bb.toBits ((bitHybrid bb (run ω') (zPackEquiv.symm w')).2.2 s) :=
          congrArg bb.toBits hz
      _ = (bitFuseEquiv bb (loc ω') (ω' (loc ω'), w' (Sum.inr s))).1 := hvirt ω' w'

/-- **Solved-form conditional virtual pin** (PHASE P1b4b V2; slice twin of
`bit_virtualPin_solved_le`): the solved-expression interface for `z₃ˢ`,
restricted to the validity slice `S`.  (Oracle: `bit_virtualPin_cond_solved_le`.) -/
theorem bit_virtualPin_cond_solved_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop)
    (rhs : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hVP : ∀ t z, P (t, z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hsolve : ∀ d t, TweakablePRP.admissible E t → P (t, bitHybrid bb t d) →
      (bitHybrid bb t d).2.2 s = rhs d t)
    (hcongr : ∀ (d d' : F × F × (Fin q → F)) t t',
      TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      d.1 = d'.1 → d.2.1 = d'.2.1 → (∀ r : Fin q, r ≠ s → d.2.2 r = d'.2.2 r) →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      rhs d t = rhs d' t') :
    (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb)
        E.1).mass P
      ≤ (Fintype.card F : NNReal)⁻¹ *
        (extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb)
          E.1).mass (fun td => S td.1) := by
  refine bit_virtualPin_cond_le bb E hE s P S hVP hSoff ?_
  intro d d' t t' hadm hadm' hd1 hd2 hd3 hq hr hblocks hP hP'
  rw [hsolve d t hadm hP, hsolve d' t' hadm' hP']
  exact hcongr d d' t t' hadm hadm' hd1 hd2 hd3 hq hr hblocks

/-! ### Congruence toolkit for the leaves (bit `RespPinCtx`-era lemmas) -/

/-- `bitPlain` reads only the query and response at its index.  (Oracle: `bitPlain_congr`.) -/
theorem bitPlain_congr {t t' : TranscriptPrefix HQB HMB q} {r : Fin q}
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    bitPlain t r = bitPlain t' r := by
  unfold bitPlain
  rw [hq, hr]

/-- `bitCipher` reads only the query and response at its index.  (Oracle: `bitCipher_congr`.) -/
theorem bitCipher_congr {t t' : TranscriptPrefix HQB HMB q} {r : Fin q}
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    bitCipher t r = bitCipher t' r := by
  unfold bitCipher
  rw [hq, hr]

/-- Matching forward queries have matching inferred plaintexts.  (Oracle: `bitPlain_eq_of_fwd`.) -/
theorem bitPlain_eq_of_fwd {t t' : TranscriptPrefix HQB HMB q} {s : Fin q}
    (hqs : t.1.get s = t'.1.get s) (hdir : (t.1.get s).1 = QueryDir.fwd) :
    bitPlain t s = bitPlain t' s := by
  rw [bitPlain_fwd t s hdir,
    bitPlain_fwd t' s (show (t'.1.get s).1 = QueryDir.fwd by rw [← hqs]; exact hdir),
    hqs]

/-- Matching inverse queries have matching inferred ciphertexts.  (Oracle: `bitCipher_eq_of_inv`.) -/
theorem bitCipher_eq_of_inv {t t' : TranscriptPrefix HQB HMB q} {s : Fin q}
    (hqs : t.1.get s = t'.1.get s) (hdir : (t.1.get s).1 = QueryDir.inv) :
    bitCipher t s = bitCipher t' s := by
  rw [bitCipher_inv t s hdir,
    bitCipher_inv t' s (show (t'.1.get s).1 = QueryDir.inv by rw [← hqs]; exact hdir),
    hqs]

/-- `MMvB` reads only the query and response at its index (two-transcript
version of `MMvB_congr`).  (Oracle: `MMvB_congr`.) -/
theorem MMvB_congr₂ (z : F × F × (Fin q → F)) {t t' : TranscriptPrefix HQB HMB q}
    {r : Fin q} (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    MMvB bb Hf z t r = MMvB bb Hf z t' r := by
  have hT : bitTweak t r = bitTweak t' r := by
    unfold bitTweak
    rw [hq]
  have hP : bitPlain t r = bitPlain t' r := bitPlain_congr hq hr
  show hashBlkB bb Hf z (bitTweak t r) (bitPlain t r)
    = hashBlkB bb Hf z (bitTweak t' r) (bitPlain t' r)
  rw [hT, hP]

/-- `UUvB` reads only the query and response at its index.  (Oracle: `UUvB_congr`.) -/
theorem UUvB_congr₂ (z : F × F × (Fin q → F)) {t t' : TranscriptPrefix HQB HMB q}
    {r : Fin q} (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    UUvB bb Hf z t r = UUvB bb Hf z t' r := by
  have hT : bitTweak t r = bitTweak t' r := by
    unfold bitTweak
    rw [hq]
  have hC : bitCipher t r = bitCipher t' r := bitCipher_congr hq hr
  show hashBlkB bb Hf z (bitTweak t r) (bitCipher t r)
    = hashBlkB bb Hf z (bitTweak t' r) (bitCipher t' r)
  rw [hT, hC]

/-- `SjvB` reads only the query and response at its index.  (Oracle: `SjvB_congr`.) -/
theorem SjvB_congr₂ (z : F × F × (Fin q → F)) {t t' : TranscriptPrefix HQB HMB q}
    {r : Fin q} (j : ℕ) (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    SjvB bb be Hf z t r j = SjvB bb be Hf z t' r j := by
  unfold SjvB SvB
  rw [MMvB_congr₂ bb Hf z hq hr, UUvB_congr₂ bb Hf z hq hr]

/-- `YjvB` reads only the query and response at its index.  (Oracle: `YjvB_congr`.) -/
theorem YjvB_congr₂ {t t' : TranscriptPrefix HQB HMB q} {r : Fin q} (j : ℕ)
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    YjvB t r j = YjvB t' r j := by
  unfold YjvB bitTailN bitTailV
  rw [bitPlain_congr hq hr, bitCipher_congr hq hr]

/-- On matching forward queries `MMˢ` agrees.  (Oracle: `MMvB_eq_of_fwd`.) -/
theorem MMvB_eq_of_fwd (z : F × F × (Fin q → F)) {t t' : TranscriptPrefix HQB HMB q}
    {s : Fin q} (hqs : t.1.get s = t'.1.get s) (hdir : (t.1.get s).1 = QueryDir.fwd) :
    MMvB bb Hf z t s = MMvB bb Hf z t' s := by
  have hT : bitTweak t s = bitTweak t' s := by
    unfold bitTweak
    rw [hqs]
  have hP : bitPlain t s = bitPlain t' s := bitPlain_eq_of_fwd hqs hdir
  show hashBlkB bb Hf z (bitTweak t s) (bitPlain t s)
    = hashBlkB bb Hf z (bitTweak t' s) (bitPlain t' s)
  rw [hT, hP]

/-- On matching inverse queries `UUˢ` agrees.  (Oracle: `UUvB_eq_of_inv`.) -/
theorem UUvB_eq_of_inv (z : F × F × (Fin q → F)) {t t' : TranscriptPrefix HQB HMB q}
    {s : Fin q} (hqs : t.1.get s = t'.1.get s) (hdir : (t.1.get s).1 = QueryDir.inv) :
    UUvB bb Hf z t s = UUvB bb Hf z t' s := by
  have hT : bitTweak t s = bitTweak t' s := by
    unfold bitTweak
    rw [hqs]
  have hC : bitCipher t s = bitCipher t' s := bitCipher_eq_of_inv hqs hdir
  show hashBlkB bb Hf z (bitTweak t s) (bitCipher t s)
    = hashBlkB bb Hf z (bitTweak t' s) (bitCipher t' s)
  rw [hT, hC]

theorem UUvB_z_congr {z z' : F × F × (Fin q → F)} (hz : z.1 = z'.1)
    (t : TranscriptPrefix HQB HMB q) (r : Fin q) :
    UUvB bb Hf z t r = UUvB bb Hf z' t r := by
  unfold UUvB hashBlkB
  rw [hz]

/-- The hybrid reveal preserves `h̄` and `L` (definitional).  (Oracle: `bitHybrid_fst`.) -/
theorem bitHybrid_fst (t : TranscriptPrefix HQB HMB q) (d : F × F × (Fin q → F)) :
    (bitHybrid bb t d).1 = d.1 := rfl

/-- `Yⱼ` in the block view (at a nonzero index `j`, mirror `Yjv_eq_totBlock`).  (Oracle: `YjvB_eq_totBlockB`.) -/
theorem YjvB_eq_totBlockB (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : ℕ)
    (hj : j ≠ 0) :
    YjvB t s (j - 1)
      = totBlockB (bitPlain t s) j + totBlockB (bitCipher t s) j := by
  unfold YjvB bitTailN bitTailV totBlockB
  rw [show j = (j - 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
  simp only [Nat.add_sub_cancel]

/-- `bitHybridBlock` reads only the query and the plain/cipher pair at its
index.  (Oracle: `bitHybridBlock_congr`.) -/
theorem bitHybridBlock_congr {t t' : TranscriptPrefix HQB HMB q} {r : Fin q}
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) (w : F) :
    bitHybridBlock bb t r w = bitHybridBlock bb t' r w := by
  show (fun (x : HQB) (pl ci : HMB) => bb.toBits.symm
      (hybridBits (splitIdx x.2.2.1).2.val
        ((pl.2.2.2.setWidth n ^^^ ci.2.2.2.setWidth n).setWidth
          (splitIdx x.2.2.1).2.val)
        (bb.toBits w)))
      (t.1.get r) (bitPlain t r) (bitCipher t r)
    = (fun (x : HQB) (pl ci : HMB) => bb.toBits.symm
      (hybridBits (splitIdx x.2.2.1).2.val
        ((pl.2.2.2.setWidth n ^^^ ci.2.2.2.setWidth n).setWidth
          (splitIdx x.2.2.1).2.val)
        (bb.toBits w)))
      (t'.1.get r) (bitPlain t' r) (bitCipher t' r)
  rw [hq, bitPlain_congr hq hr, bitCipher_congr hq hr]

end BitResponsePin

/-! ### Stage-5 atoms: uniform-triple engines and the pair-sum closer

The generic mass engines the stage-5 dispatch consumes: the first-coordinate functional
twin of `uniform_triple_middle_functional`, the Fubini slice bound over the first
coordinate of a uniform product, and the ordered-pair sum closer
`Σ_{r<s} aᵣ·aₛ ≤ C(Σa, 2)` (paper §3.4.3). -/

section BitStage5Leaves

variable (bb : BlockBits F n) (be : BinEnc F L) (Hf : HashFamily F T (L + 2))

/-- Local shorthand for the **hybrid** ideal extended transcript distribution (the stage-5
union-bound carrier). -/
local notation:max "bitExtH" E:max =>
  extendedTranscriptDistRep (q := q) bitIdealP bitIdealF (bitIdealAugH bb) E

/-! ### New reveal-shape leaves (uniform-triple atoms) -/

/-- `h̄ = c` (transcript-determined target): `≤ 1/N`.  (Oracle: `revealhbarB_const_le`.) -/
theorem revealhbarB_const_le (c : F) :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun z => z.1 = c)
      ≤ (Fintype.card F : NNReal)⁻¹ :=
  uniform_triple_fst_functional _ (fun _ _ _ _ h1 h2 => h1.trans h2.symm)

/-- `L = c` (transcript-determined target): `≤ 1/N`.  (Oracle: `revealLB_const_le`.) -/
theorem revealLB_const_le (c : F) :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun z => z.2.1 = c)
      ≤ (Fintype.card F : NNReal)⁻¹ :=
  uniform_triple_middle_functional _ (fun _ _ _ _ h1 h2 => h1.trans h2.symm)

/-- `h̄ = L`: `≤ 1/N` (pins the middle coordinate).  (Oracle: `revealhbarB_L_le`.) -/
theorem revealhbarB_L_le :
    (Dist.uniform (F × F × (Fin q → F))).mass (fun z => z.1 = z.2.1)
      ≤ (Fintype.card F : NNReal)⁻¹ :=
  uniform_triple_middle_functional _ (fun _ _ _ _ h1 h2 => h1.symm.trans h2)

/-- `L = UUˢ`: `≤ 1/N` (`UUvB` reads only `h̄`, so the middle coordinate is pinned).
(Oracle: `revealLB_UUvB_le`.) -/
theorem revealLB_UUvB_le (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    (Dist.uniform (F × F × (Fin q → F))).mass
        (fun z => z.2.1 = UUvB bb Hf z t s)
      ≤ (Fintype.card F : NNReal)⁻¹ := by
  refine uniform_triple_middle_functional _ (fun a b b' c h1 h2 => ?_)
  have hc : UUvB bb Hf (a, b, c) t s = UUvB bb Hf (a, b', c) t s := rfl
  exact h1.trans (hc.trans h2.symm)

/-! ### Counterfactual pointless exclusion (paper p. 13, bit level)

Mirrors Part 1's `io_share_false` chain at the bit carriers: in an admissible transcript
of a `TweakablePRP.NP`-respecting environment, a later query never shares its full
`(tweak, input side)` with an earlier query — response surgery (`envReplay`) plus the
filter's pinned-pair injectivity (`bit_shares_eq`; the oracle routes through its
`lpNPV`/`facIO` factorization, the consolidated `TweakablePRP.NP` filter gives the pinned pair
directly). -/

/-- The filter's pinned pair *is* the bit `(plaintext, ciphertext)` extraction — bit twin
of `pinnedIO_get` (instance of the `TweakablePRP.pinnedIO` layer; subsumes the oracle's
`bitIO_fst_heq_plain`/`bitIO_snd_heq_cipher` transports). -/
theorem bit_pinnedIO_get (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    TweakablePRP.pinnedIO (t.1.get s) (t.2.get s) = (bitPlain t s, bitCipher t s) := by
  unfold TweakablePRP.pinnedIO bitPlain bitCipher; rcases (t.1.get s).1 <;> rfl

/-- **Shared plaintext + shared ciphertext ⟹ same step** (under the `TweakablePRP.NP` filter, both
responses length-matched) — bit twin of `shares_eq`.  (Oracle:
`bit_queries_eq_of_shares`, whose query-equality conclusion the filter's injectivity turns
into `r = s`.) -/
theorem bit_shares_eq (t : TranscriptPrefix HQB HMB q) (hnp : TweakablePRP.NP t) {r s : Fin q}
    (hmr : (t.2.get r).1 = (t.1.get r).2.2.1) (hms : (t.2.get s).1 = (t.1.get s).2.2.1)
    (hT : bitTweak t r = bitTweak t s) (hP : bitPlain t r = bitPlain t s)
    (hC : bitCipher t r = bitCipher t s) : r = s :=
  hnp.2 r s hT hmr hms (by rw [bit_pinnedIO_get, bit_pinnedIO_get, hP, hC])

/-- **Counterfactual exclusion, unified I/O side**: a later query `s` never shares its
`(tweak, input)` with an earlier `r` — plaintext for a forward `s`, ciphertext for an
inverse one.  (Oracle: `bit_io_share_false`.) -/
theorem bit_io_share_false
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (t : TranscriptPrefix HQB HMB q)
    (hadm : TweakablePRP.admissible E t) {r s : Fin q} (hrs : r < s)
    (hT : bitTweak t r = bitTweak t s)
    (hshare : ((t.1.get s).1 = QueryDir.fwd ∧ bitPlain t r = bitPlain t s)
            ∨ ((t.1.get s).1 = QueryDir.inv ∧ bitCipher t r = bitCipher t s)) :
    False := by
  obtain ⟨hnp, hcon, hmatch⟩ := hadm
  -- splice value: `r`'s ciphertext on a forward `s`, `r`'s plaintext on an inverse one
  set v : HMB := match (t.1.get s).1 with
    | QueryDir.fwd => bitCipher t r
    | QueryDir.inv => bitPlain t r with hvdef
  have hnp' : TweakablePRP.NP (envReplay E (t.2.set s v)) := hE _ (envReplay_consistent E _)
  set t' := envReplay E (t.2.set s v) with ht'def
  -- queries through step `s` are unchanged; responses change only at `s`
  have hq' : ∀ k : Fin q, k ≤ s → t'.1.get k = t.1.get k := by
    intro k hk
    have h1 : t'.1.get k = envReplayQuery E (t.2.set s v) k := List.Vector.get_ofFn _ _
    rw [h1, envReplay_set_query_eq E t.2 s _ hk, ← consistent_queries_eq E hcon k]
  have hr'ne : ∀ k : Fin q, k ≠ s → t'.2.get k = t.2.get k := fun k hk =>
    List.Vector.get_set_of_ne (Ne.symm hk) _
  have hr's : t'.2.get s = v := List.Vector.get_set_same t.2 s _
  -- splice-independent transfers at `r`, the shared tweak, and `r`'s length match
  have hplain'r : bitPlain t' r = bitPlain t r := by
    unfold bitPlain
    rw [hq' r hrs.le]
    rcases hd : (t.1.get r).1 with _ | _
    · rfl
    · exact hr'ne r (ne_of_lt hrs)
  have hcipher'r : bitCipher t' r = bitCipher t r := by
    unfold bitCipher
    rw [hq' r hrs.le]
    rcases hd : (t.1.get r).1 with _ | _
    · exact hr'ne r (ne_of_lt hrs)
    · rfl
  have htweak' : bitTweak t' r = bitTweak t' s := by
    unfold bitTweak
    rw [hq' r hrs.le, hq' s le_rfl]
    exact hT
  have hmr' : (t'.2.get r).1 = (t'.1.get r).2.2.1 := by
    rw [hr'ne r (ne_of_lt hrs), hq' r hrs.le]
    exact hmatch r
  -- direction-specific closing: `r` and `s` share plaintext AND ciphertext in `t'`
  rcases hshare with ⟨hds, hP⟩ | ⟨hds, hC⟩
  · -- forward: `s` shares `(tweak, plaintext)`; splice = `r`'s ciphertext
    have hvs : v = bitCipher t r := by rw [hvdef, hds]
    have hplain's : bitPlain t' s = bitPlain t s := by
      unfold bitPlain
      rw [hq' s le_rfl]
      rcases hd : (t.1.get s).1 with _ | _
      · rfl
      · exact QueryDir.noConfusion (hds.symm.trans hd)
    have hcipher's : bitCipher t' s = v := by
      unfold bitCipher
      rw [hq' s le_rfl]
      rcases hd : (t.1.get s).1 with _ | _
      · exact hr's
      · exact QueryDir.noConfusion (hds.symm.trans hd)
    have hms' : (t'.2.get s).1 = (t'.1.get s).2.2.1 := by
      rw [hr's, hq' s le_rfl, hvs, bitCipher_fst t r (hmatch r),
        ← bitPlain_fst t r (hmatch r), hP, bitPlain_fst t s (hmatch s)]
    exact absurd
      (bit_shares_eq t' hnp' hmr' hms' htweak'
        (hplain'r.trans (hP.trans hplain's.symm))
        (hcipher'r.trans (hcipher's.trans hvs).symm))
      (ne_of_lt hrs)
  · -- inverse: `s` shares `(tweak, ciphertext)`; splice = `r`'s plaintext
    have hvs : v = bitPlain t r := by rw [hvdef, hds]
    have hcipher's : bitCipher t' s = bitCipher t s := by
      unfold bitCipher
      rw [hq' s le_rfl]
      rcases hd : (t.1.get s).1 with _ | _
      · exact QueryDir.noConfusion (hds.symm.trans hd)
      · rfl
    have hplain's : bitPlain t' s = v := by
      unfold bitPlain
      rw [hq' s le_rfl]
      rcases hd : (t.1.get s).1 with _ | _
      · exact QueryDir.noConfusion (hds.symm.trans hd)
      · exact hr's
    have hms' : (t'.2.get s).1 = (t'.1.get s).2.2.1 := by
      rw [hr's, hq' s le_rfl, hvs, bitPlain_fst t r (hmatch r),
        ← bitCipher_fst t r (hmatch r), hC, bitCipher_fst t s (hmatch s)]
    exact absurd
      (bit_shares_eq t' hnp' hmr' hms' htweak'
        (hplain'r.trans (hplain's.trans hvs).symm)
        (hcipher'r.trans (hC.trans hcipher's.symm)))
      (ne_of_lt hrs)

/-- **Plaintext-side exclusion**: a later *forward* query never shares its
`(tweak, plaintext)` with an earlier query.  (Oracle: `bit_plain_share_false`.) -/
theorem bit_plain_share_false
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (t : TranscriptPrefix HQB HMB q)
    (hadm : TweakablePRP.admissible E t) {r s : Fin q} (hrs : r < s)
    (hds : (t.1.get s).1 = QueryDir.fwd)
    (hT : bitTweak t r = bitTweak t s) (hP : bitPlain t r = bitPlain t s) :
    False :=
  bit_io_share_false E hE t hadm hrs hT (Or.inl ⟨hds, hP⟩)

/-- **Ciphertext-side exclusion**: the mirror for a later *inverse* query.  (Oracle:
`bit_cipher_share_false`.) -/
theorem bit_cipher_share_false
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (t : TranscriptPrefix HQB HMB q)
    (hadm : TweakablePRP.admissible E t) {r s : Fin q} (hrs : r < s)
    (hds : (t.1.get s).1 = QueryDir.inv)
    (hT : bitTweak t r = bitTweak t s) (hC : bitCipher t r = bitCipher t s) :
    False :=
  bit_io_share_false E hE t hadm hrs hT (Or.inr ⟨hds, hC⟩)

/-! ### Fixed-cap embedding (mirror `drInclude`/`DfullFix`/`RfullFix`)

The `t`-dependent index `DRIdxBit t` embeds in the fixed cap `Bool ⊕ Fin q × Fin (L + 2)`
(block indices run to `ℓˢ + 1 ≤ L`, so `L + 2` strictly caps them); Part 1's `pairRank`/
`capRank` and their order lemmas are reused verbatim at width `L + 2` (they are
`L`-parametric).  The per-query budget bridges (`dˢ` and `σ_m ≤ σ + 2`) feed the phase-P1
σ-accounting. -/

/-- Per-query block count is within the fixed cap: `mˢ = ℓˢ + 2 ≤ L + 2`.  (Oracle:
`mBlocksBit_le_cap`.) -/
theorem mBlocksBit_le_cap (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    mBlocksBit t s ≤ L + 2 := by
  have h := (splitIdx (bitPlain t s).1).1.isLt
  unfold mBlocksBit
  omega

/-- **The `dˢ` bridge**: `degB (bitTweak t s) mˢ ≤ bitD twBlocks t s`, under the honest
degree↔block-count hypothesis `hdegB : degB t' k ≤ k + twBlocks t'` — what makes the sharp
green weights per-query.  (Oracle: `bit_degB_le_bitD`.) -/
theorem bit_degB_le_bitD (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) :
    bitMsgDeg Hfs (bitTweak t s) (bitPlain t s) ≤ bitD twBlocks t s := by
  have h := hdegB (bitTweak t s)
    (1 + (splitIdx (bitPlain t s).1).1.val
      + (if (splitIdx (bitPlain t s).1).2.val = 0 then 0 else 1))
  unfold bitMsgDeg bitD mBlocksBit
  split_ifs at h ⊢ <;> omega

/-- **The `σ_m ≤ σ + 2` bridge** (feeds the summation's `hle`): the inferred-index count
`σ_m t = 2 + Σ_s mˢ` is within `2` of the block budget `σ⁺_D t = Σ_s dˢ`, because
`dˢ = mˢ + ⌈|Tˢ|/n⌉ ≥ mˢ` per query.  (Oracle: `sigmaMBit_le_sigmaDBit_add_two`.) -/
theorem sigmaMBit_le_sigmaDBit_add_two (twBlocks : T → ℕ)
    (t : TranscriptPrefix HQB HMB q) :
    sigmaMBit t ≤ sigmaDBit twBlocks t + 2 := by
  have hmono : ∑ s : Fin q, mBlocksBit t s ≤ ∑ s : Fin q, bitD twBlocks t s :=
    Finset.sum_le_sum fun s _ => Nat.le_add_right _ _
  unfold sigmaMBit sigmaDBit
  omega

/-- Injective embedding `DRIdxBit t ↪ Bool ⊕ Fin q × Fin (L + 2)`.  (Oracle:
`drIncludeBit`.) -/
def drIncludeBit (t : TranscriptPrefix HQB HMB q) :
    DRIdxBit (L := L) (n := n) t → Bool ⊕ Fin q × Fin (L + 2)
  | Sum.inl b => Sum.inl b
  | Sum.inr ⟨s, j⟩ =>
      Sum.inr (s, ⟨j.val, lt_of_lt_of_le j.isLt (mBlocksBit_le_cap t s)⟩)

/-- (Oracle: `drIncludeBit_injective`.) -/
theorem drIncludeBit_injective (t : TranscriptPrefix HQB HMB q) :
    Function.Injective (drIncludeBit (L := L) (n := n) t) := by
  rintro (b | ⟨s, j⟩) (b' | ⟨s', j'⟩) h <;>
    simp only [drIncludeBit, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      Fin.mk.injEq, reduceCtorEq] at h
  · rw [h]
  · obtain ⟨rfl, hj⟩ := h
    exact congrArg (fun z => Sum.inr (⟨s, z⟩ : Σ s : Fin q, Fin (mBlocksBit t s)))
      (Fin.ext hj)

/-- Decidable cap-index validity for `t` (mirror `capValid`).  (Oracle: `bitCapValid`.) -/
def bitCapValid (t : TranscriptPrefix HQB HMB q) :
    (Bool ⊕ Fin q × Fin (L + 2)) → Prop
  | Sum.inl _ => True
  | Sum.inr ⟨s, j⟩ => j.val < mBlocksBit t s

instance bitCapValid_decidable (t : TranscriptPrefix HQB HMB q) :
    DecidablePred (bitCapValid (L := L) (n := n) t) :=
  fun c => by cases c with
    | inl b => exact instDecidableTrue
    | inr sj => exact Nat.decLt _ _

/-- (Oracle: `bitCapValid_drIncludeBit`.) -/
theorem bitCapValid_drIncludeBit (t : TranscriptPrefix HQB HMB q)
    (a : DRIdxBit (L := L) (n := n) t) :
    bitCapValid t (drIncludeBit t a) := by
  rcases a with (b | ⟨s, j⟩)
  · trivial
  · exact j.isLt

/-- **Cap-validity slice invariance under the pin update**: for a cap index
`Sum.inr (s', j)` whose query `s' ≤ s`, `bitCapValid` of the run is invariant under an
off-`p` update (`p.1 = (run ω).1.get s`) — the `hS` cylinder property the classic pin's
validity slice needs.  Wraps `mBlocksBit_run_stable_of_off`; `inl` cap indices are `True`,
trivially invariant.  (Oracle: `bitCapValid_run_stable_of_off`.) -/
theorem bitCapValid_run_stable_of_off
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i)
    (s' : Fin q) (hs' : s' ≤ s) (j : Fin (L + 2)) :
    bitCapValid (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))) (Sum.inr (s', j))
      ↔ bitCapValid (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))) (Sum.inr (s', j)) :=
  iff_of_eq (congrArg (fun m => j.val < m)
    (mBlocksBit_run_stable_of_off E hE s ω ω' p hp hoff s' hs'))

/-- `DfullB` extended to the fixed cap (total; `SjvB` accepts any index).  (Oracle:
`DfullBFix`.) -/
def DfullBFix (reveal : F × F × (Fin q → F)) (t : TranscriptPrefix HQB HMB q) :
    (Bool ⊕ Fin q × Fin (L + 2)) → F
  | Sum.inl false => be.bin 0
  | Sum.inl true => be.bin 1
  | Sum.inr (s, j) =>
      if j.val = 0 then MMvB bb Hf reveal t s else SjvB bb be Hf reveal t s j.val

/-- `RfullB` extended to the fixed cap: block `0` is `UUˢ`, blocks `1 ≤ j ≤ ℓˢ` are
`Yⱼˢ`, anything above reads the revealed last block.  (Oracle: `RfullBFix`.) -/
def RfullBFix (reveal : F × F × (Fin q → F)) (t : TranscriptPrefix HQB HMB q) :
    (Bool ⊕ Fin q × Fin (L + 2)) → F
  | Sum.inl false => reveal.1
  | Sum.inl true => reveal.2.1
  | Sum.inr (s, j) =>
      if j.val = 0 then UUvB bb Hf reveal t s
      else if j.val ≤ (splitIdx (bitPlain t s).1).1.val then YjvB t s (j.val - 1)
      else reveal.2.2 s

set_option maxHeartbeats 1000000 in
/-- `DfullBFix` agrees with `DfullB` on the image of the embedding.  (Oracle:
`DfullBFix_drIncludeBit`.) -/
theorem DfullBFix_drIncludeBit (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (a : DRIdxBit (L := L) (n := n) t) :
    DfullBFix bb be Hf reveal t (drIncludeBit t a)
      = DfullB bb be Hf reveal t a := by
  rcases a with (b | ⟨s, j⟩)
  · cases b <;> rfl
  · rfl

set_option maxHeartbeats 1000000 in
/-- `RfullBFix` agrees with `RfullB` on the image of the embedding.  (Oracle:
`RfullBFix_drIncludeBit`.) -/
theorem RfullBFix_drIncludeBit (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (a : DRIdxBit (L := L) (n := n) t) :
    RfullBFix bb Hf reveal t (drIncludeBit t a) = RfullB bb Hf reveal t a := by
  rcases a with (b | ⟨s, j⟩)
  · cases b <;> rfl
  · rfl

/-! Cap reduction pack (used by name in the dispatch).  (Oracle: `DfullBFix_inl_false` …
`RfullBFix_inr_last`.) -/

theorem DfullBFix_inr_zero (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : Fin (L + 2))
    (hj : j.val = 0) :
    DfullBFix bb be Hf reveal t (Sum.inr (s, j)) = MMvB bb Hf reveal t s := by
  simp [DfullBFix, hj]
theorem DfullBFix_inr_pos (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : Fin (L + 2))
    (hj : j.val ≠ 0) :
    DfullBFix bb be Hf reveal t (Sum.inr (s, j))
      = SjvB bb be Hf reveal t s j.val := by
  simp [DfullBFix, hj]
theorem RfullBFix_inr_zero (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : Fin (L + 2))
    (hj : j.val = 0) :
    RfullBFix bb Hf reveal t (Sum.inr (s, j)) = UUvB bb Hf reveal t s := by
  simp [RfullBFix, hj]
theorem RfullBFix_inr_Y (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : Fin (L + 2))
    (hj : j.val ≠ 0) (hle : j.val ≤ (splitIdx (bitPlain t s).1).1.val) :
    RfullBFix bb Hf reveal t (Sum.inr (s, j)) = YjvB t s (j.val - 1) := by
  simp [RfullBFix, hj, hle]
theorem RfullBFix_inr_last (reveal : F × F × (Fin q → F))
    (t : TranscriptPrefix HQB HMB q) (s : Fin q) (j : Fin (L + 2))
    (hj : j.val ≠ 0) (hgt : ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val) :
    RfullBFix bb Hf reveal t (Sum.inr (s, j)) = reveal.2.2 s := by
  simp [RfullBFix, hj, hgt]

/-- **Hybrid two-dummy congruence for `RfullBFix` at an untouched index**: under the
(virtual or classic) agreement package the earlier `R`-value — whatever its
transcript-dependent kind — is stable.  (Oracle: `RfullBFix_hybrid_congr₂`.) -/
theorem RfullBFix_hybrid_congr₂ (d d' : F × F × (Fin q → F))
    {t t' : TranscriptPrefix HQB HMB q} {r : Fin q} (i : Fin (L + 2))
    (hd1 : d.1 = d'.1) (hd3r : d.2.2 r = d'.2.2 r)
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    RfullBFix bb Hf (bitHybrid bb t d) t (Sum.inr (r, i))
      = RfullBFix bb Hf (bitHybrid bb t' d') t' (Sum.inr (r, i)) := by
  have hplain : (bitPlain t r).1 = (bitPlain t' r).1 :=
    congrArg Sigma.fst (bitPlain_congr hq hr)
  by_cases hi0 : i.val = 0
  · rw [RfullBFix_inr_zero bb Hf _ t r i hi0, RfullBFix_inr_zero bb Hf _ t' r i hi0]
    refine (UUvB_z_congr bb Hf (show (bitHybrid bb t d).1 = (bitHybrid bb t' d').1
      from hd1) t r).trans ?_
    exact UUvB_congr₂ bb Hf _ hq hr
  · by_cases hle : i.val ≤ (splitIdx (bitPlain t r).1).1.val
    · have hle' : i.val ≤ (splitIdx (bitPlain t' r).1).1.val := by
        rw [← hplain]; exact hle
      rw [RfullBFix_inr_Y bb Hf _ t r i hi0 hle,
        RfullBFix_inr_Y bb Hf _ t' r i hi0 hle']
      exact YjvB_congr₂ (i.val - 1) hq hr
    · have hle' : ¬ i.val ≤ (splitIdx (bitPlain t' r).1).1.val := by
        rw [← hplain]; exact hle
      rw [RfullBFix_inr_last bb Hf _ t r i hi0 hle,
        RfullBFix_inr_last bb Hf _ t' r i hi0 hle']
      show bitHybridBlock bb t r (d.2.2 r) = bitHybridBlock bb t' r (d'.2.2 r)
      rw [hd3r]
      exact bitHybridBlock_congr bb hq hr _

/-- Single-dummy instance of `RfullBFix_hybrid_congr₂` (the classic response-pin package
shape).  (Oracle: `RfullBFix_hybrid_congr`.) -/
theorem RfullBFix_hybrid_congr (z : F × F × (Fin q → F))
    {t t' : TranscriptPrefix HQB HMB q} {r : Fin q} (i : Fin (L + 2))
    (hq : t.1.get r = t'.1.get r) (hr : t.2.get r = t'.2.get r) :
    RfullBFix bb Hf (bitHybrid bb t z) t (Sum.inr (r, i))
      = RfullBFix bb Hf (bitHybrid bb t' z) t' (Sum.inr (r, i)) :=
  RfullBFix_hybrid_congr₂ bb Hf z z i rfl rfl hq hr

/-! ### Response-pin leaves (paper §3.4.2 grey cells, bit level)

All leaves are stated over the **hybrid** ideal extension (the stage-5 object) and reduced
to the dummy engine through `bitIdealExtH_mass`; cells that read the reveal only via
`(h̄, L)` compose invisibly (the hybrid preserves those components definitionally). -/

/-! ### Virtual-last-block leaves (paper `Dˢ` cells, all `1/N`) -/

/-- `bitHybridBlock` at `s` is stable when the query and the XOR of the zero-extended
partials are (the classic-package form of hybrid-entry stability).  (Oracle:
`bitHybridBlock_congr_of_low`.) -/
theorem bitHybridBlock_congr_of_low {t t' : TranscriptPrefix HQB HMB q}
    {s : Fin q} (hq : t.1.get s = t'.1.get s)
    (hx : (bitPlain t s).2.2.2.setWidth n ^^^ (bitCipher t s).2.2.2.setWidth n
        = (bitPlain t' s).2.2.2.setWidth n ^^^ (bitCipher t' s).2.2.2.setWidth n)
    (w : F) : bitHybridBlock bb t s w = bitHybridBlock bb t' s w := by
  show (fun (x : HQB) (X : BitVec n) => bb.toBits.symm
      (hybridBits (splitIdx x.2.2.1).2.val (X.setWidth (splitIdx x.2.2.1).2.val)
        (bb.toBits w)))
      (t.1.get s)
      ((bitPlain t s).2.2.2.setWidth n ^^^ (bitCipher t s).2.2.2.setWidth n)
    = (fun (x : HQB) (X : BitVec n) => bb.toBits.symm
      (hybridBits (splitIdx x.2.2.1).2.val (X.setWidth (splitIdx x.2.2.1).2.val)
        (bb.toBits w)))
      (t'.1.get s)
      ((bitPlain t' s).2.2.2.setWidth n ^^^ (bitCipher t' s).2.2.2.setWidth n)
  rw [hq, hx]

/-- The hybrid entry at `s` is stable under the **classic** agreement package (query at
`s` + zero-extended partial of the response).  (Oracle: `bitHybridBlock_stable`.) -/
theorem bitHybridBlock_stable
    {t t' : TranscriptPrefix HQB HMB q} {s : Fin q}
    (hqs : t.1.get s = t'.1.get s)
    (hpart : partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s))
    (w : F) : bitHybridBlock bb t s w = bitHybridBlock bb t' s w := by
  refine bitHybridBlock_congr_of_low bb hqs ?_ w
  by_cases hdir : (t.1.get s).1 = QueryDir.fwd
  · have h1 : (bitPlain t s).2.2.2.setWidth n = (bitPlain t' s).2.2.2.setWidth n := by
      rw [bitPlain_eq_of_fwd hqs hdir]
    have h2 : (bitCipher t s).2.2.2.setWidth n = (bitCipher t' s).2.2.2.setWidth n := by
      rw [bitCipher_fwd t s hdir, bitCipher_fwd t' s (show (t'.1.get s).1 = QueryDir.fwd
        from by rw [← hqs]; exact hdir)]
      exact hpart
    rw [h1, h2]
  · have hdir' : (t.1.get s).1 = QueryDir.inv := QueryDir.eq_inv_of_ne_fwd hdir
    have h1 : (bitCipher t s).2.2.2.setWidth n = (bitCipher t' s).2.2.2.setWidth n := by
      rw [bitCipher_eq_of_inv hqs hdir']
    have h2 : (bitPlain t s).2.2.2.setWidth n = (bitPlain t' s).2.2.2.setWidth n := by
      rw [bitPlain_inv t s hdir', bitPlain_inv t' s (show (t'.1.get s).1 = QueryDir.inv
        from by rw [← hqs]; exact hdir')]
      exact hpart
    rw [h1, h2]

/-! ### New pair leaves (hybrid extension) -/

/-! ### Plain-length-guard response-pin variants

The fixed-cap dispatch reads block ranges off `bitPlain` (the cap validity is
`j < mˢ = ℓ_plain + 2`), while the stage-4 leaves carried query-length guards.  These
variants take the plain-length guard; admissibility converts inside the engine
(`bitPlain_fst`). -/

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-! ### The conditional σ-cell dispatch twins, `D`-side (oracle PHASE P1b4a)

The `_cond` twins of the stage-5 dispatch: SAME sorted-pair case tree, but each leaf
routes to the *weighted* engine (`bitPairMassH_cond_wexp_le_of_reveal` for reveal leaves,
the sharp per-`t` green weight `bitMsgDeg …/N`; `bit_respPin_cond_solved_le` for pin
leaves, `1/N` conditioned on the pair's validity slice).  The conclusion bounds the
per-pair event mass by `expectW (bitExtD E.1) (bitCellWeightD/R' … p)`, whose weight is
the per-`t` cell charge gated by the pair's cap-validity — exactly the `hcell` slot
`mass_sorted_pair_le_of_embed` consumes after the sum-swap. -/

/-- Local shorthand for the **dummy** ideal extended transcript distribution (the
`expectW` carrier of the σ-cell dispatch). -/
local notation:max "bitExtD" E:max =>
  extendedTranscriptDistRep (q := q) bitIdealP bitIdealF bitIdealAug E

/-- **Kind-sliced virtual pin** (`bit_virtualPin_cond_solved_le`, `expectW` form): the
per-leaf conclusion `mass P ≤ expectW (if S then 1/N else 0)` of the σ-cell dispatch. -/
theorem bit_virtualPin_ks_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop) [DecidablePred S]
    (rhs : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hVP : ∀ t z, P (t, z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hsolve : ∀ d t, TweakablePRP.admissible E t → P (t, bitHybrid bb t d) →
      (bitHybrid bb t d).2.2 s = rhs d t)
    (hcongr : ∀ (d d' : F × F × (Fin q → F)) t t',
      TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      d.1 = d'.1 → d.2.1 = d'.2.1 → (∀ r : Fin q, r ≠ s → d.2.2 r = d'.2.2 r) →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      rhs d t = rhs d' t') :
    (bitExtH E.1).mass P
      ≤ expectW (bitExtD E.1)
          (fun td => if S td.1 then (Fintype.card F : NNReal)⁻¹ else 0) := by
  rw [expectW_indicator_const,
    show (bitExtD E.1).mass (fun td => S td.1) = (bitExtH E.1).mass (fun td => S td.1)
      from (bitIdealExtH_mass bb E.1 (fun td => S td.1)).symm]
  exact bit_virtualPin_cond_solved_le bb E hE s P S rhs hVP hSoff hsolve hcongr

/-- **Kind-sliced response pin** (`bit_respPin_cond_solved_le`, `expectW` form): the
per-leaf conclusion of the classic-pin σ-cells, the hybrid mass transported to the dummy
carrier by `bitIdealExtH_mass`. -/
theorem bit_respPin_ks_le
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (jbf : HQB → ℕ)
    (P : (TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) → Prop)
    (S : TranscriptPrefix HQB HMB q → Prop) [DecidablePred S]
    (rhs : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hVP : ∀ t z, P (t, bitHybrid bb t z) → S t)
    (hSoff : ∀ (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
      (p : Σ x : HQB, BitBlockIdx x),
      p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s →
      (∀ i, i ≠ p → ω i = ω' i) →
      (S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω')))
        ↔ S (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω)))))
    (hrange : ∀ z t, TweakablePRP.admissible E t → P (t, bitHybrid bb t z) →
      jbf (t.1.get s) < (splitIdx (t.1.get s).2.2.1).1.val + 1)
    (hsolve : ∀ z t, TweakablePRP.admissible E t → P (t, bitHybrid bb t z) →
      totBlockB (t.2.get s) (jbf (t.1.get s)) = rhs z t)
    (hcongr : ∀ z t t', TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, b ≠ jbf (t.1.get s) →
        totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s) →
      rhs z t = rhs z t') :
    (bitExtH E.1).mass P
      ≤ expectW (bitExtD E.1)
          (fun td => if S td.1 then (Fintype.card F : NNReal)⁻¹ else 0) := by
  rw [expectW_indicator_const, bitIdealExtH_mass]
  exact bit_respPin_cond_solved_le E hE s jbf
    (fun tz => P (tz.1, bitHybrid bb tz.1 tz.2)) S rhs hVP hSoff hrange hsolve hcongr


/-- **Per-pair raw D-charge** (the C2-INPUT table, D side).  (Oracle: `bitCellRawD`.) -/
noncomputable def bitCellRawD (bb : BlockBits F n) (be : BinEnc F L)
    (Hfs : HashFamilyS F T (L + 2))
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (t : TranscriptPrefix HQB HMB q) : NNReal :=
  match p.1, p.2 with
  | Sum.inl _, Sum.inr (s, j) =>
      if j.val = 0 then
        (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s) : NNReal) / Fintype.card F
      else (Fintype.card F : NNReal)⁻¹
  | Sum.inr (r, i), Sum.inr (s, j) =>
      if r = s then
        (if i.val = 0 then (Fintype.card F : NNReal)⁻¹ else 0)
      else if i.val = 0 ∧ j.val = 0 then
        (max (bitMsgDeg Hfs (bitTweak t r) (bitPlain t r))
              (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s)) : NNReal) / Fintype.card F
          + (Fintype.card F : NNReal)⁻¹
      else (Fintype.card F : NNReal)⁻¹
  | _, _ => 0

/-- **Per-pair D-weight**: the raw charge gated by the pair's cap-validity at `td.1`; a
weight over the extended (transcript × reveal) space, matching the `_wexp` engine's
`fun td => if V td.1 then bnd td.1 else 0`.  (Oracle: `bitCellWeightD`.) -/
noncomputable def bitCellWeightD (bb : BlockBits F n) (be : BinEnc F L)
    (Hfs : HashFamilyS F T (L + 2))
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) : NNReal :=
  if bitCapValid td.1 p.1 ∧ bitCapValid td.1 p.2 then bitCellRawD bb be Hfs p td.1 else 0

/-- **Conditional `senc` leg of the `MMʳ = MMˢ` cross cell** (forward `s`, sharp
no-share `max` bound on the pair's validity slice; paper p. 13, "considering first
collisions with `MMˢ` where query `s` is an encryption query"). -/
theorem bit_pairD_MM_MM_senc_cond_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hrs : r < s) :
    (bitExtH E.1).mass
      (fun tz => (bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
        ∧ MMvB bb Hfs.toHashFamily tz.2 tz.1 r = MMvB bb Hfs.toHashFamily tz.2 tz.1 s
        ∧ (tz.1.1.get s).1 = QueryDir.fwd)
      ≤ expectW (bitExtD E.1)
        (fun td => if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then (max (bitMsgDeg Hfs (bitTweak td.1 r) (bitPlain td.1 r))
                (bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)) : NNReal)
              / Fintype.card F else 0) := by
  refine bitPairMassH_cond_wexp_le_of_reveal bb E hE _
    (fun t d => MMvB bb Hfs.toHashFamily d t r = MMvB bb Hfs.toHashFamily d t s
      ∧ (t.1.get s).1 = QueryDir.fwd)
    (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
    (fun t => (max (bitMsgDeg Hfs (bitTweak t r) (bitPlain t r))
          (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s)) : NNReal) / Fintype.card F)
    (fun _ _ h => h.1) (fun t hadm _ => ?_) (fun t d h => ⟨h.2.1, h.2.2⟩)
  by_cases hds : (t.1.get s).1 = QueryDir.fwd
  · refine le_trans (CR18.mass_mono Dist.uniform_nonNeg (fun d hd => hd.1)) ?_
    exact_mod_cast revealMMvB_of_no_share_sharp bb Hfs t r s (fun hT hP =>
      bit_plain_share_false E hE t hadm hrs hds hT hP)
  · exact le_trans (le_of_eq (mass_eq_zero_of_forall _
      (fun d hd => (hds hd.2).elim))) (NNReal.coe_nonneg _)

/-- **Conditional `sdec` leg of the `MMʳ = MMˢ` cross cell** (inverse `s`, response pin
`1/N` on the pair's validity slice; paper p. 13, "if query `s` is a decryption query …
all values of `Mˢ` are equally likely"). -/
theorem bit_pairD_MM_MM_sdec_cond_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hrs : r < s) :
    (bitExtH E.1).mass
      (fun tz => (bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
        ∧ MMvB bb Hfs.toHashFamily tz.2 tz.1 r = MMvB bb Hfs.toHashFamily tz.2 tz.1 s
        ∧ (tz.1.1.get s).1 = QueryDir.inv)
      ≤ expectW (bitExtD E.1)
        (fun td => if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_respPin_ks_le bb E hE s (fun _ => 0) _
    (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
    (fun z t => MMvB bb Hfs.toHashFamily z t r
      + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)))
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff r hrs.le i)
      (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
    (fun z t _ _ => Nat.succ_pos _) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · have heq : MMvB bb Hfs.toHashFamily z t r = MMvB bb Hfs.toHashFamily z t s :=
      hP.2.1
    have hdir : (t.1.get s).1 = QueryDir.inv := hP.2.2
    have hMMs : MMvB bb Hfs.toHashFamily z t s = (t.2.get s).2.1
        + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)) := by
      unfold MMvB hashBlkB
      rw [bitPlain_inv t s hdir]
    rw [totBlockB_zero]
    linear_combination (norm := char2_norm) heq.trans hMMs
  · obtain ⟨-, -, hhash⟩ :=
      respPinB_head_ctx bb Hfs.toHashFamily hadm hadm' (hq s le_rfl) hblocks hpart z.1
    dsimp only
    rw [MMvB_congr₂ bb Hfs.toHashFamily z (hq r hrs.le) (hr' r hrs), hhash]

set_option maxHeartbeats 4000000 in
/-- **Sorted per-pair dispatch, `D`-side, conditional weighted twin** (the `_wexp` twin
of the stage-5 D dispatch).  (Oracle: `bit_cell_D_cond_le`.) -/
theorem bit_cell_D_cond_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (hp : capRank p.1 < capRank p.2) :
    (bitExtH E.1).mass
      (fun tz => bitCapValid tz.1 p.1 ∧ bitCapValid tz.1 p.2 ∧
        DfullBFix bb be Hfs.toHashFamily tz.2 tz.1 p.1
          = DfullBFix bb be Hfs.toHashFamily tz.2 tz.1 p.2)
      ≤ expectW (bitExtD E.1) (bitCellWeightD bb be Hfs p) := by
  obtain ⟨(b₁ | ⟨r, i⟩), (b₂ | ⟨s, j⟩)⟩ := p
  · -- inl–inl: mass 0 (unsorted, or `bin` injective)
    refine le_trans (le_of_eq (mass_eq_zero_of_forall _ (fun tz h => ?_)))
      (expectW_nonneg (extendedTranscriptDistRep_nonNeg _ _ _ _) _)
    cases b₁ <;> cases b₂
    · exact absurd hp (by simp [capRank])
    · exact absurd (be.bin_inj 0 1 (by omega) (by omega) h.2.2) (by omega)
    · exact absurd hp (by simp [capRank])
    · exact absurd hp (by simp [capRank])
  · -- inl–inr
    by_cases hj : j.val = 0
    · -- constMM: sharp `MMˢ` head, `degB/N`
      refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
        (fun t d => MMvB bb Hfs.toHashFamily d t s = be.bin (bif b₁ then 1 else 0))
        (fun t => bitCapValid t (Sum.inl b₁) ∧ bitCapValid t (Sum.inr (s, j)))
        (fun t => (bitMsgDeg Hfs (bitTweak t s) (bitPlain t s) : NNReal) / Fintype.card F)
        (fun _ _ h => ⟨h.1, h.2.1⟩)
        (fun t _ _ => revealMMvB_const_le_sharp bb Hfs t s _)
        (fun t d h => ?_)) (le_of_eq ?_)
      · have heq := h.2.2
        rw [DfullBFix_inr_zero bb be Hfs.toHashFamily _ t s j hj] at heq
        cases b₁ <;> exact heq.symm
      · congr 1
        funext td
        simp [bitCellWeightD, bitCellRawD, hj]
    · -- constSj: `Sⱼˢ = bin b₁`, `1/N`
      refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
        (fun t d => SjvB bb be Hfs.toHashFamily d t s j.val = be.bin (bif b₁ then 1 else 0))
        (fun t => bitCapValid t (Sum.inl b₁) ∧ bitCapValid t (Sum.inr (s, j)))
        (fun _ => (Fintype.card F : NNReal)⁻¹)
        (fun _ _ h => ⟨h.1, h.2.1⟩)
        (fun t _ _ => revealSjvB_const_le bb be Hfs.toHashFamily t s j.val _)
        (fun t d h => ?_)) (le_of_eq ?_)
      · have heq := h.2.2
        rw [DfullBFix_inr_pos bb be Hfs.toHashFamily _ t s j hj] at heq
        cases b₁ <;> exact heq.symm
      · congr 1
        funext td
        simp [bitCellWeightD, bitCellRawD, hj]
  · -- inr–inl: unsorted, mass 0
    refine le_trans (le_of_eq (mass_eq_zero_of_forall _ (fun tz h => ?_)))
      (expectW_nonneg (extendedTranscriptDistRep_nonNeg _ _ _ _) _)
    exfalso
    cases b₂ <;> simp [capRank] at hp
  · -- inr–inr
    rcases capRank_lt_inr_inr hp with hrs | ⟨rfl, hij⟩
    · by_cases hi : i.val = 0
      · by_cases hj : j.val = 0
        · -- mmCross: senc (fwd, sharp no-share max) + sdec (inv, pin 1/N)
          rw [show bitCellWeightD bb be Hfs (Sum.inr (r, i), Sum.inr (s, j))
                = (fun td => (if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
                    then (max (bitMsgDeg Hfs (bitTweak td.1 r) (bitPlain td.1 r))
                          (bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)) : NNReal)
                        / Fintype.card F else 0)
                  + (if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
                    then (Fintype.card F : NNReal)⁻¹ else 0)) from by
              funext td
              simp only [bitCellWeightD, bitCellRawD]
              rw [if_neg (Fin.ne_of_lt hrs),
                if_pos (show i.val = 0 ∧ j.val = 0 from ⟨hi, hj⟩), ite_add_ite_zero],
            ← expectW_add]
          refine le_trans
            (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _)
              (fun tz h => ?_))
            (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _)
              (add_le_add
                (bit_pairD_MM_MM_senc_cond_le bb Hfs E hE r s i j hrs)
                (bit_pairD_MM_MM_sdec_cond_le bb Hfs E hE r s i j hrs)))
          have heq := h.2.2
          rw [DfullBFix_inr_zero bb be Hfs.toHashFamily _ tz.1 r i hi,
            DfullBFix_inr_zero bb be Hfs.toHashFamily _ tz.1 s j hj] at heq
          rcases hdd : (tz.1.1.get s).1 with _ | _
          · exact Or.inl ⟨⟨h.1, h.2.1⟩, heq, rfl⟩
          · exact Or.inr ⟨⟨h.1, h.2.1⟩, heq, rfl⟩
        · -- mmSj: `Sⱼˢ = MMʳ`, `1/N`
          refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
            (fun t d => SjvB bb be Hfs.toHashFamily d t s j.val = MMvB bb Hfs.toHashFamily d t r)
            (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
            (fun _ => (Fintype.card F : NNReal)⁻¹)
            (fun _ _ h => ⟨h.1, h.2.1⟩)
            (fun t _ _ => revealSjvB_MMvB_le bb be Hfs.toHashFamily t s r j.val)
            (fun t d h => ?_)) (le_of_eq ?_)
          · have heq := h.2.2
            rw [DfullBFix_inr_zero bb be Hfs.toHashFamily _ t r i hi,
              DfullBFix_inr_pos bb be Hfs.toHashFamily _ t s j hj] at heq
            exact heq.symm
          · congr 1
            funext td
            simp [bitCellWeightD, bitCellRawD, Fin.ne_of_lt hrs, hi, hj]
      · by_cases hj : j.val = 0
        · -- sjMM: `Sᵢʳ = MMˢ`, `1/N`
          refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
            (fun t d => SjvB bb be Hfs.toHashFamily d t r i.val = MMvB bb Hfs.toHashFamily d t s)
            (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
            (fun _ => (Fintype.card F : NNReal)⁻¹)
            (fun _ _ h => ⟨h.1, h.2.1⟩)
            (fun t _ _ => revealSjvB_MMvB_le bb be Hfs.toHashFamily t r s i.val)
            (fun t d h => ?_)) (le_of_eq ?_)
          · have heq := h.2.2
            rw [DfullBFix_inr_pos bb be Hfs.toHashFamily _ t r i hi,
              DfullBFix_inr_zero bb be Hfs.toHashFamily _ t s j hj] at heq
            exact heq
          · congr 1
            funext td
            simp [bitCellWeightD, bitCellRawD, Fin.ne_of_lt hrs, hi]
        · -- ssCross: response pin, `1/N`
          rw [show bitCellWeightD bb be Hfs (Sum.inr (r, i), Sum.inr (s, j))
                = (fun td => if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
                    then (Fintype.card F : NNReal)⁻¹ else 0) from by
              funext td
              simp [bitCellWeightD, bitCellRawD, Fin.ne_of_lt hrs, hi],
            expectW_indicator_const, bitIdealExtH_mass]
          refine bit_respPin_cond_solved_le E hE s (fun _ => 0) _
            (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
            (fun z t => SjvB bb be Hfs.toHashFamily z t r i.val + z.2.1 + be.bin j.val
              + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s))
              + if (t.1.get s).1 = QueryDir.fwd then MMvB bb Hfs.toHashFamily z t s
                else UUvB bb Hfs.toHashFamily z t s)
            (fun _ _ h => ⟨h.1, h.2.1⟩)
            (fun ω ω' pp hpp hoff => and_congr
              (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff r hrs.le i)
              (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
            (fun z t _ _ => Nat.succ_pos _) (fun z t hadm hP => ?_)
            (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
          · have heq : SjvB bb be Hfs.toHashFamily z t r i.val
                = SjvB bb be Hfs.toHashFamily z t s j.val := by
              have h1 := hP.2.2
              rw [DfullBFix_inr_pos bb be Hfs.toHashFamily _ t r i hi,
                DfullBFix_inr_pos bb be Hfs.toHashFamily _ t s j hj] at h1
              exact h1
            rw [totBlockB_zero]
            dsimp only
            by_cases hdir : (t.1.get s).1 = QueryDir.fwd
            · rw [if_pos hdir]
              have hSs : SjvB bb be Hfs.toHashFamily z t s j.val
                  = MMvB bb Hfs.toHashFamily z t s + ((t.2.get s).2.1
                      + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)))
                    + z.2.1 + be.bin j.val := by
                unfold SjvB SvB UUvB hashBlkB
                rw [bitCipher_fwd t s hdir]
              linear_combination (norm := char2_norm) heq.trans hSs
            · rw [if_neg hdir]
              have hSs : SjvB bb be Hfs.toHashFamily z t s j.val
                  = ((t.2.get s).2.1
                      + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)))
                    + UUvB bb Hfs.toHashFamily z t s + z.2.1 + be.bin j.val := by
                unfold SjvB SvB MMvB hashBlkB
                rw [bitPlain_inv t s (QueryDir.eq_inv_of_ne_fwd hdir)]
              linear_combination (norm := char2_norm) heq.trans hSs
          · have hqs := hq s le_rfl
            obtain ⟨-, -, hhash⟩ :=
              respPinB_head_ctx bb Hfs.toHashFamily hadm hadm' hqs hblocks hpart z.1
            have hif : (if (t.1.get s).1 = QueryDir.fwd
                  then MMvB bb Hfs.toHashFamily z t s else UUvB bb Hfs.toHashFamily z t s)
                = (if (t'.1.get s).1 = QueryDir.fwd
                  then MMvB bb Hfs.toHashFamily z t' s else UUvB bb Hfs.toHashFamily z t' s) := by
              by_cases hdir : (t.1.get s).1 = QueryDir.fwd
              · rw [if_pos hdir, if_pos (show (t'.1.get s).1 = QueryDir.fwd from by
                  rw [← hqs]; exact hdir)]
                exact MMvB_eq_of_fwd bb Hfs.toHashFamily z hqs hdir
              · rw [if_neg hdir, if_neg (show ¬ (t'.1.get s).1 = QueryDir.fwd from by
                  rw [← hqs]; exact hdir)]
                exact UUvB_eq_of_inv bb Hfs.toHashFamily z hqs (QueryDir.eq_inv_of_ne_fwd hdir)
            dsimp only
            rw [SjvB_congr₂ bb be Hfs.toHashFamily z i.val (hq r hrs.le) (hr' r hrs), hhash, hif]
    · -- same query, i < j
      have hj : j.val ≠ 0 := by omega
      by_cases hi : i.val = 0
      · -- sameHead: `Sⱼʳ = MMʳ`, `1/N`
        refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
          (fun t d => SjvB bb be Hfs.toHashFamily d t r j.val = MMvB bb Hfs.toHashFamily d t r)
          (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (r, j)))
          (fun _ => (Fintype.card F : NNReal)⁻¹)
          (fun _ _ h => ⟨h.1, h.2.1⟩)
          (fun t _ _ => revealSjvB_MMvB_le bb be Hfs.toHashFamily t r r j.val)
          (fun t d h => ?_)) (le_of_eq ?_)
        · have heq := h.2.2
          rw [DfullBFix_inr_zero bb be Hfs.toHashFamily _ t r i hi,
            DfullBFix_inr_pos bb be Hfs.toHashFamily _ t r j hj] at heq
          exact heq.symm
        · congr 1
          funext td
          simp [bitCellWeightD, bitCellRawD, hi]
      · -- sameTail: impossible, mass 0
        refine le_trans (le_of_eq (mass_eq_zero_of_forall _ (fun tz h => ?_)))
          (expectW_nonneg (extendedTranscriptDistRep_nonNeg _ _ _ _) _)
        have heq := h.2.2
        rw [DfullBFix_inr_pos bb be Hfs.toHashFamily _ tz.1 r i hi,
          DfullBFix_inr_pos bb be Hfs.toHashFamily _ tz.1 r j hj] at heq
        unfold SjvB at heq
        have hb := add_left_cancel heq
        have hi2 := i.isLt
        have hj2 := j.isLt
        exact absurd (be.bin_inj i.val j.val (by omega) (by omega) hb)
          (Nat.ne_of_lt hij)

/-! ### The conditional σ-cell dispatch twin, R-side prep (oracle PHASE P1b4c/P1b4e)

The `_cond` twin of the stage-5 R dispatch shares the D twin's sorted-pair case tree;
each leaf routes to the weighted engine (`bitPairMassH_cond_wexp_le_of_reveal` for reveal
leaves — sharp green `bnd t = bitMsgDeg …/N`, u-cells `1/N`;
`bit_respPin_cond_solved_le` / `bit_virtualPin_cond_solved_le` for the pin/virtual
leaves, `1/N` on the pair's validity slice). -/

/-- **Sharp per-`t` core, hybrid last block `z₃ʳ` vs `UUˢ`** (the ONE new leg): the sharp
`bitMsgDeg`-weighted twin of `bit_lastB_UUvB_any_le`'s inner uniform-slice bound,
`Hfs.prop1'` in place of `Hf.prop1`, at `UUˢ`'s cipher degree.  (Oracle:
`bit_lastB_UUvB_any_sharp`.) -/
theorem bit_lastB_UUvB_any_sharp (Hfs : HashFamilyS F T (L + 2))
    (t : TranscriptPrefix HQB HMB q) (r s : Fin q) :
    (Dist.uniform (F × F × (Fin q → F))).mass
      (fun d => (bitHybrid bb t d).2.2 r = UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s)
      ≤ (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F := by
  rw [bitMsgDeg_eq bb Hfs (bitTweak t s) (bitCipher t s),
    Dist.mass_congr _ (fun d : F × F × (Fin q → F) =>
    show ((bitHybrid bb t d).2.2 r = UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s)
        ↔ (Hfs.toHashFamily.hash d.1 (bitTweak t s) (msgHashTail bb (bitCipher t s))
            = bitHybridBlock bb t r (d.2.2 r) + (bitCipher t s).2.1) by
      rw [show (bitHybrid bb t d).2.2 r = bitHybridBlock bb t r (d.2.2 r) from rfl,
        UUvB_z_congr bb Hfs.toHashFamily (bitHybrid_fst bb t d) t s, UUvB_eq_hashBlkB,
        eq_comm, hashBlkB_eq_const_iff])]
  refine uniform_prod_fst_slice_le _ _ (fun y => ?_)
  refine le_trans (le_of_eq (Dist.mass_congr _ (fun a => Iff.rfl))) ?_
  exact Hfs.prop1'
    (bitTweak t s) (msgHashTail bb (bitCipher t s)) (msgHashTail_fst_le bb (bitCipher t s))
    (bitHybridBlock bb t r (y.2 r) + (bitCipher t s).2.1)

/-- Conditional `senc` leg of the `UUʳ = UUˢ` cross cell (forward `s`): `1/N` on the
pair's validity slice.  (Oracle: `bit_pairR_UU_UU_senc_cond_le`.) -/
theorem bit_pairR_UU_UU_senc_cond_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hrs : r < s) :
    (bitExtH E.1).mass
      (fun tz => (bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
        ∧ UUvB bb Hfs.toHashFamily tz.2 tz.1 r = UUvB bb Hfs.toHashFamily tz.2 tz.1 s
        ∧ (tz.1.1.get s).1 = QueryDir.fwd)
      ≤ expectW (bitExtD E.1) (fun td =>
          if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_respPin_ks_le bb E hE s (fun _ => 0) _
    (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
    (fun z t => UUvB bb Hfs.toHashFamily z t r
      + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)))
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff r hrs.le i)
      (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
    (fun z t _ _ => Nat.succ_pos _) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · have heq : UUvB bb Hfs.toHashFamily z t r = UUvB bb Hfs.toHashFamily z t s := hP.2.1
    have hdir : (t.1.get s).1 = QueryDir.fwd := hP.2.2
    have hUUs : UUvB bb Hfs.toHashFamily z t s = (t.2.get s).2.1
        + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)) := by
      unfold UUvB hashBlkB
      rw [bitCipher_fwd t s hdir]
    rw [totBlockB_zero]
    linear_combination (norm := char2_norm) heq.trans hUUs
  · obtain ⟨-, -, hhash⟩ :=
      respPinB_head_ctx bb Hfs.toHashFamily hadm hadm' (hq s le_rfl) hblocks hpart z.1
    dsimp only
    rw [UUvB_congr₂ bb Hfs.toHashFamily z (hq r hrs.le) (hr' r hrs), hhash]

/-- **Conditional `sdec` leg of the `UUʳ = UUˢ` cross cell** (inverse `s`, sharp
no-share `max` bound on the pair's validity slice; paper p. 13, "considering
collisions with `UUˢ` where query `s` is a decryption query"). -/
theorem bit_pairR_UU_UU_sdec_cond_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hrs : r < s) :
    (bitExtH E.1).mass
      (fun tz => (bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
        ∧ UUvB bb Hfs.toHashFamily tz.2 tz.1 r = UUvB bb Hfs.toHashFamily tz.2 tz.1 s
        ∧ (tz.1.1.get s).1 = QueryDir.inv)
      ≤ expectW (bitExtD E.1) (fun td =>
          if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then (max (bitMsgDeg Hfs (bitTweak td.1 r) (bitCipher td.1 r))
                (bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s)) : NNReal)
              / Fintype.card F else 0) := by
  refine bitPairMassH_cond_wexp_le_of_reveal bb E hE _
    (fun t d => UUvB bb Hfs.toHashFamily d t r = UUvB bb Hfs.toHashFamily d t s
      ∧ (t.1.get s).1 = QueryDir.inv)
    (fun t => bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
    (fun t => (max (bitMsgDeg Hfs (bitTweak t r) (bitCipher t r))
          (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s)) : NNReal) / Fintype.card F)
    (fun _ _ h => h.1) (fun t hadm _ => ?_) (fun t d h => ⟨h.2.1, h.2.2⟩)
  by_cases hds : (t.1.get s).1 = QueryDir.inv
  · refine le_trans (CR18.mass_mono Dist.uniform_nonNeg (fun d hd => hd.1)) ?_
    exact_mod_cast revealUUvB_of_no_share_sharp bb Hfs t r s (fun hT hC =>
      bit_cipher_share_false E hE t hadm hrs hds hT hC)
  · exact le_trans (le_of_eq (mass_eq_zero_of_forall _
      (fun d hd => (hds hd.2).elim))) (NNReal.coe_nonneg _)

/-! ### The SINGLE-CHARGE R-side table (oracle PHASE P1b4e — overflow resolution)

The R-side multi-leg arms are gated on DISJOINT, TRANSCRIPT-ONLY events that partition
the validity — the tail index kind at `j ≥ 1` (`j ≤ plain-length`, `Y`-kind, reveal leg,
vs `j = last index`, `lastB`-kind, virtual leg) and, on the same-query head–tail arm, a
further direction split.  Re-deriving each leg with the KIND-SLICED validity
`V := valid ∧ kind` and adding via `ite_add_ite_of_disjoint` collapses each multi-leg
arm to a SINGLE `w` per valid pair, which is what closes the σ-budgeted count. -/

/-- **Direction-partition indicator collapse**: the two direction slices `inv` / `fwd`
of `A ∧ K` sum to the single indicator over `A ∧ K`.  (Oracle: `ite_add_ite_dir`.) -/
theorem ite_add_ite_dir {A K : Prop} [Decidable A] [Decidable K] (d : QueryDir)
    (w : NNReal) :
    (if A ∧ K ∧ d = QueryDir.inv then w else 0)
        + (if A ∧ K ∧ d = QueryDir.fwd then w else 0)
      = if A ∧ K then w else 0 := by
  cases d <;> by_cases hA : A <;> by_cases hK : K <;> simp [hA, hK]

/-- **Per-pair raw R-charge, SINGLE-CHARGE table** (the corrected C2-INPUT (R)): the
multi-leg arms whose legs are gated on the disjoint `Y`/`lastB` index-kind partition are
collapsed to a single charge per valid pair.  (Oracle: `bitCellRawR'`.) -/
noncomputable def bitCellRawR' (Hfs : HashFamilyS F T (L + 2))
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (t : TranscriptPrefix HQB HMB q) : NNReal :=
  match p.1, p.2 with
  | Sum.inl _, Sum.inl _ => (Fintype.card F : NNReal)⁻¹
  | Sum.inl b₁, Sum.inr (s, j) =>
      if j.val = 0 then
        (if b₁ then (Fintype.card F : NNReal)⁻¹
         else (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F)
      else (Fintype.card F : NNReal)⁻¹
  | Sum.inr (r, i), Sum.inr (s, j) =>
      if r = s then
        (Fintype.card F : NNReal)⁻¹
      else if i.val = 0 ∧ j.val = 0 then
        (max (bitMsgDeg Hfs (bitTweak t r) (bitCipher t r))
              (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s)) : NNReal) / Fintype.card F
          + (Fintype.card F : NNReal)⁻¹
      else if j.val = 0 then
        (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F
      else (Fintype.card F : NNReal)⁻¹
  | _, _ => 0

/-- **Per-pair R-weight, single-charge**: the collapsed raw charge gated by the pair's
cap-validity at `td.1`.  (Oracle: `bitCellWeightR'`.) -/
noncomputable def bitCellWeightR' (Hfs : HashFamilyS F T (L + 2))
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) : NNReal :=
  if bitCapValid td.1 p.1 ∧ bitCapValid td.1 p.2 then bitCellRawR' Hfs p td.1 else 0

/-! ### Kind-stability helpers (oracle PHASE P1b4f) -/

/-- **Index-kind slice invariance under the pin update**: the R-side tail kind
`j ≤ plain-length` of a query `s' ≤ s` is invariant under an off-`p` update
(`p.1 = (run ω).1.get s`); wraps `mBlocksBit_run_stable_of_off`.  (Oracle:
`bitYkind_run_stable_of_off`.) -/
theorem bitYkind_run_stable_of_off
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i)
    (s' : Fin q) (hs' : s' ≤ s) (j : Fin (L + 2)) :
    (j.val ≤ (splitIdx (bitPlain
        (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))) s').1).1.val)
      ↔ (j.val ≤ (splitIdx (bitPlain
        (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))) s').1).1.val) := by
  have h := mBlocksBit_run_stable_of_off E hE s ω ω' p hp hoff s' hs'
  unfold mBlocksBit at h
  exact iff_of_eq (congrArg (fun m => j.val ≤ m) (by omega))

/-- **Direction slice invariance under the pin update**: the direction of the run's
`s`-th query is invariant under an off-`p` update; wraps `bit_run_prefix_congr_off`.
(Oracle: `bitDir_run_stable_of_off`.) -/
theorem bitDir_run_stable_of_off
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E) (s : Fin q)
    (ω ω' : ∀ p : Σ x : HQB, BitBlockIdx x, bitCoord p)
    (p : Σ x : HQB, BitBlockIdx x)
    (hp : p.1 = (envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s)
    (hoff : ∀ i, i ≠ p → ω i = ω' i)
    (dir : QueryDir) :
    (((envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω'))).1.get s).1 = dir)
      ↔ (((envRun E (TweakablePRP.rndFun (bitOmegaEquiv.symm ω))).1.get s).1 = dir) :=
  iff_of_eq (congrArg (fun x => x.1 = dir)
    ((bit_run_prefix_congr_off E hE s ω ω' p hp hoff).1 s le_rfl))

/-! ### Kind-sliced R legs (oracle PHASE P1b4f)

Verbatim twins of the conditional R legs with `S`/event carrying the kind conjunct: the
`hSoff` cylinder extends to the kind via `bitYkind_run_stable_of_off` /
`bitDir_run_stable_of_off`, since the kind reads only plain-lengths/directions of
queries `≤ s`.  Every leaf is one `bit_virtualPin_ks_le` / `bit_respPin_ks_le`
application. -/

/-- Kind-sliced last block vs `h̄` (arm 1 lastB leg): `lastBkind`.  (Oracle:
`bit_lastB_hbar_ks_le`.) -/
theorem bit_lastB_hbar_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (b₁ : Bool) (s : Fin q) (j : Fin (L + 2)) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inl b₁) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ tz.2.2.2 s = tz.2.1)
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inl b₁) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_virtualPin_ks_le bb E hE s _
    (fun t => (bitCapValid t (Sum.inl b₁) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun d t => d.1)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr Iff.rfl (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j)))
    (fun d t _ hP => hP.2)
    (fun d d' t t' hadm hadm' hd1 hd2 hd3 hq hr' hblocks => hd1)

/-- Kind-sliced last block vs `L` (arm 1 lastB leg): `lastBkind`.  (Oracle:
`bit_lastB_L_ks_le`.) -/
theorem bit_lastB_L_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (b₁ : Bool) (s : Fin q) (j : Fin (L + 2)) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inl b₁) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ tz.2.2.2 s = tz.2.2.1)
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inl b₁) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_virtualPin_ks_le bb E hE s _
    (fun t => (bitCapValid t (Sum.inl b₁) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun d t => d.2.1)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr Iff.rfl (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j)))
    (fun d t _ hP => hP.2)
    (fun d d' t t' hadm hadm' hd1 hd2 hd3 hq hr' hblocks => hd2)

/-- Kind-sliced generic virtual leaf (`z₃ˢ` vs stable target `ψ`, arm 3 lastB leg):
`lastBkind` on `s`.  (Oracle: `bit_lastB_stable_ks_le`.) -/
theorem bit_lastB_stable_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hrs : r < s)
    (ψ : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hψ : ∀ (d d' : F × F × (Fin q → F)) t t',
      TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      d.1 = d'.1 → d.2.1 = d'.2.1 → (∀ r : Fin q, r ≠ s → d.2.2 r = d'.2.2 r) →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      ψ (bitHybrid bb t d) t = ψ (bitHybrid bb t' d') t') :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ tz.2.2.2 s = ψ tz.2 tz.1)
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_virtualPin_ks_le bb E hE s _
    (fun t => (bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun d t => ψ (bitHybrid bb t d) t)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff r hrs.le i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j)))
    (fun d t _ hP => hP.2) hψ

/-- Kind-sliced same-query last block vs earlier `Yᵢˢ` (arm 5 lastB leg): `lastBkind`.
(Oracle: `bit_lastB_YjvB_same_ks_le`.) -/
theorem bit_lastB_YjvB_same_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (i j : Fin (L + 2)) (hi : i.val ≠ 0) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (s, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ tz.2.2.2 s = YjvB tz.1 s (i.val - 1))
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (s, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_virtualPin_ks_le bb E hE s _
    (fun t => (bitCapValid t (Sum.inr (s, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun d t => YjvB t s (i.val - 1))
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j)))
    (fun d t _ hP => hP.2)
    (fun d d' t t' hadm hadm' hd1 hd2 hd3 hq hr' hblocks => ?_)
  have hqs := hq s le_rfl
  show YjvB t s (i.val - 1) = YjvB t' s (i.val - 1)
  rw [YjvB_eq_totBlockB t s i.val hi, YjvB_eq_totBlockB t' s i.val hi]
  by_cases hdir : (t.1.get s).1 = QueryDir.fwd
  · rw [bitPlain_eq_of_fwd hqs hdir,
      bitCipher_fwd t s hdir,
      bitCipher_fwd t' s (show (t'.1.get s).1 = QueryDir.fwd from by
        rw [← hqs]; exact hdir),
      hblocks i.val]
  · have hdir' : (t.1.get s).1 = QueryDir.inv := QueryDir.eq_inv_of_ne_fwd hdir
    rw [bitCipher_eq_of_inv hqs hdir',
      bitPlain_inv t s hdir',
      bitPlain_inv t' s (show (t'.1.get s).1 = QueryDir.inv from by
        rw [← hqs]; exact hdir'),
      hblocks i.val]

/-- Kind-sliced same-query `UUˢ` last-decryption leg (arm 4 lastB/inv leg):
`lastBkind ∧ inv`.  (Oracle: `bit_lastB_UU_same_sdec_ks_le`.) -/
theorem bit_lastB_UU_same_sdec_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (i j : Fin (L + 2)) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (s, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val
          ∧ (tz.1.1.get s).1 = QueryDir.inv)
        ∧ tz.2.2.2 s = UUvB bb Hfs.toHashFamily tz.2 tz.1 s)
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (s, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
              ∧ (td.1.1.get s).1 = QueryDir.inv
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_virtualPin_ks_le bb E hE s _
    (fun t => (bitCapValid t (Sum.inr (s, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val ∧ (t.1.get s).1 = QueryDir.inv)
    (fun d t => if (t.1.get s).1 = QueryDir.inv
      then UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s else 0)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (and_congr (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
        (bitDir_run_stable_of_off E hE s ω ω' pp hpp hoff QueryDir.inv)))
    (fun d t hadm hP => ?_)
    (fun d d' t t' hadm hadm' hd1 hd2 hd3 hq hr' hblocks => ?_)
  · show (bitHybrid bb t d).2.2 s = if (t.1.get s).1 = QueryDir.inv
      then UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s else 0
    rw [if_pos hP.1.2.2]
    exact hP.2
  · have hqs := hq s le_rfl
    show (if (t.1.get s).1 = QueryDir.inv
        then UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s else 0)
      = (if (t'.1.get s).1 = QueryDir.inv
        then UUvB bb Hfs.toHashFamily (bitHybrid bb t' d') t' s else 0)
    by_cases hdir : (t.1.get s).1 = QueryDir.inv
    · rw [if_pos hdir, if_pos (show (t'.1.get s).1 = QueryDir.inv from by
        rw [← hqs]; exact hdir)]
      exact (UUvB_z_congr bb Hfs.toHashFamily (show (bitHybrid bb t d).1 = (bitHybrid bb t' d').1
          from hd1) t s).trans
        (UUvB_eq_of_inv bb Hfs.toHashFamily _ hqs hdir)
    · rw [if_neg hdir, if_neg (show ¬ (t'.1.get s).1 = QueryDir.inv from by
        rw [← hqs]; exact hdir)]

/-- Kind-sliced same-query `UUˢ` last-encryption leg (arm 4 lastB/fwd leg, classic
response pin): `lastBkind ∧ fwd`.  (Oracle: `bit_lastB_UU_same_senc_ks_le`.) -/
theorem bit_lastB_UU_same_senc_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (i j : Fin (L + 2)) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (s, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ ¬ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val
          ∧ (tz.1.1.get s).1 = QueryDir.fwd)
        ∧ tz.2.2.2 s = UUvB bb Hfs.toHashFamily tz.2 tz.1 s)
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (s, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ ¬ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
              ∧ (td.1.1.get s).1 = QueryDir.fwd
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_respPin_ks_le bb E hE s (fun _ => 0) _
    (fun t => (bitCapValid t (Sum.inr (s, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ ¬ j.val ≤ (splitIdx (bitPlain t s).1).1.val ∧ (t.1.get s).1 = QueryDir.fwd)
    (fun z t => (bitHybrid bb t z).2.2 s
      + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)))
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (and_congr (not_congr (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
        (bitDir_run_stable_of_off E hE s ω ω' pp hpp hoff QueryDir.fwd)))
    (fun z t _ _ => Nat.succ_pos _) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · have heq : (bitHybrid bb t z).2.2 s = UUvB bb Hfs.toHashFamily z t s := hP.2
    have hdir : (t.1.get s).1 = QueryDir.fwd := hP.1.2.2
    have hUUs : UUvB bb Hfs.toHashFamily z t s = (t.2.get s).2.1
        + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)) := by
      unfold UUvB hashBlkB
      rw [bitCipher_fwd t s hdir]
    rw [totBlockB_zero]
    linear_combination (norm := char2_norm) heq.trans hUUs
  · obtain ⟨-, -, hhash⟩ :=
      respPinB_head_ctx bb Hfs.toHashFamily hadm hadm' (hq s le_rfl) hblocks hpart z.1
    dsimp only
    show bitHybridBlock bb t s (z.2.2 s) + _ = bitHybridBlock bb t' s (z.2.2 s) + _
    rw [bitHybridBlock_stable bb (hq s le_rfl) hpart (z.2.2 s), hhash]

/-- Kind-sliced cross-`Y` pin leg (arm 3 Y leg, generic earlier target `ψ`): `Ykind` in
`V`.  (Oracle: `bit_pairR_cross_Y_pin_plain_ks_le`.) -/
theorem bit_pairR_cross_Y_pin_plain_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (r s : Fin q) (i j : Fin (L + 2)) (hj : j.val ≠ 0) (hrs : r < s)
    (ψ : (F × F × (Fin q → F)) → TranscriptPrefix HQB HMB q → F)
    (hψ : ∀ (z : F × F × (Fin q → F)) t t', TweakablePRP.admissible E t → TweakablePRP.admissible E t' →
      (∀ k : Fin q, k ≤ s → t.1.get k = t'.1.get k) →
      (∀ k : Fin q, k < s → t.2.get k = t'.2.get k) →
      (∀ b : ℕ, b ≠ j.val → totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b) →
      partSW (F := F) (L := L) (n := n) (t.2.get s) = partSW (t'.2.get s) →
      ψ (bitHybrid bb t z) t = ψ (bitHybrid bb t' z) t') :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ ψ tz.2 tz.1 = YjvB tz.1 s (j.val - 1))
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_respPin_ks_le bb E hE s (fun _ => j.val) _
    (fun t => (bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun z t => ψ (bitHybrid bb t z) t
      + if (t.1.get s).1 = QueryDir.fwd then totBlockB (bitPlain t s) j.val
        else totBlockB (bitCipher t s) j.val)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff r hrs.le i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
    (fun z t hadm hP => ?_) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · have h1 := hP.1.2
    rw [bitPlain_fst t s (hadm.2.2 s)] at h1
    exact Nat.lt_succ_of_le h1
  · have heq : ψ (bitHybrid bb t z) t = YjvB t s (j.val - 1) := hP.2
    rw [YjvB_eq_totBlockB t s j.val hj] at heq
    dsimp only
    by_cases hdir : (t.1.get s).1 = QueryDir.fwd
    · rw [if_pos hdir]
      rw [bitCipher_fwd t s hdir] at heq
      linear_combination (norm := char2_norm) heq
    · rw [if_neg hdir]
      rw [bitPlain_inv t s (QueryDir.eq_inv_of_ne_fwd hdir)] at heq
      linear_combination (norm := char2_norm) heq
  · have hqs := hq s le_rfl
    have hif : (if (t.1.get s).1 = QueryDir.fwd then totBlockB (bitPlain t s) j.val
          else totBlockB (bitCipher t s) j.val)
        = (if (t'.1.get s).1 = QueryDir.fwd then totBlockB (bitPlain t' s) j.val
          else totBlockB (bitCipher t' s) j.val) := by
      by_cases hdir : (t.1.get s).1 = QueryDir.fwd
      · rw [if_pos hdir, if_pos (show (t'.1.get s).1 = QueryDir.fwd from by
          rw [← hqs]; exact hdir), bitPlain_eq_of_fwd hqs hdir]
      · rw [if_neg hdir, if_neg (show ¬ (t'.1.get s).1 = QueryDir.fwd from by
          rw [← hqs]; exact hdir),
          bitCipher_eq_of_inv hqs (QueryDir.eq_inv_of_ne_fwd hdir)]
    dsimp only
    rw [hψ z t t' hadm hadm' hq hr' hblocks hpart, hif]

/-- Kind-sliced same-query `UUˢ ≟ Yⱼˢ` pin leg (arm 4 Y leg): `Ykind` in `V`.  (Oracle:
`bit_pairR_UU_Y_same_plain_ks_le`.) -/
theorem bit_pairR_UU_Y_same_plain_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (i j : Fin (L + 2)) (hj : j.val ≠ 0) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (s, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ UUvB bb Hfs.toHashFamily tz.2 tz.1 s = YjvB tz.1 s (j.val - 1))
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (s, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  refine bit_respPin_ks_le bb E hE s
    (fun x => if x.1 = QueryDir.fwd then 0 else j.val) _
    (fun t => (bitCapValid t (Sum.inr (s, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun z t => if (t.1.get s).1 = QueryDir.fwd
      then Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s))
        + totBlockB (bitPlain t s) j.val + totBlockB (t.2.get s) j.val
      else UUvB bb Hfs.toHashFamily z t s + totBlockB (bitCipher t s) j.val)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
    (fun z t hadm hP => ?_) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · dsimp only
    by_cases hd : (t.1.get s).1 = QueryDir.fwd
    · rw [if_pos hd]
      exact Nat.succ_pos _
    · rw [if_neg hd]
      have h1 := hP.1.2
      rw [bitPlain_fst t s (hadm.2.2 s)] at h1
      exact Nat.lt_succ_of_le h1
  · have heq : UUvB bb Hfs.toHashFamily z t s = YjvB t s (j.val - 1) := hP.2
    rw [YjvB_eq_totBlockB t s j.val hj] at heq
    dsimp only
    by_cases hdir : (t.1.get s).1 = QueryDir.fwd
    · rw [if_pos hdir, if_pos hdir, totBlockB_zero]
      rw [bitCipher_fwd t s hdir] at heq
      have hUUs : UUvB bb Hfs.toHashFamily z t s = (t.2.get s).2.1
          + Hfs.toHashFamily.hash z.1 (bitTweak t s) (msgHashTail bb (t.2.get s)) := by
        unfold UUvB hashBlkB
        rw [bitCipher_fwd t s hdir]
      linear_combination (norm := char2_norm) hUUs.symm.trans heq
    · rw [if_neg hdir, if_neg hdir]
      rw [bitPlain_inv t s (QueryDir.eq_inv_of_ne_fwd hdir)] at heq
      linear_combination (norm := char2_norm) heq
  · have hqs := hq s le_rfl
    dsimp only
    by_cases hdir : (t.1.get s).1 = QueryDir.fwd
    · have hdir' : (t'.1.get s).1 = QueryDir.fwd := by rw [← hqs]; exact hdir
      have hbl : ∀ b : ℕ, b ≠ 0 →
          totBlockB (t.2.get s) b = totBlockB (t'.2.get s) b := by
        intro b hb
        refine hblocks b ?_
        dsimp only
        rw [if_pos hdir]
        exact hb
      obtain ⟨-, -, hhash⟩ := respPinB_head_ctx bb Hfs.toHashFamily hadm hadm' hqs hbl hpart z.1
      rw [if_pos hdir, if_pos hdir', hhash, bitPlain_eq_of_fwd hqs hdir, hbl j.val hj]
    · have hdir' : ¬ (t'.1.get s).1 = QueryDir.fwd := by rw [← hqs]; exact hdir
      rw [if_neg hdir, if_neg hdir',
        UUvB_eq_of_inv bb Hfs.toHashFamily z hqs (QueryDir.eq_inv_of_ne_fwd hdir),
        bitCipher_eq_of_inv hqs (QueryDir.eq_inv_of_ne_fwd hdir)]

/-- Kind-sliced same-query `Yᵢˢ ≟ Yⱼˢ` pin leg (arm 5 Y leg, `1 ≤ i < j`): `Ykind` in
`V`.  (Oracle: `bit_pairR_Y_Y_same_plain_ks_le`.) -/
theorem bit_pairR_Y_Y_same_plain_ks_le (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (s : Fin q) (i j : Fin (L + 2)) (hi : i.val ≠ 0) (hij : i.val < j.val) :
    (bitExtH E.1).mass
      (fun tz => ((bitCapValid tz.1 (Sum.inr (s, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
          ∧ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
        ∧ YjvB tz.1 s (i.val - 1) = YjvB tz.1 s (j.val - 1))
      ≤ expectW (bitExtD E.1) (fun td =>
          if (bitCapValid td.1 (Sum.inr (s, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
              ∧ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
          then (Fintype.card F : NNReal)⁻¹ else 0) := by
  have hj : j.val ≠ 0 := by omega
  refine bit_respPin_ks_le bb E hE s (fun _ => j.val) _
    (fun t => (bitCapValid t (Sum.inr (s, i)) ∧ bitCapValid t (Sum.inr (s, j)))
      ∧ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
    (fun z t => if (t.1.get s).1 = QueryDir.fwd
      then totBlockB (bitPlain t s) i.val + totBlockB (t.2.get s) i.val
        + totBlockB (bitPlain t s) j.val
      else totBlockB (t.2.get s) i.val + totBlockB (bitCipher t s) i.val
        + totBlockB (bitCipher t s) j.val)
    (fun _ _ h => h.1)
    (fun ω ω' pp hpp hoff => and_congr
      (and_congr (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl i)
        (bitCapValid_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
      (bitYkind_run_stable_of_off E hE s ω ω' pp hpp hoff s le_rfl j))
    (fun z t hadm hP => ?_) (fun z t hadm hP => ?_)
    (fun z t t' hadm hadm' hq hr' hblocks hpart => ?_)
  · have h1 := hP.1.2
    rw [bitPlain_fst t s (hadm.2.2 s)] at h1
    exact Nat.lt_succ_of_le h1
  · have heq : YjvB t s (i.val - 1) = YjvB t s (j.val - 1) := hP.2
    rw [YjvB_eq_totBlockB t s i.val hi, YjvB_eq_totBlockB t s j.val hj] at heq
    dsimp only
    by_cases hdir : (t.1.get s).1 = QueryDir.fwd
    · rw [if_pos hdir]
      rw [bitCipher_fwd t s hdir] at heq
      linear_combination (norm := char2_norm) heq
    · rw [if_neg hdir]
      rw [bitPlain_inv t s (QueryDir.eq_inv_of_ne_fwd hdir)] at heq
      linear_combination (norm := char2_norm) heq
  · have hqs := hq s le_rfl
    have hij' : i.val ≠ j.val := Nat.ne_of_lt hij
    dsimp only
    by_cases hdir : (t.1.get s).1 = QueryDir.fwd
    · rw [if_pos hdir, if_pos (show (t'.1.get s).1 = QueryDir.fwd from by
        rw [← hqs]; exact hdir), bitPlain_eq_of_fwd hqs hdir, hblocks i.val hij']
    · rw [if_neg hdir, if_neg (show ¬ (t'.1.get s).1 = QueryDir.fwd from by
        rw [← hqs]; exact hdir),
        bitCipher_eq_of_inv hqs (QueryDir.eq_inv_of_ne_fwd hdir),
        hblocks i.val hij']

set_option maxHeartbeats 8000000 in
/-- **Sorted per-pair dispatch, `R`-side, SINGLE-CHARGE conditional twin**, charging
`bitCellWeightR'`.  Same sorted case tree as the D twin; the four single-leg arms copy
verbatim, and the five multi-leg arms collapse their kind-disjoint (and, on the
same-query head–tail arm, direction-disjoint) legs to a single charge per valid pair via
`ite_add_ite_of_disjoint`/`ite_add_ite_dir`/`ite_kind_or`.  (Oracle:
`bit_cell_R_cond_le'`.) -/
theorem bit_cell_R_cond_le' (Hfs : HashFamilyS F T (L + 2))
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects TweakablePRP.NP E)
    (p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)))
    (hp : capRank p.1 < capRank p.2) :
    (bitExtH E.1).mass
      (fun tz => bitCapValid tz.1 p.1 ∧ bitCapValid tz.1 p.2 ∧
        RfullBFix bb Hfs.toHashFamily tz.2 tz.1 p.1
          = RfullBFix bb Hfs.toHashFamily tz.2 tz.1 p.2)
      ≤ expectW (bitExtD E.1) (bitCellWeightR' Hfs p) := by
  obtain ⟨(b₁ | ⟨r, i⟩), (b₂ | ⟨s, j⟩)⟩ := p
  · -- inl–inl (single leg, verbatim)
    cases b₁ <;> cases b₂
    · exact absurd hp (by simp [capRank])
    · refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
        (fun t d => d.1 = d.2.1)
        (fun t => bitCapValid t (Sum.inl false) ∧ bitCapValid t (Sum.inl true))
        (fun _ => (Fintype.card F : NNReal)⁻¹)
        (fun _ _ h => ⟨h.1, h.2.1⟩)
        (fun t _ _ => revealhbarB_L_le)
        (fun t d h => h.2.2)) (le_of_eq rfl)
    · exact absurd hp (by simp [capRank])
    · exact absurd hp (by simp [capRank])
  · -- inl–inr
    by_cases hj : j.val = 0
    · -- heads (single leg, verbatim)
      cases b₁
      · refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
          (fun t d => d.1 = UUvB bb Hfs.toHashFamily d t s)
          (fun t => bitCapValid t (Sum.inl false) ∧ bitCapValid t (Sum.inr (s, j)))
          (fun t => (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F)
          (fun _ _ h => ⟨h.1, h.2.1⟩)
          (fun t _ _ => revealhbarB_UUvB_le_sharp bb Hfs t s)
          (fun t d h => ?_)) (le_of_eq ?_)
        · have heq := h.2.2
          rw [RfullBFix_inr_zero bb Hfs.toHashFamily _ t s j hj] at heq
          exact heq
        · congr 1
          funext td
          simp [bitCellWeightR', bitCellRawR', hj]
      · refine le_trans (bitPairMassH_cond_wexp_le_of_reveal bb E hE _
          (fun t d => d.2.1 = UUvB bb Hfs.toHashFamily d t s)
          (fun t => bitCapValid t (Sum.inl true) ∧ bitCapValid t (Sum.inr (s, j)))
          (fun _ => (Fintype.card F : NNReal)⁻¹)
          (fun _ _ h => ⟨h.1, h.2.1⟩)
          (fun t _ _ => revealLB_UUvB_le bb Hfs.toHashFamily t s)
          (fun t d h => ?_)) (le_of_eq ?_)
        · have heq := h.2.2
          rw [RfullBFix_inr_zero bb Hfs.toHashFamily _ t s j hj] at heq
          exact heq
        · congr 1
          funext td
          simp [bitCellWeightR', bitCellRawR', hj]
    · -- vs the `j ≥ 1` column: kind collapse (`1/N`)
      cases b₁
      · -- h̄ row
        have hY : (bitExtH E.1).mass
            (fun tz => ((bitCapValid tz.1 (Sum.inl false) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
                ∧ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
              ∧ tz.2.1 = YjvB tz.1 s (j.val - 1))
            ≤ expectW (bitExtD E.1) (fun td =>
                if (bitCapValid td.1 (Sum.inl false) ∧ bitCapValid td.1 (Sum.inr (s, j)))
                    ∧ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
                then (Fintype.card F : NNReal)⁻¹ else 0) :=
          bitPairMassH_cond_wexp_le_of_reveal bb E hE _
            (fun t d => d.1 = YjvB t s (j.val - 1))
            (fun t => (bitCapValid t (Sum.inl false) ∧ bitCapValid t (Sum.inr (s, j)))
              ∧ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
            (fun _ => (Fintype.card F : NNReal)⁻¹)
            (fun _ _ h => h.1)
            (fun t _ _ => revealhbarB_const_le (YjvB t s (j.val - 1)))
            (fun t d h => h.2)
        refine le_trans (le_trans
          (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _)
            (fun tz h => ?_))
          (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _)
            (add_le_add hY
              (bit_lastB_hbar_ks_le bb Hfs E hE false s j)))) (le_of_eq ?_)
        · have heq := h.2.2
          by_cases hle : j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val
          · rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · rw [RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq.symm⟩
        · rw [expectW_add]
          congr 1
          funext td
          rw [ite_add_ite_of_disjoint (Fintype.card F : NNReal)⁻¹ (fun hh => hh.2.2 hh.1.2),
            ite_kind_or]
          simp [bitCellWeightR', bitCellRawR', hj]
      · -- L row
        have hY : (bitExtH E.1).mass
            (fun tz => ((bitCapValid tz.1 (Sum.inl true) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
                ∧ j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val)
              ∧ tz.2.2.1 = YjvB tz.1 s (j.val - 1))
            ≤ expectW (bitExtD E.1) (fun td =>
                if (bitCapValid td.1 (Sum.inl true) ∧ bitCapValid td.1 (Sum.inr (s, j)))
                    ∧ j.val ≤ (splitIdx (bitPlain td.1 s).1).1.val
                then (Fintype.card F : NNReal)⁻¹ else 0) :=
          bitPairMassH_cond_wexp_le_of_reveal bb E hE _
            (fun t d => d.2.1 = YjvB t s (j.val - 1))
            (fun t => (bitCapValid t (Sum.inl true) ∧ bitCapValid t (Sum.inr (s, j)))
              ∧ j.val ≤ (splitIdx (bitPlain t s).1).1.val)
            (fun _ => (Fintype.card F : NNReal)⁻¹)
            (fun _ _ h => h.1)
            (fun t _ _ => revealLB_const_le (YjvB t s (j.val - 1)))
            (fun t d h => h.2)
        refine le_trans (le_trans
          (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _)
            (fun tz h => ?_))
          (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _)
            (add_le_add hY
              (bit_lastB_L_ks_le bb Hfs E hE true s j)))) (le_of_eq ?_)
        · have heq := h.2.2
          by_cases hle : j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val
          · rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · rw [RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq.symm⟩
        · rw [expectW_add]
          congr 1
          funext td
          rw [ite_add_ite_of_disjoint (Fintype.card F : NNReal)⁻¹ (fun hh => hh.2.2 hh.1.2),
            ite_kind_or]
          simp [bitCellWeightR', bitCellRawR', hj]
  · -- inr–inl: unsorted
    exfalso
    cases b₂ <;> simp [capRank] at hp
  · -- inr–inr
    rcases capRank_lt_inr_inr hp with hrs | ⟨rfl, hij⟩
    · by_cases hj : j.val = 0
      · by_cases hi : i.val = 0
        · -- uuCross (single leg, verbatim): max/N + 1/N
          rw [show bitCellWeightR' Hfs (Sum.inr (r, i), Sum.inr (s, j))
                = (fun td => (if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
                    then (max (bitMsgDeg Hfs (bitTweak td.1 r) (bitCipher td.1 r))
                          (bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s)) : NNReal)
                        / Fintype.card F else 0)
                  + (if bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j))
                    then (Fintype.card F : NNReal)⁻¹ else 0)) from by
              funext td
              simp only [bitCellWeightR', bitCellRawR']
              rw [if_neg (Fin.ne_of_lt hrs),
                if_pos (show i.val = 0 ∧ j.val = 0 from ⟨hi, hj⟩), ite_add_ite_zero],
            ← expectW_add]
          refine le_trans
            (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _)
              (fun tz h => ?_))
            (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _)
              (add_le_add
                (bit_pairR_UU_UU_sdec_cond_le bb Hfs E hE r s i j hrs)
                (bit_pairR_UU_UU_senc_cond_le bb Hfs E hE r s i j hrs)))
          have heq := h.2.2
          rw [RfullBFix_inr_zero bb Hfs.toHashFamily tz.2 tz.1 r i hi,
            RfullBFix_inr_zero bb Hfs.toHashFamily tz.2 tz.1 s j hj] at heq
          rcases hdd : (tz.1.1.get s).1 with _ | _
          · exact Or.inr ⟨⟨h.1, h.2.1⟩, heq, rfl⟩
          · exact Or.inl ⟨⟨h.1, h.2.1⟩, heq, rfl⟩
        · -- `Yᵢʳ` vs `UUˢ` collapse (kind on earlier index `i`): dˢ/N
          have hY : (bitExtH E.1).mass
              (fun tz => ((bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
                  ∧ i.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val)
                ∧ YjvB tz.1 r (i.val - 1) = UUvB bb Hfs.toHashFamily tz.2 tz.1 s)
              ≤ expectW (bitExtD E.1) (fun td =>
                  if (bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
                      ∧ i.val ≤ (splitIdx (bitPlain td.1 r).1).1.val
                  then (bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) : NNReal)
                    / Fintype.card F else 0) := by
            refine bitPairMassH_cond_wexp_le_of_reveal bb E hE _
              (fun t d => YjvB t r (i.val - 1) = UUvB bb Hfs.toHashFamily d t s)
              (fun t => (bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
                ∧ i.val ≤ (splitIdx (bitPlain t r).1).1.val)
              (fun t => (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F)
              (fun _ _ h => h.1) (fun t _ _ => ?_) (fun t d h => h.2)
            rw [Dist.mass_congr _ (fun z => eq_comm)]
            exact revealUUvB_YjvB_le_sharp bb Hfs t s r (i.val - 1)
          have hLast : (bitExtH E.1).mass
              (fun tz => ((bitCapValid tz.1 (Sum.inr (r, i)) ∧ bitCapValid tz.1 (Sum.inr (s, j)))
                  ∧ ¬ i.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val)
                ∧ tz.2.2.2 r = UUvB bb Hfs.toHashFamily tz.2 tz.1 s)
              ≤ expectW (bitExtD E.1) (fun td =>
                  if (bitCapValid td.1 (Sum.inr (r, i)) ∧ bitCapValid td.1 (Sum.inr (s, j)))
                      ∧ ¬ i.val ≤ (splitIdx (bitPlain td.1 r).1).1.val
                  then (bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) : NNReal)
                    / Fintype.card F else 0) :=
            bitPairMassH_cond_wexp_le_of_reveal bb E hE _
              (fun t d => (bitHybrid bb t d).2.2 r = UUvB bb Hfs.toHashFamily (bitHybrid bb t d) t s)
              (fun t => (bitCapValid t (Sum.inr (r, i)) ∧ bitCapValid t (Sum.inr (s, j)))
                ∧ ¬ i.val ≤ (splitIdx (bitPlain t r).1).1.val)
              (fun t => (bitMsgDeg Hfs (bitTweak t s) (bitCipher t s) : NNReal) / Fintype.card F)
              (fun _ _ h => h.1) (fun t _ _ => bit_lastB_UUvB_any_sharp bb Hfs t r s)
              (fun t d h => h.2)
          refine le_trans (le_trans (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _) (fun tz h => ?_))
            (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _) (add_le_add hY hLast))) (le_of_eq ?_)
          · have heq := h.2.2
            rw [RfullBFix_inr_zero bb Hfs.toHashFamily tz.2 tz.1 s j hj] at heq
            by_cases hle : i.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val
            · rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 r i hi hle] at heq
              exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
            · rw [RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 r i hi hle] at heq
              exact Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · rw [expectW_add]
            congr 1
            funext td
            rw [ite_add_ite_of_disjoint
                ((bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) : NNReal) / Fintype.card F)
                (fun hh => hh.2.2 hh.1.2),
              ite_kind_or]
            simp only [bitCellWeightR', bitCellRawR']
            rw [if_neg (Fin.ne_of_lt hrs),
              if_neg (show ¬(i.val = 0 ∧ j.val = 0) from fun hh => hi hh.1), if_pos hj]
      · -- `j ≥ 1` cross collapse (kind on (s,j)): 1/N
        refine le_trans (le_trans (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _) (fun tz h => ?_))
          (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _) (add_le_add
            (bit_pairR_cross_Y_pin_plain_ks_le bb Hfs E hE r s i j hj hrs
              (fun z t => RfullBFix bb Hfs.toHashFamily z t (Sum.inr (r, i)))
              (fun z t t' _ _ hq' hr'' _ _ =>
                RfullBFix_hybrid_congr bb Hfs.toHashFamily z i (hq' r hrs.le) (hr'' r hrs)))
            (bit_lastB_stable_ks_le bb Hfs E hE r s i j hrs
              (fun z t => RfullBFix bb Hfs.toHashFamily z t (Sum.inr (r, i)))
              (fun d d' t t' _ _ hd1 _ hd3 hq' hr'' _ =>
                RfullBFix_hybrid_congr₂ bb Hfs.toHashFamily d d' i hd1
                  (hd3 r (Fin.ne_of_lt hrs)) (hq' r hrs.le) (hr'' r hrs)))))) (le_of_eq ?_)
        · have heq := h.2.2
          by_cases hle : j.val ≤ (splitIdx (bitPlain tz.1 s).1).1.val
          · rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · rw [RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 s j hj hle] at heq
            exact Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq.symm⟩
        · rw [expectW_add]
          congr 1
          funext td
          rw [ite_add_ite_of_disjoint (Fintype.card F : NNReal)⁻¹ (fun hh => hh.2.2 hh.1.2),
            ite_kind_or]
          simp only [bitCellWeightR', bitCellRawR']
          rw [if_neg (Fin.ne_of_lt hrs),
            if_neg (show ¬(i.val = 0 ∧ j.val = 0) from fun hh => hj hh.2), if_neg hj]
    · -- same query, `i < j`
      have hj0 : j.val ≠ 0 := by omega
      by_cases hi : i.val = 0
      · -- `UUˢ` vs `Yⱼˢ`/last collapse (direction-split lastB): 1/N
        refine le_trans (le_trans (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _) (fun tz h => ?_))
          (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _) (add_le_add
            (bit_pairR_UU_Y_same_plain_ks_le bb Hfs E hE r i j hj0)
            (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _) (add_le_add
              (bit_lastB_UU_same_sdec_ks_le bb Hfs E hE r i j)
              (bit_lastB_UU_same_senc_ks_le bb Hfs E hE r i j)))))) (le_of_eq ?_)
        · have heq := h.2.2
          rw [RfullBFix_inr_zero bb Hfs.toHashFamily tz.2 tz.1 r i hi] at heq
          by_cases hle : j.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val
          · rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 r j hj0 hle] at heq
            exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · rw [RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 r j hj0 hle] at heq
            rcases hdd : (tz.1.1.get r).1 with _ | _
            · exact Or.inr (Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle, rfl⟩, heq.symm⟩)
            · exact Or.inr (Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle, rfl⟩, heq.symm⟩)
        · rw [expectW_add, expectW_add]
          congr 1
          funext td
          rw [ite_add_ite_dir ((td.1.1.get r).1) (Fintype.card F : NNReal)⁻¹,
            ite_add_ite_of_disjoint (Fintype.card F : NNReal)⁻¹ (fun hh => hh.2.2 hh.1.2),
            ite_kind_or]
          simp [bitCellWeightR', bitCellRawR']
      · -- `Yᵢˢ` vs `Yⱼˢ`/last collapse (kind on (s,j)): 1/N
        refine le_trans (le_trans (CR18.mass_mono (extendedTranscriptDistRep_nonNeg _ _ _ _) (fun tz h => ?_))
          (le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _) (add_le_add
            (bit_pairR_Y_Y_same_plain_ks_le bb Hfs E hE r i j hi hij)
            (bit_lastB_YjvB_same_ks_le bb Hfs E hE r i j hi)))) (le_of_eq ?_)
        · have heq := h.2.2
          have hvj : j.val < mBlocksBit tz.1 r := h.2.1
          have hvj' : j.val < (splitIdx (bitPlain tz.1 r).1).1.val + 2 := hvj
          by_cases hle : j.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val
          · have hile : i.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val := by omega
            rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 r i hi hile,
              RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 r j hj0 hle] at heq
            exact Or.inl ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq⟩
          · have hile : i.val ≤ (splitIdx (bitPlain tz.1 r).1).1.val := by omega
            rw [RfullBFix_inr_Y bb Hfs.toHashFamily tz.2 tz.1 r i hi hile,
              RfullBFix_inr_last bb Hfs.toHashFamily tz.2 tz.1 r j hj0 hle] at heq
            exact Or.inr ⟨⟨⟨h.1, h.2.1⟩, hle⟩, heq.symm⟩
        · rw [expectW_add]
          congr 1
          funext td
          rw [ite_add_ite_of_disjoint (Fintype.card F : NNReal)⁻¹ (fun hh => hh.2.2 hh.1.2),
            ite_kind_or]
          simp [bitCellWeightR', bitCellRawR']

/-! ### Counting and the budget (oracle "Counting and the budget" / PHASE P1 C2)

The per-transcript weighted count `bitW` (the paper's §3.4.3 bad-cell total, closed
numerator over `2^{n+1}`), its budget lemma against the paper's σ-accounted constant,
and the exact single-charge slack decomposition (`bit_count_diag`/`bit_count_cross`/
`bit_count_core`) that closes the nine-class numerator against it. -/

/-- **The paper's σ-accounted bad budget**, the exact constants of ePrint 2021/1441
p.17: `(3σ² + 2qσ + 7σ + 2)/2^{n+1}` with the per-transcript block budget `σ`
(`Σ dˢ ≤ σ`, p.10) in place of the uniform-cap `σ = q·d`.  `/2^{n+1} = /(2·|F|)` since
`|F| = 2ⁿ`.  (Oracle: `bitBadBudgetSigma`.) -/
noncomputable def bitBadBudgetSigma (q σB : ℕ) : NNReal :=
  ((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) / (2 * Fintype.card F)

/-- **Bad-bound summation arithmetic** (paper §3.4.3): the `c`-corrected sum of
per-pair collision bounds closes to the `§3.4` numerator.  With `σ_m ≤ σ+2` the
numerator `2·C(σ_m,2) + (c_b+c_f+c_w+c_a)` (`c_b=−1`, `c_f≤2σ`, `c_w≤0`,
`c_a≤(q−1)σ+C(σ,2)`) is `≤ (3σ²+2qσ+7σ+2)/2`; doubled, exact.  (Oracle:
`hctr_bad_summation`, `HTechnique/HCTR2.lean`.) -/
theorem hctr_bad_summation (σm σ q : ℕ) (hq : 1 ≤ q) (hσm : 2 ≤ σm)
    (hle : σm ≤ σ + 2) :
    2 * (2 * σm.choose 2 - 1 + 2 * σ + (q - 1) * σ + σ.choose 2)
      ≤ 3 * σ ^ 2 + 2 * q * σ + 7 * σ + 2 := by
  -- monotonize `C(σm,2) ≤ C(σ+2,2)`; after that the bound is exact
  have h1 : 1 ≤ σm.choose 2 := by simpa using Nat.choose_le_choose 2 hσm
  have hm : (σm.choose 2 : ℤ) ≤ ((σ + 2).choose 2 : ℤ) := by
    exact_mod_cast Nat.choose_le_choose 2 hle
  have e1 : (2 : ℤ) * (σ + 2).choose 2 = ((σ : ℤ) + 2) * ((σ : ℤ) + 1) := by
    rw [two_mul_choose_two_int]; push_cast; ring
  have e2 := two_mul_choose_two_int σ
  zify [hq, show 1 ≤ 2 * σm.choose 2 by omega]
  linarith

/-- **The per-transcript weighted count**: the paper's §3.4.3 per-transcript bad-cell
total `W t`, as its closed numerator value over `2^{n+1}`.  `σ = sigmaDBit twBlocks t`
carries the per-query `bitD` weights of the green cells.  (Oracle: `bitW`.) -/
noncomputable def bitW (twBlocks : T → ℕ) (t : TranscriptPrefix HQB HMB q) : NNReal :=
  ((2 * (2 * (sigmaMBit t).choose 2 - 1 + 2 * sigmaDBit twBlocks t
      + (q - 1) * sigmaDBit twBlocks t + (sigmaDBit twBlocks t).choose 2) : ℕ) : NNReal)
    / (2 * Fintype.card F)

/-- **The per-transcript budget lemma** (paper §3.4.3): every `σB`-budget transcript's
weighted count is within `bitBadBudgetSigma q σB`.  Assembly: `hctr_bad_summation` at
`σm := σ_m t`, `σ := sigmaDBit t` (hypotheses `2 ≤ σ_m` and `σ_m ≤ σ + 2` via
`sigmaMBit_le_sigmaDBit_add_two`) bounds the count by `3σ²+2qσ+7σ+2`; the budget filter
`σ ≤ σB` lifts that to the `σB` numerator.  (Oracle: `bitW_le`.) -/
theorem bitW_le (twBlocks : T → ℕ) (hq : 1 ≤ q)
    (t : TranscriptPrefix HQB HMB q) {σB : ℕ}
    (hbudget : sigmaDBit twBlocks t ≤ σB) :
    bitW twBlocks t ≤ bitBadBudgetSigma (F := F) q σB := by
  have hsum := hctr_bad_summation (sigmaMBit t) (sigmaDBit twBlocks t) q hq
    (by unfold sigmaMBit; omega)
    (sigmaMBit_le_sigmaDBit_add_two twBlocks t)
  have hmono : 3 * sigmaDBit twBlocks t ^ 2 + 2 * q * sigmaDBit twBlocks t
        + 7 * sigmaDBit twBlocks t + 2
      ≤ 3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 := by gcongr
  have hAB : 2 * (2 * (sigmaMBit t).choose 2 - 1 + 2 * sigmaDBit twBlocks t
        + (q - 1) * sigmaDBit twBlocks t + (sigmaDBit twBlocks t).choose 2)
      ≤ 3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 := le_trans hsum hmono
  unfold bitW bitBadBudgetSigma
  gcongr


/-- **Per-query (diagonal) slack** of the single-charge count: the doubled per-query
charges (const–head greens `2dP + dC`, the `L`-const `1`, six `1/N`-tails, and the
same-query tail–tail pairs) are within the per-query budget allocation.  (Oracle:
`bit_count_diag`.) -/
theorem bit_count_diag (m d dP dC : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d)
    (hdP : dP ≤ d) (hdC : dC ≤ d) :
    2 * (2 * dP + dC + 1 + 6 * (m - 1)) + (m - 1) * (m - 1 - 1)
      ≤ (m - 1) * (m - 1 - 1) + m * (m - 1) + 10 * (m - 1) + 8 + 4 * d
        + d * (d - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
  obtain ⟨f, rfl⟩ : ∃ f, d = f + (a + 2) := ⟨d - (a + 2), by omega⟩
  have e1 : a + 2 - 1 = a + 1 := by omega
  have e2 : a + 1 - 1 = a := by omega
  have e3 : f + (a + 2) - 1 = f + (a + 1) := by omega
  rw [e1, e2, e3]
  nlinarith [hdP, hdC, sq_nonneg a, sq_nonneg f]

/-- **Per-cross-pair slack** of the single-charge count.  Reduces to
`max dP + max dC + aʳ·dCˢ ≤ aʳ + dʳ + dˢ + dʳdˢ`; the `dʳ > dˢ` case is paid by the
tweak-block excess `dʳ − aʳ ≥ 1` — exactly where `mʳ ≤ dʳ` is load-bearing.  (Oracle:
`bit_count_cross`.) -/
theorem bit_count_cross (mr ms dr ds dPr dPs dCr dCs : ℕ)
    (hmr : 2 ≤ mr) (hmrd : mr ≤ dr) (hds : 1 ≤ ds)
    (hdPr : dPr ≤ dr) (hdPs : dPs ≤ ds) (hdCr : dCr ≤ dr) (hdCs : dCs ≤ ds) :
    2 * (max dPr dPs + max dCr dCs + 2 + 2 * (ms - 1) + (1 + dCs) * (mr - 1)
        + 2 * ((mr - 1) * (ms - 1)))
      ≤ 4 + 4 * ((mr - 1) * (ms - 1)) + 4 * ((mr - 1) + (ms - 1))
        + 2 * (dr + ds) + 2 * (dr * ds) := by
  have hP : max dPr dPs ≤ max dr ds :=
    max_le (hdPr.trans (le_max_left dr ds)) (hdPs.trans (le_max_right dr ds))
  have hC : max dCr dCs ≤ max dr ds :=
    max_le (hdCr.trans (le_max_left dr ds)) (hdCs.trans (le_max_right dr ds))
  obtain ⟨a, rfl⟩ : ∃ a, mr = a + 2 := ⟨mr - 2, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, dr = g + (a + 2) := ⟨dr - (a + 2), by omega⟩
  have e1 : a + 2 - 1 = a + 1 := by omega
  rw [e1]
  rcases le_total (g + (a + 2)) ds with h | h
  · rw [max_eq_right h] at hP hC
    nlinarith [hdCs, hP, hC, hds]
  · rw [max_eq_left h] at hP hC
    nlinarith [hdCs, hP, hC, hds]

/-- **The count core** (paper §3.4.3, exact single-charge accounting): the doubled
nine-class numerator is within the doubled `bitW` numerator.  Stated over abstract
per-query data `(m, d, dP, dC)` — the count instantiates it at
`mBlocksBit / bitD / bitMsgDeg(plain) / bitMsgDeg(cipher)`.  (Oracle:
`bit_count_core`.) -/
theorem bit_count_core {q : ℕ} (m d dP dC : Fin q → ℕ)
    (hm : ∀ s, 2 ≤ m s) (hmd : ∀ s, m s ≤ d s)
    (hdP : ∀ s, dP s ≤ d s) (hdC : ∀ s, dC s ≤ d s) :
    2 * (1 + (∑ s, (2 * dP s + dC s + 1 + 6 * (m s - 1) + (m s - 1).choose 2))
      + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
          (max (dP p.1) (dP p.2) + max (dC p.1) (dC p.2) + 2
            + 2 * (m p.2 - 1) + (1 + dC p.2) * (m p.1 - 1)
            + 2 * ((m p.1 - 1) * (m p.2 - 1))))
      ≤ 2 * (2 * (2 + ∑ s, m s).choose 2 - 1 + 2 * (∑ s, d s)
          + (q - 1) * (∑ s, d s) + (∑ s, d s).choose 2) := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hLexp : 2 * (1 + (∑ s, (2 * dP s + dC s + 1 + 6 * (m s - 1)
        + (m s - 1).choose 2))
      + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
          (max (dP p.1) (dP p.2) + max (dC p.1) (dC p.2) + 2
            + 2 * (m p.2 - 1) + (1 + dC p.2) * (m p.1 - 1)
            + 2 * ((m p.1 - 1) * (m p.2 - 1))))
      = 2 + (∑ s, (2 * (2 * dP s + dC s + 1 + 6 * (m s - 1))
            + (m s - 1) * (m s - 1 - 1)))
        + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
            2 * (max (dP p.1) (dP p.2) + max (dC p.1) (dC p.2) + 2
              + 2 * (m p.2 - 1) + (1 + dC p.2) * (m p.1 - 1)
              + 2 * ((m p.1 - 1) * (m p.2 - 1))) := by
    rw [Nat.mul_add, Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by
      rw [Nat.mul_add, two_mul_choose_two])
  rw [hLexp]
  have hstep : 2 + (∑ s, (2 * (2 * dP s + dC s + 1 + 6 * (m s - 1))
        + (m s - 1) * (m s - 1 - 1)))
      + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
          2 * (max (dP p.1) (dP p.2) + max (dC p.1) (dC p.2) + 2
            + 2 * (m p.2 - 1) + (1 + dC p.2) * (m p.1 - 1)
            + 2 * ((m p.1 - 1) * (m p.2 - 1)))
      ≤ 2 + (∑ s, ((m s - 1) * (m s - 1 - 1) + m s * (m s - 1)
            + 10 * (m s - 1) + 8 + 4 * d s + d s * (d s - 1)))
        + ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
            (4 + 4 * ((m p.1 - 1) * (m p.2 - 1))
              + 4 * ((m p.1 - 1) + (m p.2 - 1))
              + 2 * (d p.1 + d p.2) + 2 * (d p.1 * d p.2)) := by
    refine Nat.add_le_add (Nat.add_le_add le_rfl (Finset.sum_le_sum
      (fun s _ => bit_count_diag (m s) (d s) (dP s) (dC s)
        (hm s) (hmd s) (hdP s) (hdC s)))) (Finset.sum_le_sum (fun p hp => ?_))
    exact bit_count_cross (m p.1) (m p.2) (d p.1) (d p.2)
      (dP p.1) (dP p.2) (dC p.1) (dC p.2)
      (hm p.1) (hmd p.1) (le_trans (by omega) (le_trans (hm p.2) (hmd p.2)))
      (hdP p.1) (hdP p.2) (hdC p.1) (hdC p.2)
  refine le_trans hstep ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, card_filter_fin_lt, smul_eq_mul]
  have hSaa : (∑ s, (m s - 1) * (m s - 1 - 1)) + (∑ s, (m s - 1))
      = ∑ s, (m s - 1) * (m s - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => Counting.mul_pred_add _)
  have hSmm : (∑ s, m s * (m s - 1)) + (∑ s, m s) = ∑ s, m s * m s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => Counting.mul_pred_add _)
  have hSdd : (∑ s, d s * (d s - 1)) + (∑ s, d s) = ∑ s, d s * d s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => Counting.mul_pred_add _)
  have hSm2 : (∑ s, m s * m s)
      = (∑ s, (m s - 1) * (m s - 1)) + (2 * ∑ s, (m s - 1)) + q := by
    have hpt : ∀ s : Fin q, m s * m s
        = (m s - 1) * (m s - 1) + 2 * (m s - 1) + 1 := by
      intro s
      obtain ⟨a, ha⟩ : ∃ a, m s = a + 1 := ⟨m s - 1, by have := hm s; omega⟩
      rw [ha]
      simp only [Nat.succ_sub_one]
      ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hMq : (∑ s, m s) = (∑ s, (m s - 1)) + q := by
    have hpt : ∀ s : Fin q, m s = (m s - 1) + 1 := fun s => by
      have := hm s; omega
    rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
  have hSA : (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
        (m p.1 - 1))
      + (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
        (m p.2 - 1))
      = (q - 1) * ∑ s, (m s - 1) := by
    have h := Counting.sum_sorted_add (ι := Fin q) (fun s => m s - 1)
    rwa [Fintype.card_fin, Finset.sum_add_distrib] at h
  have hSD : (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
        d p.1)
      + (∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
        d p.2)
      = (q - 1) * ∑ s, d s := by
    have h := Counting.sum_sorted_add (ι := Fin q) (fun s => d s)
    rwa [Fintype.card_fin, Finset.sum_add_distrib] at h
  have hAA : (∑ s, (m s - 1)) * (∑ s, (m s - 1))
      = (∑ s, (m s - 1) * (m s - 1))
        + 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
            ((m p.1 - 1) * (m p.2 - 1)) :=
    Counting.sq_sum_eq_sum_sq_add_two_mul_sorted (ι := Fin q) (fun s => m s - 1)
  have hσσ : (∑ s, d s) * (∑ s, d s)
      = (∑ s, d s * d s)
        + 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2),
            (d p.1 * d p.2) :=
    Counting.sq_sum_eq_sum_sq_add_two_mul_sorted (ι := Fin q) (fun s => d s)
  have hσm2 : 2 * (2 + ∑ s, m s).choose 2
      = (∑ s, m s) * (∑ s, m s) + 3 * (∑ s, m s) + 2 := by
    have h := two_mul_choose_two (2 + ∑ s, m s)
    have h2 : 2 + (∑ s, m s) - 1 = (∑ s, m s) + 1 := by omega
    rw [h2] at h
    rw [h]
    ring
  have hσ2 : 2 * (∑ s, d s).choose 2 + (∑ s, d s)
      = (∑ s, d s) * (∑ s, d s) := by
    rw [two_mul_choose_two]
    exact Counting.mul_pred_add _
  have hq2 : 2 * q.choose 2 + q = q * q := by
    rw [two_mul_choose_two]
    exact Counting.mul_pred_add _
  have hMM : (∑ s, m s) * (∑ s, m s)
      = (∑ s, (m s - 1)) * (∑ s, (m s - 1))
        + 2 * (q * (∑ s, (m s - 1))) + q * q := by
    rw [hMq]
    ring
  have hqA : (q - 1) * (∑ s, (m s - 1)) + (∑ s, (m s - 1))
      = q * (∑ s, (m s - 1)) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.succ_sub_one]
    ring
  have hqσ : (q - 1) * (∑ s, d s) + (∑ s, d s) = q * (∑ s, d s) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.succ_sub_one]
    ring
  omega

set_option maxHeartbeats 1600000 in
/-- **The single-charge per-transcript count** (C2, PROVEN): the
validity-gated sum of the D-side (`bitCellWeightD`) and single-charge R-side
(`bitCellWeightR'`) per-pair charges over the sorted cap pairs is within
`bitW` — on length-matched transcripts (`hmatch`; the C3 consumer supplies it
from the ideal support, which vanishes off length-match by `bitIdeal_zero`).
Stated in the exact shape the C3 assembly consumes after `expectW_sum_swap`.
(Oracle: `bit_cellWeight_sum_le`.) -/
theorem bit_cellWeight_sum_le
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (hmatch : ∀ s : Fin q, (td.1.2.get s).1 = (td.1.1.get s).2.2.1) :
    (∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)) =>
          capRank p.1 < capRank p.2),
        (bitCellWeightD bb be Hfs p td + bitCellWeightR' Hfs p td))
      ≤ bitW twBlocks td.1 := by
  classical
  -- the four data families of the count
  have hm2 : ∀ s : Fin q, 2 ≤ mBlocksBit td.1 s := fun s => Nat.le_add_left 2 _
  have hmd : ∀ s : Fin q, mBlocksBit td.1 s ≤ bitD twBlocks td.1 s :=
    fun s => Nat.le_add_right _ _
  have hdPf : ∀ s : Fin q,
      bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
        ≤ bitD twBlocks td.1 s :=
    fun s => bit_degB_le_bitD Hfs twBlocks hdegB td.1 s
  have hdCf : ∀ s : Fin q,
      bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s)
        ≤ bitD twBlocks td.1 s := by
    intro s
    have hcp : (bitCipher td.1 s).1 = (bitPlain td.1 s).1 := by
      rw [bitCipher_fst td.1 s (hmatch s), bitPlain_fst td.1 s (hmatch s)]
    have h := bit_degB_le_bitD Hfs twBlocks hdegB td.1 s
    unfold bitMsgDeg at h ⊢
    rw [hcp]
    exact h
  -- merge the two validity gates pointwise, then block-split
  have hval : ∀ p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)),
      bitCellWeightD bb be Hfs p td + bitCellWeightR' Hfs p td
      = if bitCapValid td.1 p.1 ∧ bitCapValid td.1 p.2 then
          bitCellRawD bb be Hfs p td.1 + bitCellRawR' Hfs p td.1 else 0 :=
    fun p => ite_add_ite_zero _ _
  rw [Finset.sum_congr rfl (fun p _ => hval p),
    sum_sorted_capSplit capRank
      (by simp)
      (fun b x => capRank_inl_lt_inr b x.1 x.2)
      (fun x b => by
        obtain ⟨s', j'⟩ := x
        cases b <;> simp only [capRank_inr, capRank_inl_false,
          capRank_inl_true] <;> omega)
      (fun r i s j => capRank_lt_inr_inr_iff)]
  dsimp only
  -- block A: the sorted constant pair `(h̄-row, L-row)` — `1/N`
  have hA : (if bitCapValid td.1 (Sum.inl false) ∧ bitCapValid td.1 (Sum.inl true)
      then bitCellRawD bb be Hfs (Sum.inl false, Sum.inl true) td.1
        + bitCellRawR' Hfs (Sum.inl false, Sum.inl true) td.1 else 0)
      = ((1 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹ := by
    simp [bitCapValid, bitCellRawD, bitCellRawR']
  -- block B: const–entry rows, gated head/tail sum per query
  have hB : ∀ s : Fin q, (∑ j : Fin (L + 2),
      ((if bitCapValid td.1 (Sum.inl false) ∧ bitCapValid td.1 (Sum.inr (s, j))
        then bitCellRawD bb be Hfs (Sum.inl false, Sum.inr (s, j)) td.1
          + bitCellRawR' Hfs (Sum.inl false, Sum.inr (s, j)) td.1 else 0)
      + (if bitCapValid td.1 (Sum.inl true) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then bitCellRawD bb be Hfs (Sum.inl true, Sum.inr (s, j)) td.1
            + bitCellRawR' Hfs (Sum.inl true, Sum.inr (s, j)) td.1 else 0)))
      = ((2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
            + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1
            + 4 * (mBlocksBit td.1 s - 1) : ℕ) : NNReal)
          * (Fintype.card F : NNReal)⁻¹ := by
    intro s
    have hpt : ∀ j : Fin (L + 2),
        ((if bitCapValid td.1 (Sum.inl false) ∧ bitCapValid td.1 (Sum.inr (s, j))
          then bitCellRawD bb be Hfs (Sum.inl false, Sum.inr (s, j)) td.1
            + bitCellRawR' Hfs (Sum.inl false, Sum.inr (s, j)) td.1 else 0)
        + (if bitCapValid td.1 (Sum.inl true) ∧ bitCapValid td.1 (Sum.inr (s, j))
            then bitCellRawD bb be Hfs (Sum.inl true, Sum.inr (s, j)) td.1
              + bitCellRawR' Hfs (Sum.inl true, Sum.inr (s, j)) td.1 else 0))
        = if j.val < mBlocksBit td.1 s then
            (if j.val = 0 then
              ((2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
                + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1 : ℕ)
                  : NNReal) * (Fintype.card F : NNReal)⁻¹
             else ((4 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹)
          else 0 := by
      intro j
      simp only [bitCapValid, bitCellRawD, bitCellRawR', true_and,
        div_eq_mul_inv, Bool.false_eq_true, eq_self_iff_true, if_true,
        if_false]
      split_ifs <;>
        first
          | rfl
          | (push_cast; ring1)
          | (exfalso; omega)
          | (hctr2_ite_arith)
    rw [Finset.sum_congr rfl (fun j _ => hpt j),
      sum_fin_gate (le_trans one_le_two (hm2 s)) (mBlocksBit_le_cap td.1 s)]
    obtain ⟨a, ha⟩ : ∃ x, mBlocksBit td.1 s - 1 = x := ⟨_, rfl⟩
    rw [ha, nsmul_eq_mul]
    push_cast
    ring
  -- block C: cross-query entries, gated product sum per sorted query pair
  have hC : ∀ rs : Fin q × Fin q, rs.1 < rs.2 →
      (∑ i : Fin (L + 2), ∑ j : Fin (L + 2),
        (if bitCapValid td.1 (Sum.inr (rs.1, i))
            ∧ bitCapValid td.1 (Sum.inr (rs.2, j)) then
          bitCellRawD bb be Hfs (Sum.inr (rs.1, i), Sum.inr (rs.2, j)) td.1
            + bitCellRawR' Hfs (Sum.inr (rs.1, i), Sum.inr (rs.2, j)) td.1
          else 0))
      = ((max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitPlain td.1 rs.1))
              (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitPlain td.1 rs.2))
          + max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitCipher td.1 rs.1))
              (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
          + 2 + 2 * (mBlocksBit td.1 rs.2 - 1)
          + (1 + bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
              * (mBlocksBit td.1 rs.1 - 1)
          + 2 * ((mBlocksBit td.1 rs.1 - 1) * (mBlocksBit td.1 rs.2 - 1)) : ℕ)
          : NNReal) * (Fintype.card F : NNReal)⁻¹ := by
    intro rs hrs
    have hne : rs.1 ≠ rs.2 := ne_of_lt hrs
    rw [← Fintype.sum_prod_type']
    have hpt : ∀ p : Fin (L + 2) × Fin (L + 2),
        (if bitCapValid td.1 (Sum.inr (rs.1, p.1))
            ∧ bitCapValid td.1 (Sum.inr (rs.2, p.2)) then
          bitCellRawD bb be Hfs (Sum.inr (rs.1, p.1), Sum.inr (rs.2, p.2)) td.1
            + bitCellRawR' Hfs (Sum.inr (rs.1, p.1), Sum.inr (rs.2, p.2)) td.1
          else 0)
        = if p.1.val < mBlocksBit td.1 rs.1 ∧ p.2.val < mBlocksBit td.1 rs.2
          then (if p.1.val = 0 then
              (if p.2.val = 0 then
                ((max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitPlain td.1 rs.1))
                    (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitPlain td.1 rs.2))
                  + max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitCipher td.1 rs.1))
                      (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
                  + 2 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹
               else ((2 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹)
            else (if p.2.val = 0 then
                ((1 + bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2)
                  : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹
               else ((2 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹))
          else 0 := by
      intro p
      clear hval hA hB hmatch hm2 hmd hdPf hdCf hdegB
      by_cases h1 : p.1.val < mBlocksBit td.1 rs.1 <;>
        by_cases h2 : p.2.val < mBlocksBit td.1 rs.2 <;>
          by_cases h3 : p.1.val = 0 <;> by_cases h4 : p.2.val = 0 <;>
            simp_all [bitCapValid, bitCellRawD, bitCellRawR',
              div_eq_mul_inv] <;>
          first
            | rfl
            | (push_cast; ring1)
            | (exfalso; omega)
            | (hctr2_ite_arith)
    rw [Finset.sum_congr rfl (fun p _ => hpt p),
      sum_fin_gate_prod (le_trans one_le_two (hm2 rs.1))
        (mBlocksBit_le_cap td.1 rs.1) (le_trans one_le_two (hm2 rs.2))
        (mBlocksBit_le_cap td.1 rs.2)]
    obtain ⟨ar, har⟩ : ∃ x, mBlocksBit td.1 rs.1 - 1 = x := ⟨_, rfl⟩
    obtain ⟨as', has⟩ : ∃ x, mBlocksBit td.1 rs.2 - 1 = x := ⟨_, rfl⟩
    rw [har, has]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  -- block D: same-query entries, gated sorted sum per query
  have hD : ∀ s : Fin q, (∑ i : Fin (L + 2), ∑ j : Fin (L + 2),
      (if i.val < j.val then
        (if bitCapValid td.1 (Sum.inr (s, i))
            ∧ bitCapValid td.1 (Sum.inr (s, j)) then
          bitCellRawD bb be Hfs (Sum.inr (s, i), Sum.inr (s, j)) td.1
            + bitCellRawR' Hfs (Sum.inr (s, i), Sum.inr (s, j)) td.1
          else 0) else 0))
      = ((2 * (mBlocksBit td.1 s - 1) + (mBlocksBit td.1 s - 1).choose 2 : ℕ)
          : NNReal) * (Fintype.card F : NNReal)⁻¹ := by
    intro s
    rw [← Fintype.sum_prod_type']
    have hpt : ∀ p : Fin (L + 2) × Fin (L + 2),
        (if p.1.val < p.2.val then
          (if bitCapValid td.1 (Sum.inr (s, p.1))
              ∧ bitCapValid td.1 (Sum.inr (s, p.2)) then
            bitCellRawD bb be Hfs (Sum.inr (s, p.1), Sum.inr (s, p.2)) td.1
              + bitCellRawR' Hfs (Sum.inr (s, p.1), Sum.inr (s, p.2)) td.1
            else 0) else 0)
        = if p.1.val < p.2.val ∧ p.2.val < mBlocksBit td.1 s then
            (if p.1.val = 0 then
              ((2 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹
             else ((1 : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹)
          else 0 := by
      intro p
      clear hval hA hB hC hmatch hm2 hmd hdPf hdCf hdegB
      by_cases h0 : p.1.val < mBlocksBit td.1 s <;>
        by_cases h1 : p.1.val < p.2.val <;>
          by_cases h2 : p.2.val < mBlocksBit td.1 s <;>
            by_cases h3 : p.1.val = 0 <;>
              simp only [bitCapValid, bitCellRawD, bitCellRawR',
                div_eq_mul_inv, h0, h1, h2, h3, eq_self_iff_true, if_true,
                if_false, true_and, and_true, false_and, and_false, and_self,
                not_true, not_false_iff, ite_self] <;>
            first
              | rfl
              | (push_cast; ring1)
              | (exfalso; omega)
              | (hctr2_ite_arith)
    rw [Finset.sum_congr rfl (fun p _ => hpt p),
      sum_fin_gate_sorted (mBlocksBit_le_cap td.1 s)]
    obtain ⟨a, ha⟩ : ∃ x, mBlocksBit td.1 s - 1 = x := ⟨_, rfl⟩
    rw [ha]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hA, Finset.sum_congr rfl (fun s _ => hB s),
    Finset.sum_congr rfl (fun rs hrs => hC rs (Finset.mem_filter.mp hrs).2),
    Finset.sum_congr rfl (fun s _ => hD s)]
  -- collect all blocks into a single ℕ numerator over `1/N`
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum]
  have hcollect : (((1 : ℕ) : NNReal))
        * (Fintype.card F : NNReal)⁻¹
      + ((∑ s : Fin q, (2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
            + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1
            + 4 * (mBlocksBit td.1 s - 1)) : ℕ) : NNReal)
          * (Fintype.card F : NNReal)⁻¹
      + ((((∑ rs ∈ Finset.univ.filter (fun rs : Fin q × Fin q => rs.1 < rs.2),
            (max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitPlain td.1 rs.1))
                (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitPlain td.1 rs.2))
              + max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitCipher td.1 rs.1))
                  (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
              + 2 + 2 * (mBlocksBit td.1 rs.2 - 1)
              + (1 + bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
                  * (mBlocksBit td.1 rs.1 - 1)
              + 2 * ((mBlocksBit td.1 rs.1 - 1) * (mBlocksBit td.1 rs.2 - 1)))
            : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹)
        + ((∑ s : Fin q, (2 * (mBlocksBit td.1 s - 1)
              + (mBlocksBit td.1 s - 1).choose 2) : ℕ) : NNReal)
            * (Fintype.card F : NNReal)⁻¹)
      = ((1 + (∑ s : Fin q,
            (2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
              + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1
              + 6 * (mBlocksBit td.1 s - 1)
              + (mBlocksBit td.1 s - 1).choose 2))
          + ∑ rs ∈ Finset.univ.filter (fun rs : Fin q × Fin q => rs.1 < rs.2),
              (max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitPlain td.1 rs.1))
                  (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitPlain td.1 rs.2))
                + max (bitMsgDeg Hfs (bitTweak td.1 rs.1) (bitCipher td.1 rs.1))
                    (bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
                + 2 + 2 * (mBlocksBit td.1 rs.2 - 1)
                + (1 + bitMsgDeg Hfs (bitTweak td.1 rs.2) (bitCipher td.1 rs.2))
                    * (mBlocksBit td.1 rs.1 - 1)
                + 2 * ((mBlocksBit td.1 rs.1 - 1) * (mBlocksBit td.1 rs.2 - 1)))
          : ℕ) : NNReal) * (Fintype.card F : NNReal)⁻¹ := by
    have hmerge : (∑ s : Fin q,
          (2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
            + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1
            + 4 * (mBlocksBit td.1 s - 1)))
        + (∑ s : Fin q, (2 * (mBlocksBit td.1 s - 1)
            + (mBlocksBit td.1 s - 1).choose 2))
        = ∑ s : Fin q,
            (2 * bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s)
              + bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s) + 1
              + 6 * (mBlocksBit td.1 s - 1)
              + (mBlocksBit td.1 s - 1).choose 2) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun s _ => by omega)
    rw [← hmerge]
    push_cast
    ring
  rw [hcollect]
  -- close against the σ-budget numerator via the count core
  unfold bitW
  refine cast_mul_inv_le_div _ _ _ ?_
  have hcore := bit_count_core (fun s => mBlocksBit td.1 s)
    (fun s => bitD twBlocks td.1 s)
    (fun s => bitMsgDeg Hfs (bitTweak td.1 s) (bitPlain td.1 s))
    (fun s => bitMsgDeg Hfs (bitTweak td.1 s) (bitCipher td.1 s))
    hm2 hmd hdPf hdCf
  simpa [sigmaMBit, sigmaDBit] using hcore

/-- **Budget corollary** (C2 → paper budget): under the `σB`-budget filter the
single-charge count lands within the paper's `bitBadBudgetSigma q σB` — the
form the C3 assembly's `expectW_le_of_support_bound` consumes.  Chains
`bit_cellWeight_sum_le` with `bitW_le`.  (Oracle: `bit_cellWeight_sum_le_budget`.) -/
theorem bit_cellWeight_sum_le_budget
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ) (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F))) {σB : ℕ}
    (hbudget : sigmaDBit twBlocks td.1 ≤ σB)
    (hmatch : ∀ s : Fin q, (td.1.2.get s).1 = (td.1.1.get s).2.2.1) :
    (∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)) =>
          capRank p.1 < capRank p.2),
        (bitCellWeightD bb be Hfs p td + bitCellWeightR' Hfs p td))
      ≤ bitBadBudgetSigma (F := F) q σB :=
  le_trans (bit_cellWeight_sum_le bb be Hfs twBlocks hdegB td hmatch)
    (bitW_le twBlocks hq td.1 hbudget)

/-! ### The σ-budgeted union bound and the bad-event bound (oracle C3)

The assembly that consumes the PROVEN count: `mass_sorted_pair_le_of_embed` at the sharp
conditional dispatch twins (`bit_cell_D_cond_le` / `bit_cell_R_cond_le'`, whose per-pair
bounds are `expectW`-weighted cell charges over the dummy ideal extension), the `expectW`
sum-swap, the per-transcript count `bit_cellWeight_sum_le_budget` on the ideal support
(where the `bitNPB` filter and the length-match hold), and `bitW_le` down to the paper's
`bitBadBudgetSigma q σB = (3σB² + 2qσB + 7σB + 2)/(2·|F|)`. -/

/-- **Ideal-support extraction** (the C3 support facts; filter-generic): a
transcript–reveal pair carrying dummy-ideal mass under a `Filt`-respecting environment
satisfies the filter and is length-matched.  (Oracle: `bitIdealExtD_support`.) -/
theorem bitIdealExtD_support {Filt : TranscriptPrefix HQB HMB q → Prop}
    (E : QQueryEnvironment HQB HMB q) (hE : EnvRespects Filt E)
    (td : TranscriptPrefix HQB HMB q × (F × F × (Fin q → F)))
    (hne : (bitExtD E.1) td ≠ 0) :
    Filt td.1 ∧ ∀ i : Fin q, (td.1.2.get i).1 = (td.1.1.get i).2.2.1 := by
  obtain ⟨t, z⟩ := td
  rw [bitIdealExt_apply E.1 t z] at hne
  have htr : (tr[q](TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T),
      E.1)) t ≠ 0 := by
    intro h
    rw [h, mul_zero] at hne
    exact hne rfl
  unfold TweakablePRP.rnd at htr
  rw [deterministicTranscriptDist_apply_eq_sysFactor_mul_envFactor,
    sysFactor_functionEvaluator] at htr
  have hcon : E.1 ⊨ t := by
    by_contra hcon
    rw [envFactor_eq_indicator, if_neg hcon, mul_zero] at htr
    exact htr rfl
  refine ⟨hE t hcon, ?_⟩
  by_contra hm
  rw [mass_eq_zero_of_forall _
    (fun g hg => (hm fun i => by rw [← hg i]; rfl).elim), zero_mul] at htr
  exact htr rfl

/-- **Layer-4 union bound at the paper budget** (C3): the combined `D`/`R` collision mass
under the hybrid ideal extension is within the σ-accounted `bitBadBudgetSigma q σB`, over
`bitNPB`-respecting environments.  (Oracle: `bit_col_bound`.) -/
theorem bit_col_bound (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ)
    {σB : ℕ} (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (E : QQueryEnvironment HQB HMB q)
    (hE : EnvRespects (bitNPB twBlocks σB) E) :
    (bitExtH E.1).mass
        (fun tz => ∃ a b : DRIdxBit (L := L) (n := n) tz.1, a ≠ b ∧
          DfullB bb be Hfs.toHashFamily tz.2 tz.1 a
            = DfullB bb be Hfs.toHashFamily tz.2 tz.1 b)
      + (bitExtH E.1).mass
        (fun tz => ∃ a b : DRIdxBit (L := L) (n := n) tz.1, a ≠ b ∧
          RfullB bb Hfs.toHashFamily tz.2 tz.1 a
            = RfullB bb Hfs.toHashFamily tz.2 tz.1 b)
      ≤ bitBadBudgetSigma (F := F) q σB := by
  have hEnp : EnvRespects TweakablePRP.NP E := fun t ht => (hE t ht).1
  refine le_trans (add_le_add
    (mass_sorted_pair_le_of_embed
      (extendedTranscriptDistRep_nonNeg bitIdealP bitIdealF (bitIdealAugH bb) E.1)
      capRank capRank_injective
      (ι := fun tz => DRIdxBit (L := L) (n := n) tz.1)
      (fun tz => drIncludeBit tz.1) (fun tz => drIncludeBit_injective tz.1)
      (fun tz => DfullB bb be Hfs.toHashFamily tz.2 tz.1)
      (fun tz k => bitCapValid tz.1 k)
      (fun tz k => DfullBFix bb be Hfs.toHashFamily tz.2 tz.1 k)
      (fun tz a => bitCapValid_drIncludeBit tz.1 a)
      (fun tz a => DfullBFix_drIncludeBit bb be Hfs.toHashFamily tz.2 tz.1 a)
      (fun p => expectW (bitExtD E.1) (bitCellWeightD bb be Hfs p))
      (fun p hp => bit_cell_D_cond_le bb be Hfs E hEnp p hp))
    (mass_sorted_pair_le_of_embed
      (extendedTranscriptDistRep_nonNeg bitIdealP bitIdealF (bitIdealAugH bb) E.1)
      capRank capRank_injective
      (ι := fun tz => DRIdxBit (L := L) (n := n) tz.1)
      (fun tz => drIncludeBit tz.1) (fun tz => drIncludeBit_injective tz.1)
      (fun tz => RfullB bb Hfs.toHashFamily tz.2 tz.1)
      (fun tz k => bitCapValid tz.1 k)
      (fun tz k => RfullBFix bb Hfs.toHashFamily tz.2 tz.1 k)
      (fun tz a => bitCapValid_drIncludeBit tz.1 a)
      (fun tz a => RfullBFix_drIncludeBit bb Hfs.toHashFamily tz.2 tz.1 a)
      (fun p => expectW (bitExtD E.1) (bitCellWeightR' Hfs p))
      (fun p hp => bit_cell_R_cond_le' bb Hfs E hEnp p hp))) ?_
  rw [expectW_sum_swap, expectW_sum_swap, expectW_add]
  have hmerge : (fun td => (∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)) =>
          capRank p.1 < capRank p.2), bitCellWeightD bb be Hfs p td)
      + ∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)) =>
          capRank p.1 < capRank p.2), bitCellWeightR' Hfs p td)
      = fun td => ∑ p ∈ Finset.univ.filter
        (fun p : (Bool ⊕ Fin q × Fin (L + 2)) × (Bool ⊕ Fin q × Fin (L + 2)) =>
          capRank p.1 < capRank p.2),
        (bitCellWeightD bb be Hfs p td + bitCellWeightR' Hfs p td) :=
    funext (fun td => (Finset.sum_add_distrib).symm)
  rw [hmerge]
  refine le_trans (expectW_le_of_support_bound
    (extendedTranscriptDistRep_nonNeg _ _ _ _) _
    (bitBadBudgetSigma (F := F) q σB) (fun td hne => ?_)) ?_
  · obtain ⟨hfilt, hmatch⟩ := bitIdealExtD_support E hE td hne
    exact bit_cellWeight_sum_le_budget bb be Hfs twBlocks hq hdegB td
      hfilt.2 hmatch
  · rw [extendedTranscriptDistRep_weight, pmf_bitIdeal_eq,
      deterministicTranscriptDist_weight_eq_one _ E TweakablePRP.rnd_KStepTotal, mul_one]

/-- **The bad-event bound at the paper budget** (C3): the mass of `bitBad` under the
hybrid ideal extension is within `bitBadBudgetSigma q σB` over `bitNPB`-respecting
environments — the `Pr[bitBad ∣ hybrid ext] ≤ budget` form the main lemma consumes.
(Oracle: `bit_bad_bound`.) -/
theorem bit_bad_bound (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ)
    {σB : ℕ} (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (E : QQueryEnvironment HQB HMB q)
    (hE : EnvRespects (bitNPB twBlocks σB) E) :
    Pr[bitBad bb be Hfs.toHashFamily ∣
        extendedTranscriptDistRep (q := q) bitIdealP bitIdealF
          (bitIdealAugH bb) E.1] ≤
      bitBadBudgetSigma (F := F) q σB :=
  -- NOTE (Part-1 `bad_bound` convention): the disjunct predicates stay `_` — explicit
  -- lambdas force a non-pattern higher-order defeq against `bitBad` (whnf blowup);
  -- metavariables pattern-unify instantly.
  le_trans (mass_or_le (extendedTranscriptDistRep_nonNeg _ _ _ _) _ _)
    (bit_col_bound bb be Hfs twBlocks hq hdegB E hE)

end BitStage5Leaves

/-! ### The bit-level theorems

The statements are final (constants pinned to ePrint 2021/1441 p. 17 at `σ = σB`, the
per-transcript block budget); the main-lemma proof — extraction, reveal, and the σ-budgeted
union bound at the bit carriers — is the Part-2 program. -/

/-- **The main lemma, bit level** (paper §3.4 at the σ-accounted constants): against the
paper's adversary class (`bitNPB`), bit-level HCTR2 over a uniform permutation is
`(3σ² + 2qσ + 7σ + 2)/2ⁿ⁺¹`-close to `±rnd`, `σ = σB`.  `hdegB` ties the hash degree to
the honest block count: `degB t k ≤ k + ⌈|Tˢ|/n⌉`. -/
theorem hctr2Bit_main_lemma (bb : BlockBits F n) (be : BinEnc F L)
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ) {σB : ℕ} (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t') :
    filteredAdaptiveTranscriptAdvantage (q := q) (bitNPB twBlocks σB)
        (hctr2BitReal bb be Hfs.toHashFamily)
        (TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) ≤
      (((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) /
        (2 * Fintype.card F) : ℝ) := by
  rw [← pmf_bitReal_eq bb be Hfs.toHashFamily, ← pmf_bitIdeal_eq]
  refine le_of_le_of_eq
    (adv_le_of_extFixedQueryRep_ratio_of_good_filtered
      (q := q) (bitNPB twBlocks σB) bitRealP (bitRealF bb be Hfs.toHashFamily)
      bitIdealP bitIdealF
      (bitRealAug bb be Hfs.toHashFamily) (bitIdealAugH bb)
      (bitBad bb be Hfs.toHashFamily) 0 (bitBadBudgetSigma (F := F) q σB)
      (functionEvaluatorProb_KStepTotal _ _ q)
      (functionEvaluatorProb_KStepTotal _ _ q)
      (fun xs tz h_good => by
        rw [NNReal.coe_zero, sub_zero, one_mul]
        exact bitSigma_ratio bb be Hfs.toHashFamily xs tz h_good)
      (fun E hE => bit_bad_bound bb be Hfs twBlocks hq hdegB E hE)) ?_
  rw [add_zero]
  simp [bitBadBudgetSigma]

/-- **HCTR2 security, bit level** (paper §3.5, Theorem p. 17 over the abstract field): for
the paper's adversary class — no pointless queries, at most `σB` blocks of total work —

    Adv±p̃rp_{HCTR2[Perm F]}(q, σB) ≤ (3σ² + 2qσ + 7σ + 2)/2ⁿ⁺¹ + C(q,2)/2ⁿ,  σ = σB.

Assembly: filtered triangle through `±rnd`, the main lemma, and the bit PRP-RND leg lifted
along `bitNPB ⟹ TweakablePRP.NP` (`filteredAdv_mono`). -/
theorem hctr2Bit_security (bb : BlockBits F n) (be : BinEnc F L)
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ) {σB : ℕ} (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t') :
    filteredAdaptiveTranscriptAdvantage (q := q) (bitNPB twBlocks σB)
        (hctr2BitReal bb be Hfs.toHashFamily)
        (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) ≤
      (((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) /
          (2 * Fintype.card F) +
        (choose2 q : NNReal) / Fintype.card F : ℝ) := by
  refine le_trans (filteredAdv_triangle (bitNPB twBlocks σB)
    (hctr2BitReal bb be Hfs.toHashFamily)
    (TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T))
    (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T))
    (hctr2BitReal_KStepTotal bb be Hfs.toHashFamily) TweakablePRP.rnd_KStepTotal) ?_
  refine add_le_add (hctr2Bit_main_lemma bb be Hfs twBlocks hq hdegB) ?_
  rw [filteredAdv_symm (bitNPB twBlocks σB)
    (TweakablePRP.rnd (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T))
    (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T))
    TweakablePRP.rnd_KStepTotal TweakablePRP.tprp_KStepTotal]
  exact le_trans (filteredAdv_mono TweakablePRP.NP (bitNPB twBlocks σB) (fun t ht => ht.1)
    _ _ TweakablePRP.tprp_KStepTotal) bit_tprp_rnd

/-! ### The unrestricted-adversary reduction, bit level (pointless-query WLOG)

Bit twin of Part 1's §"unrestricted-adversary reduction", declaration-for-declaration at
the bit carriers (oracle: `HCTR2Bit.lean` §PointlessWlog).  The generic converter is again
`SelfAnswerFilter` (`Derivation.lean`); this section supplies its bit-level instance
(`ptl`/`det`/`pad` and their laws) and the hand-off `bit_input_fresh_NP`: stepwise
freshness ⟹ the `TweakablePRP.NP` filter — directly through `bit_pinnedIO_get`, no `facIO`/HEq
machinery. -/

section BitPointlessWlog

variable (bb : BlockBits F n) (be : BinEnc F L) (Hfb : HashFamily F T (L + 2))

/-- Direction normalizer for a constraint's `(plaintext, ciphertext)` payload (mirror of
Part 1's `sides`; oracle: `bitSides`). -/
private def bitSides : QueryDir → HMB × HMB → HMB × HMB
  | QueryDir.fwd, p => p
  | QueryDir.inv, p => p.swap

/-- The permutation constraints established by a list of query/answer pairs:
`(tweak, plaintext, ciphertext)` triples, direction-normalized (mirror of Part 1's
`constraints`; oracle: `bitConstraints`). -/
private def bitConstraints (l : List (HQB × HMB)) : List (T × HMB × HMB) :=
  l.map (fun xy => match xy.1.1 with
    | QueryDir.fwd => (xy.1.2.1, xy.1.2.2, xy.2)
    | QueryDir.inv => (xy.1.2.1, xy.2, xy.1.2.2))

/-- A query is *checkably pointless* against a history when some established constraint
shares its tweak and its input side (mirror of Part 1's `isPointless`; oracle:
`bitIsPointless`). -/
private def bitIsPointless (l : List (HQB × HMB)) (x : HQB) : Prop :=
  match x.1 with
  | QueryDir.fwd => ∃ c ∈ bitConstraints l, c.1 = x.2.1 ∧ c.2.1 = x.2.2
  | QueryDir.inv => ∃ c ∈ bitConstraints l, c.1 = x.2.1 ∧ c.2.2 = x.2.2

/-- The `find?` predicate of `bitDeterminedAnswer`: the constraint matches the query's
tweak and input side (mirror of Part 1's `matchesQ`; oracle: `bitMatches`). -/
private def bitMatchesQ (x : HQB) (c : T × HMB × HMB) : Bool :=
  match x.1 with
  | QueryDir.fwd => decide (c.1 = x.2.1 ∧ c.2.1 = x.2.2)
  | QueryDir.inv => decide (c.1 = x.2.1 ∧ c.2.2 = x.2.2)

/-- The answer determined by a pointless query: the output side of the first matching
constraint (junk default `x.2.2` when none matches — never consulted when `bitIsPointless`
holds; mirror of Part 1's `determinedAnswer`; oracle: `bitDeterminedAnswer`). -/
private def bitDeterminedAnswer (l : List (HQB × HMB)) (x : HQB) : HMB :=
  match (bitConstraints l).find? (bitMatchesQ x) with
  | none => x.2.2
  | some c => match x.1 with
    | QueryDir.fwd => c.2.2
    | QueryDir.inv => c.2.1

/-- Pointlessness makes the `find?` of `bitDeterminedAnswer` succeed (mirror of Part 1's
`isPointless_find?_isSome`; oracle: `bitIsPointless_find?_isSome`). -/
private theorem bitIsPointless_find?_isSome (l : List (HQB × HMB)) (x : HQB)
    (h : bitIsPointless l x) :
    ((bitConstraints l).find? (bitMatchesQ x)).isSome := by
  rw [List.find?_isSome]
  obtain ⟨d, tw, m⟩ := x
  cases d <;>
  · obtain ⟨c, hc, h1, h2⟩ := h
    exact ⟨c, hc, by simp [bitMatchesQ, h1, h2]⟩

/-- **`find?`-spec of the determined answer** (both directions, `bitSides`-unified; mirror
of Part 1's `determinedAnswer_spec`; oracle: `bitDeterminedAnswer_spec`). -/
private theorem bitDeterminedAnswer_spec (l : List (HQB × HMB)) (x : HQB)
    (c : T × HMB × HMB)
    (hfind : (bitConstraints l).find? (bitMatchesQ x) = some c) :
    c ∈ bitConstraints l ∧ c.1 = x.2.1 ∧ (bitSides x.1 c.2).1 = x.2.2 ∧
      bitDeterminedAnswer l x = (bitSides x.1 c.2).2 := by
  obtain ⟨d, tw, m⟩ := x
  have hmem := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  cases d <;>
  · simp only [bitMatchesQ, decide_eq_true_eq] at hp
    exact ⟨hmem, hp.1, hp.2, by unfold bitDeterminedAnswer; rw [hfind]; rfl⟩

/-- Pointlessness is monotone in the history (mirror of Part 1's `isPointless_mono`;
oracle: `bitIsPointless_mono`). -/
private theorem bitIsPointless_mono {l l' : List (HQB × HMB)}
    (hsub : ∀ p ∈ l, p ∈ l') {x : HQB}
    (h : bitIsPointless l x) : bitIsPointless l' x := by
  have hc : ∀ c ∈ bitConstraints l, c ∈ bitConstraints l' := by
    intro c hcm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcm
    exact List.mem_map.mpr ⟨p, hsub p hp, rfl⟩
  obtain ⟨d, tw, msg⟩ := x
  cases d
  · obtain ⟨c, hcm, h1, h2⟩ := h
    exact ⟨c, hc c hcm, h1, h2⟩
  · obtain ⟨c, hcm, h1, h2⟩ := h
    exact ⟨c, hc c hcm, h1, h2⟩

/-- Constraint view of a pair-prefix, index form (mirror of Part 1's
`constraints_pairs_mem`; oracle: `bitConstraints_pairs_mem`). -/
private theorem bitConstraints_pairs_mem (t : TranscriptPrefix HQB HMB q) (m : ℕ)
    (c : T × HMB × HMB) :
    c ∈ bitConstraints (TranscriptPrefix.pairs t m) ↔
      ∃ k : Fin q, k.val < m ∧ c = (bitTweak t k, bitPlain t k, bitCipher t k) := by
  have hval : ∀ k : Fin q,
      (match (t.1.get k).1 with
        | QueryDir.fwd => ((t.1.get k).2.1, (t.1.get k).2.2, t.2.get k)
        | QueryDir.inv => ((t.1.get k).2.1, t.2.get k, (t.1.get k).2.2)) =
        (bitTweak t k, bitPlain t k, bitCipher t k) := by
    intro k
    unfold bitTweak bitPlain bitCipher
    cases (t.1.get k).1 <;> rfl
  unfold bitConstraints
  rw [List.mem_map]
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (TranscriptPrefix.mem_pairs_iff t m xy).mp hxy
    exact ⟨k, hk, hval k⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(t.1.get k, t.2.get k),
      (TranscriptPrefix.mem_pairs_iff t m _).mpr ⟨k, hk, rfl⟩, hval k⟩

/-- An earlier index sharing the tweak and the later query's **input side** makes the
later query checkably pointless against its pair-prefix (mirror of Part 1's
`pointless_of_share`; oracle: `bit_pointless_of_share`). -/
private theorem bit_pointless_of_share (t : TranscriptPrefix HQB HMB q) {r m : Fin q}
    (hrm : r.val < m.val)
    (hT : bitTweak t r = bitTweak t m)
    (hP : (t.1.get m).1 = QueryDir.fwd → bitPlain t r = (t.1.get m).2.2)
    (hC : (t.1.get m).1 = QueryDir.inv → bitCipher t r = (t.1.get m).2.2) :
    bitIsPointless (TranscriptPrefix.pairs t m.val) (t.1.get m) := by
  have hc : (bitTweak t r, bitPlain t r, bitCipher t r) ∈
      bitConstraints (TranscriptPrefix.pairs t m.val) :=
    (bitConstraints_pairs_mem t m.val _).mpr ⟨r, hrm, rfl⟩
  unfold bitIsPointless
  rcases hd : (t.1.get m).1 with _ | _
  · exact ⟨_, hc, hT, hP hd⟩
  · exact ⟨_, hc, hT, hC hd⟩

/-- **Stepwise freshness forces the `TweakablePRP.NP` filter** (the `SelfAnswerFilter` hand-off;
mirror of Part 1's `input_fresh_NP`): a literal repeat is checkably pointless at the later
index, and two same-tweak steps pinning the same `(plaintext, ciphertext)` pair —
`bit_pinnedIO_get` — make the later one checkably pointless through its shared input side.
(The oracle's `bit_input_fresh_NP` routes through its `lpNPV`/`facIO` HEq bridges; the
consolidated `TweakablePRP.NP` filter takes the pinned pair directly.) -/
private theorem bit_input_fresh_NP (t : TranscriptPrefix HQB HMB q)
    (hfresh : ∀ m : Fin q,
      ¬ bitIsPointless (TranscriptPrefix.pairs t m.val) (t.1.get m)) :
    TweakablePRP.NP t := by
  constructor
  · -- injectivity: a literal repeat is checkably pointless at the later index
    intro a b hab
    have key : ∀ r s : Fin q, r < s → t.1.get r = t.1.get s → False := by
      intro r s hrs hq
      exact hfresh s (bit_pointless_of_share t hrs (congrArg (fun x => x.2.1) hq)
        (fun hd => by
          rw [bitPlain_fwd t r ((congrArg Prod.fst hq).trans hd)]
          exact congrArg (fun x => x.2.2) hq)
        (fun hd => by
          rw [bitCipher_inv t r ((congrArg Prod.fst hq).trans hd)]
          exact congrArg (fun x => x.2.2) hq))
    rcases lt_trichotomy a b with h | h | h
    · exact (key a b h hab).elim
    · exact h
    · exact (key b a h hab.symm).elim
  · -- pinned-pair injectivity: a shared (tweak, plaintext, ciphertext) triple makes the
    -- later step checkably pointless via its input side
    intro i j hT hmi hmj hpin
    rw [bit_pinnedIO_get, bit_pinnedIO_get, Prod.mk.injEq] at hpin
    have hshare : ∀ {r s : Fin q}, r < s → bitTweak t r = bitTweak t s →
        bitPlain t r = bitPlain t s → bitCipher t r = bitCipher t s → False := by
      intro r s hrs hTs hP hC
      exact hfresh s (bit_pointless_of_share t hrs hTs
        (fun hd => hP.trans (bitPlain_fwd t s hd))
        (fun hd => hC.trans (bitCipher_inv t s hd)))
    rcases lt_trichotomy i j with h | h | h
    · exact (hshare h hT hpin.1 hpin.2).elim
    · exact h
    · exact (hshare h hT.symm hpin.1.symm hpin.2.symm).elim

/-- Correctness (§2.4), inverse composition: `Enc ∘ Dec = id` at every bit length class
(companion of `bitDecCore_bitEncCore`; a left inverse of an injection on a finite fiber is
two-sided; mirror of Part 1's `encCore_decCore`; oracle:
`hctr2BitEncCore_hctr2BitDecCore`). -/
private theorem bitEncCore_bitDecCore (π : Equiv.Perm F) (τ : T) (ℓ : Fin L) (r : Fin n)
    (c : bitMsg F ℓ.val r.val) :
    bitEncCore bb be Hfb π τ ℓ r (bitDecCore bb be Hfb π τ ℓ r c) = c := by
  have hli : Function.LeftInverse (bitDecCore bb be Hfb π τ ℓ r)
      (bitEncCore bb be Hfb π τ ℓ r) := fun p =>
    bitDecCore_bitEncCore bb be Hfb π τ ℓ r p
  exact hli.rightInverse_of_surjective
    (Finite.injective_iff_surjective.mp hli.injective) c

/-- **Coherent two-sided oracle**: per tweak, the forward and inverse directions are
mutually inverse (mirror of Part 1's `Coherent`; oracle: `bitCoherent`). -/
private def bitCoherent (f : HQB → HMB) : Prop :=
  (∀ (tw : T) (msg : HMB), f (QueryDir.inv, tw, f (QueryDir.fwd, tw, msg)) = msg) ∧
  (∀ (tw : T) (msg : HMB), f (QueryDir.fwd, tw, f (QueryDir.inv, tw, msg)) = msg)

/-- World X (bit level) is coherent (Enc/Dec correctness at the sigma level; mirror of
Part 1's `hctr2Fun_coherent`; oracle: `hctr2BitFun_coherent`). -/
private theorem hctr2BitFun_coherent (π : Equiv.Perm F) :
    bitCoherent (hctr2BitFun bb be Hfb π) := by
  constructor
  · rintro tw ⟨k, m⟩
    show (⟨k, bitDecCore bb be Hfb π tw (splitIdx k).1 (splitIdx k).2
        (bitEncCore bb be Hfb π tw (splitIdx k).1 (splitIdx k).2 m)⟩ : HMB) = ⟨k, m⟩
    rw [bitDecCore_bitEncCore]
  · rintro tw ⟨k, m⟩
    show (⟨k, bitEncCore bb be Hfb π tw (splitIdx k).1 (splitIdx k).2
        (bitDecCore bb be Hfb π tw (splitIdx k).1 (splitIdx k).2 m)⟩ : HMB) = ⟨k, m⟩
    rw [bitEncCore_bitDecCore]

/-- World Z (the tweakable strong URP at the bit fibers) is coherent (mirror of Part 1's
`tprpFun_coherent`; oracle: `bit_lpStrongPermFunction_coherent`). -/
private theorem bit_tprpFun_coherent
    (fam : ∀ p : T × Fin (L * n),
      Equiv.Perm (bitMsgL (F := F) (L := L) (n := n) p.2)) :
    bitCoherent (TweakablePRP.tprpFun fam) := by
  constructor
  · rintro tw ⟨k, m⟩
    show (⟨k, (fam (tw, k)).symm (fam (tw, k) m)⟩ : HMB) = ⟨k, m⟩
    rw [Equiv.symm_apply_apply]
  · rintro tw ⟨k, m⟩
    show (⟨k, fam (tw, k) ((fam (tw, k)).symm m)⟩ : HMB) = ⟨k, m⟩
    rw [Equiv.apply_symm_apply]

/-- **Every constraint is a coherent `f`-fact** (mirror of Part 1's `constraints_sound`;
oracle: `bitConstraints_sound`). -/
private theorem bitConstraints_sound {f : HQB → HMB} (hf : bitCoherent f)
    {l : List (HQB × HMB)} (hl : ∀ p ∈ l, p.2 = f p.1)
    {c : T × HMB × HMB} (hc : c ∈ bitConstraints l) :
    f (QueryDir.fwd, c.1, c.2.1) = c.2.2 ∧ f (QueryDir.inv, c.1, c.2.2) = c.2.1 := by
  obtain ⟨p, hp, hcp⟩ := List.mem_map.mp hc
  have hpy := hl p hp
  obtain ⟨⟨d', tw', msg'⟩, y'⟩ := p
  replace hpy : y' = f (d', tw', msg') := hpy
  cases d'
  · -- fwd contributor: `c = (T, M, C)` with `C = f(fwd, T, M)`
    simp only at hcp
    subst hcp
    refine ⟨hpy.symm, ?_⟩
    show f (QueryDir.inv, tw', y') = msg'
    rw [hpy]; exact hf.1 tw' msg'
  · -- inv contributor: `c = (T, M, C)` with `M = f(inv, T, C)`
    simp only at hcp
    subst hcp
    refine ⟨?_, hpy.symm⟩
    show f (QueryDir.fwd, tw', y') = msg'
    rw [hpy]; exact hf.2 tw' msg'

/-- **Coherence determines pointless answers** (mirror of Part 1's `coherent_determined`;
oracle: `bitCoherent_determined`). -/
private theorem bitCoherent_determined {f : HQB → HMB} (hf : bitCoherent f)
    (l : List (HQB × HMB)) (hl : ∀ p ∈ l, p.2 = f p.1) (x : HQB)
    (hx : bitIsPointless l x) :
    f x = bitDeterminedAnswer l x := by
  obtain ⟨c, hfind⟩ := Option.isSome_iff_exists.mp (bitIsPointless_find?_isSome l x hx)
  obtain ⟨hcmem, hc1, hc2, hans⟩ := bitDeterminedAnswer_spec l x c hfind
  obtain ⟨hsfwd, hsinv⟩ := bitConstraints_sound hf hl hcmem
  rw [hans]
  obtain ⟨d, tw, msg⟩ := x
  cases d
  · simp only [bitSides] at hc1 hc2 ⊢
    rw [← hc1, ← hc2]; exact hsfwd
  · simp only [bitSides] at hc1 hc2 ⊢
    rw [← hc1, ← hc2]; exact hsinv

/-- The plaintext-side head blocks of a history's constraints — heads live in the first
block of every bit fiber (mirror of Part 1's `usedHeads`; oracle: `bitUsedHeads`). -/
private def bitUsedHeads (l : List (HQB × HMB)) : Finset F :=
  ((bitConstraints l).map (fun c => c.2.1.2.1)).toFinset

/-- Mirror of Part 1's `usedHeads_card_le` (oracle: `bitUsedHeads_card_le`). -/
private theorem bitUsedHeads_card_le (l : List (HQB × HMB)) :
    (bitUsedHeads l).card ≤ l.length := by
  refine le_trans (List.toFinset_card_le _) ?_
  simp [bitConstraints]

/-- A head-fresh forward pad query is never checkably pointless — the pad sits in the
flattened class `⟨0, hLn⟩` with a zero tail and zero leftover bits, `pickFresh` reused
from Part 1 (mirror of Part 1's `pad_not_pointless`; oracle: `bit_pad_not_pointless`). -/
private theorem bit_pad_not_pointless (t₀ : T) (hLn : 0 < L * n)
    (l : List (HQB × HMB)) (hcard : l.length < Fintype.card F) :
    ¬ bitIsPointless l
      (QueryDir.fwd, t₀, ⟨⟨0, hLn⟩, (pickFresh (bitUsedHeads l), fun _ => 0, 0)⟩) := by
  intro h
  obtain ⟨c, hcm, -, h2⟩ := h
  have hmem : c.2.1.2.1 ∈ bitUsedHeads l := by
    rw [bitUsedHeads, List.mem_toFinset]
    exact List.mem_map.mpr ⟨c, hcm, rfl⟩
  have hhead : c.2.1.2.1 = pickFresh (bitUsedHeads l) := by rw [h2]
  rw [hhead] at hmem
  exact pickFresh_notMem (lt_of_le_of_lt (bitUsedHeads_card_le l) hcard) hmem

/-- **The bit-level HCTR2 self-answering filter** (the `SelfAnswerFilter` instance of the
generic pointless-query WLOG layer; mirror of Part 1's `selfFilter`; oracle: `bitFilter`).
`hqF` is the pad-freshness supply: `q` fresh head blocks must exist. -/
private def bitSelfFilter (t₀ : T) (hLn : 0 < L * n) (hqF : q ≤ Fintype.card F) :
    SelfAnswerFilter HQB HMB q where
  ptl := bitIsPointless
  det := bitDeterminedAnswer
  pad := fun l =>
    (QueryDir.fwd, t₀, ⟨⟨0, hLn⟩, (pickFresh (bitUsedHeads l), fun _ => 0, 0)⟩)
  pad_ok := fun l hl => bit_pad_not_pointless t₀ hLn l (lt_of_lt_of_le hl hqF)
  ptl_mono := by
    intro l l' x hsub h
    exact bitIsPointless_mono hsub h

/-- **Pointless-query WLOG, bit level** (unrestricted reduction — an addition *beyond*
the paper, which assumes §3.4's prohibition; mirror of Part 1's `pointless_wlog`; oracle:
`bit_pointless_wlog`).  `hqF` is the pad-freshness supply. -/
private theorem bit_pointless_wlog (hqF : q ≤ Fintype.card F) :
    Adv[q](hctr2BitReal bb be Hfb,
        TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) ≤
      filteredAdaptiveTranscriptAdvantage (q := q) TweakablePRP.NP (hctr2BitReal bb be Hfb)
        (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) := by
  classical
  have hnn : 0 ≤ filteredAdaptiveTranscriptAdvantage (q := q) TweakablePRP.NP
      (hctr2BitReal bb be Hfb)
      (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) := by
    unfold filteredAdaptiveTranscriptAdvantage
    refine Real.sSup_nonneg ?_
    rintro x ⟨E', -, rfl⟩
    exact statDist_nonneg _ _
  unfold PFunPDS.Prob.adaptiveTranscriptAdvantage
  refine Real.sSup_le ?_ hnn
  rintro x ⟨E, -, rfl⟩
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · -- `q = 0`: the empty transcript vacuously satisfies the filter, so every
    -- environment respects it and the sup already includes this distance.
    subst hq0
    refine statDist_le_filteredAdv TweakablePRP.NP _ _ (hctr2BitReal_KStepTotal bb be Hfb) E ?_
    intro t' _
    exact ⟨fun a => a.elim0, fun i => i.elim0⟩
  · -- `1 ≤ q`: totality at the empty history supplies a tweak, `0 < L * n`, and a junk
    -- message; the generic self-answering layer does the rest (both worlds are
    -- coherent, so determined answers are the true ones).
    obtain ⟨x0, -⟩ := E.2 [] (by simpa using hq)
    exact SelfAnswerFilter.statDist_le_filteredAdv_of_selfAnswer
      (bitSelfFilter x0.2.1 x0.2.2.1.pos hqF) TweakablePRP.NP
      (fun t hfresh => bit_input_fresh_NP t hfresh)
      ⟨Dist.uniform (Equiv.Perm F), Dist.uniform_isProbDist⟩
      ⟨Dist.uniform (∀ p : T × Fin (L * n),
          Equiv.Perm (bitMsgL (F := F) (L := L) (n := n) p.2)),
        Dist.uniform_isProbDist⟩
      (fun π => hctr2BitFun bb be Hfb π)
      (fun fam => TweakablePRP.tprpFun fam)
      (fun π h x hh hp =>
        bitCoherent_determined (hctr2BitFun_coherent bb be Hfb π) h hh x hp)
      (fun fam h x hh hp =>
        bitCoherent_determined (bit_tprpFun_coherent fam) h hh x hp)
      E (x0, x0.2.2)

end BitPointlessWlog

/-- **HCTR2 security, bit level, unrestricted adversaries** (beyond the paper): the same
bound over the plain `Adv[q]`, via the pointless-query WLOG, under a universal σ-budget
`hσB` (with it the `TweakablePRP.NP`- and `bitNPB`-respecting environment classes coincide; e.g.
`σB = q·(L + 1 + B)` for any per-tweak cap `twBlocks ≤ B`, since `mˢ ≤ L + 1`). -/
theorem hctr2Bit_security_unrestricted (bb : BlockBits F n) (be : BinEnc F L)
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ) {σB : ℕ} (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (hσB : ∀ t : TranscriptPrefix HQB HMB q, sigmaDBit twBlocks t ≤ σB) :
    Adv[q](hctr2BitReal bb be Hfs.toHashFamily,
        TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) ≤
      (((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) /
          (2 * Fintype.card F) +
        (choose2 q : NNReal) / Fintype.card F : ℝ) := by
  rcases Nat.lt_or_ge (Fintype.card F) q with hqF | hqF
  swap
  · -- the WLOG's pad-freshness supply `q ≤ |F|` holds: reduce to the `TweakablePRP.NP` filter,
    -- upgrade to `bitNPB` via the universal σ-budget `hσB` (`filteredAdv_mono`), and
    -- compose with `hctr2Bit_security`
    refine le_trans (bit_pointless_wlog bb be Hfs.toHashFamily hqF) ?_
    exact le_trans (filteredAdv_mono (bitNPB twBlocks σB) TweakablePRP.NP
        (fun t ht => ⟨ht, hσB t⟩) _ _ (hctr2BitReal_KStepTotal bb be Hfs.toHashFamily))
      (hctr2Bit_security bb be Hfs twBlocks hq hdegB)
  · -- vacuous regime `q > |F|`:  Adv ≤ 1 ≤ C(q,2)/|F| ≤ RHS (mirror of Part 1's split)
    have hF1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have hAdv : Adv[q](hctr2BitReal bb be Hfs.toHashFamily,
        TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)) ≤
        ((1 : NNReal) : ℝ) :=
      PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise _ _ 1
        (fun E => le_trans
          (statDist_le_weight (deterministicTranscriptDist_nonNeg _ _)
            (deterministicTranscriptDist_nonNeg _ _))
          (deterministicTranscriptDist_weight_le_one _ E
            (hctr2BitReal_KStepTotal bb be Hfs.toHashFamily)))
    have hchoose : Fintype.card F ≤ q.choose 2 := by
      have h2 := two_mul_choose_two_int q
      have hcq : (Fintype.card F : ℤ) + 1 ≤ (q : ℤ) := by exact_mod_cast hqF
      have h1 : (1 : ℤ) ≤ (Fintype.card F : ℤ) := by exact_mod_cast hF1
      have hle : (Fintype.card F : ℤ) ≤ (q.choose 2 : ℤ) := by nlinarith
      exact_mod_cast hle
    have hpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := F)
    have hone : (1 : ℝ) ≤ ((choose2 q : NNReal) : ℝ) / (Fintype.card F : ℝ) := by
      rw [one_le_div hpos]
      have hc : ((Fintype.card F : ℕ) : ℝ) ≤ ((q.choose 2 : ℕ) : ℝ) := by
        exact_mod_cast hchoose
      simpa [choose2] using hc
    refine le_trans hAdv (le_trans (by simpa using hone)
      (le_add_of_nonneg_left (by positivity)))

end RandomSystems.CR18.HCTR2
