/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HCTR2
import RandomSystems.AbsorbDPI
import RandomSystems.GameOf
import RandomSystems.StrictContextSharedDomain
import RandomSystems.Theorem417
import RandomSystems.HTechnique.GF2Field

/-!
# The HCTR2 paper theorem (ePrint 2021/1441 p. 17) over GF(2¹²⁸) + POLYVAL

The paper's Theorem (p. 17) at the paper's own objects and constants — field,
hash, and TRUE arbitrary-bit-string message space: computational substitution
+ concrete hash instance + spec reconciliation, in one file (formerly
`HCTR2Computational.lean` / `HCTR2Instance.lean` / `HCTR2Spec.lean` /
`HCTR2Paper.lean`).

* **Part I — the computational substitution step** (paper §3.5, namespace
  `HCTR2`).  The block cipher is an abstract keyed permutation family
  `E : K → Equiv.Perm F` with a uniform key; the two-sided (±) cipher
  resource is `bcOracle`/`bcE`/`bcPerm`.  Bit-level HCTR2
  (`RandomSystems/HCTR2.lean` Part 2: fibers `bitMsgL`, oracle
  `hctr2BitFun`) is realized as a CR18 protocol converter `bitHctrStep`
  applied to the ± resource — the realization theorem `applyG_bitHctrStep`
  proves `HCTR2[X] = bitHctrStep · (±X)` exactly.  The absorption DPI gives
  the substitution bound `Δ(HCTR2[E], HCTR2[Perm]) ≤ Δ(±E, ±Perm)`, with
  the cipher term filtered to the paper's `σ + 2` query budget
  (`2 + q·(L+1)`, from the distinct-call count `2 + Σₛ mˢ`, `mˢ = ℓˢ + 2`)
  via the de-dup cache (`pad → absorb → cacheDDD`), and the composed
  headline chains through the σ-budgeted endpoint
  `hctr2Bit_security_unrestricted`.  The paper's `t/t′` time terms are a
  resource cost model with no counterpart on this surface (out of scope).
* **Part II — the POLYVAL-class ε-AXU library** (namespace
  `HCTR2Instance`).  The shared root-counting engine
  `uniform_mass_poly_root_le`, the coefficient-block polynomial toolkit
  (`blockPoly`, `polyQ`), a POLYVAL-style `HashFamily` inhabitant
  `polyvalHf` at degree `L + τ + 2`, and the gap-#8 record
  `hashFamilyL_card_le_d` (the unguarded hash abstraction is
  unsatisfiable).
* **Part III — the spec-literal objects** (namespace `HCTR2Spec`).  The
  block↔bits bridge `specBlockBits`, the little-endian encoder `specBin` /
  `specBinEnc`, the RFC-8452 POLYVAL (`POLYVAL`/`polyvalPoly`, dot-unit
  `u`), the paper-form reconciliation (`paperPoly`,
  `polyvalPoly_eq_paperPoly`, `specH_eq_paper_form` — the p. 6–7 display as
  a THEOREM), Appendix-A injectivity (`specH_input_inj`), and the spec hash
  bundles at the honest degree: variable-length-tweak `specHashFamilyV` and
  the σ-accounted sharp `specHashFamilyVS : HashFamilyS`
  (`degB t k = ⌈|T|/n⌉ + k`, so `degB t mˢ = mˢ + ⌈|T|/n⌉ = dˢ` — the paper's
  per-query charge, over the structured tail `BitTailS`).
* **Part IV — the composed paper theorem** (namespace `HCTR2Paper`).
  `hctr2_paper_theorem`: over the paper's field
  `GF(2¹²⁸) = F₂[x]/(x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1)` (`GF2Field.GF128`),
  the paper's `H` (RFC-8452 POLYVAL dot at the honest unit `u = x⁻¹²⁸`,
  σ-accounted: `paperHashS`), and the paper's message space (arbitrary bit
  strings, length classes `(ℓ, r)` with `ℓ < L` whole blocks and `r < 128`
  leftover bits),

      Δ(⌈q⌉ HCTR2[E], ⌈q⌉ ±p̃rp)
        ≤ Δ(⌈2 + q(L+1)⌉ ±E, ⌈2 + q(L+1)⌉ ±Perm)
          + (3σ² + 2qσ + q² + 7σ + 2) / 2¹²⁹ ,   σ = q·(L + τ + 1),

  at the paper's per-query charge `dˢ = mˢ + ⌈|Tˢ|/n⌉` (p. 9): the hash consumes
  the **structured** tail `BitTailS` (paper §3.2), so the green Fig-4/5 cells pay
  exactly `degB t mˢ = dˢ` at every query, and injectivity is the App.-A mode block
  `bin(2|T|+2/3)` (`specBlockV_sigma_inj`) — no invented length block.

The two intermediate security theorems (`hctr2Bit_substitution_sigma`,
`hctr2Bit_security_computational_sigma`) are `private` stepping stones; the
public deliverable is `hctr2_paper_theorem`.  The POLYVAL/polynomial layer
(Parts II–III) is public, reusable ε-AXU library content.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace HTechnique

/-! ## Part I — the computational substitution step (paper §3.5) at the bit carriers -/

namespace HCTR2

open RandomSystems.CR18
open RandomSystems.CR18.HCTR2
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique (QueryDir)
open RandomSystems.HTechnique.HashThenPRF (choose2)
open scoped RandomSystems.CR18.PFunDDS

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {T : Type} [Fintype T] [DecidableEq T]
variable {L : ℕ}

/-! ## The two-sided block-cipher resource -/

/-- The two-sided (±) oracle function of a permutation: forward queries
evaluate `π`, inverse queries `π⁻¹`. -/
def bcFun (π : Equiv.Perm F) : QueryDir × F → F := fun z =>
  match z.1 with
  | QueryDir.fwd => π z.2
  | QueryDir.inv => π.symm z.2

omit [Field F] [Fintype F] [DecidableEq F] [CharP F 2] in
@[simp] theorem bcFun_fwd (π : Equiv.Perm F) (x : F) :
    bcFun π (QueryDir.fwd, x) = π x := rfl

omit [Field F] [Fintype F] [DecidableEq F] [CharP F 2] in
@[simp] theorem bcFun_inv (π : Equiv.Perm F) (x : F) :
    bcFun π (QueryDir.inv, x) = π.symm x := rfl

/-- A two-sided block-cipher resource: sample `ω` from `p` and evaluate
`± f ω` statelessly.  `p := uniform K, f := E` is the paper's `±E`;
`p := uniform (Perm F), f := id` is the ideal `±Perm(n)`. -/
noncomputable def bcOracle {Ω : Type} (p : Dist.ProbDist Ω)
    (f : Ω → Equiv.Perm F) : ProbPDS (QueryDir × F) F :=
  PFunPDS.Prob.functionEvaluator p (fun ω => bcFun (f ω))

/-- `±E`: the two-sided keyed cipher with a uniform key — the paper's `E`,
abstract. -/
noncomputable def bcE {K : Type} [Fintype K] [Nonempty K]
    (E : K → Equiv.Perm F) : ProbPDS (QueryDir × F) F :=
  bcOracle ⟨Dist.uniform K, Dist.uniform_isProbDist⟩ E

/-- `±Perm(n)`: the two-sided uniform permutation oracle. -/
noncomputable def bcPerm : ProbPDS (QueryDir × F) F :=
  bcOracle ⟨Dist.uniform (Equiv.Perm F), Dist.uniform_isProbDist⟩ id

/-! ## The converter at the BIT carriers (paper Figures 2–3 over arbitrary bit strings)

`RandomSystems/HCTR2.lean` Part 2 formalizes HCTR2 over the paper's true message space
(arbitrary bit strings: fibers `bitMsgL`, construction `hctr2BitFun`, σ-accounted endpoint
`hctr2Bit_security_unrestricted`).  This block builds the converter layer at those
carriers.  Call structure per outer query (read off `bitEncCore`/`bitDecCore`): the two
header calls `±π(+, bin 0)`, `±π(+, bin 1)`, the message call `±π(dir, m ⊕ H)`, the `ℓ`
full-block XCTR calls `±π(+, S ⊕ bin (j+1))`, and the ALWAYS-present partial-block XCTR
call `±π(+, S ⊕ bin (ℓ+1))` (consumed to `r` bits, issued even at `r = 0`) — `4 + ℓ ≤
L + 3` calls per round.  The two header calls are shared across rounds, so a `q`-round
run makes at most `2 + Σₛ (2 + ℓˢ) = 2 + Σₛ mˢ` DISTINCT cipher calls (`mˢ = ℓˢ + 2` is
exactly the σ-accounting's `mBlocksBit`), capped by `2 + q·(L + 1)` (`ℓˢ ≤ L − 1`) — the
same paper `σ + 2` cap as the block-aligned model (one extra call per query there traded
against a one-smaller length range: `mˢ ≤ L + 1` both ways). -/

section BitConverter

variable {n : ℕ} (bb : BlockBits F n) (be : BinEnc F L)

local notation:max "HQB" => QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))
local notation:max "HMB" => Sigma (bitMsgL (F := F) (L := L) (n := n))

section BitRealization

variable (Hfb : HashFamily F T (L + 2))

/-- **The HCTR2 protocol converter, bit carriers** (paper Figures 2–3, transcribed as a
CR18 `ofStep` protocol): on outer query `u = (dir, t, ⟨(ℓ,r), (m, nn, np)⟩)` and inner
answers `ys` received so far, emit the next block-cipher query or the final answer.

Call sequence (the history `ys` *is* the round state):
1. `h̄ := ±π(+, bin 0)`;
2. `L := ±π(+, bin 1)`;
3. enc: `UU := ±π(+, M ⊕ H_h̄(t, tail))`; dec: `MM := ±π(−, U ⊕ H_h̄(t, tail))` — the
   hashed tail is the paper's `bin(2|M|+2/3) ‖ N ‖ pad(P‖1)` (`hashTailB`);
4. XCTR keystream, `ℓ + 1` calls: `±π(+, S ⊕ bin (j+1))`, `j = 0..ℓ`, where
   `S := (m ⊕ H) ⊕ w ⊕ L` (`w` the answer of call 3; in both directions
   `S = MM ⊕ UU ⊕ L`) — the last call is the partial-block keystream, consumed to `r`
   bits;
5. answer `⟨(ℓ,r), (w ⊕ H_h̄(t, tail′), v, vp)⟩` with `vᵢ := nnᵢ ⊕ ksᵢ` and
   `vp := np ^^^ setWidth r (toBits ks_ℓ)`. -/
def bitHctrStep :
    (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) → List F →
      (QueryDir × F) ⊕ Sigma (bitMsgL (F := F) (L := L) (n := n)) := fun u ys =>
  match ys with
  | [] => Sum.inl (QueryDir.fwd, be.bin 0)
  | [_] => Sum.inl (QueryDir.fwd, be.bin 1)
  | [hk, _] => Sum.inl (u.1, u.2.2.2.1 + Hfb.hash hk u.2.1
      (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2 u.2.2.2.2.1 u.2.2.2.2.2))
  | hk :: Lv :: w :: ks =>
      if h : (splitIdx u.2.2.1).1.val + 1 ≤ ks.length then
        Sum.inr ⟨u.2.2.1,
          (w + Hfb.hash hk u.2.1
              (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2
                (fun i => u.2.2.2.2.1 i +
                  ks[i.1]'(lt_of_lt_of_le (lt_of_lt_of_le i.2 (Nat.le_succ _)) h))
                (u.2.2.2.2.2 ^^^
                  (bb.toBits (ks[(splitIdx u.2.2.1).1.val]'(lt_of_lt_of_le
                    (Nat.lt_succ_self _) h))).setWidth (splitIdx u.2.2.1).2.val)),
            fun i => u.2.2.2.2.1 i +
              ks[i.1]'(lt_of_lt_of_le (lt_of_lt_of_le i.2 (Nat.le_succ _)) h),
            u.2.2.2.2.2 ^^^
              (bb.toBits (ks[(splitIdx u.2.2.1).1.val]'(lt_of_lt_of_le
                (Nat.lt_succ_self _) h))).setWidth (splitIdx u.2.2.1).2.val)⟩
      else
        Sum.inl (QueryDir.fwd,
          (u.2.2.2.1 + Hfb.hash hk u.2.1
              (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2
                u.2.2.2.2.1 u.2.2.2.2.2)) + w + Lv +
            be.bin (ks.length + 1))

omit [CharP F 2] [Fintype T] [DecidableEq T] in
/-- **Def 3.8 round bound, bit carriers**: the converter answers after at most `L + 3`
inner calls (`4 + ℓ ≤ L + 3` since `ℓ < L`). -/
theorem bitHctrStep_bound (u : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))
    (ys : List F) (h : L + 3 ≤ ys.length) :
    ∃ v, bitHctrStep bb be Hfb u ys = Sum.inr v := by
  have hℓ : (splitIdx u.2.2.1).1.val < L := (splitIdx u.2.2.1).1.isLt
  match ys with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | hk :: Lv :: w :: ks =>
      have hks : (splitIdx u.2.2.1).1.val + 1 ≤ ks.length := by
        simp only [List.length_cons] at h
        omega
      exact ⟨_, by simp only [bitHctrStep]; rw [dif_pos hks]⟩

/-- The block-cipher call trace of one bit-HCTR2 round against `±π`: two header calls,
the message call, and the `ℓ + 1` XCTR keystream calls (full blocks + the partial
call). -/
def bitHctrCalls (π : Equiv.Perm F)
    (u : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) :
    List (QueryDir × F) :=
  [(QueryDir.fwd, be.bin 0), (QueryDir.fwd, be.bin 1),
    (u.1, u.2.2.2.1 + Hfb.hash (π (be.bin 0)) u.2.1
      (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2 u.2.2.2.2.1 u.2.2.2.2.2))] ++
    (List.range ((splitIdx u.2.2.1).1.val + 1)).map fun j =>
      (QueryDir.fwd,
        (u.2.2.2.1 + Hfb.hash (π (be.bin 0)) u.2.1
            (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2
              u.2.2.2.2.1 u.2.2.2.2.2)) +
          bcFun π (u.1, u.2.2.2.1 + Hfb.hash (π (be.bin 0)) u.2.1
            (hashTailB bb (splitIdx u.2.2.1).1 (splitIdx u.2.2.1).2
              u.2.2.2.2.1 u.2.2.2.2.2)) +
          π (be.bin 1) + be.bin (j + 1))

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- The bit XCTR loop, closed form: from the round state with `c` keystream blocks
already received, the drive runs the remaining `k = (ℓ + 1) − c` keystream calls and
answers.  All received values (`hk`, `Lv`, `w`) are abstract — the step function only
reads the history. -/
theorem driveG_bitHctrStep_loop (π : Equiv.Perm F)
    (dir : QueryDir) (t : T) (kx : Fin (L * n)) (m : F)
    (nn : Fin (splitIdx kx).1.val → F) (np : BitVec (splitIdx kx).2.val)
    (hk Lv w : F) :
    ∀ (k c : ℕ), c + k = (splitIdx kx).1.val + 1 →
      ∀ (fl : ℕ) (xs : List (QueryDir × F)),
      CausalApply.driveG (bitHctrStep bb be Hfb (dir, t, ⟨kx, (m, nn, np)⟩))
          (PFunDDS.functionEvaluator (bcFun π)).1 (fl + k + 1) xs
          (hk :: Lv :: w ::
            ((List.range c).map fun j =>
              π ((m + Hfb.hash hk t
                    (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                  + w + Lv + be.bin (j + 1))))
        = Part.some
            ((⟨kx,
              (w + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2
                  (fun i => nn i +
                    π ((m + Hfb.hash hk t
                          (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                        + w + Lv + be.bin (i.1 + 1)))
                  (np ^^^ (bb.toBits (π ((m + Hfb.hash hk t
                          (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                        + w + Lv + be.bin ((splitIdx kx).1.val + 1)))).setWidth
                      (splitIdx kx).2.val)),
                fun i => nn i +
                  π ((m + Hfb.hash hk t
                        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                      + w + Lv + be.bin (i.1 + 1)),
                np ^^^ (bb.toBits (π ((m + Hfb.hash hk t
                        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                      + w + Lv + be.bin ((splitIdx kx).1.val + 1)))).setWidth
                    (splitIdx kx).2.val)⟩ :
              Sigma (bitMsgL (F := F) (L := L) (n := n))),
              xs ++ (List.range' c k).map fun j =>
                (QueryDir.fwd,
                  (m + Hfb.hash hk t
                      (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                    + w + Lv + be.bin (j + 1))) := by
  intro k
  induction k with
  | zero =>
      intro c hc fl xs
      obtain rfl : c = (splitIdx kx).1.val + 1 := by omega
      have hlen : ((List.range ((splitIdx kx).1.val + 1)).map fun j =>
          π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
              + w + Lv + be.bin (j + 1))).length = (splitIdx kx).1.val + 1 := by
        simp
      have hstep : bitHctrStep bb be Hfb (dir, t, ⟨kx, (m, nn, np)⟩)
          (hk :: Lv :: w ::
            ((List.range ((splitIdx kx).1.val + 1)).map fun j =>
              π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                  + w + Lv + be.bin (j + 1))))
          = Sum.inr ⟨kx,
              (w + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2
                  (fun i => nn i +
                    π ((m + Hfb.hash hk t
                          (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                        + w + Lv + be.bin (i.1 + 1)))
                  (np ^^^ (bb.toBits (π ((m + Hfb.hash hk t
                          (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                        + w + Lv + be.bin ((splitIdx kx).1.val + 1)))).setWidth
                      (splitIdx kx).2.val)),
                fun i => nn i +
                  π ((m + Hfb.hash hk t
                        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                      + w + Lv + be.bin (i.1 + 1)),
                np ^^^ (bb.toBits (π ((m + Hfb.hash hk t
                        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                      + w + Lv + be.bin ((splitIdx kx).1.val + 1)))).setWidth
                    (splitIdx kx).2.val)⟩ := by
        simp only [bitHctrStep]
        rw [dif_pos hlen.ge]
        simp only [List.getElem_map, List.getElem_range]
      simp only [CausalApply.driveG, hstep, List.range'_zero,
        List.map_nil, List.append_nil]
  | succ k ih =>
      intro c hc fl xs
      have hclt : c < (splitIdx kx).1.val + 1 := by omega
      have hlen : ((List.range c).map fun j =>
          π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
              + w + Lv + be.bin (j + 1))).length = c := by
        simp
      have hstep : bitHctrStep bb be Hfb (dir, t, ⟨kx, (m, nn, np)⟩)
          (hk :: Lv :: w ::
            ((List.range c).map fun j =>
              π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                  + w + Lv + be.bin (j + 1))))
          = Sum.inl (QueryDir.fwd,
              (m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                + w + Lv + be.bin (c + 1)) := by
        simp only [bitHctrStep]
        rw [dif_neg (by rw [hlen]; omega), hlen]
      have hih := ih (c + 1) (by omega) fl
        (xs ++ [(QueryDir.fwd,
          (m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
            + w + Lv + be.bin (c + 1))])
      have h1 : fl + (k + 1) + 1 = (fl + k + 1) + 1 := by omega
      rw [h1]
      generalize fl + k + 1 = f' at hih ⊢
      simp only [CausalApply.driveG, hstep,
        CausalApply.functionEvaluator_raw_append, Part.bind_some, bcFun_fwd,
        List.cons_append]
      have hsnoc : ((List.range c).map fun j =>
            π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                + w + Lv + be.bin (j + 1))) ++
            [π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                + w + Lv + be.bin (c + 1))]
          = (List.range (c + 1)).map fun j =>
              π ((m + Hfb.hash hk t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
                  + w + Lv + be.bin (j + 1)) := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [hsnoc, hih]
      simp [List.range'_succ]

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- The loop's final answer *is* the bit HCTR2 oracle answer (paper Figures 2–3, bit
domain): `w = UU` and the formula is `bitEncCore` on enc; `w = MM` and it is
`bitDecCore` on dec (up to `⊕`-commutativity of `S = MM ⊕ UU ⊕ L`). -/
theorem bitHctrRoundAnswer_eq (π : Equiv.Perm F) (dir : QueryDir) (t : T)
    (kx : Fin (L * n)) (m : F) (nn : Fin (splitIdx kx).1.val → F)
    (np : BitVec (splitIdx kx).2.val) :
    (⟨kx,
      (bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
            (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
          Hfb.hash (π (be.bin 0)) t (hashTailB bb (splitIdx kx).1 (splitIdx kx).2
            (fun i => nn i +
              π ((m + Hfb.hash (π (be.bin 0)) t
                    (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
                  bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
                    (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
                  π (be.bin 1) + be.bin (i.1 + 1)))
            (np ^^^ (bb.toBits (π ((m + Hfb.hash (π (be.bin 0)) t
                    (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
                  bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
                    (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
                  π (be.bin 1) + be.bin ((splitIdx kx).1.val + 1)))).setWidth
                (splitIdx kx).2.val)),
        fun i => nn i +
          π ((m + Hfb.hash (π (be.bin 0)) t
                (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
              bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
                (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
              π (be.bin 1) + be.bin (i.1 + 1)),
        np ^^^ (bb.toBits (π ((m + Hfb.hash (π (be.bin 0)) t
                (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
              bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
                (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)) +
              π (be.bin 1) + be.bin ((splitIdx kx).1.val + 1)))).setWidth
            (splitIdx kx).2.val)⟩ :
      Sigma (bitMsgL (F := F) (L := L) (n := n)))
      = hctr2BitFun bb be Hfb π (dir, t, ⟨kx, (m, nn, np)⟩) := by
  cases dir
  · -- fwd: literally `bitEncCore`
    simp only [hctr2BitFun, bitEncCore, bcFun_fwd]
  · -- inv: `bitDecCore`, with `S = MM ⊕ UU ⊕ L` read as `UU ⊕ MM ⊕ L`
    have hcomm : ∀ a b : F, a + b = b + a := fun a b => add_comm a b
    simp only [hctr2BitFun, bitDecCore, bcFun_inv,
      hcomm (m + Hfb.hash (π (be.bin 0)) t
        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))
        (π.symm (m + Hfb.hash (π (be.bin 0)) t
          (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)))]

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- One full bit-HCTR2 round against the `±π` evaluator, closed form: three header
calls, the `ℓ + 1`-call XCTR loop, and the oracle answer. -/
theorem driveG_bitHctrStep_round (π : Equiv.Perm F)
    (u : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) (fl : ℕ)
    (xs : List (QueryDir × F)) :
    CausalApply.driveG (bitHctrStep bb be Hfb u)
        (PFunDDS.functionEvaluator (bcFun π)).1 (fl + (splitIdx u.2.2.1).1.val + 5) xs []
      = Part.some (hctr2BitFun bb be Hfb π u, xs ++ bitHctrCalls bb be Hfb π u) := by
  obtain ⟨dir, t, kx, p⟩ := u
  obtain ⟨m, nn, np⟩ := p
  have h5 : fl + (splitIdx kx).1.val + 5 = ((fl + ((splitIdx kx).1.val + 1) + 1) + 1) + 1 + 1 := by
    omega
  rw [h5]
  -- call 1: h̄
  rw [CausalApply.driveG]
  simp only [bitHctrStep, CausalApply.functionEvaluator_raw_append, Part.bind_some,
    List.nil_append]
  -- call 2: L
  rw [CausalApply.driveG]
  simp only [bitHctrStep, List.nil_append, List.cons_append,
    CausalApply.functionEvaluator_raw_append, Part.bind_some]
  -- call 3: UU (enc) / MM (dec)
  rw [CausalApply.driveG]
  simp only [bitHctrStep, List.nil_append, List.cons_append,
    CausalApply.functionEvaluator_raw_append, Part.bind_some, bcFun_fwd]
  -- the XCTR loop from `c = 0` (`ℓ + 1` keystream calls)
  have hloop := driveG_bitHctrStep_loop bb be Hfb π dir t kx m nn np
    (π (be.bin 0)) (π (be.bin 1))
    (bcFun π (dir, m + Hfb.hash (π (be.bin 0)) t
      (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np)))
    ((splitIdx kx).1.val + 1) 0 (by omega) fl
    (((xs ++ [(QueryDir.fwd, be.bin 0)]) ++ [(QueryDir.fwd, be.bin 1)]) ++
      [(dir, m + Hfb.hash (π (be.bin 0)) t
        (hashTailB bb (splitIdx kx).1 (splitIdx kx).2 nn np))])
  simp only [List.range_zero, List.map_nil] at hloop
  rw [hloop, bitHctrRoundAnswer_eq bb be Hfb π dir t kx m nn np]
  simp [bitHctrCalls, List.range_eq_range', List.append_assoc]

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- All outer rounds against the `±π` evaluator, closed form (bit carriers). -/
theorem driveOuter_bitHctrStep_functionEvaluator (π : Equiv.Perm F) (fl : ℕ) :
    ∀ (us : List (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))))
      (xs : List (QueryDir × F)),
      CausalApply.driveOuter (bitHctrStep bb be Hfb)
          (PFunDDS.functionEvaluator (bcFun π)).1 (fl + L + 5) xs us
        = Part.some (us.map (hctr2BitFun bb be Hfb π),
            xs ++ us.flatMap (bitHctrCalls bb be Hfb π)) := by
  intro us
  induction us with
  | nil => intro xs; simp [CausalApply.driveOuter]
  | cons u rest ih =>
      intro xs
      have harith : (fl + (L - (splitIdx u.2.2.1).1.val)) + (splitIdx u.2.2.1).1.val + 5
          = fl + L + 5 := by
        have := (splitIdx u.2.2.1).1.isLt; omega
      have hG := driveG_bitHctrStep_round bb be Hfb π u
        (fl + (L - (splitIdx u.2.2.1).1.val)) xs
      rw [harith] at hG
      simp only [CausalApply.driveOuter, hG, Part.bind_some, ih, Part.map_some]
      simp [List.append_assoc]

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- **The realization equation, bit carriers**: applying the bit HCTR2 protocol
converter to the two-sided evaluator of `π` yields exactly the bit HCTR2 oracle —
a full DDS equality across all outer histories, domains included. -/
theorem applyG_bitHctrStep (π : Equiv.Perm F) :
    CausalApply.applyG (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1
      = PFunDDS.functionEvaluator (hctr2BitFun bb be Hfb π) := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro v
  rw [show (CausalApply.applyG (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1).1
      = CausalApply.applyRaw (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1 from rfl,
    CausalApply.mem_applyRaw, PFunConverter.DDC.mem_functionEvaluator_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    have hv' : v ∈ CausalApply.applyRawAt (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1 (fuel + L + 5) us :=
      CausalApply.applyRawAt_mono_le _ _ (by omega) hv
    rw [CausalApply.mem_applyRawAt_iff] at hv'
    obtain ⟨r, hr, hlast⟩ := hv'
    rw [driveOuter_bitHctrStep_functionEvaluator bb be Hfb π fuel us [],
      Part.mem_some_iff] at hr
    subst hr
    rw [List.getLast?_map] at hlast
    obtain ⟨u, hu, hfu⟩ := Option.map_eq_some_iff.mp hlast
    exact ⟨u, hu, hfu.symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨0 + L + 5, ?_⟩
    rw [CausalApply.mem_applyRawAt_iff]
    refine ⟨(us.map (hctr2BitFun bb be Hfb π),
      [] ++ us.flatMap (bitHctrCalls bb be Hfb π)), ?_, ?_⟩
    · rw [driveOuter_bitHctrStep_functionEvaluator bb be Hfb π 0 us []]
      exact Part.mem_some _
    · rw [List.getLast?_map, hu]
      rfl

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- The bit realization equation at the CR18 Def 3.9 surface. -/
theorem apply_ofStep_bitHctrStep (π : Equiv.Perm F) :
    PFunConverter.DDC.apply (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
        (PFunDDS.functionEvaluator (bcFun π))
      = PFunDDS.functionEvaluator (hctr2BitFun bb be Hfb π) := by
  rw [show PFunConverter.DDC.apply (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
      (PFunDDS.functionEvaluator (bcFun π))
      = CausalApply.applyG (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1 from
    PFunConverter.DDC.apply_ofStep (bitHctrStep bb be Hfb) _]
  exact applyG_bitHctrStep bb be Hfb π

/-! ### Distinct cipher-call count, bit carriers (paper p.17 `σ + 2`) -/

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- Split a round's call trace into the two constant header calls and the
`mˢ = 2 + ℓˢ` per-round tail calls. -/
theorem bitHctrCalls_eq_header_cons (π : Equiv.Perm F)
    (u : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) :
    bitHctrCalls bb be Hfb π u
      = (QueryDir.fwd, be.bin 0) :: (QueryDir.fwd, be.bin 1)
        :: (bitHctrCalls bb be Hfb π u).drop 2 := rfl

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- The per-round tail (non-header) call trace has length `mˢ = 2 + ℓˢ` — exactly the
σ-accounting's per-query block count `mBlocksBit`. -/
theorem bitHctrCalls_drop2_length (π : Equiv.Perm F)
    (u : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) :
    ((bitHctrCalls bb be Hfb π u).drop 2).length = 2 + (splitIdx u.2.2.1).1.val := by
  have hlen : (bitHctrCalls bb be Hfb π u).length = 4 + (splitIdx u.2.2.1).1.val := by
    simp only [bitHctrCalls, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_range]
    omega
  rw [List.length_drop, hlen]
  omega

omit [CharP F 2] [Fintype T] [DecidableEq T] in
/-- **The distinct cipher-call count, bit carriers (Σ-form).**  Over a run of the outer
queries `us`, the number of *distinct* block-cipher calls is at most `2 + Σₛ mˢ` with
`mˢ := 2 + ℓˢ` — the paper's `σ + 2` (p.17) at the honest bit-level per-query block
count. -/
theorem bitHctrCalls_flatMap_toFinset_card_le (π : Equiv.Perm F)
    (us : List (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))) :
    (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset.card
      ≤ 2 + (us.map (fun u => 2 + (splitIdx u.2.2.1).1.val)).sum := by
  classical
  set a : QueryDir × F := (QueryDir.fwd, be.bin 0) with ha
  set b : QueryDir × F := (QueryDir.fwd, be.bin 1) with hb
  set tails : List (QueryDir × F) :=
    us.flatMap (fun u => (bitHctrCalls bb be Hfb π u).drop 2) with htails
  have hsub : (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset
      ⊆ insert a (insert b tails.toFinset) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_flatMap] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    rw [bitHctrCalls_eq_header_cons bb be Hfb π u, List.mem_cons, List.mem_cons] at hxu
    rcases hxu with rfl | rfl | htl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
      rw [List.mem_toFinset, htails, List.mem_flatMap]
      exact ⟨u, hu, htl⟩
  calc (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset.card
      ≤ (insert a (insert b tails.toFinset)).card := Finset.card_le_card hsub
    _ ≤ 2 + tails.toFinset.card := by
        have h1 := Finset.card_insert_le a (insert b tails.toFinset)
        have h2 := Finset.card_insert_le b tails.toFinset
        omega
    _ ≤ 2 + tails.length := Nat.add_le_add_left (List.toFinset_card_le tails) 2
    _ = 2 + (us.map (fun u => 2 + (splitIdx u.2.2.1).1.val)).sum := by
        congr 1
        rw [htails, List.length_flatMap]
        refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
        exact bitHctrCalls_drop2_length bb be Hfb π u

omit [CharP F 2] [Fintype T] [DecidableEq T] in
/-- **The `B := 2 + q·(L+1)` query budget, bit carriers.**  Since each block count
`mˢ = 2 + ℓˢ ≤ L + 1` (`ℓˢ < L`), a `q`-outer-query run makes at most `2 + q·(L+1)`
distinct block-cipher calls — the same cap as the block-aligned model. -/
theorem bitHctrCalls_flatMap_toFinset_card_le_cap (π : Equiv.Perm F)
    (us : List (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))) :
    (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset.card
      ≤ 2 + us.length * (L + 1) := by
  refine le_trans (bitHctrCalls_flatMap_toFinset_card_le bb be Hfb π us) ?_
  have hbound : (us.map (fun u => 2 + (splitIdx u.2.2.1).1.val)).sum
      ≤ us.length * (L + 1) := by
    have hle := List.sum_le_card_nsmul
      (us.map (fun u => 2 + (splitIdx u.2.2.1).1.val)) (L + 1)
      (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨u, _, rfl⟩ := hx
        have := (splitIdx u.2.2.1).1.isLt
        omega)
    simpa [List.length_map, smul_eq_mul] using hle
  omega

/-! ### Law level: bit `HCTR2[X] = bitHctrStep · (±X)` -/

/-- Bit HCTR2 with block-cipher sample space `Ω`: the paper's `HCTR2[X]` over arbitrary
bit strings, defined directly as the sampled construction (uniformly with
`hctr2BitReal`). -/
noncomputable def hctr2BitCipher {Ω : Type} (p : Dist.ProbDist Ω)
    (f : Ω → Equiv.Perm F) : ProbPDS HQB HMB :=
  PFunPDS.Prob.functionEvaluator p (fun ω => hctr2BitFun bb be Hfb (f ω))

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- **Law-level realization, bit carriers**: applying the bit HCTR2 converter to the
± cipher resource *is* the sampled bit HCTR2 construction. -/
theorem applyDDC_bitHctrStep_bcOracle {Ω : Type} (p : Dist.ProbDist Ω)
    (f : Ω → Equiv.Perm F) :
    PFunPDS.applyDDC (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
        (bcOracle p f).val
      = (hctr2BitCipher bb be Hfb p f).val := by
  show Dist.fTransform _
      (Dist.fTransform (functionEvaluatorRV fun ω => bcFun (f ω)) p.val)
    = Dist.fTransform (functionEvaluatorRV fun ω => hctr2BitFun bb be Hfb (f ω)) p.val
  rw [Dist.fTransform_comp]
  refine congrArg (fun g => Dist.fTransform g p.val) (funext fun ω => ?_)
  exact apply_ofStep_bitHctrStep bb be Hfb (f ω)

end BitRealization

/-! ### The cache's cipher-query bound, bit carriers -/

section BitCipherQueryBound

open PFunDDS PFunDDS.Cache CausalApply

variable (Hfb : HashFamily F T (L + 2))

/-- The absorbed distinguisher makes at most `q·(L + 3)` base (cipher) queries
(bit round bound `L + 3`). -/
theorem bit_queriesAtMostN_absorb (dd : PFunDDS.DDD HQB HMB) {q : ℕ}
    (hQE : QueriesExactly (PFunDDS.ddToDDE dd) q) :
    QueriesAtMostN (absorb dd (bitHctrStep bb be Hfb)) (q * (L + 3)) := by
  intro h hlen
  obtain ⟨b, fuel, hfuel⟩ := absorbGo_none_reaches_verdict dd (bitHctrStep bb be Hfb)
    q (L + 3) hQE (fun u ys hle => bitHctrStep_bound bb be Hfb u ys hle) q [] h
    (by simp) hlen
  exact ⟨b, absorbFun_eq_of_go hfuel⟩

/-- **The absorbed distinguisher's cipher-call trace lies in `us.flatMap
(bitHctrCalls π)`** for an outer-query list `us` of length `≤ q` (bit twin of the
block-aligned B1). -/
theorem bit_absorb_dRun_fst_subset (dd : PFunDDS.DDD HQB HMB) {q : ℕ}
    (hQE : QueriesExactly (PFunDDS.ddToDDE dd) q) (π : Equiv.Perm F) :
    ∃ us : List HQB, us.length ≤ q ∧
      ∀ (m : ℕ), (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) m).map Prod.fst
        ⊆ us.flatMap (bitHctrCalls bb be Hfb π) := by
  classical
  have hs : ∀ xs : List (QueryDir × F), xs ≠ [] →
      xs ∈ PFunDDS.dom (PFunDDS.functionEvaluator (bcFun π)) := by
    intro xs hne; rw [PFunDDS.dom_functionEvaluator]; exact hne
  have hQN : QueriesAtMostN (absorb dd (bitHctrStep bb be Hfb)) (q * (L + 3)) :=
    bit_queriesAtMostN_absorb bb be Hfb dd hQE
  have hlenN : ∀ m, (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) m).length
      ≤ q * (L + 3) :=
    dRun_length_le_of_QueriesAtMostN (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) _ hQN
  obtain ⟨b, hbN⟩ := dRun_verdict_at_of_length_le (absorb dd (bitHctrStep bb be Hfb))
    (bcFun π) (q * (L + 3)) hlenN
  obtain ⟨t, T', mode, hr, heqT⟩ :=
    transcript_base_reachable (d := dd) (step := bitHctrStep bb be Hfb) hs (q * (L + 3))
  have htN : PFunDDS.transcript (PFunDDS.functionEvaluator (bcFun π))
        (PFunDDS.ddToDDE (absorb dd (bitHctrStep bb be Hfb))) (q * (L + 3))
      = (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) (q * (L + 3))).map
          (fun p => (p.1, some p.2)) :=
    transcript_functionEvaluator_eq (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) _
  have htout : PFunDDS.transcriptOutputs t
      = (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) (q * (L + 3))).map
          (fun p => some p.2) := by
    rw [← heqT, htN, PFunDDS.transcriptOutputs, List.map_map]; rfl
  have hAval : absorbFun dd (bitHctrStep bb be Hfb) (PFunDDS.transcriptOutputs t)
      = Sum.inr b := by
    rw [htout]; exact hbN
  obtain ⟨b', fuelP, hfuelP⟩ := absorbGo_none_reaches_verdict dd (bitHctrStep bb be Hfb)
    q (L + 3) hQE (fun u ys hle => bitHctrStep_bound bb be Hfb u ys hle) q []
    (PFunDDS.transcriptOutputs t ++ List.replicate (q * (L + 3)) none)
    (by simp) (by rw [List.length_append, List.length_replicate]; omega)
  have happ : (absorbGo dd (bitHctrStep bb be Hfb) fuelP [] none
      (PFunDDS.transcriptOutputs t ++ List.replicate (q * (L + 3)) none)).isSome :=
    Option.isSome_iff_exists.mpr ⟨Sum.inr b', hfuelP⟩
  obtain ⟨fuel₀, hsome₀⟩ := absorbGo_isSome_of_append dd (bitHctrStep bb be Hfb) happ
  obtain ⟨m₀, hm₀⟩ := Option.isSome_iff_exists.mp hsome₀
  have hm₀b : m₀ = Sum.inr b := by
    rw [← absorbFun_eq_of_go hm₀]; exact hAval
  subst hm₀b
  have hm₀' : absorbGo dd (bitHctrStep bb be Hfb) fuel₀ [] none
      (PFunDDS.transcriptOutputs t ++ []) = some (Sum.inr b) := by
    rw [List.append_nil]; exact hm₀
  obtain ⟨fuel₁, hstate⟩ := absorbGo_replay_rev hr hm₀'
  rcases absorbGo_run_extract hr hstate with
    ⟨T'', u, ys, x, hr', hstep', hbad⟩ | ⟨T'', b'', hr', hd', _⟩
  · exact absurd hbad (by simp)
  · obtain ⟨ws, xs₀, hws, ⟨fuelD, hdrive⟩, hxs₀, _⟩ := absRun_driveOuter hs hr'
    have hxs : xs₀ = PFunDDS.transcriptInputs t := hxs₀ rfl
    have hmem : (ws, xs₀) ∈ driveOuter (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1 (fuelD + L + 5) []
        (PFunDDS.transcriptInputs T'') :=
      driveOuter_mono_le (bitHctrStep bb be Hfb)
        (PFunDDS.functionEvaluator (bcFun π)).1 (by omega) hdrive
    rw [driveOuter_bitHctrStep_functionEvaluator bb be Hfb π fuelD
        (PFunDDS.transcriptInputs T'') [],
      Part.mem_some_iff] at hmem
    have hxs2 : xs₀ = (PFunDDS.transcriptInputs T'').flatMap (bitHctrCalls bb be Hfb π) := by
      have := congrArg Prod.snd hmem; simpa using this
    have htId : PFunDDS.transcriptInputs t
        = (PFunDDS.transcriptInputs T'').flatMap (bitHctrCalls bb be Hfb π) := by
      rw [← hxs, hxs2]
    have htFst : PFunDDS.transcriptInputs t
        = (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) (q * (L + 3))).map
            Prod.fst := by
      rw [← heqT, htN, PFunDDS.transcriptInputs, List.map_map]; rfl
    have hTq : (PFunDDS.transcriptInputs T'').length ≤ q := by
      have htr := absRun_transcript_comp hs hr'
      obtain ⟨n', hn'⟩ := (PFunDDS.transcript_mem_iff _ _ _).mp htr
      rw [PFunDDS.transcriptInputs, List.length_map, ← hn']
      exact transcript_length_le_of_queriesExactly _ (PFunDDS.ddToDDE dd) q hQE n'
    refine ⟨PFunDDS.transcriptInputs T'', hTq, ?_⟩
    intro m y hy
    have hpre : dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) m
        <+: dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) (q * (L + 3)) := by
      rcases le_total m (q * (L + 3)) with hmN | hNm
      · exact dRun_mono (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) hmN
      · rw [dRun_eq_of_verdict (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) hbN hNm]
    have hy2 : y ∈ (dRun (absorb dd (bitHctrStep bb be Hfb)) (bcFun π)
        (q * (L + 3))).map Prod.fst :=
      ((hpre.map Prod.fst).subset) hy
    rw [← htFst, htId] at hy2
    exact hy2

/-- **The de-dup cache forwards at most `2 + q·(L+1)` cipher queries, bit carriers**
(the paper's `σ + 2` cap). -/
theorem bit_cache_dRun_length_le (dd : PFunDDS.DDD HQB HMB) {q : ℕ}
    (hQE : QueriesExactly (PFunDDS.ddToDDE dd) q) (π : Equiv.Perm F) (m : ℕ) :
    (dRun (cacheDDD (q * (L + 3)) (absorb dd (bitHctrStep bb be Hfb))) (bcFun π) m).length
      ≤ 2 + q * (L + 1) := by
  classical
  obtain ⟨us, hus, hsubtrace⟩ := bit_absorb_dRun_fst_subset bb be Hfb dd hQE π
  have hQN : QueriesAtMostN (absorb dd (bitHctrStep bb be Hfb)) (q * (L + 3)) :=
    bit_queriesAtMostN_absorb bb be Hfb dd hQE
  have hsub : ∀ x ∈ (dRun (cacheDDD (q * (L + 3)) (absorb dd (bitHctrStep bb be Hfb)))
        (bcFun π) m).map Prod.fst,
      x ∈ (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset := by
    intro x hx
    obtain ⟨_, hsubcons⟩ := cacheDDD_run_nodup (q * (L + 3))
      (absorb dd (bitHctrStep bb be Hfb)) hQN (bcFun π) (QueryDir.fwd, (0 : F)) m
    have hx1 := hsubcons x hx
    rcases consume_run_spec (q * (L + 3)) (absorb dd (bitHctrStep bb be Hfb)) (bcFun π) hQN
        (QueryDir.fwd, (0 : F)) _
        (cacheSupply_valid (q * (L + 3)) (absorb dd (bitHctrStep bb be Hfb)) (bcFun π)
          (QueryDir.fwd, (0 : F)) m)
      with ⟨m', _, _, _, _, hcons⟩ | ⟨m', _, _, hcons⟩
    · rw [hcons] at hx1; rw [List.mem_toFinset]; exact hsubtrace m' hx1
    · rw [hcons] at hx1; rw [List.mem_toFinset]; exact hsubtrace m' hx1
  have hcard := cacheDDD_forwarded_card_le (q * (L + 3)) (absorb dd (bitHctrStep bb be Hfb))
    hQN (bcFun π) (QueryDir.fwd, (0 : F)) (us.flatMap (bitHctrCalls bb be Hfb π)).toFinset
    m hsub
  rw [List.length_map] at hcard
  refine le_trans hcard
    (le_trans (bitHctrCalls_flatMap_toFinset_card_le_cap bb be Hfb π us) ?_)
  have hml : us.length * (L + 1) ≤ q * (L + 1) := Nat.mul_le_mul_right _ hus
  omega

end BitCipherQueryBound

/-! ### The substitution + composed bounds, bit carriers -/

section BitSubstitution

variable (Hfb : HashFamily F T (L + 2))
variable {K : Type} [Fintype K] [Nonempty K]

/-- Bit `HCTR2[E]`: the construction with the real (abstract) block cipher over the
paper's arbitrary-bit-string message space. -/
noncomputable def hctr2BitE (E : K → Equiv.Perm F) : ProbPDS HQB HMB :=
  hctr2BitCipher bb be Hfb ⟨Dist.uniform K, Dist.uniform_isProbDist⟩ E

omit [DecidableEq F] [CharP F 2] [Fintype T] [DecidableEq T] in
/-- Bit `HCTR2[E]` is the converter applied to `±E`. -/
theorem applyDDC_bitHctrStep_bcE (E : K → Equiv.Perm F) :
    PFunPDS.applyDDC (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
        (bcE (F := F) E).val
      = (hctr2BitE bb be Hfb E).val :=
  applyDDC_bitHctrStep_bcOracle bb be Hfb _ E

omit [CharP F 2] [Fintype T] [DecidableEq T] in
/-- Bit `HCTR2[Perm(n)]` — the converter applied to `±Perm` — is *the* ideal-cipher
construction `hctr2BitReal` of the information-theoretic development. -/
theorem applyDDC_bitHctrStep_bcPerm :
    PFunPDS.applyDDC (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
        (bcPerm (F := F)).val
      = (hctr2BitReal bb be Hfb).val :=
  applyDDC_bitHctrStep_bcOracle bb be Hfb
    ⟨Dist.uniform (Equiv.Perm F), Dist.uniform_isProbDist⟩ id

/-- **The `σ`-budgeted substitution step, bit carriers**: replacing the ideal
permutation by the cipher costs at most the ±prp advantage of `E` *against a
`[2 + q·(L+1)]`-query distinguisher* — the paper's `σ + 2` cipher-query budget (p.17)
over the true bit message space.  The substitution distinguisher is
`pad → absorb → de-dup cache`; `bit_cache_dRun_length_le` caps its cipher queries at
`2 + q·(L+1)`, on which the cipher-side `[B]` filter is invisible. -/
private theorem hctr2Bit_substitution_sigma (E : K → Equiv.Perm F) {q : ℕ}
    (dummy : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n))) :
    Δ(⌈q⌉ (hctr2BitE bb be Hfb E).val, ⌈q⌉ (hctr2BitReal bb be Hfb).val)
      ≤ Δ(⌈2 + q * (L + 1)⌉ (bcE (F := F) E).val,
          ⌈2 + q * (L + 1)⌉ (bcPerm (F := F)).val) := by
  classical
  haveI : Inhabited (QueryDir × F) := ⟨(QueryDir.fwd, 0)⟩
  have hAtot : CondEquiv.TotalOnNonempty (hctr2BitE bb be Hfb E).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  have hBtot : CondEquiv.TotalOnNonempty (hctr2BitReal bb be Hfb).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  have hSbcE : CondEquiv.TotalOnNonempty (bcE (F := F) E).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  have hTbcPerm : CondEquiv.TotalOnNonempty (bcPerm (F := F)).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  unfold maxAdvantage
  refine csSup_le (advantage_image_nonempty _ _) ?_
  rintro x ⟨D, hD, rfl⟩
  have hQ := PFunDDS.padDDDDist_queriesExactly_support dummy q D
  have hbackedE : ∀ s ∈ (bcE (F := F) E).val.support,
      ∃ f, s = PFunDDS.functionEvaluator f := by
    intro s hs
    obtain ⟨ω, _, hω⟩ :=
      Dist.mem_support_fTransform (functionEvaluatorRV (fun ω => bcFun (E ω)))
        (Dist.uniform K) hs
    exact ⟨bcFun (E ω), hω.symm⟩
  have hbackedPerm : ∀ s ∈ (bcPerm (F := F)).val.support,
      ∃ f, s = PFunDDS.functionEvaluator f := by
    intro s hs
    obtain ⟨ω, _, hω⟩ :=
      Dist.mem_support_fTransform (functionEvaluatorRV (fun ω => bcFun (id ω)))
        (Dist.uniform (Equiv.Perm F)) hs
    exact ⟨bcFun ω, hω.symm⟩
  have hQabs : ∀ dABS ∈ (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
        (PFunDDS.padDDDDist dummy q D)).support,
      PFunDDS.Cache.QueriesAtMostN dABS (q * (L + 3)) := by
    intro dABS hdABS
    obtain ⟨dd, hdd, rfl⟩ := Dist.mem_support_fTransform _ _ hdABS
    exact bit_queriesAtMostN_absorb bb be Hfb dd (hQ dd hdd)
  have hboundE : ∀ dC ∈ (Dist.fTransform (PFunDDS.Cache.cacheDDD (q * (L + 3)))
        (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
          (PFunDDS.padDDDDist dummy q D))).support,
      ∀ f, PFunDDS.functionEvaluator f ∈ (bcE (F := F) E).val.support →
        ∀ m, (PFunDDS.Cache.dRun dC f m).length ≤ 2 + q * (L + 1) := by
    intro dC hdC f hf m
    obtain ⟨dABS, hdABS, rfl⟩ := Dist.mem_support_fTransform _ _ hdC
    obtain ⟨dd, hdd, rfl⟩ := Dist.mem_support_fTransform _ _ hdABS
    obtain ⟨ω, _, hω⟩ :=
      Dist.mem_support_fTransform (functionEvaluatorRV (fun ω => bcFun (E ω)))
        (Dist.uniform K) hf
    have hωe : PFunDDS.functionEvaluator (bcFun (E ω)) = PFunDDS.functionEvaluator f := hω
    have hfω : f = bcFun (E ω) := (PFunDDS.Cache.functionEvaluator_inj hωe).symm
    subst hfω
    exact bit_cache_dRun_length_le bb be Hfb dd (hQ dd hdd) (E ω) m
  have hboundPerm : ∀ dC ∈ (Dist.fTransform (PFunDDS.Cache.cacheDDD (q * (L + 3)))
        (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
          (PFunDDS.padDDDDist dummy q D))).support,
      ∀ f, PFunDDS.functionEvaluator f ∈ (bcPerm (F := F)).val.support →
        ∀ m, (PFunDDS.Cache.dRun dC f m).length ≤ 2 + q * (L + 1) := by
    intro dC hdC f hf m
    obtain ⟨dABS, hdABS, rfl⟩ := Dist.mem_support_fTransform _ _ hdC
    obtain ⟨dd, hdd, rfl⟩ := Dist.mem_support_fTransform _ _ hdABS
    obtain ⟨ω, _, hω⟩ :=
      Dist.mem_support_fTransform (functionEvaluatorRV (fun ω => bcFun (id ω)))
        (Dist.uniform (Equiv.Perm F)) hf
    have hωe : PFunDDS.functionEvaluator (bcFun ω) = PFunDDS.functionEvaluator f := hω
    have hfω : f = bcFun ω := (PFunDDS.Cache.functionEvaluator_inj hωe).symm
    subst hfω
    exact bit_cache_dRun_length_le bb be Hfb dd (hQ dd hdd) ω m
  calc advantage D (⌈q⌉ (hctr2BitE bb be Hfb E).val) (⌈q⌉ (hctr2BitReal bb be Hfb).val)
      = advantage (PFunDDS.padDDDDist dummy q D)
          (⌈q⌉ (hctr2BitE bb be Hfb E).val) (⌈q⌉ (hctr2BitReal bb be Hfb).val) :=
        (advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty dummy q D
          (hctr2BitE bb be Hfb E).val (hctr2BitReal bb be Hfb).val hAtot hBtot).symm
    _ = advantage (PFunDDS.padDDDDist dummy q D)
          (hctr2BitE bb be Hfb E).val (hctr2BitReal bb be Hfb).val := by
        unfold advantage
        rw [verdictProb_filterQueries_eq_of_queriesExactly q _
            (hctr2BitE bb be Hfb E).val hAtot hQ,
          verdictProb_filterQueries_eq_of_queriesExactly q _
            (hctr2BitReal bb be Hfb).val hBtot hQ]
    _ = advantage (PFunDDS.padDDDDist dummy q D)
          (PFunPDS.applyDDC (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
            (bcE (F := F) E).val)
          (PFunPDS.applyDDC (PFunConverter.DDC.ofStep (bitHctrStep bb be Hfb))
            (bcPerm (F := F)).val) := by
        rw [applyDDC_bitHctrStep_bcE bb be Hfb E, applyDDC_bitHctrStep_bcPerm bb be Hfb]
    _ = advantage (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
            (PFunDDS.padDDDDist dummy q D))
          (bcE (F := F) E).val (bcPerm (F := F)).val :=
        advantage_absorb (bitHctrStep bb be Hfb)
          (fun u ys hle => bitHctrStep_bound bb be Hfb u ys hle)
          (PFunDDS.padDDDDist dummy q D) _ _ hSbcE hTbcPerm
    _ = advantage (Dist.fTransform (PFunDDS.Cache.cacheDDD (q * (L + 3)))
            (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
              (PFunDDS.padDDDDist dummy q D)))
          (bcE (F := F) E).val (bcPerm (F := F)).val := by
        unfold advantage
        rw [PFunDDS.Cache.verdictProb_cacheDDD_eq (q * (L + 3)) _
            (bcPerm (F := F)).val hbackedPerm hQabs,
          PFunDDS.Cache.verdictProb_cacheDDD_eq (q * (L + 3)) _
            (bcE (F := F) E).val hbackedE hQabs]
    _ = advantage (Dist.fTransform (PFunDDS.Cache.cacheDDD (q * (L + 3)))
            (Dist.fTransform (fun dd => absorb dd (bitHctrStep bb be Hfb))
              (PFunDDS.padDDDDist dummy q D)))
          (⌈2 + q * (L + 1)⌉ (bcE (F := F) E).val)
          (⌈2 + q * (L + 1)⌉ (bcPerm (F := F)).val) := by
        unfold advantage
        rw [PFunDDS.Cache.verdictProb_filterQueries_eq_of_dRunBounded (2 + q * (L + 1)) _
            (bcPerm (F := F)).val hbackedPerm hboundPerm,
          PFunDDS.Cache.verdictProb_filterQueries_eq_of_dRunBounded (2 + q * (L + 1)) _
            (bcE (F := F) E).val hbackedE hboundE]
    _ ≤ Δ(⌈2 + q * (L + 1)⌉ (bcE (F := F) E).val,
          ⌈2 + q * (L + 1)⌉ (bcPerm (F := F)).val) :=
        advantage_le_maxAdvantage _ _ _
          (Dist.fTransform_isProbDist _
            (Dist.fTransform_isProbDist _
              (PFunDDS.padDDDDist_isProbDist dummy q D hD)))

/-- **HCTR2 security with the `σ + 2` cipher-query budget, over the TRUE bit message
space** (paper p.17 shape at the σ-accounted constants): at the CR18 game surface, a
`q`-query distinguisher of bit-`HCTR2[E]` from the ideal tweakable strong URP over the
bit fibers is bounded by the `[2 + q·(L+1)]`-filtered ±prp advantage of `E` plus the
σ-budgeted information-theoretic bound at `σ = σB`.

`hσB` is the universal per-transcript block budget (every `q`-query transcript has
`Σ_s dˢ ≤ σB`; e.g. `σB = q·(L + 1 + B)` for any per-tweak cap `twBlocks ≤ B`, since
`mˢ ≤ L + 1`) — it upgrades the pointless-query WLOG of
`hctr2Bit_security_unrestricted` to the `bitNPB` class. -/
private theorem hctr2Bit_security_computational_sigma [Nonempty T]
    (Hfs : HashFamilyS F T (L + 2)) (twBlocks : T → ℕ) {σB : ℕ}
    (E : K → Equiv.Perm F) {q : ℕ} (hLn : 0 < L * n) (hq : 1 ≤ q)
    (hdegB : ∀ (t' : T) (k : ℕ), Hfs.degB t' k ≤ k + twBlocks t')
    (hσB : ∀ t : TranscriptPrefix
        (QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)))
        (Sigma (bitMsgL (F := F) (L := L) (n := n))) q,
      sigmaDBit twBlocks t ≤ σB) :
    Δ(⌈q⌉ (hctr2BitE bb be Hfs.toHashFamily E).val,
        ⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n))
          (T := T)).val)
      ≤ Δ(⌈2 + q * (L + 1)⌉ (bcE (F := F) E).val,
            ⌈2 + q * (L + 1)⌉ (bcPerm (F := F)).val) +
        (((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) /
            (2 * Fintype.card F) +
          (choose2 q : NNReal) / Fintype.card F : ℝ) := by
  classical
  have dummy : QueryDir × T × Sigma (bitMsgL (F := F) (L := L) (n := n)) :=
    (QueryDir.fwd, Classical.arbitrary T, ⟨⟨0, hLn⟩, Classical.arbitrary _⟩)
  have hBtot : CondEquiv.TotalOnNonempty (hctr2BitReal bb be Hfs.toHashFamily).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  have hItot : CondEquiv.TotalOnNonempty
      (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)).val :=
    functionEvaluatorProb_totalOnNonempty _ _
  have htri := maxAdvantage_triangle
    (⌈q⌉ (hctr2BitE bb be Hfs.toHashFamily E).val)
    (⌈q⌉ (hctr2BitReal bb be Hfs.toHashFamily).val)
    (⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)).val)
  have h1 := hctr2Bit_substitution_sigma bb be Hfs.toHashFamily E (q := q) dummy
  have hNorm := deltaFilteredFiniteQueryNormalization_of_totalOnNonempty
    dummy q (hctr2BitReal bb be Hfs.toHashFamily).val
    (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)).val
    hBtot hItot
  have h2 : Δ(⌈q⌉ (hctr2BitReal bb be Hfs.toHashFamily).val,
        ⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n))
          (T := T)).val)
      ≤ (((3 * σB ^ 2 + 2 * q * σB + 7 * σB + 2 : ℕ) : NNReal) /
            (2 * Fintype.card F) +
          (choose2 q : NNReal) / Fintype.card F : ℝ) :=
    le_trans
      (maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage (q := q)
        (hctr2BitReal bb be Hfs.toHashFamily)
        (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T))
        (functionEvaluatorProb_KStepTotal _ _ q)
        (functionEvaluatorProb_KStepTotal _ _ q) hNorm)
      (hctr2Bit_security_unrestricted bb be Hfs twBlocks hq hdegB hσB)
  linarith

omit [CharP F 2] in
/-- **The HCTR2 headline pair carries no metric slack.**  On the `[q]`-filtered pair
that `hctr2_paper_theorem` bounds, the strict contextual metric `maxEDist`
(`StrictContext.maxEDist`) equals `ENNReal.ofReal Δ` — so the p.17 bound constrains the
strict metric exactly as tightly as it constrains the CR18 advantage, and no strength is
lost by stating the headline in `Δ`.

`maxEDist ≤ ofReal Δ` holds unconditionally; equality needs the shared-domain hypotheses,
here supplied by `[q]` being a prefix-closed history filter plus totality of both sides
(both are `functionEvaluator`s).  Twin of CBC-MAC's
`maxEDist_filterQueries_cbcReal_Vn_eq_ofReal_maxAdvantage`.  Purely systems-level — no
field algebra enters, hence `omit [CharP F 2]`. -/
theorem maxEDist_filterQueries_hctr2BitE_tprp_eq_ofReal_maxAdvantage
    (E : K → Equiv.Perm F) (q : ℕ) :
    StrictContext.maxEDist
        (⌈q⌉ (hctr2BitE bb be Hfb E).val)
        (⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)).val)
      = ENNReal.ofReal
          Δ(⌈q⌉ (hctr2BitE bb be Hfb E).val,
            ⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n))
              (T := T)).val) := by
  rw [PFunPDS.filterQueries_eq_filterDom, PFunPDS.filterQueries_eq_filterDom]
  exact StrictContextSharedDomain.maxEDist_filterDom_eq_ofReal_maxAdvantage
    _ (prefixClosed_length_le q) _ _
    (hctr2BitE bb be Hfb E).property
    (TweakablePRP.tprp (MsgK := bitMsgL (F := F) (L := L) (n := n)) (T := T)).property
    (functionEvaluatorProb_totalOnNonempty _ _)
    (functionEvaluatorProb_totalOnNonempty _ _)

end BitSubstitution

end BitConverter


end HCTR2

/-! ## Part II — the POLYVAL-class ε-AXU library -/

namespace HCTR2Instance

open RandomSystems.CR18
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.CR18.HCTR2
open RandomSystems.HTechnique.HashThenPRF (choose2)
open Polynomial

/-! ## The engine: uniform mass of a polynomial's root event -/

section Engine

variable {F : Type} [Field F] [Fintype F]

/-- **The shared engine** behind all three hash properties: the uniform mass
of the root event of a nonzero polynomial of degree ≤ `d` is at most
`d / |F|`. -/
theorem uniform_mass_poly_root_le {d : ℕ} (Q : Polynomial F) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ d) :
    (Dist.uniform F).mass (fun x => Q.eval x = 0) ≤ (d : NNReal) / Fintype.card F := by
  classical
  rw [Dist.uniform_mass_eq_card_filter, div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hsub : ({x ∈ Finset.univ | Q.eval x = 0} : Finset F) ⊆ Q.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hQ, (Finset.mem_filter.mp hx).2⟩
  have hcard : ({x ∈ Finset.univ | Q.eval x = 0} : Finset F).card ≤ d :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Multiset.toFinset_card_le _)
        (le_trans (Polynomial.card_roots' Q) hdeg))
  exact_mod_cast hcard

end Engine

/-! ## Coefficient blocks and the POLYVAL polynomial -/

section BlockPoly

variable {F : Type} [Field F]

/-- One contiguous coefficient block: `Σᵢ cᵢ · X^(off+i)` — the blocks `cᵢ`
placed at consecutive degrees starting at `off`. -/
def blockPoly (off : ℕ) {len : ℕ} (c : Fin len → F) : Polynomial F :=
  ∑ i : Fin len, C (c i) * X ^ (off + i.val)

theorem blockPoly_coeff_mem (off : ℕ) {len : ℕ} (c : Fin len → F) (j : Fin len) :
    (blockPoly off c).coeff (off + j.val) = c j := by
  rw [blockPoly, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [coeff_C_mul, coeff_X_pow,
      if_neg (fun h => hij (Fin.val_injective (by omega))), mul_zero]
  · exact fun h => absurd (Finset.mem_univ j) h

theorem blockPoly_coeff_notin (off : ℕ) {len : ℕ} (c : Fin len → F) {N : ℕ}
    (hN : ∀ i : Fin len, N ≠ off + i.val) :
    (blockPoly off c).coeff N = 0 := by
  rw [blockPoly, finset_sum_coeff]
  exact Finset.sum_eq_zero fun i _ => by
    rw [coeff_C_mul, coeff_X_pow, if_neg (hN i), mul_zero]

theorem blockPoly_natDegree_le (off : ℕ) {len : ℕ} (c : Fin len → F) :
    (blockPoly off c).natDegree ≤ off + len :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    le_trans (natDegree_C_mul_le _ _)
      (le_trans (natDegree_X_pow_le _) (by have := i.isLt; omega))

variable {τ : ℕ}

/-- The POLYVAL-style hash polynomial for tweak `t` and tail `m` of length
`k`: monic of degree `k+τ+2`, tweak blocks at degrees `k+2 .. k+τ+1`,
message blocks at degrees `2 .. k+1`, and **zero** coefficients at `X¹`
and `X⁰` (no constant term). -/
def polyQ (t : Fin τ → F) {k : ℕ} (m : Fin k → F) : Polynomial F :=
  X ^ (k + τ + 2) + blockPoly (k + 2) t + blockPoly 2 m

theorem polyQ_coeff_top (t : Fin τ → F) {k : ℕ} (m : Fin k → F) :
    (polyQ t m).coeff (k + τ + 2) = 1 := by
  rw [polyQ, coeff_add, coeff_add, coeff_X_pow, if_pos rfl,
    blockPoly_coeff_notin _ _ (fun i => by have := i.isLt; omega),
    blockPoly_coeff_notin _ _ (fun i => by have := i.isLt; omega)]
  norm_num

theorem polyQ_coeff_tweak (t : Fin τ → F) {k : ℕ} (m : Fin k → F) (i : Fin τ) :
    (polyQ t m).coeff (k + 2 + i.val) = t i := by
  rw [polyQ, coeff_add, coeff_add, coeff_X_pow,
    if_neg (by have := i.isLt; omega), blockPoly_coeff_mem,
    blockPoly_coeff_notin _ _ (fun j => by have := j.isLt; omega)]
  norm_num

theorem polyQ_coeff_msg (t : Fin τ → F) {k : ℕ} (m : Fin k → F) (j : Fin k) :
    (polyQ t m).coeff (2 + j.val) = m j := by
  rw [polyQ, coeff_add, coeff_add, coeff_X_pow,
    if_neg (by have := j.isLt; omega),
    blockPoly_coeff_notin _ _ (fun i => by have := j.isLt; omega),
    blockPoly_coeff_mem]
  norm_num

theorem polyQ_natDegree_le (t : Fin τ → F) {k : ℕ} (m : Fin k → F) :
    (polyQ t m).natDegree ≤ k + τ + 2 := by
  refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
    (max_le (natDegree_X_pow_le _) ?_)) ?_)
  · exact le_trans (blockPoly_natDegree_le _ _) (by omega)
  · exact le_trans (blockPoly_natDegree_le _ _) (by omega)

/-- Coefficient-extraction helper: a polynomial with a nonzero coefficient is
nonzero. -/
theorem ne_zero_of_coeff {p : Polynomial F} (N : ℕ) (h : p.coeff N ≠ 0) :
    p ≠ 0 := fun h0 => h (by rw [h0]; exact coeff_zero N)

/-- Cross-length separation: two POLYVAL polynomials at *different* tail
lengths never cancel (the longer one's monic top coefficient survives), even
after subtracting any constant. -/
theorem polyQ_add_sub_C_ne_zero_of_lt {k k' : ℕ} (hlt : k < k') (t₁ : Fin τ → F)
    (m₁ : Fin k → F) (t₂ : Fin τ → F) (m₂ : Fin k' → F) (g : F) :
    polyQ t₁ m₁ + polyQ t₂ m₂ - C g ≠ 0 := by
  refine ne_zero_of_coeff (k' + τ + 2) ?_
  rw [coeff_sub, coeff_add, polyQ_coeff_top,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (polyQ_natDegree_le t₁ m₁) (by omega)),
    coeff_C, if_neg (by omega)]
  norm_num

/-- Same-length separation (characteristic 2): two POLYVAL polynomials at the
same tail length with different `(tweak, message)` data never cancel — some
tweak or message coefficient survives the XOR. -/
theorem polyQ_add_sub_C_ne_zero_of_pair_ne [CharP F 2] {k : ℕ}
    (t₁ t₂ : Fin τ → F) (m₁ m₂ : Fin k → F) (g : F)
    (hpair : (t₁, m₁) ≠ (t₂, m₂)) :
    polyQ t₁ m₁ + polyQ t₂ m₂ - C g ≠ 0 := by
  by_cases ht : t₁ = t₂
  · have hm : m₁ ≠ m₂ := fun hm => hpair (by rw [ht, hm])
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hm
    refine ne_zero_of_coeff (2 + j.val) fun hc => hj ?_
    rw [coeff_sub, coeff_add, polyQ_coeff_msg, polyQ_coeff_msg, coeff_C,
      if_neg (by omega), sub_zero] at hc
    exact CharTwo.add_eq_zero.mp hc
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
    refine ne_zero_of_coeff (k + 2 + i.val) fun hc => hi ?_
    rw [coeff_sub, coeff_add, polyQ_coeff_tweak, polyQ_coeff_tweak, coeff_C,
      if_neg (by omega), sub_zero] at hc
    exact CharTwo.add_eq_zero.mp hc

end BlockPoly

/-! ## The hash family: POLYVAL at every length, properties within the cap

The hash simply evaluates `polyQ` at every tail length — no cap fallback is
needed, because `HashFamily` claims the three properties only for
`k ≤ L`, which is exactly where the degree bound `k + τ + 2 ≤ L + τ + 2 = d`
holds. -/

section Hash

variable {F : Type} [Field F] {τ : ℕ} [Fintype F]

/-- **Property 1** (almost uniformity) for the POLYVAL hash, within the cap:
`polyQ − C g` is monic at `X^(k+τ+2)`, of degree ≤ `L+τ+2` by `k ≤ L`. -/
theorem polyval_prop1 (L : ℕ) {k : ℕ} (hk : k ≤ L) (t : Fin τ → F)
    (m : Fin k → F) (g : F) :
    (Dist.uniform F).mass (fun h => (polyQ t m).eval h = g) ≤
      ((L + τ + 2 : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _
    (fun h : F =>
      show (polyQ t m).eval h = g ↔ (polyQ t m - C g).eval h = 0 by
        rw [eval_sub, eval_C, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (polyQ_natDegree_le t m) (by omega))
        (le_trans (natDegree_C g).le (Nat.zero_le _))))
  refine ne_zero_of_coeff (k + τ + 2) ?_
  rw [coeff_sub, polyQ_coeff_top, coeff_C, if_neg (by omega)]
  norm_num

/-- **Property 3** (key-offset) for the POLYVAL hash, within the cap: the
added `X` never reaches the monic top coefficient `X^(k+τ+2)`. -/
theorem polyval_prop3 (L : ℕ) {k : ℕ} (hk : k ≤ L) (t : Fin τ → F)
    (m : Fin k → F) (g : F) :
    (Dist.uniform F).mass (fun h => (polyQ t m).eval h + h = g) ≤
      ((L + τ + 2 : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _
    (fun h : F =>
      show (polyQ t m).eval h + h = g ↔
          Polynomial.eval h (polyQ t m + X - C g) = 0 by
        rw [eval_sub, eval_add, eval_C, eval_X, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (natDegree_add_le _ _)
          (max_le (le_trans (polyQ_natDegree_le t m) (by omega))
            (le_trans natDegree_X_le (by omega))))
        (le_trans (natDegree_C g).le (Nat.zero_le _))))
  refine ne_zero_of_coeff (k + τ + 2) ?_
  rw [coeff_sub, coeff_add, polyQ_coeff_top, coeff_X, if_neg (by omega),
    coeff_C, if_neg (by omega)]
  norm_num

variable [CharP F 2]

/-- **Property 2** (almost-XOR-universality) for the POLYVAL hash, across
length classes within the cap.  Trichotomy on the lengths: cross-length
(the longer monic top survives, `polyQ_add_sub_C_ne_zero_of_lt`) or
same-length (some tweak/message coefficient survives the XOR,
`polyQ_add_sub_C_ne_zero_of_pair_ne`). -/
theorem polyval_prop2 (L : ℕ) {k : ℕ} (hk : k ≤ L) (t₁ : Fin τ → F)
    (m₁ : Fin k → F) {k' : ℕ} (hk' : k' ≤ L) (t₂ : Fin τ → F)
    (m₂ : Fin k' → F) (g : F)
    (hne : (⟨k, t₁, m₁⟩ : Σ k, (Fin τ → F) × (Fin k → F)) ≠ ⟨k', t₂, m₂⟩) :
    (Dist.uniform F).mass
        (fun h => (polyQ t₁ m₁).eval h + (polyQ t₂ m₂).eval h = g) ≤
      ((L + τ + 2 : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _ (fun h : F =>
    show (polyQ t₁ m₁).eval h + (polyQ t₂ m₂).eval h = g ↔
        (polyQ t₁ m₁ + polyQ t₂ m₂ - C g).eval h = 0 by
      rw [eval_sub, eval_add, eval_C, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (natDegree_add_le _ _)
          (max_le (le_trans (polyQ_natDegree_le t₁ m₁) (by omega))
            (le_trans (polyQ_natDegree_le t₂ m₂) (by omega))))
        (le_trans (natDegree_C g).le (Nat.zero_le _))))
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact polyQ_add_sub_C_ne_zero_of_lt hlt t₁ m₁ t₂ m₂ g
  · subst heq
    refine polyQ_add_sub_C_ne_zero_of_pair_ne t₁ t₂ m₁ m₂ g fun hp => ?_
    exact hne (congrArg (Sigma.mk k) hp)
  · rw [add_comm (polyQ t₁ m₁)]
    exact polyQ_add_sub_C_ne_zero_of_lt hgt t₂ m₂ t₁ m₁ g

end Hash

/-! ## The flat POLYVAL polynomial `polyQ` (retired `HashFamily` inhabitant)

The generic-field `polyQ`/`blockPoly` polynomial and its coefficient lemmas
(`polyQ_coeff_*`, `polyval_prop1/2/3`) below were the old flat-`Fin k → F`
`HashFamily` inhabitant `polyvalHf`.  Since the hash interface moved to the
paper's **structured** tail `BitTailS` (alignment-injective via the
`bin(2|T|+2/3)` mode block, App. A), the load-bearing spec inhabitant is
`specHashFamilyVS` (below); the flat `polyQ` inhabitant is retired (its flat
encoding cannot separate an aligned tail from an unaligned tail with the same
blocks, which the structured `prop2` requires).  The `polyQ` lemmas are kept as
standalone POLYVAL facts. -/

/-! ## Historical record (gap #8): the unguarded abstraction was empty

`HashFamily` originally stated Properties 1–3 for **all** tail lengths
`k : ℕ` — no `k ≤ L` guard.  That structure (reproduced verbatim below as
`HashFamilyLUnbounded`, local to this file) admits no instance with a
cryptographically meaningful degree bound: `hashFamilyL_card_le_d` proves
`|F| ≤ d` for *every* inhabitant.  This theorem is kept as the documented
evidence for why the guards on `HashFamily`'s properties exist. -/

/-- The ORIGINAL, unguarded hash bundle (gap #8): identical to `HashFamily`
except that the three properties quantify over **all** tail lengths `k : ℕ`.
Kept only as the subject of the impossibility theorem
`hashFamilyL_card_le_d`; do not use for new development. -/
structure HashFamilyLUnbounded (F T : Type) [Field F] [Fintype F] where
  /-- `H_h̄(tweak, tail)` on a tail of any length `k`. -/
  hash : F → T → ∀ {k : ℕ}, (Fin k → F) → F
  /-- Claimed degree bound. -/
  d : ℕ
  /-- Property 1 (almost uniformity), unguarded. -/
  prop1 : ∀ {k} (t : T) (m : Fin k → F) (g : F),
    (Dist.uniform F).mass (fun h => hash h t m = g) ≤ (d : NNReal) / Fintype.card F
  /-- Property 2 (almost-XOR-universality), unguarded — the fatal field. -/
  prop2 : ∀ {k} (t₁ : T) (m₁ : Fin k → F) {k'} (t₂ : T) (m₂ : Fin k' → F) (g : F),
    (⟨k, t₁, m₁⟩ : Σ k, T × (Fin k → F)) ≠ ⟨k', t₂, m₂⟩ →
    (Dist.uniform F).mass (fun h => hash h t₁ m₁ + hash h t₂ m₂ = g) ≤
      (d : NNReal) / Fintype.card F
  /-- Property 3 (key-offset), unguarded. -/
  prop3 : ∀ {k} (t : T) (m : Fin k → F) (g : F),
    (Dist.uniform F).mass (fun h => hash h t m + h = g) ≤ (d : NNReal) / Fintype.card F

/-- **Pigeonhole obstruction** (gap #8): any `HashFamilyLUnbounded F T` with
`T` nonempty has `|F| ≤ d`.  The input space `Σ k, T × (Fin k → F)` is
infinite, the function space `F → F` is finite, so two distinct inputs induce
the same hash function and unguarded Property 2 at `g = 0` forces
`1 ≤ d/|F|`. -/
theorem hashFamilyL_card_le_d {F T : Type} [Field F] [Fintype F] [CharP F 2]
    [Nonempty T] (Hf : HashFamilyLUnbounded F T) : Fintype.card F ≤ Hf.d := by
  obtain ⟨t0⟩ := ‹Nonempty T›
  have : Infinite (Σ k : ℕ, T × (Fin k → F)) :=
    Infinite.of_injective (fun k : ℕ => ⟨k, t0, fun _ => 0⟩)
      (fun a b hab => congrArg Sigma.fst hab)
  obtain ⟨x, y, hxy, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun z : Σ k : ℕ, T × (Fin k → F) => (fun h => Hf.hash h z.2.1 z.2.2 : F → F))
  have h2 := Hf.prop2 x.2.1 x.2.2 y.2.1 y.2.2 0 hxy
  have hmass : (Dist.uniform F).mass
      (fun h => Hf.hash h x.2.1 x.2.2 + Hf.hash h y.2.1 y.2.2 = 0) = 1 := by
    rw [Dist.mass_congr _ (fun h : F =>
      show (Hf.hash h x.2.1 x.2.2 + Hf.hash h y.2.1 y.2.2 = 0) ↔ True by
        rw [iff_true, show Hf.hash h y.2.1 y.2.2 = Hf.hash h x.2.1 x.2.2 from
          (congrFun heq h).symm]
        exact CharTwo.add_self_eq_zero _)]
    rw [Dist.mass_true]
    exact Dist.weight_uniform
  rw [hmass] at h2
  have hcard0 : ((Fintype.card F : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hle := mul_le_mul_of_nonneg_right h2
    (by positivity : (0 : ℝ) ≤ ((Fintype.card F : ℕ) : ℝ))
  rw [one_mul, div_mul_cancel₀ _ hcard0] at hle
  exact_mod_cast hle

end HCTR2Instance

/-! ## Part III — the spec-literal objects: `specBin`, RFC-8452 POLYVAL, the spec `H` -/

namespace HCTR2Spec

open RandomSystems.CR18.HCTR2
open RandomSystems.HTechnique.HCTR2Instance
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique.HashThenPRF (choose2)
open Polynomial

/-! ## Phase A — the block↔bits bridge for any CharP-2 field

We construct `BlockBits F n` (not assumed) for `Fintype.card F = 2 ^ n`, over
an abstract characteristic-2 finite field. -/

section PhaseA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- `BitVec w ≃ Fin (2^w)` (the structure's `toFin`/`ofFin` pair; formerly
`HCTR2Bit.bitVecEquivFin`, relocated here with the retirement of that module). -/
def bitVecEquivFin (w : ℕ) : BitVec w ≃ Fin (2 ^ w) :=
  ⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩

/-- The componentwise bijection `(Fin n → ZMod 2) ≃ BitVec n`, packing the
`ZMod 2 = Fin 2` coordinates into a bit vector via `finFunctionFinEquiv`. -/
def gBits (n : ℕ) : (Fin n → ZMod 2) ≃ BitVec n :=
  (finFunctionFinEquiv (m := 2)).trans (bitVecEquivFin n).symm

/-- Bit `i` of `gBits n u` reads coordinate `u i`. -/
theorem gBits_getLsbD (n : ℕ) (u : Fin n → ZMod 2) (i : Fin n) :
    (gBits n u).getLsbD i.val = decide ((u i).val = 1) := by
  show (BitVec.ofFin (finFunctionFinEquiv u)).getLsbD i.val = _
  have hb : (BitVec.ofFin (finFunctionFinEquiv u)).getLsbD i.val
      = (finFunctionFinEquiv u : Fin (2 ^ n)).val.testBit i.val := by
    simp [BitVec.getLsbD]
  rw [hb]
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv u) i
  rw [Equiv.symm_apply_apply] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, ← h]; rfl

/-- **The additive law**: `gBits` carries pointwise `ZMod 2` addition to bit XOR. -/
theorem gBits_add (n : ℕ) (u v : Fin n → ZMod 2) :
    gBits n (u + v) = gBits n u ^^^ gBits n v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, gBits_getLsbD n u ⟨i, hi⟩, gBits_getLsbD n v ⟨i, hi⟩,
    gBits_getLsbD n (u + v) ⟨i, hi⟩]
  have hzmod : ∀ x y : ZMod 2, decide ((x + y).val = 1)
      = xor (decide (x.val = 1)) (decide (y.val = 1)) := by decide
  simpa using hzmod (u ⟨i, hi⟩) (v ⟨i, hi⟩)

/-- **ACCEPTANCE A** — `specBlockBits : BlockBits F n`: the block↔bits bridge,
constructed for any characteristic-2 field with `Fintype.card F = 2 ^ n`.  Its
`toBits_add` field (the additive law) is *supplied*, not assumed. -/
def specBlockBits (n : ℕ) (hcard : Fintype.card F = 2 ^ n) : BlockBits F n := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfr : Module.finrank (ZMod 2) F = n := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, hcard] at hc
    exact (Nat.pow_right_injective (le_refl 2) hc).symm
  let bF : Module.Basis (Fin (Module.finrank (ZMod 2) F)) (ZMod 2) F :=
    Module.finBasis (ZMod 2) F
  let e1 : F ≃ (Fin (Module.finrank (ZMod 2) F) → ZMod 2) := bF.equivFun.toEquiv
  let reix : (Fin (Module.finrank (ZMod 2) F) → ZMod 2) ≃ (Fin n → ZMod 2) :=
    Equiv.arrowCongr (finCongr hfr) (Equiv.refl (ZMod 2))
  exact
    { toBits := (e1.trans reix).trans (gBits n)
      toBits_add := by
        intro a b
        show gBits n (reix (e1 (a + b)))
            = gBits n (reix (e1 a)) ^^^ gBits n (reix (e1 b))
        have hlin : e1 (a + b) = e1 a + e1 b := by
          simp only [e1, LinearEquiv.coe_toEquiv, map_add]
        rw [hlin]
        have hrei : reix (e1 a + e1 b) = reix (e1 a) + reix (e1 b) := by
          funext i; simp [reix, Equiv.arrowCongr]
        rw [hrei, gBits_add] }

end PhaseA

/-! ## Phase B — the little-endian block encoder `bin`

`specBin i = toBits⁻¹(ofNat n i)`, the field element whose bit pattern is the
`n`-bit little-endian encoding of `i`.  Injective below `2 ^ n` (the `ofNat`
round-trips through `toNat` modulo `2 ^ n`). -/

section PhaseB

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **ACCEPTANCE B (encoder)** — the little-endian block encoder from the
bridge. -/
def specBin (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (i : ℕ) : F :=
  (specBlockBits n hcard).toBits.symm (BitVec.ofNat n i)

/-- **ACCEPTANCE B (injectivity)** — `specBin` is injective on `0 .. 2ⁿ − 1`. -/
theorem specBin_inj (n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    ∀ i j, i < 2 ^ n → j < 2 ^ n →
      specBin n hcard i = specBin n hcard j → i = j := by
  intro i j hi hj hij
  have hbv : (BitVec.ofNat n i) = BitVec.ofNat n j :=
    (specBlockBits n hcard).toBits.symm.injective hij
  have := congrArg BitVec.toNat hbv
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj] at this

/-- **ACCEPTANCE B (`BinEnc`)** — the encoder packaged as a `BinEnc F L`, using
`L + 1 < 2ⁿ` to place the used index range `0 .. L+1` inside the injective
window. -/
def specBinEnc (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (L : ℕ)
    (hL : L + 1 < 2 ^ n) : BinEnc F L where
  bin := specBin n hcard
  bin_inj i j hi hj hij :=
    specBin_inj n hcard i j (lt_of_le_of_lt hi hL) (lt_of_le_of_lt hj hL) hij

end PhaseB

/-! ## Phase C — the literal POLYVAL hash (RFC-8452 dot convention)

RFC-8452's `POLYVAL(h, X₁..Xₛ) = Σᵢ Xᵢ ⊗ hˢ⁻ⁱ⁺¹` with `a ⊗ b = a·b·x⁻¹²⁸`.
The representation-dependent factor `x⁻¹²⁸` is abstracted as a unit `u : Fˣ`
(for the concrete field, `u = (xclass ^ 128)⁻¹`).

We use the **0-based** index `i : Fin s` with exponent `s − i` (so `i = 0`, the
first block, sits at the *top* degree `s`, and `i = s−1`, the last block, sits
at degree `1`).  This matches the RFC's 1-based `s − i + 1` after the `0↔1`
shift; the last block has degree `1` in `h` and there is **no constant term**.

The polynomial in `h` is therefore
`polyvalPoly u blocks = Σᵢ (blocks[i] · u) · X^(s−i)` — degrees `1 .. s`, with
a possibly-nonzero *linear* coefficient (RFC's last block times `h`), unlike
`polyvalHf`'s `polyQ` whose linear coefficient was forced to zero.  Every hash
property below therefore relies on the **top** coefficient `blocks[0] · u` (the
domain/length block), which the `+ X` and `− C g` perturbations never reach. -/

section PhaseC

variable {F : Type} [Field F]

/-- RFC-8452 dot product `a ⊗ b = a · b · u`. -/
def polyvalDot (u : Fˣ) (a b : F) : F := a * b * (u : F)

/-- **The literal POLYVAL** — `Σᵢ blocks[i] ⊗ hˢ⁻ⁱ` over `i : Fin s`
(`s = blocks.length`), 0-based, so the last block has exponent `1`. -/
def POLYVAL (u : Fˣ) (h : F) (blocks : List F) : F :=
  ∑ i : Fin blocks.length, polyvalDot u (blocks.get i) (h ^ (blocks.length - i.val))

/-- The POLYVAL polynomial `Σᵢ (blocks[i] · u) · X^(s−i)`. -/
def polyvalPoly (u : Fˣ) (blocks : List F) : Polynomial F :=
  ∑ i : Fin blocks.length, C (blocks.get i * (u : F)) * X ^ (blocks.length - i.val)

/-- **ACCEPTANCE C (eval bridge)** — `POLYVAL = eval ∘ polyvalPoly`. -/
theorem POLYVAL_eq_eval (u : Fˣ) (h : F) (blocks : List F) :
    POLYVAL u h blocks = Polynomial.eval h (polyvalPoly u blocks) := by
  rw [POLYVAL, polyvalPoly, eval_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X, polyvalDot]; ring

/-- **ACCEPTANCE C (coefficient extraction)** — coefficient at degree `s − i`
is `blocks[i] · u`.  The exponents `s − i` are distinct across `i : Fin s`
(Nat subtraction is injective on `[0, s)`), so exactly one term contributes. -/
theorem polyvalPoly_coeff (u : Fˣ) (blocks : List F) (i : Fin blocks.length) :
    (polyvalPoly u blocks).coeff (blocks.length - i.val) = blocks.get i * (u : F) := by
  rw [polyvalPoly, finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hji ?_), mul_zero]
    exact Fin.val_injective (by have := i.isLt; have := j.isLt; omega)
  · exact fun h => absurd (Finset.mem_univ i) h

/-- **ACCEPTANCE C (degree bound)** — the honest degree bound `natDegree ≤ s`. -/
theorem polyvalPoly_natDegree_le (u : Fˣ) (blocks : List F) :
    (polyvalPoly u blocks).natDegree ≤ blocks.length :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    le_trans (natDegree_C_mul_le _ _)
      (le_trans (natDegree_X_pow_le _) (by have := i.isLt; omega))

/-- The **top** coefficient (degree `s`) is `blocks[0] · u`, for a nonempty
block list — the domain/length separator that drives every property. -/
theorem polyvalPoly_coeff_top (u : Fˣ) (blocks : List F) (hne : 0 < blocks.length) :
    (polyvalPoly u blocks).coeff blocks.length = blocks.get ⟨0, hne⟩ * (u : F) := by
  have := polyvalPoly_coeff u blocks ⟨0, hne⟩
  simpa using this

/-! ### Task 1 — the paper's formal `poly` / `H` and the bridge to POLYVAL

**Reconciliation (paper p.6–7 vs our POLYVAL) — the exponent table.**

Paper p.6 defines `poly(M₀‖…‖M_{l-1}) = M₀·h^{l-1} ⊕ … ⊕ M_{l-1}`: block `i`
sits at power `h^{l-1-i}`, so block `0` is the leading (top-degree) block and
the **last** block `M_{l-1}` is the *constant term* `h^0`.  The paper's `H`
(p.7) hashes the block list `bin(2|T|+2/3) ‖ pad(T) ‖ M ‖ 0ⁿ` — note the
**trailing `0ⁿ` block**, which lands in the constant-term slot.

Our `POLYVAL u h blocks = Σᵢ blocks[i]·u·h^{s-i}` (`i : Fin s`, `s = length`):
exponent floor is **`1`** (`i = s-1` gives `h^1`), so there is *no* constant
term at all, and each block carries an extra dot-unit factor `u`.

Correspondence on the block list `B` (our list, WITHOUT the trailing `0ⁿ`),
with `s = B.length = 1 + τ + k`:

| block            | list idx | paper `poly(B‖0ⁿ)` power | our `POLYVAL B` power |
|------------------|----------|--------------------------|-----------------------|
| `bin(2|T|+…)`    | `0`      | `h^s` (= `h^{d}`)        | `h^s` (= `h^{d}`)     |
| last msg block   | `s-1`    | `h^1`                    | `h^1`                 |
| trailing `0ⁿ`    | `s`      | `h^0` (coeff `0`)        | *(absent)*            |

Both give top degree `s = d = 1 + τ + k` (matching `d(T,M) = 1 + ⌈|T|/n⌉ +
⌈|M|/n⌉`) and a zero constant term.  **Verdict: PROPERTY-EQUIVALENT, equal up
to the unit `u` — NOT pointwise.**  The identity is
`polyvalPoly u B = C u · paperPoly (B ‖ 0ⁿ)` (`polyvalPoly_eq_paperPoly` below):
the trailing `0ⁿ` supplies the paper's "constant term is zero" while our
exponent floor of `1` gives the same structurally; the `u` is the RFC-8452 dot
factor (`H_h̄` additionally evaluates at `h = x⁻ⁿh̄`, a change of the free
evaluation point that leaves the uniform-mass bounds invariant).  `specH` is
therefore kept as-is and the bridge is proved as a THEOREM. -/

/-- **The paper's `poly`** (paper p.6): the formal polynomial
`poly(M₀‖…‖M_{l-1}) = Σᵢ Mᵢ·h^{l-1-i}` — block `i` at power `h^{l-1-i}`, so
block `0` is the leading block and the last block is the constant term. -/
def paperPoly (blocks : List F) : Polynomial F :=
  ∑ i : Fin blocks.length, C (blocks.get i) * X ^ (blocks.length - 1 - i.val)

/-- Coefficient extraction for the paper `poly`: coeff at `l-1-i` is `blocks[i]`
(the exponents `l-1-i` are distinct across `i : Fin l`). -/
theorem paperPoly_coeff (blocks : List F) (i : Fin blocks.length) :
    (paperPoly blocks).coeff (blocks.length - 1 - i.val) = blocks.get i := by
  rw [paperPoly, finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hji
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hji ?_), mul_zero]
    exact Fin.val_injective (by have := i.isLt; have := j.isLt; omega)
  · exact fun h => absurd (Finset.mem_univ i) h

/-- **Bridge (unit shift)** — `polyvalPoly u = C u · X · paperPoly`: our
POLYVAL polynomial is `C u · X` times the paper's `poly` (the exponent floor of
`1` is the paper's `poly` shifted up one power of `h`, dot-factor `u` pulled
out).  Both sums range over `Fin blocks.length`, so no reindexing is needed. -/
theorem polyvalPoly_eq_CX_paperPoly (u : Fˣ) (blocks : List F) :
    polyvalPoly u blocks = C (u : F) * X * paperPoly blocks := by
  rw [polyvalPoly, paperPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have he : blocks.length - i.val = (blocks.length - 1 - i.val) + 1 := by
    have := i.isLt; omega
  rw [he, pow_succ, map_mul]
  ring

/-- **The trailing `0ⁿ` block** (paper p.7): appending the paper's `0ⁿ` block
multiplies `poly` by `X` — the zero block takes the constant-term slot
(contributing `0`) and shifts every other block up one power of `h`. -/
theorem paperPoly_snoc_zero (blocks : List F) :
    paperPoly (blocks ++ [(0 : F)]) = paperPoly blocks * X := by
  have hlen : blocks.length + 1 = (blocks ++ [(0 : F)]).length := by simp
  rw [paperPoly, ← Fin.sum_congr' _ hlen, Fin.sum_univ_castSucc]
  have hlast : ((blocks ++ [(0 : F)]).get (Fin.cast hlen (Fin.last blocks.length))) = 0 := by
    simp
  rw [show (C ((blocks ++ [(0 : F)]).get (Fin.cast hlen (Fin.last blocks.length)))
        * X ^ ((blocks ++ [(0 : F)]).length - 1 - (Fin.cast hlen (Fin.last blocks.length)).val))
      = 0 by rw [hlast]; simp, add_zero, paperPoly, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hget : (blocks ++ [(0 : F)]).get (Fin.cast hlen (Fin.castSucc i)) = blocks.get i := by
    have hi : i.val < blocks.length := i.isLt
    simp [List.getElem_append_left hi]
  have hval : (Fin.cast hlen (Fin.castSucc i)).val = i.val := rfl
  rw [hget, hval, show (blocks ++ [(0 : F)]).length = blocks.length + 1 from hlen.symm]
  have he : blocks.length + 1 - 1 - i.val = (blocks.length - 1 - i.val) + 1 := by
    have := i.isLt; omega
  rw [he, pow_succ]
  ring

/-- **Bridge (literal paper form)** — `polyvalPoly u B = C u · paperPoly (B ‖ 0ⁿ)`:
our POLYVAL over `B` equals the unit `u` times the paper's `poly` over the
p.7 block list `B ‖ 0ⁿ` (with the trailing `0ⁿ` block).  This makes the p.7
display's exponent/constant-term convention a THEOREM, not a claim. -/
theorem polyvalPoly_eq_paperPoly (u : Fˣ) (blocks : List F) :
    polyvalPoly u blocks = C (u : F) * paperPoly (blocks ++ [(0 : F)]) := by
  rw [paperPoly_snoc_zero, polyvalPoly_eq_CX_paperPoly]; ring

end PhaseC

/-! ## Phase D — the `10*` pad, the spec `H`, and the paper-form reconciliation

The spec's `H` prepends the length/domain-separation block `bin(2·|T| + 2)`
(aligned) / `bin(2·|T| + 3)` (unaligned) to the tweak blocks and the (padded)
message blocks, then applies `POLYVAL`.  The block list has length
`s = 1 + ⌈|T|/n⌉ + k`; under the literal POLYVAL exponents `s − i` the length
block (list index `0`) sits at the **top** degree `s` — the honest per-query
hash degree (`+1` LESS than a separate-monic-top design).  Every property is
driven by that top coefficient `lengthBlock · u`: it survives the `− C g` and
`+ X` perturbations (cross-length and prop1/prop3 cases), and at equal length
the tops cancel in characteristic 2 so a differing lower block survives.

SPEC DEVIATION notes carried by the bundles below: the literal POLYVAL shape
needs `1 ≤ ⌈|T|/n⌉` (so prop3's `+ X` misses the top) and `lengthBlock ≠ 0`
(so the top coefficient is nonzero) — both honest consequences of the spec's
own hash, not modeling slack. -/

section PhaseD

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {T : Type} [Fintype T] [DecidableEq T]

/-! ### The `10*` padding block (ACCEPTANCE D1)

`padMsg m part` appends one block: the `r` low bits `part`, a marker `1` at
position `r`, and zeros above — the classic injective `10*` pad.  The marker is
the highest set bit, so it recovers `r`; the low `r` bits recover `part`; the
prefix recovers `m`.  Requires `r < n` (the marker needs room). -/

-- The `10*` pad block `padBlockBits` and its recovery lemmas
-- (`padBlockBits_r_inj`, `padBlockBits_setWidth`) now come from the
-- consolidated `RandomSystems.CR18.HCTR2` (opened above).

/-- The padded message: `m` followed by the `10*` pad block, mapped into `F`. -/
def padMsg {n : ℕ} (bb : BlockBits F n) (m : List F) {r : ℕ} (part : BitVec r) : List F :=
  m ++ [bb.toBits.symm (padBlockBits n r part)]

-- D1 exact form: for `r₁, r₂ < n`, the map `(m, r, part) ↦ padMsg bb m part` is
-- injective — equal padded messages force equal prefixes (`m₁ = m₂`), equal
-- leftover-bit counts (`r₁ = r₂`), and equal leftover bits (`HEq p₁ p₂`, since the
-- `partial`s live in the length-dependent types `BitVec r₁`, `BitVec r₂`).
/-- **ACCEPTANCE D1** — injectivity of the `10*` padding. -/
theorem padMsg_inj {n : ℕ} (bb : BlockBits F n) (m1 m2 : List F) {r1 r2 : ℕ}
    (hr1 : r1 < n) (hr2 : r2 < n) (p1 : BitVec r1) (p2 : BitVec r2)
    (h : padMsg bb m1 p1 = padMsg bb m2 p2) :
    m1 = m2 ∧ r1 = r2 ∧ HEq p1 p2 := by
  unfold padMsg at h
  obtain ⟨hm, he⟩ := List.append_inj' h rfl
  have hblk : padBlockBits n r1 p1 = padBlockBits n r2 p2 := by simpa using he
  have hr : r1 = r2 := padBlockBits_r_inj n r1 r2 hr1 hr2 p1 p2 hblk
  subst hr
  refine ⟨hm, rfl, heq_of_eq ?_⟩
  have hpad := padBlockBits_setWidth n r1 hr1 p1
  rw [hblk, padBlockBits_setWidth n r1 hr2 p2] at hpad
  exact hpad.symm

/-- **ACCEPTANCE D (spec `H`)** — the spec hash: length/domain-separation block
`bin(2·τn + [2 aligned | 3 unaligned])`, then tweak blocks, then message
blocks, under `POLYVAL`. -/
def specH (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (τ : ℕ)
    (tweakBlocks : T ↪ (Fin τ → F)) (h : F) (t : T) (msgBlocks : List F)
    (aligned : Bool) : F :=
  POLYVAL u h (specBin n hcard (2 * (τ * n) + if aligned then 2 else 3)
    :: (List.ofFn (tweakBlocks t) ++ msgBlocks))

/-- **The paper's `H(T,M)` formal polynomial** (paper p.7 display, literal):

  `H(T,M) = poly(bin(2|T|+2) ‖ pad(T) ‖ M ‖ 0ⁿ)`     if `n ∣ |M|` (aligned)
  `H(T,M) = poly(bin(2|T|+3) ‖ pad(T) ‖ pad(M‖1) ‖ 0ⁿ)`  otherwise

At block level both branches are `c :: (tw ++ m ++ [0ⁿ])` with `c` the
length/domain block `bin(…)`, `tw = pad(T)`, `m = M` (aligned) or `pad(M‖1)`
(unaligned), and the trailing `0ⁿ` block; the aligned/unaligned choice is the
value of `c` and the shape of `m` at the call site. -/
def paperHPoly (c : F) (tw m : List F) : Polynomial F :=
  paperPoly (c :: (tw ++ m ++ [0]))

/-- **ACCEPTANCE 1** — the p.7 `H` display as a THEOREM: `specH` equals the unit
`u` times the evaluation of the paper's literal `poly(bin(…) ‖ pad(T) ‖ M ‖ 0ⁿ)`.
The `0ⁿ` block and the paper's `h^{l-1-i}` convention are transcribed exactly;
the sole difference from a pointwise equality is the RFC-8452 dot-unit `u` (and
`H_h̄`'s evaluation point `h = x⁻ⁿh̄`, folded into the free `h`).  See the Phase
C reconciliation table. -/
theorem specH_eq_paper_form (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (τ : ℕ)
    (tweakBlocks : T ↪ (Fin τ → F)) (h : F) (t : T) (msgBlocks : List F) (aligned : Bool) :
    specH u n hcard τ tweakBlocks h t msgBlocks aligned
      = (u : F) * Polynomial.eval h
          (paperHPoly (specBin n hcard (2 * (τ * n) + if aligned then 2 else 3))
            (List.ofFn (tweakBlocks t)) msgBlocks) := by
  rw [specH, POLYVAL_eq_eval, polyvalPoly_eq_paperPoly, paperHPoly, eval_mul, eval_C]
  simp [List.append_assoc]

/-! ## Phase DV — variable-length tweaks (Task 2/3)

The fixed-`τ` development above is generalized to per-tweak block lengths, as in
the paper's `H` which accepts ANY tweak length via `bin(2|T|+…) ‖ pad(T)`.  We
first lift the property/separator lemmas to arbitrary block lists `B` (driven by
the top coefficient `B[0]·u` and, at equal length, a differing lower block),
then transcribe Appendix A's injectivity, then package `specHashFamilyV`. -/

/-- **Property 1, list-level**: for any block list `B` with nonzero head and
length within the degree cap `D`, the top coefficient `B[0]·u` survives `− C g`. -/
theorem polyvalMassV_prop1 (u : Fˣ) (B : List F) (D : ℕ) (hlen : B.length ≤ D)
    (hpos : 0 < B.length) (hhead : B.get ⟨0, hpos⟩ ≠ 0) (g : F) :
    (Dist.uniform F).mass (fun h => POLYVAL u h B = g)
      ≤ ((D : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _ (fun h : F =>
    show POLYVAL u h B = g ↔ (polyvalPoly u B - C g).eval h = 0 by
      rw [POLYVAL_eq_eval, eval_sub, eval_C, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _) (max_le
      (le_trans (polyvalPoly_natDegree_le _ _) hlen)
      (le_trans (natDegree_C g).le (Nat.zero_le _))))
  refine ne_zero_of_coeff B.length ?_
  rw [coeff_sub, polyvalPoly_coeff_top u B hpos, coeff_C, if_neg (by omega), sub_zero]
  exact mul_ne_zero hhead (Units.ne_zero u)

/-- **Property 3, list-level**: the added `X` (degree `1`) misses the top degree
`s = B.length ≥ 2`, so the top coefficient survives. -/
theorem polyvalMassV_prop3 (u : Fˣ) (B : List F) (D : ℕ) (hlen : B.length ≤ D)
    (hpos : 0 < B.length) (h2 : 2 ≤ B.length) (hhead : B.get ⟨0, hpos⟩ ≠ 0) (g : F) :
    (Dist.uniform F).mass (fun h => POLYVAL u h B + h = g)
      ≤ ((D : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _ (fun h : F =>
    show POLYVAL u h B + h = g ↔
        Polynomial.eval h (polyvalPoly u B + X - C g) = 0 by
      rw [POLYVAL_eq_eval, eval_sub, eval_add, eval_C, eval_X, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _) (max_le
      (le_trans (natDegree_add_le _ _) (max_le
        (le_trans (polyvalPoly_natDegree_le _ _) hlen)
        (le_trans natDegree_X_le (by omega))))
      (le_trans (natDegree_C g).le (Nat.zero_le _))))
  refine ne_zero_of_coeff B.length ?_
  rw [coeff_sub, coeff_add, polyvalPoly_coeff_top u B hpos, coeff_X, if_neg (by omega),
    coeff_C, if_neg (by omega), add_zero, sub_zero]
  exact mul_ne_zero hhead (Units.ne_zero u)

/-- Cross-length separator, list-level: the longer list's monic top (its nonzero
head) survives, above the shorter list's degree. -/
theorem polyvalPoly_crossLenV_ne_zero (u : Fˣ) (B1 B2 : List F) (g : F)
    (hlt : B1.length < B2.length) (hpos2 : 0 < B2.length)
    (hhead2 : B2.get ⟨0, hpos2⟩ ≠ 0) :
    polyvalPoly u B1 + polyvalPoly u B2 - C g ≠ 0 := by
  refine ne_zero_of_coeff B2.length ?_
  rw [coeff_sub, coeff_add, polyvalPoly_coeff_top u B2 hpos2,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (polyvalPoly_natDegree_le _ _) hlt),
    coeff_C, if_neg (by omega), zero_add, sub_zero]
  exact mul_ne_zero hhead2 (Units.ne_zero u)

/-- Same-length separator, list-level: the shared tops (if any) cancel in
char 2, and a differing block index yields a surviving lower coefficient. -/
theorem polyvalPoly_sameLenV_ne_zero (u : Fˣ) (B1 B2 : List F) (g : F)
    (hlen : B1.length = B2.length) (hne : B1 ≠ B2) :
    polyvalPoly u B1 + polyvalPoly u B2 - C g ≠ 0 := by
  have hex : ∃ i : Fin B1.length, B1.get i ≠ B2.get ⟨i.val, hlen ▸ i.isLt⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hne (List.ext_get hlen (fun i h1 h2 => hcon ⟨i, h1⟩))
  obtain ⟨i, hi⟩ := hex
  set i' : Fin B2.length := ⟨i.val, hlen ▸ i.isLt⟩ with hi'def
  refine ne_zero_of_coeff (B1.length - i.val) ?_
  have hc1 := polyvalPoly_coeff u B1 i
  have hc2 := polyvalPoly_coeff u B2 i'
  have hD : B2.length - i'.val = B1.length - i.val := by
    have e1 : B1.length = B2.length := hlen
    have e2 : i'.val = i.val := rfl
    omega
  rw [hD] at hc2
  have hpos : B1.length - i.val ≠ 0 := by have := i.isLt; omega
  rw [coeff_sub, coeff_add, hc1, hc2, coeff_C, if_neg hpos, sub_zero]
  intro hzero; apply hi
  rw [← add_mul] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact CharTwo.add_eq_zero.mp h
  · exact absurd h (Units.ne_zero u)

/-- **Property 2, list-level**: trichotomy on the two block lists' lengths
(cross-length, or same-length with distinct lists) bounds the XOR-collision mass. -/
theorem polyvalMassV_prop2 (u : Fˣ) (B1 B2 : List F) (D : ℕ)
    (hlen1 : B1.length ≤ D) (hlen2 : B2.length ≤ D)
    (hpos1 : 0 < B1.length) (hpos2 : 0 < B2.length)
    (hhead1 : B1.get ⟨0, hpos1⟩ ≠ 0) (hhead2 : B2.get ⟨0, hpos2⟩ ≠ 0)
    (hne : B1 ≠ B2) (g : F) :
    (Dist.uniform F).mass (fun h => POLYVAL u h B1 + POLYVAL u h B2 = g)
      ≤ ((D : ℕ) : NNReal) / Fintype.card F := by
  rw [Dist.mass_congr _ (fun h : F =>
    show POLYVAL u h B1 + POLYVAL u h B2 = g ↔
        (polyvalPoly u B1 + polyvalPoly u B2 - C g).eval h = 0 by
      rw [POLYVAL_eq_eval, POLYVAL_eq_eval, eval_sub, eval_add, eval_C, sub_eq_zero])]
  refine uniform_mass_poly_root_le _ ?_
    (le_trans (natDegree_sub_le _ _) (max_le
      (le_trans (natDegree_add_le _ _) (max_le
        (le_trans (polyvalPoly_natDegree_le _ _) hlen1)
        (le_trans (polyvalPoly_natDegree_le _ _) hlen2)))
      (le_trans (natDegree_C g).le (Nat.zero_le _))))
  rcases Nat.lt_trichotomy B1.length B2.length with hlt | heq | hgt
  · exact polyvalPoly_crossLenV_ne_zero u B1 B2 g hlt hpos2 hhead2
  · exact polyvalPoly_sameLenV_ne_zero u B1 B2 g heq hne
  · rw [add_comm (polyvalPoly u B1)]
    exact polyvalPoly_crossLenV_ne_zero u B2 B1 g hgt hpos1 hhead1

/-! ### Variable-length tweak inputs and Appendix A injectivity

A variable-length input to the paper's `H` is a tweak `t : T` plus a message
payload: either a block-aligned message `M` (aligned branch, `bin(2|T|+2)`), or
an unaligned message given by full blocks `body` and an `r`-bit remainder `part`
with `r < n` (the `pad(M‖1)` branch, `bin(2|T|+3)`), `r` carried as `Fin n`. -/

/-- Variable-length message payload (`inl` = aligned `M`; `inr` = unaligned
`⟨r, body, part⟩` with `r : Fin n` the leftover-bit count `< n`). -/
abbrev SpecMsg (F : Type) (n : ℕ) : Type :=
  List F ⊕ (Σ r : Fin n, List F × BitVec r.val)

/-- The paper's full hashed block list on a variable-length input (our
convention, i.e. WITHOUT the trailing `0ⁿ` block — see the Task 1 bridge):
`bin(2|T|+2) ‖ pad(T) ‖ M` (aligned) or `bin(2|T|+3) ‖ pad(T) ‖ pad(M‖1)`
(unaligned).  `tweakEnc t = pad(T)` (block-level), `tweakBits t = |T|`. -/
def specBlockListV (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (bb : BlockBits F n)
    (tweakEnc : T → List F) (tweakBits : T → ℕ) : T × SpecMsg F n → List F
  | (t, Sum.inl M) =>
      specBin n hcard (2 * tweakBits t + 2) :: (tweakEnc t ++ M)
  | (t, Sum.inr ⟨_r, body, part⟩) =>
      specBin n hcard (2 * tweakBits t + 3) :: (tweakEnc t ++ padMsg bb body part)

/-- **ACCEPTANCE 2** — Appendix A injectivity (paper p.31–32, `GetTM`).  The map
`(t, payload) ↦ full hashed block list` is injective.  The transcription of
`GetTM`: the **first block** `bin(2|T|+2/3)` determines both `|T|` (via
`specBin` injectivity, `GetTM` l.5) and the alignment bit (its parity, `GetTM`
l.9); `|T|` (`= tweakBits`) fixes the `pad(T)` block count `= (tweakEnc t).length`
(via `htwLen`, `GetTM` l.8), so the split `pad(T) ‖ message` is determined
(`List.append_inj`); then `htwInj` recovers `t` (`GetTM` l.21), and the message
part is recovered directly (aligned, `GetTM` l.11) or by stripping the `10*`
pad (`padMsg_inj`, unaligned, `GetTM` l.14–19).

`htwLen` states `(tweakEnc t).length = ⌈|T|/n⌉` in the `(bits + n − 1)/n` form
(ceil-division for `n > 0`); only `bt₁ = bt₂ → lengths equal` is used, so the
exact formula is immaterial.  `htwBits` bounds the length-block index below `2ⁿ`
so `specBin` is injective there. -/
theorem specH_input_inj (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (bb : BlockBits F n)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n) :
    Function.Injective (specBlockListV (T := T) n hcard bb tweakEnc tweakBits) := by
  rintro ⟨t1, m1⟩ ⟨t2, m2⟩ heq
  rcases m1 with M1 | ⟨r1, body1, part1⟩ <;> rcases m2 with M2 | ⟨r2, body2, part2⟩ <;>
    simp only [specBlockListV, List.cons.injEq] at heq
  · -- aligned / aligned
    obtain ⟨hc, htail⟩ := heq
    have hbt : 2 * tweakBits t1 + 2 = 2 * tweakBits t2 + 2 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    have hbits : tweakBits t1 = tweakBits t2 := by omega
    have hlenq : (tweakEnc t1).length = (tweakEnc t2).length := by
      rw [htwLen, htwLen, hbits]
    obtain ⟨htw, hM⟩ := List.append_inj htail hlenq
    have ht : t1 = t2 := htwInj t1 t2 hbits htw
    subst ht; subst hM; rfl
  · -- aligned / unaligned : parity contradiction on the first block
    obtain ⟨hc, _⟩ := heq
    have hbt : 2 * tweakBits t1 + 2 = 2 * tweakBits t2 + 3 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    omega
  · -- unaligned / aligned : parity contradiction
    obtain ⟨hc, _⟩ := heq
    have hbt : 2 * tweakBits t1 + 3 = 2 * tweakBits t2 + 2 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    omega
  · -- unaligned / unaligned
    obtain ⟨hc, htail⟩ := heq
    have hbt : 2 * tweakBits t1 + 3 = 2 * tweakBits t2 + 3 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    have hbits : tweakBits t1 = tweakBits t2 := by omega
    have hlenq : (tweakEnc t1).length = (tweakEnc t2).length := by
      rw [htwLen, htwLen, hbits]
    obtain ⟨htw, hpad⟩ := List.append_inj htail hlenq
    have ht : t1 = t2 := htwInj t1 t2 hbits htw
    subst ht
    obtain ⟨hbody, hr, hpart⟩ := padMsg_inj bb body1 body2 r1.isLt r2.isLt part1 part2 hpad
    have hrfin : r1 = r2 := Fin.ext hr
    subst hbody
    subst hrfin
    have hpart' : part1 = part2 := eq_of_heq hpart
    subst hpart'
    rfl

/-- The **structured-tail** block list (paper §3.2): `bin(2|T|+2) ‖ pad(T) ‖ N`
(aligned, `opt = none`) or `bin(2|T|+3) ‖ pad(T) ‖ (N ‖ b)` (unaligned, `opt = some b`
with `b` the pre-`10*`-padded partial block).  The mode block `bin(2|T|+2/3)` is the
paper's App.-A injectivity witness (parity ↔ alignment). -/
def specBlockV (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (tweakEnc : T → List F)
    (tweakBits : T → ℕ) (t : T) (m : BitTailS F) : List F :=
  match m.2.2 with
  | none => specBin n hcard (2 * tweakBits t + 2) :: (tweakEnc t ++ List.ofFn m.2.1)
  | some b => specBin n hcard (2 * tweakBits t + 3) :: (tweakEnc t ++ (List.ofFn m.2.1 ++ [b]))

/-- Honest block-list length `= ⌈|T|/n⌉ + mˢ` (`mˢ = bitTailDegLen`). -/
theorem specBlockV_length (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (tweakEnc : T → List F)
    (tweakBits : T → ℕ) (t : T) (m : BitTailS F) :
    (specBlockV n hcard tweakEnc tweakBits t m).length
      = (tweakEnc t).length + bitTailDegLen m := by
  obtain ⟨ℓ, N, (_ | b)⟩ := m <;>
    simp [specBlockV, bitTailDegLen, List.length_append, List.length_ofFn] <;> omega

theorem specBlockV_pos (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (tweakEnc : T → List F)
    (tweakBits : T → ℕ) (t : T) (m : BitTailS F) :
    0 < (specBlockV n hcard tweakEnc tweakBits t m).length := by
  rw [specBlockV_length]; unfold bitTailDegLen; omega

/-- The block-list head is the nonzero mode block `bin(2|T|+2/3)`. -/
theorem specBlockV_head_ne (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (tweakEnc : T → List F)
    (tweakBits : T → ℕ) (t : T) (m : BitTailS F)
    (h2 : specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (h3 : specBin n hcard (2 * tweakBits t + 3) ≠ 0)
    (hpos : 0 < (specBlockV n hcard tweakEnc tweakBits t m).length) :
    (specBlockV n hcard tweakEnc tweakBits t m).get ⟨0, hpos⟩ ≠ 0 := by
  obtain ⟨ℓ, N, (_ | b)⟩ := m <;> simpa [specBlockV] using ‹_›

/-- Structured-tail injectivity (paper App. A): distinct `(t, tail)` give distinct block
lists.  The mode block `bin(2|T|+2/3)` separates aligned from unaligned (parity), `htwInj`
recovers `t`, and `List.append_inj` splits `pad(T) ‖ tail`. -/
theorem specBlockV_sigma_inj (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (t1 t2 : T) (m1 m2 : BitTailS F)
    (heq : specBlockV n hcard tweakEnc tweakBits t1 m1
      = specBlockV n hcard tweakEnc tweakBits t2 m2) :
    ((t1, m1) : T × BitTailS F) = (t2, m2) := by
  obtain ⟨ℓ1, N1, opt1⟩ := m1
  obtain ⟨ℓ2, N2, opt2⟩ := m2
  rcases opt1 with _ | b1 <;> rcases opt2 with _ | b2 <;>
    simp only [specBlockV, List.cons.injEq] at heq
  · obtain ⟨hc, htail⟩ := heq
    have hbt : 2 * tweakBits t1 + 2 = 2 * tweakBits t2 + 2 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    have hbits : tweakBits t1 = tweakBits t2 := by omega
    have hlenq : (tweakEnc t1).length = (tweakEnc t2).length := by rw [htwLen, htwLen, hbits]
    obtain ⟨htw, hM⟩ := List.append_inj htail hlenq
    have ht : t1 = t2 := htwInj t1 t2 hbits htw
    subst ht
    have hll : ℓ1 = ℓ2 := by have := congrArg List.length hM; simpa using this
    subst hll
    have : N1 = N2 := List.ofFn_injective hM
    subst this; rfl
  · obtain ⟨hc, _⟩ := heq
    have hbt : 2 * tweakBits t1 + 2 = 2 * tweakBits t2 + 3 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    omega
  · obtain ⟨hc, _⟩ := heq
    have hbt : 2 * tweakBits t1 + 3 = 2 * tweakBits t2 + 2 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    omega
  · obtain ⟨hc, htail⟩ := heq
    have hbt : 2 * tweakBits t1 + 3 = 2 * tweakBits t2 + 3 :=
      specBin_inj n hcard _ _ (by have := htwBits t1; omega) (by have := htwBits t2; omega) hc
    have hbits : tweakBits t1 = tweakBits t2 := by omega
    have hlenq : (tweakEnc t1).length = (tweakEnc t2).length := by rw [htwLen, htwLen, hbits]
    obtain ⟨htw, hbody⟩ := List.append_inj htail hlenq
    have ht : t1 = t2 := htwInj t1 t2 hbits htw
    subst ht
    obtain ⟨hN, hb⟩ := List.append_inj' hbody (by simp)
    have hll : ℓ1 = ℓ2 := by have := congrArg List.length hN; simpa using this
    subst hll
    have hNe : N1 = N2 := List.ofFn_injective hN
    subst hNe
    have hbe : b1 = b2 := by simpa using hb
    subst hbe; rfl

/-- **ACCEPTANCE 3** — `specHashFamilyV : HashFamily F T L` for VARIABLE-length
tweaks: the aligned hash `POLYVAL u h (bin(2|T|+2) ‖ pad(T) ‖ M)` at the uniform
degree cap `d = L + τmax + 1` (`τmax` bounds the per-tweak `pad(T)` block count),
Properties 1–3 re-derived from the list-level lemmas and `specH_input_inj`.

SPEC DEVIATION (as for the fixed-`τ` `specHashFamily`): extra hypotheses required
by the literal POLYVAL shape — `htwPos : 1 ≤ (tweakEnc t).length` (so every block
list has length `≥ 2` and prop3's `+ X` misses the top; the analogue of `1 ≤ τ`,
degenerate at `pad(T) = M = ∅`) and `hlenV : bin(2|T|+2) ≠ 0` (so the top
coefficient is nonzero).  `d = L + τmax + 1`, NOT `L + τmax + 2`. -/
def specHashFamilyV (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (L τmax : ℕ)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (hτmax : ∀ t, (tweakEnc t).length ≤ τmax)
    (htwPos : ∀ t, 1 ≤ (tweakEnc t).length)
    (hlenV : ∀ t, specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (hlenV3 : ∀ t, specBin n hcard (2 * tweakBits t + 3) ≠ 0) : HashFamily F T L where
  hash h t m := POLYVAL u h (specBlockV n hcard tweakEnc tweakBits t m)
  d := L + τmax + 2
  prop1 t m hm g := by
    refine polyvalMassV_prop1 u _ (L + τmax + 2) ?_
      (specBlockV_pos n hcard tweakEnc tweakBits t m) ?_ g
    · rw [specBlockV_length]; unfold bitTailDegLen; have := hτmax t; split_ifs <;> omega
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t m (hlenV t) (hlenV3 t)
        (specBlockV_pos n hcard tweakEnc tweakBits t m)
  prop2 t1 m1 hm1 t2 m2 hm2 g hne := by
    refine polyvalMassV_prop2 u _ _ (L + τmax + 2) ?_ ?_
      (specBlockV_pos n hcard tweakEnc tweakBits t1 m1)
      (specBlockV_pos n hcard tweakEnc tweakBits t2 m2) ?_ ?_ ?_ g
    · rw [specBlockV_length]; unfold bitTailDegLen; have := hτmax t1; split_ifs <;> omega
    · rw [specBlockV_length]; unfold bitTailDegLen; have := hτmax t2; split_ifs <;> omega
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t1 m1 (hlenV t1) (hlenV3 t1)
        (specBlockV_pos n hcard tweakEnc tweakBits t1 m1)
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t2 m2 (hlenV t2) (hlenV3 t2)
        (specBlockV_pos n hcard tweakEnc tweakBits t2 m2)
    · intro hblk
      exact hne (specBlockV_sigma_inj n hcard tweakEnc tweakBits
        htwLen htwInj htwBits t1 t2 m1 m2 hblk)
  prop3 t m hm g := by
    refine polyvalMassV_prop3 u _ (L + τmax + 2) ?_
      (specBlockV_pos n hcard tweakEnc tweakBits t m) ?_ ?_ g
    · rw [specBlockV_length]; unfold bitTailDegLen; have := hτmax t; split_ifs <;> omega
    · rw [specBlockV_length]; unfold bitTailDegLen; have := htwPos t; split_ifs <;> omega
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t m (hlenV t) (hlenV3 t)
        (specBlockV_pos n hcard tweakEnc tweakBits t m)

@[simp]
theorem specHashFamilyV_d (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (L τmax : ℕ)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (hτmax : ∀ t, (tweakEnc t).length ≤ τmax)
    (htwPos : ∀ t, 1 ≤ (tweakEnc t).length)
    (hlenV : ∀ t, specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (hlenV3 : ∀ t, specBin n hcard (2 * tweakBits t + 3) ≠ 0) :
    (specHashFamilyV u n hcard L τmax tweakEnc tweakBits htwLen htwInj htwBits hτmax htwPos
      hlenV hlenV3).d = L + τmax + 2 := rfl

/-! ### PHASE P1b2.S2 — the sharp spec instance `specHashFamilyVS`

Upgrades `specHashFamilyV` to the per-`dˢ` bundle `HashFamilyS`
(`RandomSystems.CR18.HCTR2`; formerly `HCTR2Bit.HashFamilyLS`).  The
per-query degree bound is the *honest POLYVAL block-list length*

  `degB t k = (tweakEnc t).length + k`,  so
  `degB t mˢ = (tweakEnc t).length + mˢ = (specBlockV … t m).length = dˢ`

(`(tweakEnc t).length` tweak blocks plus the `mˢ` message-side blocks whose head
is the `bin(2|T|+2/3)` mode block) — exactly the per-query polynomial degree over
the structured tail, tweak-sensitive as the degB-shape decision requires.  The
sharp property proofs need NO refactor of
`polyvalMassV_prop1/2/3`: those lemmas are ALREADY parametric in the degree cap
`D` with `B.length ≤ D`, so the sharp bound is just `D := degB t k`
(`= B.length`, `le_of_eq`) and the honest `max` in prop2' is `D := max (…) (…)`.
The relaxed lemmas' statements are untouched; the uniform `HashFamily` fields
are inherited verbatim from `specHashFamilyV` (so every existing consumer of
`specHashFamilyV` is unaffected). -/
def specHashFamilyVS (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (L τmax : ℕ)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (hτmax : ∀ t, (tweakEnc t).length ≤ τmax)
    (htwPos : ∀ t, 1 ≤ (tweakEnc t).length)
    (hlenV : ∀ t, specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (hlenV3 : ∀ t, specBin n hcard (2 * tweakBits t + 3) ≠ 0) :
    HashFamilyS F T L where
  toHashFamily := specHashFamilyV u n hcard L τmax tweakEnc tweakBits htwLen htwInj htwBits
    hτmax htwPos hlenV hlenV3
  degB t k := (tweakEnc t).length + k
  degB_mono t := fun _ _ hab => Nat.add_le_add_left hab _
  degB_le t {k} hk := by
    show (tweakEnc t).length + k ≤ L + τmax + 2
    have := hτmax t; omega
  prop1' t m hm g := by
    refine polyvalMassV_prop1 u _ ((tweakEnc t).length + bitTailDegLen m) ?_
      (specBlockV_pos n hcard tweakEnc tweakBits t m) ?_ g
    · exact le_of_eq (specBlockV_length n hcard tweakEnc tweakBits t m)
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t m (hlenV t) (hlenV3 t)
        (specBlockV_pos n hcard tweakEnc tweakBits t m)
  prop2' t1 m1 hm1 t2 m2 hm2 g hne := by
    rw [← Nat.cast_max]
    refine polyvalMassV_prop2 u _ _
      (max ((tweakEnc t1).length + bitTailDegLen m1) ((tweakEnc t2).length + bitTailDegLen m2))
      ?_ ?_ (specBlockV_pos n hcard tweakEnc tweakBits t1 m1)
      (specBlockV_pos n hcard tweakEnc tweakBits t2 m2) ?_ ?_ ?_ g
    · exact (specBlockV_length n hcard tweakEnc tweakBits t1 m1).le.trans (le_max_left _ _)
    · exact (specBlockV_length n hcard tweakEnc tweakBits t2 m2).le.trans (le_max_right _ _)
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t1 m1 (hlenV t1) (hlenV3 t1)
        (specBlockV_pos n hcard tweakEnc tweakBits t1 m1)
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t2 m2 (hlenV t2) (hlenV3 t2)
        (specBlockV_pos n hcard tweakEnc tweakBits t2 m2)
    · intro hblk
      exact hne (specBlockV_sigma_inj n hcard tweakEnc tweakBits
        htwLen htwInj htwBits t1 t2 m1 m2 hblk)
  prop3' t m hm g := by
    refine polyvalMassV_prop3 u _ ((tweakEnc t).length + bitTailDegLen m) ?_
      (specBlockV_pos n hcard tweakEnc tweakBits t m) ?_ ?_ g
    · exact le_of_eq (specBlockV_length n hcard tweakEnc tweakBits t m)
    · rw [specBlockV_length]; unfold bitTailDegLen; have := htwPos t; split_ifs <;> omega
    · exact specBlockV_head_ne n hcard tweakEnc tweakBits t m (hlenV t) (hlenV3 t)
        (specBlockV_pos n hcard tweakEnc tweakBits t m)

@[simp]
theorem specHashFamilyVS_degB (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n) (L τmax : ℕ)
    (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (hτmax : ∀ t, (tweakEnc t).length ≤ τmax)
    (htwPos : ∀ t, 1 ≤ (tweakEnc t).length)
    (hlenV : ∀ t, specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (hlenV3 : ∀ t, specBin n hcard (2 * tweakBits t + 3) ≠ 0) (t : T) (k : ℕ) :
    (specHashFamilyVS u n hcard L τmax tweakEnc tweakBits htwLen htwInj htwBits hτmax htwPos
      hlenV hlenV3).degB t k = (tweakEnc t).length + k := rfl

/-- The sharp instance's underlying `HashFamily` is exactly `specHashFamilyV`
(the uniform bundle is inherited verbatim). -/
@[simp]
theorem specHashFamilyVS_toHashFamily (u : Fˣ) (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (L τmax : ℕ) (tweakEnc : T → List F) (tweakBits : T → ℕ)
    (htwLen : ∀ t, (tweakEnc t).length = (tweakBits t + n - 1) / n)
    (htwInj : ∀ t t', tweakBits t = tweakBits t' → tweakEnc t = tweakEnc t' → t = t')
    (htwBits : ∀ t, 2 * tweakBits t + 3 < 2 ^ n)
    (hτmax : ∀ t, (tweakEnc t).length ≤ τmax)
    (htwPos : ∀ t, 1 ≤ (tweakEnc t).length)
    (hlenV : ∀ t, specBin n hcard (2 * tweakBits t + 2) ≠ 0)
    (hlenV3 : ∀ t, specBin n hcard (2 * tweakBits t + 3) ≠ 0) :
    (specHashFamilyVS u n hcard L τmax tweakEnc tweakBits htwLen htwInj htwBits hτmax htwPos
      hlenV hlenV3).toHashFamily
      = specHashFamilyV u n hcard L τmax tweakEnc tweakBits htwLen htwInj htwBits hτmax htwPos
      hlenV hlenV3 := rfl

end PhaseD

end HCTR2Spec

/-! ## Part IV — the composed paper theorem over GF(2¹²⁸) -/

namespace HCTR2Paper

open RandomSystems.CR18
open RandomSystems.CR18.HCTR2
open RandomSystems.CR18.HTechniqueDerivation
open RandomSystems.HTechnique.HCTR2
open RandomSystems.HTechnique.HCTR2Spec
open RandomSystems.HTechnique.GF2Field
open scoped RandomSystems.CR18.PFunDDS

/-- Blockwise decidable equality on `GF128` (classical; the field carrier is
noncomputable anyway). -/
noncomputable instance : DecidableEq GF128 := Classical.decEq _

/-- `GF128` has characteristic 2, inherited from `ZMod 2` along the
injective algebra map. -/
instance : CharP GF128 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GF128).injective 2

/-- `specBin` sends `0` to `0`: the block↔bits bijection is additive, so it
preserves zero. -/
theorem specBin_zero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] (n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    specBin (F := F) n hcard 0 = 0 := by
  have h0 : (specBlockBits (F := F) n hcard).toBits 0 = 0 := by
    have h := (specBlockBits (F := F) n hcard).toBits_add 0 0
    simpa using h
  unfold specBin
  rw [show BitVec.ofNat n 0 = 0 from by simp, Equiv.symm_apply_eq, h0]

/-- The spec length/domain-separation block is nonzero at every positive
in-range index (`specBin` injective below `2ⁿ` + `specBin 0 = 0`). -/
theorem specBin_ne_zero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] (n : ℕ) (hcard : Fintype.card F = 2 ^ n) {k : ℕ}
    (hk0 : 0 < k) (hk : k < 2 ^ n) :
    specBin (F := F) n hcard k ≠ 0 := by
  intro h
  have h0 := specBin_inj (F := F) n hcard k 0 hk (by positivity)
    (h.trans (specBin_zero (F := F) n hcard).symm)
  omega

/-- The paper's `H` over `GF(2¹²⁸)`, σ-accounted: `specHashFamilyVS` at the RFC-8452
POLYVAL dot unit `u = x⁻¹²⁸`, fixed `τ`-block tweaks (`pad(T) = List.ofFn`,
`|T| = 128·τ` bits), tail cap `L + 2`.  The hash consumes the paper's **structured**
tail `BitTailS` (the `ℓ` full blocks and, only when unaligned, one `10*`-padded partial
block), so the honest per-query degree is `degB t mˢ = mˢ + ⌈|T|/n⌉ = dˢ` with
`degB t k = ⌈|T|/n⌉ + k` (the leading `bin(2|T|+2/3)` mode block is absorbed into `mˢ`'s
head). -/
def paperHashS (L τ : ℕ) (hτ : 1 ≤ τ) (hτcap : 2 * (τ * 128) + 3 < 2 ^ 128) :
    HashFamilyS GF128 (Fin τ → GF128) (L + 2) :=
  specHashFamilyVS uPolyval 128 gf128_card (L + 2) τ
    (fun t => List.ofFn t) (fun _ => τ * 128)
    (fun _ => by simp only [List.length_ofFn]; omega)
    (fun t t' _ he => List.ofFn_injective he)
    (fun _ => hτcap)
    (fun _ => by simp only [List.length_ofFn]; exact le_refl τ)
    (fun _ => by simp only [List.length_ofFn]; exact hτ)
    (fun _ => specBin_ne_zero 128 gf128_card (by omega)
      (Nat.lt_of_le_of_lt
        (by omega : 2 * (τ * 128) + 2 ≤ 2 * (τ * 128) + 3) hτcap))
    (fun _ => specBin_ne_zero 128 gf128_card (by omega) hτcap)

/-- **The HCTR2 paper theorem** (ePrint 2021/1441, p. 17), over the paper's own field,
hash, and message space: for every keyed permutation family `E : K → Perm GF(2¹²⁸)`
with uniform key, every tweak width `τ ≥ 1` blocks, message cap `L` blocks (message
space: all bit strings of `1 + ℓ` full blocks plus `r` leftover bits, `ℓ < L`,
`r < 128` — the paper's `⋃_{n ≤ ℓ ≤ ...} {0,1}^ℓ`), and `q ≥ 1` queries, with
`σ := q·(L + τ + 1)` (the paper's per-query `dˢ = mˢ + ⌈|Tˢ|/n⌉` cap),

    Δ(⌈q⌉ HCTR2[E], ⌈q⌉ ±p̃rp)
      ≤ Δ(⌈2 + q(L+1)⌉ ±E, ⌈2 + q(L+1)⌉ ±Perm)
        + (3σ² + 2qσ + q² + 7σ + 2) / 2¹²⁹ ,

the paper's display with the cipher term at the `≤ σ + 2` query budget and the
`C(q,2)` birthday merged as `q²`.  Unrestricted adversaries (the pointless-query WLOG
is internal); the two side conditions are the paper's standing in-range assumptions
(`L + 1 < 2¹²⁸` block indices, `2(128τ) + 3 < 2¹²⁸` tweak-length encoding — the `+3`
covers the unaligned length block of the injectivity argument).

σ is **paper-exact**: `σ = q·(L + τ + 1)`, the paper's cap of `dˢ = mˢ + ⌈|Tˢ|/n⌉`
(p. 9; `mˢ ≤ L + 1` over this message space, so `dˢ ≤ L + τ + 1`).  The green Fig-4/5
cells pay exactly `degB t mˢ = mˢ + ⌈|T|/n⌉ = dˢ` at EVERY query (both `r = 0` and
`r > 0`): the hash consumes the paper's **structured** tail `BitTailS` (`N` and, only
when unaligned, one `10*`-padded partial block), and injectivity is the paper's App.-A
mode block `bin(2|T|+2/3)` (`specBlockV_sigma_inj`), NOT an invented length block.
(Done 2026-07-11, replacing the earlier `bitLenBlock` encoding whose extra block gave
`degB = dˢ + 1` and the `q(L+τ+2)` display.  The per-query BUDGET `bitD = mˢ_fork + τ`
still uses the fork-free cipher count `mˢ_fork = ℓ + 2 ≥ 2` — the reveal always issues the
partial call, so `bit_count_core`'s `2 ≤ mˢ` structural minimum holds — but `bitD`'s cap
and its value at every `r > 0` query equal `dˢ`, and the σ headline is `q(L+τ+1)`.) -/
theorem hctr2_paper_theorem {K : Type} [Fintype K] [Nonempty K]
    (E : K → Equiv.Perm GF128) (L τ q : ℕ)
    (hq : 1 ≤ q) (hL : 0 < L) (hL2 : L + 1 < 2 ^ 128) (hτ : 1 ≤ τ)
    (hτcap : 2 * (τ * 128) + 3 < 2 ^ 128) :
    Δ(⌈q⌉ (hctr2BitE (specBlockBits 128 gf128_card) (specBinEnc 128 gf128_card L hL2)
        (paperHashS L τ hτ hτcap).toHashFamily E).val,
      ⌈q⌉ (TweakablePRP.tprp (MsgK := bitMsgL (F := GF128) (L := L) (n := 128))
        (T := Fin τ → GF128)).val)
      ≤ Δ(⌈2 + q * (L + 1)⌉ (bcE (F := GF128) E).val,
            ⌈2 + q * (L + 1)⌉ (bcPerm (F := GF128)).val) +
        (((3 * (q * (L + τ + 1)) ^ 2 + 2 * q * (q * (L + τ + 1)) + q ^ 2
            + 7 * (q * (L + τ + 1)) + 2 : ℕ) : NNReal)
          / ((2 ^ 129 : ℕ) : NNReal) : ℝ) := by
  classical
  have hdegB : ∀ (t' : Fin τ → GF128) (k : ℕ),
      (paperHashS L τ hτ hτcap).degB t' k ≤ k + τ := by
    intro t' k
    show (List.ofFn t').length + k ≤ k + τ
    simp only [List.length_ofFn]
    omega
  have hσB : ∀ t : TranscriptPrefix
      (QueryDir × (Fin τ → GF128) × Sigma (bitMsgL (F := GF128) (L := L) (n := 128)))
      (Sigma (bitMsgL (F := GF128) (L := L) (n := 128))) q,
      sigmaDBit (fun _ => τ) t ≤ q * (L + τ + 1) := by
    intro t
    have hbound : ∀ s : Fin q, bitD (fun _ => τ) t s ≤ L + τ + 1 := by
      intro s
      have hlt := (splitIdx (bitPlain t s).1).1.isLt
      simp only [bitD, mBlocksBit]
      omega
    calc sigmaDBit (fun _ => τ) t = ∑ s : Fin q, bitD (fun _ => τ) t s := rfl
      _ ≤ ∑ _s : Fin q, (L + τ + 1) := Finset.sum_le_sum (fun s _ => hbound s)
      _ = q * (L + τ + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h := hctr2Bit_security_computational_sigma
    (bb := specBlockBits 128 gf128_card) (be := specBinEnc 128 gf128_card L hL2)
    (Hfs := paperHashS L τ hτ hτcap) (twBlocks := fun _ => τ)
    (σB := q * (L + τ + 1)) E (by omega : 0 < L * 128) hq hdegB hσB
  rw [gf128_card] at h
  refine le_trans h (add_le_add le_rfl ?_)
  -- merge `C(q,2)/2¹²⁸ = q(q−1)/2¹²⁹ ≤ q²/2¹²⁹` into the numerator, in `ℝ`
  have harith : 2 * q.choose 2 ≤ q ^ 2 := by
    rw [two_mul_choose_two]
    calc q * (q - 1) ≤ q * q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
      _ = q ^ 2 := (sq q).symm
  have harithR : (2 : ℝ) * (q.choose 2 : ℝ) ≤ (q : ℝ) ^ 2 := by
    exact_mod_cast harith
  push_cast [HashThenPRF.choose2]
  rw [show (680564733841876926926749214863536422912 : ℝ)
      = 2 * 340282366920938463463374607431768211456 from by norm_num]
  rw [show (q.choose 2 : ℝ) / (340282366920938463463374607431768211456 : ℝ)
      = (2 * (q.choose 2 : ℝ)) / (2 * 340282366920938463463374607431768211456)
    from (mul_div_mul_left _ _ two_ne_zero).symm]
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  linarith [harithR]

end HCTR2Paper

end HTechnique
end RandomSystems
