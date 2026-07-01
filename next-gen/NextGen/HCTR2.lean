/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.PDS
import NextGen.SystemMBO
import NextGen.Distinguishing
import NextGen.Lemma415
import RandomSystems.DistSimp
-- NOTE: `NextGen.SwitchingLemma` (`pcoll`, `lemma_4_18`/`lemma_4_19`, the URP–URF
-- birthday term) is the intended source of the numeric within-query bound. This
-- scaffold currently keeps an explicit arithmetic RHS so the HCTR2 modeling layer
-- can be reviewed independently of that future application-specific import.

/-!
# HCTR2 forward construction scaffold

This file fixes the first paper-facing layer: the HCTR2 real world is a construction over an inner
permutation resource, and its game bit is a hidden, per-realization history MC. It is not yet the
final ±STPRP theorem: the carrier here is the forward wide-block oracle only, not the bidirectional
encryption/decryption interface.

The CBC-MAC proof in CR18 §6.2.3 is the right analogy only at the construction/MBO layer: a
converter over an inner resource, plus a monotone condition for non-trivial internal collisions.
The later HCTR2 security proof should be stated as its own construction/fixed-transcript bound, not
as a prematurely exported conditional-equivalence theorem.

Two modeling decisions (per the manager call):
* **Multi-block body.** The body is `N : Fin L → F` (L genuine blocks), so the
  keystream `V_j = N_j + P(S + cfg.ctr j)` has L blocks and the within-query
  distinctness term `~C(L,2)/|F|` (the σ² source) actually exists. (The earlier
  single-`F` body collapsed this away and is fixed here.)
* **Derived XCTR.** The keystream is `P` evaluated at counters `S + cfg.ctr j`, NOT
  an abstract parameter. Counter injectivity is a predicate on `cfg`, used by future
  bounds rather than assumed by the construction itself.
* **Forward behavioral, filtered advantage.** `Δ` is `maxAdvantage` (the sup over
  distinguishers, CR18 §4.10.2) between the two systems each restricted by the CR18
  query **filter** `[q]` (Def 3.10, `PFunPDS.filterQueries`). No operational `D`,
  no `QueriesExactly`/`isProbDist` hypotheses — the budget is a filter on the system.
-/

noncomputable section

open RandomSystems (Dist)
open scoped Classical

namespace RandomSystems.CR18
namespace HCTR2

universe u

variable {F : Type u} [Field F] [Fintype F]

/-! ## 1. Inner resource — two-sided uniform random permutation (REUSED). -/

/-- CR18 Def 3.15 inner resource: the two-sided uniform random permutation over `F`. -/
abbrev innerURP (F : Type u) [Fintype F] : PFunPDS F F :=
  PFunPDS.URP F

/-! ## 2. Carriers and the keyed δ-AXU hash.

A wide-block query is `(T, M, N)` — tweak `T : F`, head block `M : F` (`|M| = n`),
and body `N : Fin L → F` (the `L` body blocks). A wide-block output is `(U, V)` with
`U : F` and `V : Fin L → F`. The ideal `π̃` is a per-tweak permutation of the
length-preserving body `(M, N) ↦ (U, V)`, carrier `WideBody`. -/

abbrev WideIn (F : Type u) (L : ℕ) : Type u := F × F × (Fin L → F)
abbrev WideOut (F : Type u) (L : ℕ) : Type u := F × (Fin L → F)
abbrev WideBody (F : Type u) (L : ℕ) : Type u := F × (Fin L → F)

/-- The keyed hash `H_{h̄}(T, ·)` over a body block-vector: `key → tweak → blocks → F`
(CR18 §6.2 / `CR18/AUH`; concrete POLYVAL in `hctr2-verification/.../Polyval.lean`). -/
abbrev Hash (F : Type u) (L : ℕ) : Type u := F → F → (Fin L → F) → F

/-- CR18 §6.2.6 δ-AXU (count form, field subtraction = XOR over `GF(2ⁿ)`): for
distinct bodies `N ≠ N'`, at most `bound` keys realize any fixed offset of the hash
difference. The ONLY property of `H` the cross/head terms consume (mirrors
`CR18/AUH.EpsAXU`). NOT needed for the within-query leading term. -/
def IsAXU {L : ℕ} (H : Hash F L) (bound : ℕ) : Prop :=
  ∀ (T c : F) (N N' : Fin L → F), N ≠ N' →
    (Finset.univ.filter (fun h : F => H h T N - H h T N' = c)).card ≤ bound

/-! ## 3. Construction parameters.

The two setup inputs and the XCTR counter encoding are construction parameters, not hidden
constants. Their separation/injectivity requirements belong to the later security theorem boundary,
so the denotation below takes only the raw parameters while exposing a tight validity predicate. -/

/-- Public HCTR2 construction parameters: setup inputs for `P(hbar)`/`P(Lm)`, and the XCTR counter
encoding. -/
structure Params (F : Type u) (L : ℕ) where
  bin0 : F
  bin1 : F
  ctr : Fin L → F

/-- Minimal static well-formedness for the forward scaffold: the two setup sites are distinct and
the counter encoding is injective. Collisions between shifted stream points `S + ctr j` and setup
points are dynamic bad events, not static assumptions. -/
def Params.Valid {L : ℕ} (cfg : Params F L) : Prop :=
  cfg.bin0 ≠ cfg.bin1 ∧ Function.Injective cfg.ctr

/-! ## 4. HCTR2 construction — the wide-block map as a function of `(H, cfg, P)`.

`cfg.ctr : Fin L → F` is the XCTR counter encoding `bin(j)` (the construction's fixed
counter map; distinctness of `S + cfg.ctr j` is exactly its injectivity). The map is a
pure function of the inner permutation `P` (a DDS realization, total on wide-block
inputs), pushed through `Dist.fTransform` — the CBC `cbcMacPDS` shape. -/

/-- HCTR2 wide-block map (ePrint 2021/1441 §2): `(T,M,N) ↦ (U,V)` under inner
permutation `P`, with XCTR **derived** as `V_j = N_j + P(S + cfg.ctr j)`. -/
def hctr2Fun {L : ℕ} (H : Hash F L) (cfg : Params F L) (P : F → F)
    (inp : WideIn F L) : WideOut F L :=
  let T := inp.1
  let M := inp.2.1
  let N := inp.2.2
  let hbar := P cfg.bin0
  let Lm := P cfg.bin1
  let MM := M + H hbar T N
  let UU := P MM
  let S := MM + UU + Lm
  let V := fun j : Fin L => N j + P (S + cfg.ctr j)   -- derived XCTR keystream
  let U := UU + H hbar T V
  (U, V)

/-- The real world `hctr2[P]`: the construction applied to the inner URP, realized as
the pushforward of the uniform-permutation distribution through the per-permutation
wide-block evaluator (CBC `cbcMacPDS` shape). -/
def hctr2Real {L : ℕ} (H : Hash F L) (cfg : Params F L) :
    PFunPDS (WideIn F L) (WideOut F L) :=
  Dist.fTransform
    (fun σ : Equiv.Perm F => PFunDDS.functionEvaluator (hctr2Fun H cfg σ.toFun))
    (Dist.uniform (Equiv.Perm F))

/-! ## 5. Ideal `π̃` — the tweakable length-preserving permutation.

UPSTREAM-CANDIDATE: no `tweak` primitive exists in random-systems; the lightest
faithful ideal is a per-tweak **independent** uniform permutation of the body
`WideBody = F × (Fin L → F)`. -/

-- UPSTREAM-CANDIDATE: tweakable length-preserving permutation = per-tweak independent
-- uniform random permutation family. Candidate to upstream as a generic `tweakableURP`.
/-- Ideal `π̃`: for each tweak `T`, an independent uniform permutation of the body
`(M, N) ↦ (U, V)`. Pushforward of an i.i.d. tweak-indexed permutation family. -/
def tweakablePerm {L : ℕ} :
    PFunPDS (WideIn F L) (WideOut F L) :=
  Dist.fTransform
    (fun fam : F → Equiv.Perm (WideBody F L) =>
      PFunDDS.functionEvaluator
        (fun inp : WideIn F L => (fam inp.1).toFun (inp.2.1, inp.2.2)))
    (Dist.fTransform
      (fun v : Fin (Fintype.card F) → Equiv.Perm (WideBody F L) =>
        fun T : F => v (Fintype.equivFin F T))
      (Dist.iidPow (Dist.uniform (Equiv.Perm (WideBody F L))) (Fintype.card F)))

/-! ## 6. MBO `Â` — no non-trivial inner input collision (CBC `noInternalCollision`).

The inner `P`-inputs HCTR2 feeds per wide-block query are `D = [bin0, bin1, MM] ++
[S + cfg.ctr j | j]`. By `P` injective, an output collision `R = P(D)` is an input
collision. As in CR18's CBC proof, the condition must be **non-trivial**: repeated uses of the same
logical site are not bad. The two fixed setup calls `P(cfg.bin0)` and `P(cfg.bin1)` are intentionally reused
across all outer queries, and repeated identical outer queries also reuse the same logical internal
sites. The MBO fires only when two distinct logical sites ask the inner permutation at the same
field point. -/

/-- A logical inner-permutation call site of the HCTR2 construction.

The fixed setup calls are global sites. The `head` and `stream` calls are indexed by the public
wide-block input they belong to, so repeating the same public query repeats the same logical sites
and is not a non-trivial collision. -/
inductive InnerSite (F : Type u) (L : ℕ) : Type u where
  | hbar
  | lm
  | head (inp : WideIn F L)
  | stream (inp : WideIn F L) (j : Fin L)

/-- The tagged inner `P`-input trace
`[(hbar, cfg.bin0), (lm, cfg.bin1), (head inp, MM), (stream inp j, S + cfg.ctr j) …]` for one
wide-block query under `P`. The within-query keystream segment is pairwise distinct iff `cfg.ctr` is
injective, but the bad event below is stricter: it compares the field points reached by distinct
logical sites. -/
def innerTrace {L : ℕ} (H : Hash F L) (cfg : Params F L) (P : F → F)
    (inp : WideIn F L) : List (InnerSite F L × F) :=
  let T := inp.1; let M := inp.2.1; let N := inp.2.2
  let hbar := P cfg.bin0
  let MM := M + H hbar T N
  let UU := P MM
  let S := MM + UU + P cfg.bin1
  [(InnerSite.hbar, cfg.bin0), (InnerSite.lm, cfg.bin1), (InnerSite.head inp, MM)] ++
    (List.finRange L).map (fun j => (InnerSite.stream inp j, S + cfg.ctr j))

/-- Untagged inner inputs, kept as a projection for counting lemmas that only care about the
queried field points. -/
def innerInputs {L : ℕ} (H : Hash F L) (cfg : Params F L) (P : F → F)
    (inp : WideIn F L) : List F :=
  (innerTrace H cfg P inp).map Prod.snd

/-- A non-trivial inner collision: two distinct logical sites reached the same field point. -/
def HasNontrivialInnerCollision {L : ℕ} (trace : List (InnerSite F L × F)) : Prop :=
  ∃ a ∈ trace, ∃ b ∈ trace, a.1 ≠ b.1 ∧ a.2 = b.2

/-- HCTR2 no-inner-collision MBO = Maurer's monotone MBO on the game-enhanced system
(CR18 Def 3.22, reused via the carrier-level `MonotoneMBO`). -/
abbrev NoInnerCollisionMBO {L : ℕ}
    (Shat : PFunPDS (WideIn F L) (WideOut F L × Bool)) : Prop :=
  MonotoneMBO Shat

/-- The monotone "a non-trivial inner-`P` collision has occurred" bit for the query history `l`
under permutation `P`: two distinct logical inner-call sites in the pooled trace hit the same field
point. Monotone in `l` (a witness never disappears). -/
def innerCollided {L : ℕ} (H : Hash F L) (cfg : Params F L) (P : F → F)
    (l : List (WideIn F L)) : Bool := by
  classical
  exact if HasNontrivialInnerCollision (l.flatMap (innerTrace H cfg P)) then true else false

/-- **Game-enhanced HCTR2 real world `Ŝ`**, CONSTRUCTED from the base real world
`hctr2Real` and the no-inner-collision condition — NOT a free parameter. Per
permutation `σ`, the history evaluator emits `(hctr2Fun … σ (last query), collided σ
history)`; pushed through the uniform-permutation distribution. `stripMBO` of this
is `hctr2Real`, and its MBO is monotone — both provable, not assumed.

This is deliberately a per-realization history MC (`A_σ : X* → {0,1}`), not a
`gameOf hctr2Real cond` over the public input/output transcript: the bad event depends on internal
permutation inputs that are not necessarily recoverable from public HCTR2 outputs. -/
def hctr2Hat {L : ℕ} (H : Hash F L) (cfg : Params F L) :
    PFunPDS (WideIn F L) (WideOut F L × Bool) :=
  Dist.fTransform
    (fun σ : Equiv.Perm F =>
      PFunDDS.historyEvaluator (fun l hne =>
        (hctr2Fun H cfg σ.toFun (l.getLast hne),
         innerCollided H cfg σ.toFun l)))
    (Dist.uniform (Equiv.Perm F))

/-- The HCTR2 inner-collision bit is monotone in the query history. -/
theorem innerCollided_monotone {F : Type u} [Field F] {L : ℕ}
    (H : Hash F L) (cfg : Params F L) (P : F → F)
    {l₁ l₂ : List (WideIn F L)} (hpre : l₁ <+: l₂) :
    innerCollided H cfg P l₁ ≤ innerCollided H cfg P l₂ := by
  classical
  by_cases h₁ : HasNontrivialInnerCollision (l₁.flatMap (innerTrace H cfg P))
  · have h₂ : HasNontrivialInnerCollision (l₂.flatMap (innerTrace H cfg P)) := by
      obtain ⟨a, ha, b, hb, hsite, hval⟩ := h₁
      have hpreTrace : l₁.flatMap (innerTrace H cfg P) <+: l₂.flatMap (innerTrace H cfg P) :=
        hpre.flatMap (innerTrace H cfg P)
      exact ⟨a, hpreTrace.subset ha, b, hpreTrace.subset hb, hsite, hval⟩
    simp [innerCollided, h₁, h₂]
  · simp [innerCollided, h₁]

/-- HCTR2's constructed MBO strips back to the real HCTR2 system. -/
theorem hctr2Hat_stripMBO {L : ℕ} (H : Hash F L) (cfg : Params F L) :
    PFunPDS.stripMBO (hctr2Hat H cfg) = hctr2Real H cfg := by
  unfold PFunPDS.stripMBO hctr2Hat hctr2Real
  simp only [dist_simp]
  rw [show (PFunDDS.stripMBO ∘ fun σ : Equiv.Perm F =>
      PFunDDS.historyEvaluator (fun l hne =>
        (hctr2Fun H cfg σ.toFun (l.getLast hne), innerCollided H cfg σ.toFun l))) =
      (fun σ : Equiv.Perm F => PFunDDS.functionEvaluator (hctr2Fun H cfg σ.toFun)) from by
    funext σ
    rfl]

/-- HCTR2's constructed bad-event bit is a monotone MBO. -/
theorem hctr2Hat_monotoneMBO {L : ℕ} (H : Hash F L) (cfg : Params F L) :
    MonotoneMBO (hctr2Hat H cfg) := by
  intro s hs
  obtain ⟨σ, _hσ, rfl⟩ := mem_support_fTransform _ _ hs
  exact PFunDDS.historyEvaluator_pair_isGame_of_monotone
    (fun l hne => hctr2Fun H cfg σ.toFun (l.getLast hne))
    (fun l => innerCollided H cfg σ.toFun l)
    (fun hpre => innerCollided_monotone H cfg σ.toFun hpre)

/-! ## 7. Advantage `Δ` — behavioral sup, budget as a CR18 filter.

`Δ([q]·hctr2[P], [q]·π̃)` = `maxAdvantage` (CR18 §4.10.2 sup over distinguishers)
between the two systems each restricted by the query filter `[q]` (Def 3.10,
`PFunPDS.filterQueries`). No operational distinguisher, no query/prob hypotheses. -/

/-- CR18 §4.10.2 forward-oracle advantage of the HCTR2 construction at query budget `q`: the
behavioral distinguishing advantage between `[q]·hctr2[P]` and the forward view of `[q]·π̃`.
This is not the bidirectional ±STPRP interface. -/
abbrev hctr2ForwardAdvantage {L : ℕ} (H : Hash F L) (cfg : Params F L) (q : ℕ) : ℝ :=
  maxAdvantage
    (PFunPDS.filterQueries q (hctr2Real H cfg))
    (PFunPDS.filterQueries q (tweakablePerm (F := F) (L := L)))

/-! ## 8. Next proof obligations (not exported yet).

The previous scaffold exported two unproved placeholder theorems:

* `hctr2_condEquiv : hctr2Hat H cfg |≡ tweakablePerm`
* `hctr2_stprp_withinquery_bound`

That was too strong as a modeling claim. HCTR2 should first get a construction/fixed-transcript
statement explaining which real transcripts have the same density as the ideal tweakable
permutation, and which transcript classes are paid for by the non-trivial internal-collision MC
above plus the AXU/head terms. For the full bidirectional STPRP proof, the forward carrier here must
also be replaced by a direction-indexed interface and a row-marked/score bad-event family; this single
hidden MC is only local instrumentation.

The construction layer above is the checked API for that future proof:

* `hctr2Real` is the direct denotation of the construction applied to the inner URP.
* `hctr2Hat` is the hidden per-realization MC version of that construction.
* `hctr2Hat_stripMBO` and `hctr2Hat_monotoneMBO` are proved standing facts.
-/

end HCTR2
end RandomSystems.CR18
