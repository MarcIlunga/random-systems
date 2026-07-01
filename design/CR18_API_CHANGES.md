# CR18 API changes — migration note for hctr2-verification

**Audience**: the downstream `hctr2-verification` session, which `require`s
`random-systems` by path and is currently pinned at commit `0b43428`
(`/tmp/rs-pin-0b43428`, see its `lakefile.lean` comment). **This file is the
agreed migration marker**: it exists, so revert the pin to
`require RandomSystems from "../random-systems"` (and update
`lake-manifest.json`'s `dir` back to `"../random-systems"`), then migrate per
the sections below.

* Covered range: `0b43428..HEAD` of branch `cr18-formalization`.
* Toolchain: unchanged (`leanprover/lean4:v4.29.0` on both sides).
* Scope of changes: ONLY `RandomSystems/CR18/*` and the `RandomSystems/CR18.lean`
  aggregator changed. The non-CR18 library (`RandomSystems/Dist.lean`,
  `FundamentalTheorem.lean`, `Coupling.lean`, `Applications/*`, …) is untouched.
* Every theorem named below is proven (no `sorry`) and axiom-checked:
  `[propext, Classical.choice, Quot.sound]` only.

---

## 1. Signature changes (old hypothesis list vs new)

The headline change of this endgame: **the Lemma 4.16 cancellation is now a
library proof, so every `hBridge`-style content-assuming hypothesis is GONE**,
and with it the abstract `ds`/`gs`/`phi_D`/`phi_G`/`iota` packaging that
existed only to carry it. The fundamental-lemma theorems are now stated at the
CONCRETE CR18 §4.10.2 structures `Lem416.distinctionStructure X Y q` /
`Lem416.gameStructure X Y q` (`Indist.lean`).

Common to all new statements: probability side conditions are the
`Fintype`-free raw Finsupp masses `S.sum (fun _ p => p) = 1` (equivalent to
`isProbDist` via `Dist.weight_eq_finsupp_sum`), and Δ is the `sSup` of the
signed `performance` over the **weight-1** distinguisher class (the old `⨆`
over ALL `Dist`-distinguishers was meaningless and is gone).

### 1.1 `Lem416.advantage_le_maxWinProb` (and `_pdg`)

* **Old** (pin): abstract `(ds : DistinctionStructure) (gs : GameStructure)
  [Fintype gs.Winner] [Fintype gs.Game] (φ_D) (φ_G)` + caller-supplied
  `hBridge : ∀ S T D, performance ≤ winProb` (plus `hWinMax`; the `_pdg`
  variant added `ι` and `hBridge : GameEquiv S T → …`). Hollow: the entire
  Lemma 4.16 content was the caller's.
* **New** (`Indist.lean:1336`, `:1353`):
  ```
  theorem advantage_le_maxWinProb (q : ℕ) (S T : PDG X Y)
      (heq : Def416.GameEquiv S T)
      (hS : S.sum (fun _ p => p) = 1) (hT : T.sum (fun _ p => p) = 1)
      (D : (distinctionStructure X Y q).ProbDistinguisher)
      (hD : D.isProbDist) :
      (distinctionStructure X Y q).performance (PDG.strip S, PDG.strip T) D ≤
        (Def417.maxWinProb (gameStructure X Y q) S : Real)
  ```
  Hypotheses are exactly Maurer's: game equivalence + weight-1 conditions.
  `advantage_le_maxWinProb_pdg` is the same statement under the historical name.

### 1.2 `Thm417.advantage_le_maxWinProb` / `Thm417.delta_le_gamma` / `Thm417.fundamental`

* **Old** (pin): abstract `ds/gs/phi_D/phi_G/iota` + `hShat : (phi_G Shat).isProbDist`
  + blanket `hD : ∀ D, (phi_D D).isProbDist` (unsatisfiable for the full `Dist`
  type — the reason your PO-3a went per-D) + per-distinguisher
  `hBridge : ∀ D, (Shat ≡_g That) → performance ≤ winProb`; conclusion a `⨆`
  over ALL distinguishers.
* **New** (`Indist.lean:2571`, `:2603`, `:2636`):
  ```
  theorem fundamental (q : ℕ)
      (Shat : PDG X Y) (T : PDS X Y)
      (hCondEquiv : Shat |≡ T)
      (That : PDG X Y)
      (hGameEquiv : Shat ≡_g That)
      (hStrip : PDG.strip That = T)
      (hShat : Shat.sum (fun _ p => p) = 1)
      (hThat : That.sum (fun _ p => p) = 1) :
      sSup ((fun D : (Lem416.distinctionStructure X Y q).ProbDistinguisher =>
          (Lem416.distinctionStructure X Y q).performance (PDG.strip Shat, T) D) ''
        {D | D.isProbDist}) ≤
        (Def417.maxWinProb (Lem416.gameStructure X Y q) Shat : Real)
  ```
  (`delta_le_gamma` is the same statement; `fundamental` is its headline alias;
  `advantage_le_maxWinProb` is the per-distinguisher form with explicit
  `(D) (hD : D.isProbDist)`.) **No `hBridge`, no `hD` blanket, no
  `phi_D/phi_G/iota`.** Remaining caller obligations are only the eq-4.39
  construction (`That`/`hGameEquiv`/`hStrip` — separate CR18 content, NOT
  Lemma 4.16) and the weight-1 masses.

### 1.3 `Def420.blindGame_maxWinProb_le`

* **Old** (pin): abstract `gs_orig/gs_blind/φ_orig/φ_blind` + `hne`
  (nonemptiness of the blind winner image) + `hBridge : ∀ W_b, W_b.isProbDist →
  winProb W_b (blind) ≤ maxWinProb (orig)` — i.e. the entire Γ(bS) ≤ Γ(S)
  content was assumed.
* **New** (`Indist.lean:2905`):
  ```
  theorem blindGame_maxWinProb_le (q : ℕ) [DecidableEq (DDG X PUnit)]
      (S : PDG X Y) (hS : S.sum (fun _ p => p) = 1) :
      Def417.maxWinProb (gameStructure X PUnit q) (blindGame S) ≤
        Def417.maxWinProb (gameStructure X Y q) S
  ```
  Both `hne` and `hBridge` are discharged internally (`win_blindDDG_iff` +
  `winProb_blindPDG`: the unblinded reading of a blind winner wins `S` with the
  same probability).

### 1.4 `Lem419.urp_urf_switching` — MOVED and made real

* **Old** (pin, `Indist.lean`): the hollow
  ```
  theorem urp_urf_switching (n q : ℕ) (delta : NNReal)
      (hBridge : delta ≤ pcoll (2 ^ n) q) :
      delta ≤ (q : NNReal) ^ 2 / (2 * (2 : NNReal) ^ n)
  ```
  — `delta` was an abstract number tied to URF/URP only through `hBridge`.
  **DELETED from `Indist.lean`.**
* **New** (`SwitchingPort.lean:923`, same full name
  `RandomSystems.CR18.Lem419.urp_urf_switching`):
  ```
  theorem urp_urf_switching (n q : ℕ)
      (Adm : DDE (Fin (2 ^ n)) (Fin (2 ^ n)) → Prop) :
      AdvWith (SwitchingPort.ddeDS (Fin (2 ^ n)) (Fin (2 ^ n)) q Adm)
          (id : …) (Ex35.R n n) (Ex35.P n)
        ≤ (q ^ 2 : ℝ) / (2 * 2 ^ n)
  ```
  The REAL CR18 Lemma 4.19 about the actual Example 3.5 bitstring systems, for
  ANY admissibility predicate `Adm`, via the ported transcript-factorization
  proof (your `GAP2_switching`). The numerical `pcoll` chain (`pcoll`,
  `pcoll_eq`, `pcoll_le_sq_div_two`, `pcoll_bound`) remains in `Indist.lean`
  unchanged.

### 1.5 `Def417.winProb_le_maxWinProb` and `winProb_le_one` (Game.lean) — the one you actually call

Your `PO3a_fundamental` calls `Def417.winProb_le_maxWinProb` directly. Its
signature changed:

* **Old** (pin): `[Fintype gs.Winner] [Fintype gs.Game] (G : gs.ProbGame)
  (hG : G.isProbDist) (W) (hW : W.isProbDist)`.
* **New** (`Game.lean:2237`): **`[Fintype gs.Game]` DROPPED**; game-side
  hypothesis is now the raw mass
  ```
  theorem winProb_le_maxWinProb (gs : GameStructure) [Fintype gs.Winner]
      (G : gs.ProbGame) (hG : G.sum (fun _ p => p) = 1)
      (W : gs.ProbWinner) (hW : W.isProbDist) :
      gs.winProb W G ≤ maxWinProb gs G
  ```
  (Your in-file comment "pin 0b43428 API: raw `Finsupp.sum … = 1` form" already
  anticipates exactly this NEW form — the conversion code you wrote for `hG'`
  is what the new API wants.)
* `winProb_le_one` similarly lost BOTH `Fintype` instances and takes both
  hypotheses as raw masses. `maxWinProb`, `maxWinProb_le_of_forall_le`,
  `maxWinProb_nonneg` are unchanged; `maxWinProb_le_one` / `maxWinProb_mono`
  kept their signatures (internal proofs adapted).

No other declaration your tree references
(`Def417.maxWinProb`, `Def45.GameStructure`, `Def47.DistinctionStructure`,
`Def415.preWinningDDS/preWinningPDS`, `Def416.GameEquiv`, `Def419.PDG.CondEquiv`,
`PDG.strip`, `jointProb`, `jointOutputDist`, `condSlice`, `behavior`,
`Def49.independentCopies(_apply)`, `DDS.*`, `DDE.*`, `DDC`,
`RandomFunction.*`, `RandomPermutation.URP`, `Filter`, the whole `Dist` API)
changed signature.

---

## 2. What replaced `hBridge` — the proven cancellation

The Lemma 4.16 content (CR18 eqs. 4.35–4.37: pre-winning-event cancellation,
strip partition, `Aq=1` bound, Lemma 4.15 transfer) is now the proven library
chain in `Indist.lean`:

* `Lem416.acceptNotWonProb_congr_gameEquiv` — game equivalence forces equal
  "accept ∧ not-yet-won" masses (the eqs-4.35/4.36 cancellation; built on the
  K1/K2 `preWinTranscriptDist` factorization + gameEquiv invariance),
* `Lem416.acceptProb_det_strip` — the stripped acceptance partition,
* `Lem416.acceptWonProb_le_winProb_det` — the `Aq=1` part is bounded by the
  winning probability,
* `Lem416.winProb_congr_gameEquiv` — Lemma 4.15 transfer,

assembled into `Lem416.advantage_le_winProb` and capped by
`Def417.winProb_le_maxWinProb`. For Def 4.20 the bridge content is
`Def420.win_blindDDG_iff` + `Def420.winProb_blindPDG`; for Lemma 4.19 it is
the ported `SwitchingPort.advWith_urf_urp_le_birthday`.

**Also new, and strictly stronger than what `hBridge` bought you** (all in
`Indist.lean` unless noted):

* **Def 4.19′ one-sided domination route** (`Def419'` / `Thm417'`):
  `PDG.CondDominates` (`S |⊑ T` — pointwise `jointProb (preWinningPDS S) ≤
  jointProb T`), `condDominates_of_gameEquiv`, `condDominates_of_condEquiv`,
  and the one-sided fundamental lemma
  ```
  Thm417'.delta_le_gamma (q) (S : PDG X Y) (T : PDS X Y)
      (hdomi : S |⊑ T) (hS : …= 1) (hT : …= 1) : Δ(S⁻, T) ≤ Γ(S)
  ```
  with per-distinguisher (`advantage_le_maxWinProb`) and reversed-direction
  (`delta_rev_le_gamma`) forms — **no enhanced game, no game-equivalence, no
  strip hypothesis**. This is the H-coefficient-shaped primitive.
* **Maurer's full `Γ(bŜ)` strength**: `Thm417.delta_le_blind_gamma` (via
  `Def421.enhancePDG` + the blinding analysis) and its corollary
  `delta_le_gamma_of_blind`.
* New public `Game.lean` lemmas: `mem_preWinningDDS_dom_iff`,
  `preWinningDDS_dom_subset`, `preWinningDDS_respond` (reason about
  `preWinningDDS` without private unfolds).
* `CR18/DDS.lean`: `interfaceAlphabet`, `interfaceAlphabet_disjoint`,
  `iUnion_interfaceAlphabet` (interface-partition notation).

---

## 3. What this means for PO-3e / PO-3f / PO-3g

* **PO-3f (the load-bearing `hBridge`)**: its bridge content is now
  **library-side**. The one-sided H-coefficient argument you rewired into
  `PO3f_bridge` after bug #12 (dominance ⇒ per-distinguisher performance ≤
  winProb, per deterministic `d` then weighted) is exactly the proven
  `Thm417'.advantage_le_winProb` / `advantage_le_maxWinProb`, consuming
  `hdomi : S |⊑ T` — the `Dist`-level form of your `PO3c_dominance`. Two
  options:
  1. **Re-target** PO-3a at the library route: discharge
     `badGame |⊑ hctr2OnURP` from `PO3c_dominance` (cross-multiplied count
     form → `jointProb` inequality) and conclude with
     `Thm417'.delta_le_gamma`. Note the library's concrete theorems are
     stated at `Lem416.distinctionStructure/gameStructure` (the §4.10.2
     strategy class); your `Δm/Γm` live at `msgDS/msgGS` (DDE-environment
     class), so this route needs your `phiD/phiG` transport — the F5 mapping
     you already built.
  2. **Keep** your `msgDS`-level `PO3f_bridge` proof as-is (it is proven and
     self-contained); then the ONLY breaking change in your CR18 consumption
     is the `Def417.winProb_le_maxWinProb` signature (§1.5), which your PO-3a
     code already matches (raw-mass `hG'`, and you can drop any
     `Fintype (msgGS …).Game` instance kept only for it).
* **PO-3e (`strip badGameOnURP = hctr2OnURP`)**: unchanged in role. On the
  equality route it feeds `hStrip`; on the domination route it is still what
  rewrites the visible pair inside `Δm` (and is consumed by
  `condDominates_of_gameEquiv` if you derive `|⊑` from a game equivalence
  rather than directly from `PO3c_dominance`).
* **PO-3g (probability side conditions)**: the blanket
  `hD : ∀ D, (phi_D D).isProbDist` of the old `fundamental` is gone — the new
  statements quantify over the weight-1 class only (matching your REVIEW FIX).
  Game-side conditions are now raw masses `…sum (fun _ p => p) = 1`; your
  `PO3g_probDist` content (pushforwards preserve mass) still discharges them
  after `Dist.weight_eq_finsupp_sum` conversion, exactly as your PO-3a
  already does.

`Thm417.fundamental`'s `hCondEquiv`/`hGameEquiv` premises (which you retired
with PO-3d after bug #12) are NOT needed on the domination route:
`Thm417'.delta_le_gamma` takes only `hdomi` + the two masses. The
machine-checked boundary witnesses justifying exactly this design (the bug #11
`hCross` impossibility and the bug #12 per-class-equal/aggregate-different
refutation) are preserved upstream in `RandomSystems/CR18/Counterexamples.lean`.

---

## 4. Modules ported in this run (delete your local copies, import these)

All landed sorry-free with provenance headers; aggregated in
`RandomSystems.CR18` except where noted.

| Library module (`RandomSystems/CR18/`) | hctr2 origin | Main names |
|---|---|---|
| `DistProd.lean` | `HCTR2/Proofs/CR18/Sketch.lean:392-422` (GAP-7) | `Dist.pi`, `Dist.pi_apply`, `Def49.pi_const_eq_independentCopies` (constant-family bridge to the library's `independentCopies`) |
| `AdvMetric.lean` | `Sketch.lean:4390-4566` (§1.3 `AdvWith` + GAP-5 + GAP-6) | `AdvWith` (THE shared advantage, generic in the system carrier), `Def47.DistinctionStructure.ComplementClosed`, `advWith_symm` (GAP-5, needs complement-closure + equal masses), `advWith_triangle` (GAP-6), keystone connectors `advWith_eq_keystone`, `advWith_le_gamma` |
| `Monotonicity.lean` | `Sketch.lean:3255-3326` | `applyPDS`, `ConverterCompat` (mass clause load-bearing — disproof-repaired), `converter_monotone` (cross-structure `Δ_U(αS, αT) ≤ Δ_X(S, T)`, needs `Nonempty dsU.D`) |
| `SwitchingPort.lean` | `Sketch.lean:3328-3966` (`GAP2_switching`) + `HCTR2/Proofs/Concrete/Switching.lean:144-181` + h-technique `CountingLemmas.lean:31-127` (inlined) | `SwitchingPort.ddeDS`, `falling_factorial_lower_bound`, `birthday_bound`, `factorial_ratio_eq_descFactorial_inv`, `switching_ratio_le`, `advWith_urf_urp_le_birthday` (generic alphabet + `Adm` — your GAP-2), `Lem419.urp_urf_switching` |
| `AUH.lean` | `HCTR2/Proofs/Concrete/AXU.lean:35-114` + `PolyHash.lean:31-77,217-308` (inlined) | `EpsAXU`, `EpsAXU.no_const_gap`, `no_structural_collision_of_epsAXU`, `structural_collision_eq_of_epsAXU`, `polyHash`/`polyvalHash`, `polyval_isEpsAXU`, `card_polyval_point_collision_le`. NOT ported: `hashKeyedPDS` (stays yours — depends on your `PDS.ofStatelessOracleDist`) |
| `Counterexamples.lean` | `Sketch.lean` bug #11/#12 registry (~4588-4630 at the pin era) + `TRANSCRIPT_AUGMENTATION.md` §4 + the deleted `Pin9Check.lean` / commit `102296a` content, re-derived at minimal instances | `descFactorial_lt_pow`, `hCross_count_impossible`, `hCross_minimal_instance` (URF/URP over `Fin 2`, `1/4 ≠ 1/2`), `jointProb_URF`/`jointProb_URP` (reusable fiber-count closed forms), `perClass_exact_equality`, `aggregate_exact_equality_fails`, `dominance_holds`, `condEquiv_exact_fails` (the `N = 3` scaled GF(8) witness). **NOT in the `RandomSystems.CR18` aggregator** — `import RandomSystems.CR18.Counterexamples` on demand |

### Mechanical migration steps

1. `lakefile.lean`: `require RandomSystems from "../random-systems"`; update
   `lake-manifest.json` (`dir`), drop the `/tmp/rs-pin-0b43428` worktree.
2. Delete the local Sketch.lean drafts of the six modules above (your
   §1.3 `AdvWith` def included — the library `RandomSystems.CR18.AdvWith` has
   the identical body, generic in the carrier, so `Δm/Δb/Δp/Δbp := AdvWith … id`
   keep working verbatim after `open RandomSystems.CR18`; watch for the name
   clash until the local def is deleted).
3. Adjust the one direct call site: `Def417.winProb_le_maxWinProb` per §1.5
   (your code already passes the raw-mass form).
4. If you re-target PO-3a (option 1 in §3): consume `Def419'.PDG.CondDominates`
   (scoped notation `S |⊑ T`) + `Thm417'.delta_le_gamma`.
