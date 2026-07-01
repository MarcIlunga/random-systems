# Game-Based Cryptographic Proofs in CR18's Language

**A reconciliation of the Boneh–Shoup "attack game / game-hopping" method with Maurer's
random-systems framework (CR18), grounded in the `next-gen` Lean realization — with a concrete
game-writing recipe, a transition-by-transition compiler, a breadth-first pass over the whole book,
the constructive-cryptography frontier, and the honest limits (rewinding/extraction).**

Sources (no web search; local only):
- CR18 lecture notes: `random-systems/papers/CR18_LN.txt` (cited `CR18:NNNN`).
- Complexity/cost paper: `random-systems/papers/2021-156.pdf`, locally extracted with
  `pdftotext -layout` (cited `2021-156:NN`).
- Boneh–Shoup book chapters: `boneh-shoup-verification/BonehShoup/book-md/*.md` (cited by file).
- next-gen Lean: `random-systems/next-gen/NextGen/*.lean` (cited `file:line`).
- cc-designer's CC design: `random-systems/next-gen/design/NEXTGEN_CONSTRUCTIVE_CRYPTO.md` (cited `CC-doc §`).

> **Document map.** Part I (§0–§3) is the conceptual reconciliation (the "what maps to what" and
> the philosophical gap). Part II is the depth the round-2 brief asked for: **§A** how to *write* a
> game in CR18 (recipe + instantiations), **§B** every game-hop transition worked as a `∆`/`Γ` bound
> + the full compiler, **§C** a breadth-first pass over all BS chapters (novel technique per chapter
> → CR18), **§D** the CC-native frontier (ZK simulation, key exchange), **§E** the honest limits
> (rewinding, extraction), and **§F** the cost-aware `Problem`/complexity wrapper. The
> cost/computational story is now split: CR18 already has a §4.4
> `Problem`/reduction/complexity-class nucleus, while the EasyCrypt complexity paper explains what a
> realistic cost sidecar must track. The companion `NEXTGEN_CONSTRUCTIVE_CRYPTO.md` holds the CC layer's
> full Lean design; this doc references it rather than duplicating.

---

# PART I — THE RECONCILIATION

## 0. Thesis

A Boneh–Shoup attack game is, in CR18, **either** a **distinguishing experiment** (two `(X,Y)`-systems
and a distinguisher) **or** a **game** (one system carrying a monotone binary output). The three
classical game-hop transitions map onto three CR18 moves:

- **indistinguishability transition** → a `∆` bound (often via conditional equivalence, Thm 4.17);
- **reduction transition** → the §4.7.2 reduction-by-converter identity `(4.9)/(4.10)`;
- **identical-until-bad / failure-event transition** → CR18's **monotone MBO**: BS's "bad event `Z`"
  *is* Maurer's `Aᵢ=1`, and the **Difference Lemma** (BS Thm 4.7) *is* CR18 Lemma 4.16 / Thm 4.17.

The sharpest evidence: the **PRF/PRP switching lemma** (BS Thm 4.4/4.6) and CR18's **URP–URF switching
lemma** (Lem 4.19, `CR18:5720`) are the *same theorem by two routes* — BS via the Difference Lemma +
forgetful gnome, CR18 via the collision-MBO conditional equivalence `R̂ₙ,ₙ |≡ Pₙ` + Thm 4.17 (§7, §B.2).

What CR18 buys: the "bad event" argument is a **theorem proved once** on a *semantic* primitive (the
pre-winning behavior), not a coupling re-argued in prose per hop. What it still needs: a
**cost-aware wrapper** around the exact `∆`/`Γ` statements. That wrapper is not invented from scratch:
CR18 §4.4 already supplies `Problem`, reductions, product problems, worst-case problems, and a
complexity-class interpretation (`RandomSystems/CR18/AbstractProblem.lean`), while 2021-156 shows how
mechanized cryptographic proofs should track adversary resources as explicit theorem obligations
(`2021-156:16-31`, `2021-156:57-69`). The honest limit, §E, remains **rewinding/extraction** (forking
lemma, PoK): that is outside the non-rewinding distinguishing/simulation framework entirely.

## 1. Concept-by-concept mapping table

| Boneh–Shoup term | CR18 term (line) | next-gen Lean def (file) | Status |
| --- | --- | --- | --- |
| Attack game (two-experiment) | Distinction problem: pair of `(X,Y)`-systems `(S,T)` | two `PFunPDS X Y` | clean |
| Attack game recast as bit-guessing `Pr[b̂=b]` | Bit-guessing problem `(S,B)`, `CR18:1502` | *needs new* (§4) | needs new (thin) |
| Adversary `A`, outputs `b̂` | Distinguisher `D` (Def 3.24), verdict bit `Z` | `PFunDDS.DDD`, `verdict` `Distinguishing.lean:39` | clean |
| `Pr[W_b]` = Pr[A⇒1 in Exp b] | Verdict prob `Pr^{DS}(Z=1)` | `verdictProb D S` `Distinguishing.lean:39` | clean |
| Advantage `\|Pr[W₀]−Pr[W₁]\|` | `∆^D(S,T)=Pr^{DT}(Z=1)−Pr^{DS}(Z=1)` (Def 4.1, `CR18:5458`); abs derived (`CR18:1485`) | `advantage D S T` `Distinguishing.lean:45` | clean (sign) |
| `max` over efficient `A` | `∆(S,T):=sup_D ∆^D(S,T)` (`CR18:5479`) | `maxAdvantage` = `Δ(S,T)` `Distinguishing.lean:64` | clean (info-thy) |
| Bit-guessing adv `2·\|Pr[b̂=b]−½\|` | `Λ^D(S,B):=2(Pr(Z=B)−½)` (Def 2.9, `CR18:1517`) | *needs new* (§4) | needs new (thin) |
| `A` in a win-game (CI/forgery/collision) | Winner `W` for game `G` (Def 4.5) | `winsDDS` `WinProb.lean:32` | clean |
| `Pr[A wins G]` | `G(W)=Pr^{WG}(A_q=1)` | `winProb W G` = `G（W）` `WinProb.lean:38` | clean |
| best `A` win prob | `Γ(G):=sup_W G(W)` (Def 4.17) | `maxWinProb` = `Γ G` `WinProb.lean:71` | clean |
| **bad event `Z` / `bad` flag** | **monotone MBO `Aᵢ`; `Aᵢ=1` ⇔ bad** (`CR18:3641`) | `Y×Bool` output; monotone = `DDS.IsGame` `Theorem417.lean:175` | clean (key) |
| **"identical until bad"** | **game-equivalence `G ≡ᵍ H`** (Def 4.16, `CR18:5343`) | `GameEquiv`=`≡ᵍ` `GameEquivalence.lean:64`; ptwise `MassYAfalseEq` `Theorem417.lean:246` | clean |
| **Difference Lemma** (Thm 4.7) | **Lemma 4.16** (`CR18:5508`) / **Thm 4.17** `∆≤Γ(Ŝ)` | `lemma_4_16'`/`theorem_4_17` `RelateGameDistinguishing.lean:375,410`; `theorem_4_17_condEquiv` `Theorem417.lean:398` | clean (key) |
| reduction "build wrapper `B`, perfect sim" | reduction-by-converter `ω(wc,g)=ω(w,cg)` (4.9), `CG=G∘ρ^C` (4.10) | `rhoC c`=`ρ[c]`, `winProb_apply` `ReductionByConverter.lean:54,80` | clean |
| `q`-fold replay reduction | multiple instantiation `σ^q:W↦W^q` (§4.7.3) | `sigmaPow q`=`σ[q]` `ReductionByInstantiation.lean:25` | clean |
| query bound `Q` | `[q]S` filter (§3.4.3); `QueriesExactly` | `filterQueries`; `Γ` doesn't bake `q` (`Γ([q]G)`) | clean |
| game sequence `G₀…Gₖ` telescope | hybrid lemma `∆^D(S₀,Sₖ)=Σ∆^D(Sᵢ,Sᵢ₊₁)` (Lem 2.2, `CR18:1530`) | *needs new* (one-line, §6, §B.7) | needs new (trivial) |
| PRF security (Game 4.2) | `∆([q]F_k,[q]Rₘ,ₙ)` | two `PFunPDS` | clean (instance) |
| PRP/BC security | `∆([q]E_k,[q]Pₙ)` | two `PFunPDS` | clean (instance) |
| **PRF Switching Lemma** (Thm 4.4/4.6) | **URP–URF Switching** (Lem 4.19, `CR18:5720`) | `theorem_4_17`+`pcoll`(new) | partly (Thm 4.17 done) |
| simulation-based security (ZK, AKE, AE-as-channel) | CC construction `[R]--π,σ-->S` (CR18 Ch5 §5.3.7) | `ConstructsWithSim` `CC-doc §2.2` | clean (CC-native, §D) |
| ZK simulator `Sim` | the simulator converter `σ` at interface E | `attachAt E σ`, `idealWorld` `CC-doc §4` | clean (CC-native) |
| **forking lemma / rewinding** | — (no behavior-level analogue) | — | **genuine gap (§E)** |
| **special soundness / PoK extractor** | — (rewinding-based) | — | **genuine gap (§E)** |
| efficient adversary / complexity class | CR18 §4.4.7 complexity interpretation: `Σ_c={s | γ(s)≤c}`, `p'(c)=sup{p̄(s) | s∈Σ_c}` | `complexityClass`, `derivedPerf`, `derivedReduction` in `AbstractProblem.lean:366,373,381` | foundation exists |
| negligible / poly-bounded / elementary-wrapper | asymptotic wrapper over the cost-indexed `p'(c(λ))` | *needs new* (§F): `Negligible`, `PolyBounded`, cost algebra | needs new |

## 2. The philosophical gap (syntactic rewriting vs semantic equivalence)

**Boneh–Shoup** is a sequence of probabilistic *programs* (challengers) `Game 0…Game k`, all run against
the same adversary on a *shared probability space*; each hop rewrites the challenger's code and is
justified by (1) indistinguishability, (2) a reduction/perfect simulation, or (3) identical-until-bad
+ Difference Lemma. "Closeness" is argued per hop, in prose, with the coupling set up ad hoc.

**CR18** has no program rewriting. A system is a *semantic* object (its behavior, Def 3.18). The only
quantities are `∆(S,T)` (`Distinguishing.lean:64`), `Γ(G)` (`WinProb.lean:71`), and equivalences
`≡ᵍ`/`|≡` (equalities of conditional behaviors). A "hop" is an algebraic identity on `∆`/`Γ` (the
hybrid telescope, Lem 2.2), a reduction-by-converter identity `(4.9)/(4.10)`, or invoking Lem 4.16 /
Thm 4.17.

**Reconciliation.** Both compute a bound on `|Pr[W₀]−Pr[W_k]|`. BS telescopes per-hop bounds; CR18 uses
the **hybrid lemma** `∆^D(S₀,Sₖ)=Σ∆^D(Sᵢ,Sᵢ₊₁)` (`CR18:1530`) so `∆(S₀,Sₖ)≤Σ∆(Sᵢ,Sᵢ₊₁)`. The single
*lost* structure is BS's **shared-probability-space coupling** — and CR18 *needs none*: because `≡ᵍ` is
equality of the pre-winning behavior, "replace `S` by `T`, all terms unchanged" (CR18's phrase,
`CR18:5484`) is a `tsum_congr` (`RelateGameDistinguishing.lean:169`), not a coupling argument. The full
compiler is §B.7.

## 3. What is already done in next-gen (the structural core)

`∆` (Def 4.1/§4.10.2), `Γ` (Def 4.17), `≡ᵍ` (Def 4.16), `|≡` (Def 4.19), Lemma 4.15, Lemma 4.16,
adaptive Thm 4.17 (both `≡ᵍ` and `|≡` entry points, `Theorem417.lean:398`), reduction-by-converter
`(4.9)/(4.10)`, multiple instantiation `σ^q`, `S⁻` (Def 4.18), the MBO + monotonicity (`DDS.IsGame`).
These cover the structural heart of every game-hopping proof. The residue (§6, §9): blind converter
`b`/`Γ(bŜ)`, the `∆` telescope, a bit-guessing wrapper, the `pcoll` counting lemma, and the
cost/asymptotic sidecar built on CR18 §4.4 (§F).

### §4 — The bit-guessing bridge (the one small "needs new" in Part I)

BS often phrases a game in **bit-guessing** form (`Pr[b̂=b]`, advantage `2·|Pr[b̂=b]−½|`, eq 2.11). CR18
has the identical notion — **Def 2.9** `Λ^D(S,B):=2(Pr^{D(S,B)}(Z=B)−½)` (`CR18:1517`) — and **§2.3.4**
(`CR18:1534`) proves it equals the two-system `∆` via the bit-guessing problem `(S_U,U)`, `U` an
unbiased bit. So the recast is a CR18 *lemma*, not a gap. next-gen needs: `bitGuessAdvantage` (a thin
wrapper over `verdictProb`) and `bitGuess_eq_advantage` (`Λ^D(S_U,U)=∆^D(S₀,S₁)`). `UPSTREAM-CANDIDATE`.

---

# PART II — DEPTH

## §A — How to write a game in CR18 (the recipe)

A Boneh–Shoup attack game has four moving parts: a **scheme/primitive**, a **challenger protocol**
(possibly two experiments), an **adversary** with an **interface** (the oracle queries it may make),
and a **win/output rule** defining the advantage. The recipe encodes each into a CR18 object. The first
and most important decision is the **fork**:

> **Fork rule (the single most important modeling choice).**
> - If the advantage is a **difference of two output probabilities** between two worlds
>   (`|Pr[W₀]−Pr[W₁]|`, the "is it real or ideal?" shape — PRF, IND-CPA, semantic security, PRG,
>   indistinguishability), encode it as a **distinguishing experiment**: two `PFunPDS X Y`, the
>   adversary is a **distinguisher** `PFunDDS.DDD`. Advantage = `∆` (`Distinguishing.lean:45`).
> - If the advantage is **the probability of one success event** in a single world (the "did the
>   adversary do something forbidden?" shape — EUF-CMA forgery, ciphertext integrity, collision-finding,
>   binding), encode it as a **game**: one `PFunPDS X (Y×Bool)` whose `Bool` is the MBO `Aᵢ` flagging
>   "the success event has happened", and the adversary is a **winner** `PFunDDS.Winner`. Advantage =
>   `Γ` (`WinProb.lean:71`).
>
> A bit-guessing game (`Pr[b̂=b]`) is the distinguishing form in disguise; route it through the
> bit-guessing bridge (§4, `CR18:1534`) to a `∆` between the `b=0` and `b=1` systems.

### A.1 The seven-step encoding template

Given a BS attack game, produce a CR18 object in seven steps. (`X` = adversary→challenger query
alphabet; `Y` = challenger→adversary response alphabet.)

1. **Interface alphabet `X`.** Enumerate the *kinds* of oracle query the adversary may issue; their
   disjoint union is `X`. (One oracle ⇒ `X` is the query type. Two oracles, e.g. encrypt+decrypt ⇒
   `X = EncQuery ⊕ DecQuery`. The CC multi-interface form `I × A` `PFunDDS.Resource` `CC-doc §1.1` is
   the systematic version when parties/adversary are separate interfaces.)
2. **Response alphabet `Y`.** The challenger's reply type (ciphertext, tag, function value, …).
3. **The world(s) as a system `PFunPDS X Y`.** Build the challenger's per-query behavior as a
   (probabilistic) discrete system `Dist (DDS X Y)`. The internal key/state is *integrated out into the
   distribution* — a system IS its behavior (`b(S)`, Def 3.18), not a stateful machine. Sample the key
   once at the `Dist` level; the `DDS` is the resulting deterministic input→output history map.
4. **Fork (above).** Two-world ⇒ build `S₀,S₁ : PFunPDS X Y`. Single-success ⇒ build one
   `Ŝ : PFunPDS X (Y×Bool)`.
5. **The MBO / win predicate (single-success case).** Define `Aᵢ` = the *monotone* indicator "the
   forbidden/success event has occurred by query `i`". It must satisfy `DDS.IsGame` (Def 3.22, "once
   true stays true", `Theorem417.lean:141`) — reuse it, never re-posit monotonicity (cr18-formalize §3).
   The concrete winning predicate is then `winsDDS` (`WinProb.lean:32`: ∃ a round whose MBO bit is `true`).
6. **The adversary.** Distinguishing ⇒ `D : PFunDDS.DDD X Y` (emits a verdict bit). Game ⇒
   `W : PFunDDS.Winner X Y`. The `q`-query bound is **not** baked into the system or the advantage; it
   is the filter `[q]` on the system (`Γ([q]Ŝ)`, `∆([q]S,[q]T)`) — exactly BS's "`Q`-query adversary".
7. **The advantage.** Distinguishing ⇒ `advantage D S₀ S₁`, security quantity `Δ(S₀,S₁)`. Game ⇒
   `winProb W Ŝ`, security quantity `Γ Ŝ`. Both are literal suprema over all probability-distribution
   distinguishers/winners.
8. **Optional but mandatory for computational claims: the cost envelope.** If the theorem is meant to
   say "for every efficient adversary" rather than "for every adversary", wrap the CR18 problem in the
   §F complexity layer: choose a solver type `Σ`, a cost domain `Cost`, a complexity function
   `γ : Σ → Cost`, a budget family `c(λ)`, and state security using the derived performance
   `p'(c(λ))` rather than raw `Δ`/`Γ`. Query bounds `[q]` remain semantic filters; they are only one
   coordinate of the cost vector.

The reader should be able to mechanically encode any new game by walking these seven steps. The three
instantiations below show the result.

### A.2 Instantiation 1 — PRF security (distinguishing / `∆`)

BS Attack Game 4.2 (`4-4...md:21`): two experiments; Exp 0 the keyed family `F(k,·)`, Exp 1 a random
function `f ←$ Funs[X,Y]`; advantage `|Pr[W₀]−Pr[W₁]|`. Two-world shape ⇒ distinguishing.

```lean
namespace GameInCR18.PRF
open RandomSystems RandomSystems.CR18

variable {K X Y : Type*}

/-- Step 1–2: query alphabet = the PRF input `X`; response = `Y`. -/
/-- Step 3 + fork (world 0): the keyed family as a system — sample `k`, answer `x ↦ F k x`. -/
noncomputable def prfReal (F : K → X → Y) (keyDist : Dist K) : PFunPDS X Y :=
  Dist.fTransform (fun k => keyedDDS (F k)) keyDist     -- keyedDDS: the memoryless DDS of a function
/-- Step 3 + fork (world 1): a uniform random function as a system (the URF `Rₘ,ₙ`). -/
noncomputable def prfIdeal : PFunPDS X Y := uniformRandomFunctionSystem X Y   -- CR18 `Rₘ,ₙ`

/-- Step 6–7: the PRF advantage of a distinguisher `D` making ≤ q queries is `∆([q]·,[q]·)`. -/
noncomputable def prfAdvantage (F : K → X → Y) (keyDist : Dist K) (q : ℕ)
    (D : Dist (PFunDDS.DDD X Y)) : ℝ :=
  advantage D (filterQueries q (prfReal F keyDist)) (filterQueries q prfIdeal)
/-- "secure PRF" lives in the §F cost/asymptotic wrapper: `Negligible (fun λ => maxAdvantage … )`. -/
```

`keyedDDS`, `uniformRandomFunctionSystem`, `filterQueries` are next-gen primitives (the URF is CR18's
`Rₘ,ₙ`; `filterQueries` is `[q]`). The body is `sorry`-free *shape*; PRF security is *literally* `Δ`
between two `PFunPDS`.

### A.3 Instantiation 2 — IND-CPA (bit-guessing → distinguishing / `∆`)

BS semantic security / CPA (Game 2.1, `2-2...md:49`; CPA §5.3): adversary submits `(m₀,m₁)`, challenger
returns `Enc(k,m_b)`; advantage `|Pr[W₀]−Pr[W₁]|`. CPA additionally gives an encryption oracle.
Two-world; the bit-guessing recast (`Pr[b̂=b]`) routes through §4.

```lean
namespace GameInCR18.INDCPA
open RandomSystems RandomSystems.CR18

variable {K M C : Type*}

/-- Step 1: queries are (CPA) encryption requests `m`, plus the one challenge `(m₀,m₁)`.
    Encode `X = M ⊕ (M × M)` (oracle queries ⊕ the single challenge query). -/
abbrev Query (M) := M ⊕ (M × M)
/-- Step 3 + fork: world `b∈{0,1}` answers oracle `m ↦ Enc(k,m)` and challenge `(m₀,m₁) ↦ Enc(k,m_b)`. -/
noncomputable def cpaWorld (Enc : K → M → Dist C) (keyDist : Dist K) (b : Bool) :
    PFunPDS (Query M) C :=
  Dist.fTransform (fun k => cpaChallengerDDS Enc k b) keyDist
/-- Step 7: IND-CPA advantage = `∆` between the two worlds (bit-guessing form via §4's `Λ=∆`). -/
noncomputable def cpaAdvantage (Enc : K → M → Dist C) (keyDist : Dist K) (q : ℕ)
    (D : Dist (PFunDDS.DDD (Query M) C)) : ℝ :=
  advantage D (filterQueries q (cpaWorld Enc keyDist false))
              (filterQueries q (cpaWorld Enc keyDist true))
```

Subtlety: encryption is *probabilistic* (`Enc : K → M → Dist C`); `cpaChallengerDDS` must thread the
per-query coins into the `Dist` at the system level (sample key *and* coin-tape up front). A CPA
challenger is a system whose `Dist` ranges over `(key, coin-tape)`.

### A.4 Instantiation 3 — EUF-CMA (single-success / game / `Γ`)

BS signature unforgeability (`13-1...md`): adversary queries a signing oracle, then outputs `(m*,σ*)`;
wins if `σ*` verifies on a *fresh* `m*`. Single-success ⇒ a **game** with an MBO.

```lean
namespace GameInCR18.EUFCMA
open RandomSystems RandomSystems.CR18 PFunDDS

variable {K M S : Type*}

/-- Step 1–2: queries are a signing request `m` or the forgery attempt `(m*,σ*)`. -/
abbrev Query (M S) := M ⊕ (M × S)        -- sign(m)  ⊕  attempt-forgery(m*,σ*)

/-- Step 3 + 5: the EUF-CMA game as ONE system over `Y×Bool`. The `Bool` is the MBO `Aᵢ`: it flips
    `true` exactly when a forgery query `(m*,σ*)` arrives with `Verify(vk,m*,σ*)=accept` AND `m*` was
    never signed. Monotone by construction (once forged, stays forged) ⇒ `DDS.IsGame`. -/
noncomputable def eufcmaGame (Sign : K → M → Dist S) (Verify : K → M → S → Bool)
    (keyDist : Dist K) : PFunPDS (Query M S) (S × Bool) :=
  Dist.fTransform (fun k => eufcmaChallengerDDS Sign Verify k) keyDist

/-- Step 7: EUF-CMA advantage of a `q`-signing-query winner = `Γ` of the (filtered) game. -/
noncomputable def eufcmaAdvantage (Sign Verify keyDist) (q : ℕ) : NNReal :=
  Γ (filterQueries q (eufcmaGame Sign Verify keyDist))
```

The MBO is the heart: `eufcmaChallengerDDS` records signed messages in its (deterministic, per
key+coins) history; the output `Bool` is `true` on/after the round where a fresh-message verifying
forgery occurs — monotone, hence `DDS.IsGame`, so Lemma 4.15/4.16/Thm 4.17 all apply. **This MBO is the
same object as BS's "bad event":** "adversary produced a valid forgery" is exactly an
identical-until-bad flag (§3, §B.2).

> **Recipe summary.** Two-world advantage ⇒ two `PFunPDS X Y`, distinguisher, `Δ`. Single-success ⇒ one
> `PFunPDS X (Y×Bool)` with a monotone MBO, winner, `Γ`. Oracles ⇒ summands of `X`. Key/coins ⇒
> integrated into the `Dist`. Query bound ⇒ the `[q]` filter. "Secure" ⇒ a §F cost/asymptotic wrapper
> over CR18 §4.4 `Problem` objects, not a change to the game semantics.

---

## §B — Game-hopping transitions in CR18 (each hop type, worked)

For each transition kind: the CR18 mechanism, the exact lemma, a worked `∆`/`Γ` bound. `Gⱼ` is a BS
game reinterpreted as a CR18 system `Sⱼ`.

### B.1 Indistinguishability / computational transition

**BS:** `Game j → Game j+1` replaces a primitive `P` by an indistinguishable `P'`; `|p_j−p_{j+1}| ≤
ε_P` (a reduction adversary's advantage against `P`).

**CR18 mechanism:** `Sⱼ`,`Sⱼ₊₁` differ only by the swapped sub-system, so they are equal *as seen
through* the surrounding converter `c` (the "rest of the game"). The bound is the embedded
sub-distinguisher's advantage, via reduction-by-converter data processing (the `∆`-side of `ρ[c]`):

> `∆^D(Sⱼ, Sⱼ₊₁) = ∆^{D∘c}(P, P') ≤ ∆(P, P')`

— a distinguisher `D` for the big games is `D∘c` for the swapped primitive. Exact lemma: the
`Distinguishing`-side analog of `rhoC_apply` (`ReductionByConverter.lean:64`), non-expansion of `∆`
under converter application (`CC-doc §7 L3`, CR18 §5.2.3 "non-expanding" `CR18:5933`). Worked: in a
PRF→random-function hop, `c` = "the construction wrapped around the PRF"; `∆^D(real,hybrid) =
∆^{D∘c}(F_k,R) ≤ PRFadv`.

### B.2 Identical-until-bad / failure-event transition (the deepest match)

**BS Difference Lemma (Thm 4.7, `4-4...md:118`):** `W₀∧¬Z ⟺ W₁∧¬Z` ⟹ `|Pr[W₀]−Pr[W₁]| ≤ Pr[Z]`.

**CR18 mechanism:** the bad event `Z` is a **monotone MBO** `Aᵢ`; "identical until bad" is
`Sⱼ ≡ᵍ Sⱼ₊₁`; the bound is **Lemma 4.16 / Thm 4.17**. Worked (CR18 `:5510–5563`; Lean
`RelateGameDistinguishing.lean:219`):

```
∆^D(Sⱼ⁻, Sⱼ₊₁⁻) = Pr^{D Sⱼ₊₁}(Z=1) − Pr^{D Sⱼ}(Z=1)                                  -- def of ∆
              = [Pr^{D Sⱼ₊₁}(Z1∧A0)+Pr^{D Sⱼ₊₁}(Z1∧A1)] − [Pr^{D Sⱼ}(Z1∧A0)+Pr^{D Sⱼ}(Z1∧A1)]
              = Pr^{D Sⱼ₊₁}(Z1∧A1) − Pr^{D Sⱼ}(Z1∧A1)        -- A0 terms cancel since Sⱼ ≡ᵍ Sⱼ₊₁
              ≤ Pr^{D Sⱼ₊₁}(A1) = Sⱼ₊₁(D) ≤ Γ(Ŝⱼ₊₁)          -- drop ≥0; Z1∧A1⊆A1; Lem 4.15; Def 4.17
```

So `∆(Sⱼ⁻, Sⱼ₊₁⁻) ≤ Γ(Ŝ)` (= BS's `Pr[Z]`, but a *game-winning probability* — and CR18 downgrades it
to the **non-adaptive** `Γ(bŜ)`, §B.6/§7.4). The `A0`-cancellation BS earns with a coupling ("the `zᵢ`
are literally equal") is a `tsum_congr` in `distNotWonZ1_congr_gameEquiv`
(`RelateGameDistinguishing.lean:169`). **The MBO must be monotone** (`DDS.IsGame`) — the discipline BS
leaves implicit and CR18 makes structural.

### B.3 Reduction transition (perfect simulation)

**BS:** `p_j = p_{j+1}` because a wrapper `B` perfectly simulates `Game j` to `A` (`PROSE_BASELINE.md:115`).

**CR18 mechanism:** the converter `c` *is* `B`'s interface layer; "perfect simulation" is `ω(wc,g)=ω(w,cg)`
(4.9, `CR18:4643`) lifted to `CG=G∘ρ^C` (4.10). Worked, `rfl` in next-gen:

> `winProb (Dist.fTransform ρ[c] W) G = winProb W (Dist.fTransform c G)` (`winProb_apply`,
> `ReductionByConverter.lean:80`)

— `A`-winning-`B`-simulated = `(A∘c)`-winning-real; advantages equal, `∆`-step is `0` after `ρ[c]`. The
`q`-fold replay reduction is the same with `σ[q]` (`ReductionByInstantiation.lean:25`).

### B.4 Bridging / conceptual (syntactic-rewrite) transition

**BS:** "a purely conceptual change" — `j→j+1` rewrites the challenger's *code* with *no distribution
change* (CBC-MAC Game 1→2 "faithful gnome", `6-4...md:60`; switching Game 0 "faithful gnome", `4-4...md:126`).

**CR18 mechanism:** two programs with the same *behavior* are the **same system**, so the hop is
`∆(Sⱼ,Sⱼ₊₁)=0` by **behavior-equality** — but the *cost of establishing that equality* varies:
- **purely syntactic rewrite** (rename a variable, inline a definition, reorder independent lines): the
  two `PFunPDS` are *definitionally* equal, `∆=0` by `rfl`. (e.g. the switching-lemma Game 0's faithful
  gnome *viewed as* the URP `Pₙ` — same behavior by definition.)
- **re-sampling / reindexing rewrite** (the CBC-MAC Game 1→2 "implement `f` as a faithful gnome with a
  prepared list `β₁…β_B` and a consistency check", `6-4...md:60`; or representing a random function as a
  lazily-sampled table): behaviorally equal but **not** definitionally `rfl` — it is a change of
  *representation of the same distribution*, discharged by a short distribution congruence
  (`tsum_congr` / a `Finsupp` reindexing showing the two `Dist`s have equal mass on every behavior).
  Still `∆=0`, but via a proof, not `rfl`.

Either way the hop contributes `0` to the telescope. CR18 is *simpler* than BS here — BS must *argue*
the rewrite preserves the distribution on the shared space, whereas CR18 reduces it to "the two systems
have equal behavior", a single distribution-level fact — but it is honestly a distribution congruence,
not always a definitional identity. (The faithful/forgetful gnome *pair* = B.4 then B.2: the faithful→
gnome step is this behavior-equality rewrite, the gnome→forgetful step is the identical-until-bad B.2.)

### B.5 "Large failure event" / abort transition

**BS:** the challenger *aborts* on a bad event; `|p_j−p_{j+1}| ≤ Pr[abort]`.

**CR18 mechanism:** identical to B.2 — the abort condition is a monotone MBO `Aᵢ` (once aborted, stays),
`∆ ≤ Γ(Ŝ_abort)`. If `Pr[abort]` is bounded by *counting* (union over collision pairs), that is a
`Γ(bŜ)` estimate (`pcoll`, §7). If the abort is a *guessing* step (`Pr=1/Q`, FDH `13-4...md`), it is
**not** a behavior-level step — it is a B.3 reduction whose advantage carries a `1/Q` factor; CR18 puts
the factor in the winner-transform, not a system equivalence. (Guessing is the seam where the ROM and
the asymptotic layer enter; §C ch12/13, §E.)

### B.6 Adaptive→non-adaptive transition (CR18-specific, *better* than BS)

**CR18 mechanism (no BS analogue):** the **blind converter** `b` (Def 4.20, `CR18:5616`) blocks the
replies, so `Γ(bŜ)` is the *non-adaptive* winning probability and `Γ(bŜ) ≤ Γ(Ŝ)`. Thm 4.17's headline
(`CR18:5605`) is `∆(S,T) ≤ Γ(bŜ)`: the *adaptive* distinguishing advantage bounded by the *non-adaptive*
game — turning "bound `Pr[Z]`" into "choose the worst-case fixed query sequence and count" (the
switching-lemma `pcoll`, §7.4). BS re-earns adaptivity each time via the coupling; CR18 factors it out
once. **Highest-value missing piece** (task #1; §9 item 1).

### B.7 The full compiler: `G₀…Gₖ` → an explicit chain of `∆`/`Γ` bounds

Given BS `G₀ → ⋯ → Gₖ` with per-hop labels `jᵢ ∈ {indist, bad, reduction, bridge, abort}`:

```
∆(S₀, Sₖ)
  ≤ ∆(S₀,S₁) + ∆(S₁,S₂) + ⋯ + ∆(S_{k-1},Sₖ)            -- hybrid lemma 2.2 (CR18:1530) + triangle
    │             │                    │
    jᵢ = bridge      ⟹  ∆(Sᵢ,Sᵢ₊₁) = 0                  -- behavior equality (B.4): rfl if purely
                                                         --   syntactic, else a short tsum_congr
    jᵢ = reduction   ⟹  ∆(Sᵢ,Sᵢ₊₁) = 0 after ρ[cᵢ]       -- winProb_apply (B.3)
    jᵢ = indist      ⟹  ∆(Sᵢ,Sᵢ₊₁) ≤ ∆(Pᵢ,P'ᵢ)           -- non-expansion of ∆ under cᵢ (B.1)
    jᵢ = bad / abort ⟹  ∆(Sᵢ,Sᵢ₊₁) ≤ Γ(b Ŝᵢ)             -- theorem_4_17_condEquiv (B.2/B.5/B.6)
  = Σ (the surviving terms)
```

Mechanical: each arrow's label selects the lemma; surviving terms summed by the hybrid lemma. The human
supplies only *which* MBO/converter realizes each hop — the creative content of a BS proof, now with
each hop discharged by a named CR18 theorem instead of a fresh prose coupling. Engineering this as a
proof DSL (cnl-rs `Let…/RSLemma` + `gameEquiv_winFun_eq`) is §9 item 8.

---

## §C — Breadth-first pass over the Boneh–Shoup chapters

One representative scheme per chapter, its **novel** technique, and the CR18/next-gen translation (or an
honest "needs X"). Chapters reusing an earlier technique are folded.

| Ch | Representative scheme | Novel technique | CR18 / next-gen translation |
| --- | --- | --- | --- |
| **2** (`2-2`,`2-3`) | Semantic security; message-recovery reduction (Thm 2.7) | the **reduction** paradigm + bit-guessing recast (§2.2.5, `2-2...md:130`) | distinguishing `∆` between the two SS worlds; reduction = `ρ[c]` (B.3); bit-guessing = `Λ=∆` (§4, `CR18:1534`). Clean. |
| **3** (`3-4`,`3-5`) | PRG composition (Thm 3.2); next-bit test | **hybrid argument** over `Q` parallel copies; next-bit ↔ indistinguishability | hybrid lemma 2.2 telescope (B.7); copies = `σ^q`/`PFunDDS.parallel`. next-bit↔indist = a `∆`-characterization. PRG itself: `∆(G(U_seed),U_output)`. Clean. |
| **4** (`4-4`,`4-6`) | **PRF/PRP switching** (Thm 4.4/4.6); **GGM tree PRF** (Thm 4.10) | switching = Difference Lemma; **GGM = `ℓ`-level hybrid**, each hop a PRG-distinguishing reduction, telescoped (`4-6...md:33,79`) | switching = Thm 4.17 + `pcoll` (§7, B.2). **GGM**: hybrids `H₀…H_ℓ` are systems; each `∆(Hⱼ,Hⱼ₊₁) ≤ ∆(G^{(Q)},U)` by B.1 (level-`j` relabel = the converter); telescope by B.7. "`Q` nodes touched at level `j`" = `[Q]` filter + `Q`-fold `σ^q`. **Clean; compiler showcase.** |
| **5** (`5-4`) | CPA from PRF (counter mode) | hybrid over message blocks + PRF-switching | `∆` between CPA worlds; hybrid over blocks (B.7); PRF→URF (B.1). Clean. CPA challenger-as-system needs coin-tape integration (§A.3). |
| **6** (`6-4`) | **CBC-MAC prefix-free PRF** (Thm 6.3) | **query-tree** + faithful/forgetful gnome + Difference Lemma; bad event `Z` = internal collision `γ_p⊕a=γ_{p'}⊕a'` (`6-4...md:76`) | Game 0→1 PRF-swap (B.1); 1→2 gnome = bridge (B.4); 2→3 forgetful = identical-until-bad, MBO `Aᵢ`="a CBC-chain collision occurred" (B.2), bound `Γ(b·) ≤ Q²ℓ/\|X\|` by counting. **Clean** — collision-MBO is the switching pattern at the chain level. (next-gen has CBC/HCTR2 machinery.) |
| **7** (`7-4`) | Carter–Wegman MAC; UHF | **information-theoretic** ε-almost-universal hashing; PRF∘UHF | UHF ε-AU = a *statistical* bound `δ(·)` (CR18 Def 2.8 statistical distance `CR18:1491`); composition = B.3. **Clean, CR18-native** (info-theoretic is CR18's home; cf. project δ-AUH work). |
| **8** (`8-4`,`8-3`) | Merkle–Damgård (Thm 8.4); birthday attack | **collision-resistance reduction** (collision in `H` ⟹ collision in compression fn); birthday bound | CR collision-finding = a **game** (single-success "found a collision") ⇒ `Γ`; MD reduction = B.3 (extending wrapper `c`). Birthday = `pcoll` (§7). **Mostly clean**; CR is a win-game not distinguishing. CR needs a keyed family to be non-trivial — the §F cost/asymptotic layer matters. |
| **9** (`9-2`,`9-4`) | AE; Encrypt-then-MAC (Thm 9.2); AE⟹CCA (Thm 9.1) | **multi-game CI proof** + identical-until-bad on "a decryption query verifies" (`PROSE_BASELINE.md:74`) | CI = a **game** (MBO="a non-reject forgery occurred"); CPA part = `∆`; AE⟹CCA hop = B.2 with `Z`="A made a decrypting ciphertext query". **Clean.** *AE-as-a-channel* (§9.3, `9-3...md`) is the **CC-native** reading — §D. |
| **10** (`10-4`,`10-5`) | Diffie–Hellman; DL/CDH/DDH | assumptions as distinguishing/search problems; DDH = an indistinguishability | DDH = `∆(triple_real,triple_random)` — distinguishing, clean. CDH/DL = **search/win games** (`Γ`); these are *assumptions*, encoded as the `≤ Γ` premise of a reduction, not proved. Clean as premises. |
| **11** (`11-4`,`11-5`) | ElGamal semantic security | reduction to DDH; hybrid over the one-time-pad mask | `∆` between SS worlds ≤ `∆`(DDH) by B.1 (wrapper builds the challenge from the DDH triple). **Clean** — textbook reduction. |
| **12** (`12-3`,`12-5`,`12-8`) | CCA encryption; **ROM-programmed OAEP** (`12-8`); CCA from DDH w/o RO (`12-5`) | **random-oracle programming** + plaintext-awareness/**extraction**; guessing-index reductions | CCA = `∆` with a decryption oracle; the *non-ROM* DDH proof (`12-5`, Cramer–Shoup) is **clean** game-hopping (B.1/B.2/B.4). The **ROM-programming** proofs (`12-8`) are **partly outside**: programming + *extracting the queried preimage* is a B.5 abort + a guessing/extraction step — extraction is the §E limit (the simulator reads `A`'s RO queries; not a behavior-level converter). |
| **13** (`13-3`,`13-4`,`13-5`) | **Full-Domain-Hash signatures** (Thm 13.3); tight RSA-FDH | **ROM programming** + **guessing the forgery query** (Lem 13.5, `t`-repeated OW reduction, `13-4...md`) | EUF-CMA = a **game** (`Γ`, §A.4). Signing-oracle simulation via ROM programming = a B.3 reduction with a programmed oracle. "Guess which of `Q` RO queries is the forgery, factor `1/Q`" = a B.5 guessing reduction (factor in the winner-transform). **Partly outside:** the ROM is *not* a static resource — the reduction *observes each query and programs the reply adaptively* (embed `y*` at the guessed index), needing a programmable/stateful resource interface (§E.2, the hard half); the guessing factor is handled by the §F cost/asymptotic layer. **No rewinding** (FDH is guess-not-rewind), so milder than ch19. |
| **14** (`14-1`,`14-6`) | Lamport OTS; OTS→many-time (Merkle tree) | one-wayness reduction + a tree/hybrid lift | OTS = a win-game (`Γ`) reducing to OW (B.3); tree lift = hybrid (B.7). **Clean** (no rewinding). |
| **15** (`15-5`) | BLS / pairing signatures | reduction to co-CDH in the ROM | EUF-CMA game; ROM-programmed reduction (as ch13). **Partly outside** (ROM + guessing), no rewinding. |
| **16** (`16-1`,`16-4`) | DL/CDH/DDH & factoring/RSA analysis | concrete *algorithmic* attacks (index calculus, NFS) | *attack* analyses (upper-bounding assumption hardness), **not security proofs** — outside game-hopping scope (they bound `Γ` of the assumption-game by number theory). Honest "n/a". |
| **18** (`18-3`,`18-6`) | Password / challenge-response identification | active-attack identification game; dictionary bounds | identification security = a **game** (impersonation). Challenge-response (`18-6`) reduces to PRF/MAC (B.3). **Clean**; active model = a win-game with an interactive interface. |
| **19** (`19-1`,`19-4`,`19-6`) | **Schnorr id & signatures; Σ-protocols** | **rewinding + special-soundness extractor** (Lem 19.2, Def 19.4); **special HVZK simulator** (Def 19.5); Fiat–Shamir | **SPLIT.** (a) **special HVZK** = a *simulator* producing a transcript w/o the witness (Def 19.5, `19-4...md:70`) → **CC-native** (§D): the simulator is a converter, ZK = `∆(real,sim)=0`. (b) **special soundness / PoK** = *rewind `P*` to two transcripts `(t,c,z),(t,c',z')`, extract* (Lem 19.2, `19-1`; Def 19.4, `19-4...md:60`) → **GENUINELY OUTSIDE** (§E): rewinding runs the adversary twice on a shared prefix; CR18's distinguisher/winner runs **once** against a behavior. |
| **20** (`20-1`,`20-3`,`20-4`) | **Zero-knowledge / NIZK / PoK** | **simulator-based ZK** (Def 20.6 cHVZK, Def 20.5 niZK); **soundness extractor**; CRS/RO programming | **SPLIT** (mirrors ch19). (a) **ZK** (Def 20.6/20.5) is *defined* ideal-vs-real with a simulator (`20-4...md`,`20-3...md`) → **CC-native** (§D): `Δ(realProof,simProof) ≤ ε`. (b) **knowledge soundness / extractor** = rewinding/multi-extraction (Def 19.9, `19-9...md`) → **OUTSIDE** (§E). NIZK *soundness* (a win-game, Def 20.4) is clean; *ZK* is CC-native; the *extractor* is the limit. |
| **21** (`21-1`,`21-2`,`21-3`) | **Authenticated key exchange** | Bellare–Rogaway **session-key indistinguishability** + matching/partnering + reveal/corrupt (`21-1...md`); PFS via ephemeral keys | **CC-native (and game-able).** BS phrases AKE game-based; the natural CR18/CC reading is a **construction**: the protocol *constructs* an ideal **shared-key resource** from authenticated channels + a DH/PKE resource, simulator at E for reveal/corrupt (§D). static/PFS/HSM = stronger ideal resources (more adversary interfaces). §21.2/21.3 proofs = reductions (B.3) chained (B.7) — clean *as games*, cleaner *as CC constructions*. |

**Reading.** The *distinguishing/winning + game-hopping* core (ch 2–9, 11, 14, 18) maps **cleanly and
mechanically** via §B. The *information-theoretic* parts (ch7 UHF, birthday `pcoll`) are
**CR18-native**. The *ROM-programming + guessing* proofs (ch 12–13, 15) are **partly outside**: a static
random oracle is a shared resource (easy), but *adaptive on-the-fly programming + query observation*
needs a programmable/stateful resource interface (§E.2, the hard half), and the guessing factor is
handled by the cost/asymptotic layer (§F) — but they contain **no rewinding**. The
*simulation-based* notions (ch19 HVZK, ch20 ZK/NIZK, ch21 AKE) are **CC-native** (§D). The genuine wall
is **rewinding/extraction** (ch19 special soundness, ch20 PoK) — §E.

---

## §D — The CC-native frontier (simulation-based security)

The later chapters' security notions are **native to constructive cryptography** — *simulation-based
security IS the CC construction notion*. The cc-designer's `NEXTGEN_CONSTRUCTIVE_CRYPTO.md` builds the
vocabulary; this section connects BS simulation proofs to it. Central CC object (`CC-doc §2.2/§4`):

```lean
/-- CR18 §5.3.7 simulation-based construction with ε error: real world π·R is Δ-within-ε of the
    ideal world σ^E·S (σ the simulator at adversary interface E). -/
def ConstructsWithSim (π : P → DDC A B A B) (parties) (E : P) (σ : DDC A B A B)
    (ε : ℝ) (R S : PResource P A B) : Prop :=
  (Δ( asPDS (realWorld π parties R), asPDS (idealWorld E σ S) ) : ℝ) ≤ ε
```

A BS *simulation-based* proof — "there is a simulator `Sim` whose output is indistinguishable from the
real interaction" — is *literally* `ConstructsWithSim` with `Sim = σ` and the gap = `ε`.

### D.1 Zero-knowledge (ch19 HVZK, ch20 cHVZK/niZK) → `Δ(real, sim) ≤ ε`

BS special HVZK (Def 19.5, `19-4...md:70`): a simulator `Sim(y,c)` outputs `(t,z)` with `(t,c,z)`
accepting *without the witness*, distributed identically to a real conversation. cHVZK (Def 20.6) and
niZK (Def 20.5) are the *computational* relaxation: real-vs-simulated transcripts only
**indistinguishable** (`20-4...md`,`20-3...md` — both Experiment 0 = real, Experiment 1 = `Sim`).

**CC reading.** The transcript distribution is a *resource* (the conversation at the verifier
interface). "ZK" is

> `Δ( realTranscriptResource(P,V,x,y) , simTranscriptResource(Sim,y) ) ≤ ε`

— the protocol-with-witness *constructs* (within `ε`) the same resource the simulator-without-witness
does. Perfect HVZK = `ε=0` (behavior equality `≡`); cHVZK/niZK = `ε` negligible in the §F asymptotic
wrapper. The simulator's
"generate `(t,z)` in reverse order" (`19-4...md:70`) is a *converter*; "without the witness" = the
converter has no `x`-interface — exactly CC's "simulator at E with the witness interface absent".
**Maps cleanly.** New piece: phrase a transcript as a thin `PResource`; `ConstructsWithSim` is `CC-doc §4`
ready.

### D.2 Authenticated key exchange (ch21) → constructing an ideal key resource

BS AKE (§21.1, `21-1...md`) is game-based: session-key indistinguishability + matching/partnering +
reveal/corrupt, static/PFS/HSM hierarchy.

**CC reading (the natural one).** A protocol `π` *constructs* an **ideal shared-key resource** `S_key`
(matched parties get a uniform key the adversary cannot learn) from assumed resources `R` (authenticated
channels + DH/PKE), tolerating a simulator `σ` at `E` realizing reveal/corrupt:

> `ConstructsWithSim π E σ ε R S_key`.

The **static → PFS → HSM** hierarchy is a hierarchy of *ideal resources / adversary interfaces*: PFS =
`S_key` whose `E`-interface allows post-hoc long-term-key corruption without leaking *past* keys; HSM =
plus ephemeral-key leakage in a window (`21-4...md`). Stronger security = a more capable adversary
interface on the same ideal resource — exactly CC's "the ideal resource defines what the adversary may
do". The §21.2/21.3 proofs (reductions to PKE/signature security, chained game-hops) become the
*discharge* of `ConstructsWithSim` via B.3+B.7, with matching/partnering absorbed into the ideal
resource's behavior. **Maps cleanly to CC** and is arguably *more* faithful (composability for free via
`ConstructsWithSim.comp`, `CC-doc §3.2`). Cost: AKE's session/partner state is genuinely stateful — the
ideal `S_key` carries session bookkeeping, the real modeling work.

### D.3 AE-as-a-channel (ch9 §9.3) → constructing a secure channel

BS §9.3 ("encryption as an abstract interface", `9-3...md`) already reads AE as an *interface*. CC
statement: AE *constructs* an ideal **secure channel** from a shared key + an insecure channel — the
canonical Maurer CC example; `ConstructsWithSim` with `σ` simulating the length leakage at `E`. Clean,
textbook CC.

**Summary (§D).** Simulation-based security (ZK, AKE, secure channels) is `ConstructsWithSim`
(`CC-doc §2.2/§4`). The bridge from a CC construction obligation down to a game bound is the
game-relaxation `T̂⊢` + `theorem_4_17_condEquiv` (`CC-doc §2.3`, the L9/L10 bridges). The CC layer is
*designed but not yet built* (`CC-doc` is statement-shape `sorry`); a game-based-on-CC front-end and a
CC-construction-from-games front-end are the same layer from two sides.

---

## §E — Honest limits: where CR18 / CC genuinely struggle

Following cr18-review discipline: an honest "this needs machinery CR18 doesn't have" is a finding. Three
limits, increasing severity.

### E.1 The cost/computational layer — outside core `∆`/`Γ`, but not absent from CR18

CR18 §4.10–4.11 is information-theoretic: `∆`,`Γ` are exact suprema over *all* distinguishers/winners.
So the raw game objects do **not** know what "efficient", "negligible", "poly-bounded", or
"elementary wrapper" mean. The earlier version of this document overstated the consequence: CR18 does
have a small complexity-theoretic foundation in **§4.4**. It models abstract problems, solvers,
performance functions, reductions, reduction composition, generalized/product reductions, worst-case
problems, and the derived complexity-class interpretation

```
Σ_c   = { s | γ(s) ≤ c }
p'(c) = sup { p̄(s) | s ∈ Σ_c }
ρ'(c) = sup { γ(ρ(s)) | s ∈ Σ_c }.
```

In next-gen this is already present in `RandomSystems/CR18/AbstractProblem.lean`: `Problem`,
`Reduction`, `Reduction.upperBound`, `reduction_comp`, `upperBound_comp`, product-problem instance
`instProblemPi`, `worstCasePerf`, and the exact `complexityClass`/`derivedPerf`/`derivedReduction`
objects. The missing layer is not "invent complexity theory"; it is to connect `∆`/`Γ` game objects to
that §4.4 abstraction and add a cost algebra strong enough for cryptographic reductions.

2021-156 is the useful design warning. The formal theorem should not merely say `adv_S(A) ≤ adv_H(B)+ε`;
it must also say the constructed adversary has comparable resources:

```
∀ A. ∃ B. adv_S(A) ≤ adv_H(B) + ε  ∧  cost(B) ≤ cost(A) + δ
```

where `ε` and `δ` usually depend on oracle-call counts (`2021-156:57-69`). The paper's cost model splits
intrinsic computation from calls to abstract/oracle procedures: a cost is a tuple with a distinguished
`conc`/`intr` coordinate and one coordinate per abstract procedure (`2021-156:45-49`, `2021-156:381-394`).
This is the right mental model for CR18: `[q]` is only the semantic query budget to a particular system;
the computational theorem needs a separate cost vector that can count time, oracle calls, simulator calls,
and environment calls.

The detailed design is §F. The boundary remains clean: core CR18 proves exact per-budget `∆`/`Γ` facts;
§F wraps those facts into resource-bounded and asymptotic statements. Reductions with a `1/Q` guessing
factor (FDH/OAEP-style ROM proofs, §B.5/§C ch13) are the motivating examples: the behavior proof gives
the probability relation, and the cost layer proves that the guessed-query adversary still lies in the
assumption's allowed complexity class.

### E.2 Random-oracle programming — *expressible, but as a shared resource, not a CR18 system*

ROM proofs (ch12 OAEP, ch13 FDH, ch15 BLS) have the simulator **adaptively program** the oracle's
answers and **read** `A`'s queries on the fly. A CR18 system is a fixed behavior — it cannot be
reprogrammed mid-interaction by the reduction, and observing `A`'s queries is not a distinguisher's
verdict. Two distinct demands, of *increasing* difficulty:

1. **The RO as a shared resource** (the easy half). A *uniformly random* oracle that both `A` and the
   reduction may query is a `PFunPDS` at a free interface `F` (a lazily-sampled random function). This
   is genuinely a static shared resource — modellable today.
2. **Adaptive programming + query observation** (the hard half, *not* a static resource). The reduction
   does **not** just query a fixed random oracle; it (a) *sees each query `A` makes as it is made*, and
   (b) *chooses the answer depending on its own challenge and on the query history* (e.g. embed the
   one-way challenge `y*` at a guessed query index; answer signing-related queries with programmed
   values). That requires the RO-resource to be **stateful and converter-controllable on the fly** — a
   lazy table the simulator both reads and writes per query, with the converter `σ` at `F` *observing*
   `A`'s query before *deciding* the reply. This is **more than a static shared resource**: it needs a
   *programmable* resource whose per-query output is chosen by an attached converter that can read the
   query — i.e. the RO-interface must expose the query to `σ` and let `σ` return the answer
   (a request/response converter at `F`, not a fixed `PFunPDS`).

**Resolution:** the CC layer's converter-at-interface machinery (`attachAt`, `CC-doc §1.3`) *can*
express (2) — a converter that intercepts the `F`-query, observes it, and returns a programmed reply is
exactly a converter on the shared interface — but it is **not** the plain distinguishing/winning
framework, and the per-query "observe-then-decide" behavior is real modeling work (the resource is
stateful; the converter is genuinely interactive at `F`, not a one-shot function). **Verdict:
expressible in the CC extension with non-trivial effort; the *static* shared-RO is easy, but *adaptive
on-the-fly programming with query observation* needs a programmable/stateful resource interface and is
outside the basic §B machinery.** No rewinding, so milder than E.3 — but do not gloss it as "just a
shared resource"; the adaptivity is the cost.

### E.3 Rewinding / extraction (forking lemma, PoK) — *genuinely outside; needs new machinery*

The real wall. BS special soundness / PoK (Def 19.4, Lem 19.2, Def 19.9; `19-1`,`19-4`,`19-9`) extracts
a witness by **rewinding**: run `P*` to `(t,c,z)`, then *"rewind `P*`'s internal state back to the point
just after it generated `t`"* and feed a fresh `c'≠c` to get `(t,c',z')`; `Ext` computes the witness
from the two transcripts (`19-4...md:64`, `:60`). Multi-extraction (Def 19.9, `19-9...md`) repeats
`O(B/θ)` times. Schnorr's extractor: `α = (z−z')/(c−c')` (`19-4...md:62`).

**Why this is outside CR18/CC.** The whole distinguishing/winning/simulation framework runs the
adversary **once** against a **fixed behavior** and reads one output (a verdict bit `Z`, or the MBO
`Aᵢ`). Rewinding requires:
1. **a second execution on a shared prefix** — `A` run twice with the *same* internal state to the
   challenge point, then diverging. CR18 has no notion of "the adversary's internal state at a point in
   the interaction"; a winner/distinguisher is a behavior `Ω→…`, not a resettable machine. The
   shared-probability-space coupling CR18 *eliminates* (§2) is *exactly* what rewinding *requires* — so
   the feature that makes CR18 elegant for game-hopping is the feature that makes it unable to express
   rewinding.
2. **extraction as an algorithm outputting a witness**, not a probability. `Ext` produces `x ∈ X`;
   CR18's primitives produce real-valued `∆`/`Γ`, never a witness. "`P*` *knows* `x`" is a statement
   about an extractor's *success*, not a distinguishing advantage.
3. **a forking probability analysis** (`ε²−ε/N`, Lem 19.2, `19-1...md`) over *two correlated runs* — a
   joint distribution over `(run₁,run₂)` sharing a prefix, not a behavior of a single system.

**What extension would capture it (sketch; not a claim it is easy).** Enrich the adversary model from
"a behavior / distribution over deterministic strategies" to "a *resettable* probabilistic machine with
an exposed state-and-randomness handle", plus an *extractor* as a first-class object with
success-probability semantics:
- a `RewindableWinner` carrying its randomness tape explicitly, so two runs share a tape prefix;
- a *forking lemma* as a generic probabilistic lemma over the shared-tape product (the `ε²−ε/N` bound),
  proved once;
- an `Extractor` object + a `KnowledgeSoundness` predicate (`∃ Ext, Pr[Ext extracts] ≥ Γ − κ`).

This is a **substantial new layer orthogonal to the behavior primitive** — it reasons about the
adversary's *internals*, which CR18 deliberately abstracts away. Not a contradiction with CR18 (one can
build it alongside), but *not derivable from* the distinguishing/winning machinery and would not reuse
Lemma 4.16 / Thm 4.17. **Honest verdict: forking-lemma / PoK-extractor proofs are outside both CR18 and
CC as formalized; capturing them needs a dedicated rewinding+extraction layer the project does not have
and the behavior primitive should not grow into.** The ZK *simulator* half of Σ-protocols (D.1) maps
cleanly; the *soundness/extraction* half does not.

> **Why the asymmetry is principled, not incidental.** CC/CR18 security is *indistinguishability of
> behaviors* and *construction of ideal resources* — both "outside-in" (what an environment sees).
> Knowledge extraction is "inside-out" (what the adversary must contain). The frameworks are built to
> erase the inside (that is the point of the behavior primitive), so the one thing they structurally
> cannot see is the one thing extraction needs.

---

## §F — Cost-aware game statements: CR18 §4.4 + 2021-156

This section is the promised bridge from game modeling to complexity theory. It is intentionally a
**design-document layer only**: no Lean implementation is prescribed here beyond naming the existing CR18
objects it should reuse.

### F.1 Promote `∆` and `Γ` games to CR18 `Problem`s

CR18 §4.4 starts from an abstract problem object `p`, a solver set `Σ_p`, a performance set `Ω_p`, and a
performance function `p̄ : Σ_p → Ω_p`. A game-based statement should first expose that structure:

| Game object | Problem object `p` | Solver set `Σ_p` | Performance `p̄(s)` |
| --- | --- | --- | --- |
| distinction pair `(S,T)` | `DistinctionProblem(S,T)` | distinguishers `D` | `advantage D S T` or its absolute/two-sided variant |
| query-bounded distinction | `DistinctionProblem([q]S,[q]T)` | distinguishers `D` | `advantage D ([q]S) ([q]T)` |
| win game `G` | `GameProblem(G)` | winners `W` | `winProb W G` |
| query-bounded win game | `GameProblem([q]G)` | winners `W` | `winProb W ([q]G)` |
| CC real-vs-ideal construction | `CCProblem(real,ideal)` | environments `Z` | `advantage Z real ideal` |

This is mostly plumbing: `Distinguishing.lean` and `WinProb.lean` already define the per-solver
performance functions; `AbstractProblem.lean` provides the generic typeclass. Once a game is a `Problem`,
CR18's existing reduction lemmas apply uniformly:

- information-theoretic bound: `p̄ ≤ᶜ ε`;
- reduction lower-bound form: `τ ∘ p̄ ≤ q̄ ∘ ρ`;
- reduction upper-bound form: `p̄ ≤ λ ∘ q̄ ∘ ρ`;
- product/generalized reductions: use `instProblemPi`;
- worst-case assumptions: use `Problem (Set P)` / `worstCasePerf`.

The key modeling point: `Δ(S,T)` and `Γ(G)` remain convenient abbreviations for the raw supremum over all
probability-distribution solvers. The complexity-aware statement should instead talk about
`derivedPerf γ p c`, the best performance among solvers whose cost is at most `c`.

### F.2 The cost object should be a vector, not a scalar

2021-156's main contribution is not just "add a polynomial-time predicate"; it is the observation that
reduction statements become meaningful only when the theorem tracks **which resources** are consumed.
Their module restrictions count intrinsic execution time separately from calls to each abstract
procedure/oracle (`2021-156:277-289`, `2021-156:381-394`). That maps naturally to a CR18 cost vector:

```lean
-- design shape only
structure Cost where
  intrinsic : Nat
  calls : CostLabel -> Nat

def Cost.le (a b : Cost) : Prop :=
  a.intrinsic <= b.intrinsic ∧ ∀ l, a.calls l <= b.calls l
```

`CostLabel` should include at least:

- challenged-system oracle calls (`S.query`, `G.query`, `[q]`-related coordinates);
- assumption-oracle calls (e.g. PRF, DDH, OW, RO);
- adversary subroutine calls (`A.choose`, `A.guess`, `A.sign`, `A.decrypt`);
- simulator/environment calls in CC/UC statements;
- concrete intrinsic work for wrappers, table scans, collision checks, encoding/decoding, and loops.

This prevents the common false theorem "B is efficient" with no evidence about the wrapper. The BR93
example in 2021-156 constructs an inverter from an IND-CPA adversary and proves both the advantage
relation and a bound on the inverter's intrinsic work and random-oracle calls (`2021-156:127-150`,
`2021-156:163-181`). That is exactly what CR18 reductions should record for ROM/guessing proofs:
probability from the game hop, resources from the cost sidecar.

### F.3 `q`-query filters are not a substitute for complexity

The CR18 `[q]` filter is a **semantic interaction bound**: it turns a system into one that stops answering
after `q` queries. It is perfect for birthday bounds and MBO analysis. It does **not** by itself prove:

- the adversary computes each query efficiently;
- the reduction's wrapper computes efficiently;
- the wrapper calls the assumption oracle only polynomially often;
- a simulator has comparable resources to a real-world adversary;
- the environment in a UC/CC theorem is restricted to the intended class.

So the design rule is:

> Use `[q]` to state the game bound; use `γ : Σ → Cost` and `complexityClass γ c` to state the
> computational class.

For a PRF theorem, for example, the concrete CR18 core remains:

```
Δ([q] real, [q] ideal) ≤ PRFAdv([q'] F) + ε(q,n)
```

The computational statement is the derived one:

```
derivedPerf γ_prfGame PRFGame (c_A λ)
  ≤ derivedPerf γ_assumption AssumptionGame (c_B (c_A λ)) + ε(λ)
```

where `c_B` is the cost transformer for the reduction. This is CR18 §4.4.7's `p'(c)` and `ρ'(c)` made
explicit, not a new game semantics.

### F.4 Costed reductions: the missing record

The existing `Reduction p q τ` captures only the **performance** translation:

```
τ ∘ p̄ ≤ q̄ ∘ ρ.
```

For cryptographic reductions we need the 2021-156 side condition too:

```lean
-- design shape only
structure CostedReduction (p q : ProblemObject) where
  rho : Solver p -> Solver q
  perf : ∀ A, τ (p.perf A) <= q.perf (rho A)
  cost : ∀ A, γq (rho A) <= costMap (γp A)
```

The derived theorem then follows the CR18 §4.4.7 interpretation:

```
p'(c) ≤ λ (q'(costMap c))
```

This is the precise place where the EasyCrypt paper's `∀A.∃B` shape enters CR18. If `rho` is a function,
`B = rho A`; if the reduction is existential but not canonical, use a relation or choice witness. The
important invariant is that the advantage witness and cost witness are the **same constructed solver**.

### F.5 Composition and UC/CC are where cost tracking matters most

CR18 already has reduction composition (`reduction_comp`, `upperBound_comp`) and generalized reductions.
The costed layer should mirror those lemmas with composed cost transformers:

```
rho_pq : A -> B,  cost_B <= c_pq(cost_A)
rho_qr : B -> C,  cost_C <= c_qr(cost_B)
------------------------------------------------
rho_qr ∘ rho_pq : A -> C, cost_C <= c_qr(c_pq(cost_A))
```

This is exactly the pain point in 2021-156's UC case study. UC emulation is only meaningful when the
simulator and the environment are restricted to comparable resource classes; unrestricted simulators make
the definition too weak, and unrestricted environments make it too strong (`2021-156:102-117`). Their UC
definition quantifies over simulators and environments with explicit `c_sim` and `c_env` restrictions, and
their transitivity/composition theorems carry cost transformers for composed simulators/environments
(`2021-156:634-720`). The CR18/CC version of `ConstructsWithSim` should therefore have two layers:

1. **behavioral layer:** `Δ(realWorld, idealWorldWithSim) ≤ ε`;
2. **cost layer:** `simCost σ ≤ c_sim(...)` and `envCost Z ≤ c_env(...)`, with composition lemmas updating
   `c_sim` and `c_env`.

This preserves the clean §D story while making it computationally meaningful.

### F.6 Concrete roadmap for the cost layer

1. **Instantiate `Problem` for distinction and win games.** This is the smallest bridge from §B to §4.4.
2. **Define a cost domain.** Start with a finite-label vector `(intrinsic, calls)` and pointwise order,
   close under addition, scalar multiplication, and max.
3. **Define complexity functions for solvers.** Initially axiomatic/declared: `γD : Distinguisher → Cost`,
   `γW : Winner → Cost`, `γZ : Environment → Cost`, `γσ : Simulator → Cost`.
4. **Define derived game performance.** Reuse `derivedPerf γ p c` for "best advantage at budget `c`".
5. **Add `CostedReduction`.** Pair a CR18 performance reduction with a cost transformer.
6. **Add composition lemmas.** Mirror `reduction_comp`, `upperBound_comp`, and product reductions with
   composed cost maps.
7. **Add asymptotics last.** `λ`-indexed families, `PolyBounded` costs, `Negligible` error functions, and
   closure lemmas. Asymptotics should consume concrete costed reductions; it should not replace them.
8. **Do not build a Hoare logic yet.** 2021-156's Hoare logic is a full program-analysis layer. For CR18's
   current design doc, cost certificates can be declared or proved manually for wrappers. A Hoare logic
   becomes relevant only after the project has executable adversary/reduction programs rather than
   semantic solver objects.

---

## §6/§9 — New next-gen machinery a game-based front-end requires (priority order)

1. **Blind converter `b` + sharpen Thm 4.17 to `Γ(bŜ)`** (Def 4.20, eq 4.40; `CR18:5616`,`:5677`).
   *Highest value* — turns "bound `Pr[Z]`" into non-adaptive counting (B.6, §7.4). **In-progress task
   #1.** `b` blocks replies; `Γ(b·)` = `maxWinProb` over `rhoC b`-images (reuses `ReductionByConverter`).
2. **`∆` hybrid telescope** (Lem 2.2): `advantage_telescope` + `maxAdvantage_le_sum` (§6, B.7). Trivial —
   signed `advantage` telescopes definitionally (`Distinguishing.lean:16`). This *is* "sequence-of-games".
3. **Bit-guessing layer** (Def 2.9 + `Λ=∆`, §4, `CR18:1534`): `bitGuessAdvantage` + the `(S_U,U)`-bridge.
   Thin wrapper over `verdictProb`.
4. **`pcoll`/birthday counting lemma** (Lem 4.18): `pcoll(t,q) ≤ ½q²/t`. Combinatorics; finishes the
   switching lemma (§7) and birthday bounds (ch6/8). **Task #2.**
5. **Cost-aware `Problem` layer** (§F): instantiate `Problem` for `∆`/`Γ` games, define the cost vector,
   complexity functions, `CostedReduction`, derived performance, and composition lemmas. This is the
   bridge to 2021-156-style statements `∀A.∃B. adv_A ≤ adv_B+ε ∧ cost_B ≤ costMap(cost_A)`.
6. **The asymptotic wrapper** (§F.6): `Negligible/PolyBounded` algebra + `λ`-indexed `Secure`, over
   cost-indexed derived performance `p'(c(λ))`; absorbs polynomial guessing factors (ch12/13).
7. **The CC layer** (`NEXTGEN_CONSTRUCTIVE_CRYPTO.md`): `ConstructsWithSim`, `epsRelax`, the `T̂⊢`
   bridge to `theorem_4_17_condEquiv`. Carries §D (ZK/AKE/secure-channel). Designed, not built.
8. **The programmable-RO extension** (§E.2): a static shared random oracle at a free interface `F` is
   easy; *adaptive* programming needs a **stateful, converter-controllable** resource whose per-query
   reply is chosen by an attached converter that observes the query first (a request/response converter
   at `F`, not a fixed `PFunPDS`). CC-flavored; needed for ch12/13/15 ROM proofs.
9. **The game-hop compiler / proof DSL** (§B.7): cnl-rs `Let…/RSLemma` + `gameEquiv_winFun_eq`,
   elaborating each hop to its CR18 lemma. Ergonomic surfacing of the §B compiler.
10. *(out of scope / honest non-goal)* **A rewinding + extraction layer** (§E.3): `RewindableWinner`, a
   forking lemma, `Extractor`/`KnowledgeSoundness`. Needed for ch19 special soundness, ch20 PoK. **Does
   not reuse the behavior primitive; a genuine boundary, not a planned item.**

Already done (needs nothing): `∆`, `Γ`, `≡ᵍ`, `|≡`, Lemma 4.15/4.16, adaptive Thm 4.17 (both entry
points), reduction-by-converter `(4.9)/(4.10)`, `σ^q`, `S⁻`, the MBO + `DDS.IsGame`.

---

## §7 — Worked example: PRF/PRP switching lemma (BS Thm 4.4/4.6 ↔ CR18 Lem 4.19)

The §B.2 + §B.6 archetype, line by line.

**BS (game-hop + Difference Lemma, `4-4...md:126`):** Game 0 = random permutation `Pₙ` (faithful gnome,
overrides default `zᵢ` on output-collision); Game 1 = random function `Rₙ,ₙ` (forgetful gnome, drop the
override); bad event `Z` = "`zᵢ=zⱼ` for some `i≠j`"; identical-until-`Z` ⟹ Difference Lemma ⟹
`|Pr[W₀]−Pr[W₁]| ≤ Pr[Z]`; union bound ⟹ `Pr[Z] ≤ Q²/2N`.

**CR18 (cond-equiv + Thm 4.17, `CR18:5723`):** MBO `Aᵢ=1` iff two distinct inputs gave equal outputs
(Ex 4.15, `CR18:5585`) — *this is BS's `Z`*; `R̂ₙ,ₙ |≡ Pₙ` (Ex 4.15, `CR18:5589`) — *"identical until
bad"*; Thm 4.17 ⟹ `∆(Rₙ,ₙ,Pₙ) ≤ Γ(b R̂ₙ,ₙ)` — *the Difference Lemma step as a non-adaptive winning
probability*; `Γ(b[q]R̂) = pcoll(2ⁿ,q) ≤ ½q²2⁻ⁿ` (Lem 4.18) — *BS's union bound*.

| BS step | CR18 step | next-gen |
| --- | --- | --- |
| Game 0 = `Pₙ` / Game 1 = `Rₙ,ₙ` | systems `[q]Pₙ` / `[q]Rₙ,ₙ` | two `PFunPDS X X` |
| bad event `Z` (default collision) | MBO `Aᵢ` (output collision), Ex 4.15 | `Y×Bool`; `MonotoneMBO` `Theorem417.lean:175` |
| identical until bad | `R̂ₙ,ₙ \|≡ Pₙ` | `CondEquiv`=`\|≡` `CondEquiv.lean:115` |
| Difference Lemma `≤ Pr[Z]` | Thm 4.17 `≤ Γ(bŜ)` | `theorem_4_17_condEquiv` `Theorem417.lean:398` (adaptive `Γ(Ŝ)` done; `Γ(bŜ)` = task #1) |
| `Pr[Z] ≤ Q²/2N` | `Γ(bR̂)=pcoll ≤ ½q²2⁻ⁿ` (Lem 4.18) | *needs new*: `pcoll` (task #2) |

The two proofs are **isomorphic**; the only next-gen gaps are the blind-converter form of Thm 4.17
(task #1) and the `pcoll` lemma (task #2) — exactly the two existing tasks.

### §7.4 Why the blind converter matters here

`theorem_4_17_condEquiv` currently proves the **adaptive** `∆(S,T) ≤ Γ(Ŝ)`; the PDF headline is the
**non-adaptive** `∆(S,T) ≤ Γ(bŜ)` with `Γ(bŜ) ≤ Γ(Ŝ)` (`CR18:5605`). For the switching lemma the whole
point (`CR18:5599`) is that the non-adaptive game is easy: the optimal blind strategy picks `q` distinct
inputs, and the collision probability is then `pcoll(2ⁿ,q)` — a one-line "choose distinct inputs"
argument. With only the adaptive `Γ(Ŝ)` one must bound the *adaptive* collision-winning probability,
which is what `b`/`Γ(bŜ)` (task #1) lets us avoid. The scope note at `Theorem417.lean:394` is honest
that `b` (Def 4.20) and the absorption `T̂=T̃·bŜ` (eq 4.40) are deferred.

---

## §10 — Closing assessment

- **Cleanest (done or trivial):** adversary/advantage ↔ `∆`; reduction ↔ `(4.9)/(4.10)`;
  identical-until-bad ↔ monotone MBO + Lemma 4.16/Thm 4.17 (the key match, *more* disciplined than BS);
  sequence-of-games ↔ hybrid lemma. The §A recipe makes encoding mechanical; the §B compiler makes
  hopping mechanical. GGM (ch4) and CBC-MAC (ch6) are showcases.
- **CR18-native:** UHF/AU bounds (ch7), birthday/`pcoll` (ch6/8) — information theory is CR18's home.
- **CC-native:** simulation-based ZK (ch19 HVZK, ch20 ZK/NIZK), AKE (ch21), secure channels (ch9) —
  `ConstructsWithSim` (§D); designed in `NEXTGEN_CONSTRUCTIVE_CRYPTO.md`.
- **Partly outside (expressible with effort):** ROM-programming proofs (ch12/13/15) — the RO is a
  shared resource (§E.2, CC-flavored) and guessing factors are handled by §F's cost/asymptotic layer. No
  rewinding.
- **Genuinely outside (the honest wall):** **rewinding / extraction** — forking lemma, special
  soundness, PoK extractors (ch19 soundness, ch20 PoK, §E.3). The behavior primitive erases the
  adversary's internals; extraction needs them. Needs a dedicated, orthogonal rewinding+extraction layer
  the project does not have and the behavior primitive should not grow into. The ZK *simulator* half
  maps; the *soundness/extractor* half does not.
- **Cost/computational layer:** not part of core `∆`/`Γ`, but CR18 §4.4 already supplies the abstract
  `Problem` and derived-complexity foundation. §F describes the missing cost-aware wrapper and the
  2021-156-inspired cost tuple.

The two existing planning tasks (#1 blind converter `bŜ`, #2 URP–URF switching) are precisely the
top-priority new pieces; everything structural is already proved in next-gen.
