/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.LawCoupling
import RandomSystems.Jost.Combinators
import RandomSystems.Jost.Systems
import RandomSystems.Jost.Construction
import RandomSystems.Jost.Surface
import RandomSystems.Jost.SurfaceAttach
import RandomSystems.Jost.SurfacePar
import RandomSystems.Jost.SecureChannel
import RandomSystems.Jost.OTP
import RandomSystems.Jost.SurfaceLint
import RandomSystems.Jost.SurfaceTactics
import RandomSystems.Jost.SurfaceBridge
import RandomSystems.Jost.SurfaceGrammar
import RandomSystems.Jost.SurfaceConverterGrammar
import RandomSystems.Jost.SurfaceDelab
import RandomSystems.Jost.SurfaceWidgets
import RandomSystems.Jost.SurfaceCarrier
import RandomSystems.Jost.SurfaceShuffle
import RandomSystems.Jost.SurfaceMergeLocality
import RandomSystems.Jost.SurfaceMergePar
import RandomSystems.Jost.SurfaceGamma
import RandomSystems.Jost.SurfaceNames
import RandomSystems.Jost.SurfaceChannels
import RandomSystems.Jost.SurfaceAlgebra
import RandomSystems.Jost.SurfaceLatex
import RandomSystems.Jost.SurfaceGallery
import RandomSystems.Jost.SurfaceMoves
import RandomSystems.Jost.SurfacePanel

/-!
# Jost §2.2 top to bottom: the pseudocode DSL over random systems

This folder reproduces the Jost thesis's worked example (§2.2.6,
Prop. 2.2.17 — a confidential channel from an authenticated channel and a
shared key) **entirely at the package (`Machine`) level**, as the
integration test for the claim that Fig.-2.2-style pseudocode boxes can be
first-class Lean objects whose denotation is the library's PDS carrier and
whose proof obligations are dischargeable without ever unfolding to raw
partial history functions.

## Layer map

| thesis object | here | file |
|---|---|---|
| pseudocode box (Def 2.2.1 resource) | `Machine` / `InterfaceMachine` | `ResourceMachine.lean` (pre-existing) |
| `Initialization x ←$ X` | seed-indexed family + `Machine.lawOf` | `ResourceMachine.lean` (pre-existing) |
| `[R, S]` (Fig. 2.1, DISJOINT interface sets) | `Machine.par` | `Jost/Combinators.lean` |
| `call y ← (kwd, x) at int. I of R` | `Prog` + `Converter.attach` | `Jost/Combinators.lean` |
| "couple on the key, compare transcripts" | `Machine.lawOf_congr` / `lawOf_eq_of_coupling` (+ `toDDS_eq_of_bisim` per fibre); Δ-face `lawOf_lawStatDist_le_of_coupling` for bad seed sets | `Jost/LawCoupling.lean` |
| AuthChan, Key (Fig. 2.2) | `JostFigure22.authChan`, `keyMachine` | `ResourceMachine.lean` (pre-existing) |
| SecChan, CPA_b (Fig. 2.4b) | `secChan`, `cpaMachine` | `Jost/Systems.lean` |
| π_E (Fig. 2.3), σ_E (Fig. 2.4a), reduction c | `piConv`, `sigmaConv`, `cConv` | `Jost/Systems.lean` |
| Prop. 2.2.17's two identities | `realMachine_toDDS_eq_gameMachine`, `idealMachine_toDDS_eq_gameMachine` | `Jost/Construction.lean` |
| Prop. 2.2.17 | `real_eq_game`, `ideal_eq_game`, `construction` | `Jost/Construction.lean` |

## The authoring surface (2026-08-04 second round)

Thesis vocabulary over the kernel, kernel names confined to bodies
(§10.11 discipline; one sanctioned bridge section):

| thesis notion | surface name | file |
|---|---|---|
| Def 2.2.1 resource (behavior; `=` IS behavioral identity) | `CC.Resource F` / `CC.ResourceAt S layout` | `Jost/Surface.lean`, `Jost/SurfaceAttach.lean` |
| interface alphabets / Fig. 2.2 box / Initialization block | `CC.Interfaces`, `Realization`, `Resource.ofState`/`sampleInit` | `Jost/Surface.lean` |
| what an interface provides (kernel codes) | `CC.Services` (+ `Services.free`, the sum-closure a MERGE of two interfaces lands in) | `Jost/SurfaceAttach.lean`, `Jost/SurfacePar.lean` |
| Def 2.2.2 converter, `π R` | `CC.Converter.ofRounds`/`ofMaps`; attachment now `α •[i] R` (`Converter.attachAt`, TOTAL — the layout-indexed `ResourceAt.attach` is demoted with successor) | `Jost/SurfaceAttach.lean`, `Jost/SurfaceCarrier.lean` |
| Prop 2.2.3 order independence | `Converter.attachAt_comm` (bare `=`; the HEq form is demoted) | `Jost/SurfaceCarrier.lean` |
| `[R, S]` at DISJOINT interface sets (Jost §2.2.2, p. 17) and Maurer11 eq. (3) | `∥ : ResourceSystem S I → ResourceSystem S J → ResourceSystem S (I ⊕ J)` with `close_par` in `≈[ε]` notation (`edist_par_le` demoted); `Φ` is a family indexed by interface sets, which costs Maurer11 Def. 1 nothing — fn. 9 constrains ATTACHMENT, still an endo-operation | `Jost/SurfacePar.lean`, `Jost/SurfaceCarrier.lean` |
| Jost Prop. 2.2.3 (2), `π^γ [R,S] = [π^γ R, S]` | `Converter.attachAt_par_left` — a plain `=`, total, no coding | `Jost/SurfaceCarrier.lean` |
| Jost Thm 2.2.5 (2), parallel composability | `Converter.close_par_attachAt_left` — from a construction for `R`, one for `[R,T]` at the same ε | `Jost/SurfaceCarrier.lean` |
| Jost's connection function `γ : I_in ↪ I_P` (p. 18), two-interface case | `Connection K rest`, `α ••[γ] R` (`Converter.attachAlong`) = `π^γ R`, at interface set `rest ⊕ Unit` = `(I_P \ img γ) ∪ I_out`; merge-then-attach, the merge an isometry (`close_mergeAlong`) | `Jost/SurfaceCarrier.lean` |
| renaming an interface set | `ResourceSystem.reindex` along a bijection, an isometry **in both directions** (`close_reindex_iff`) — the contrast with `mergeAlong`, which is an isometry but not invertible | `Jost/SurfaceShuffle.lean`, `RandomSystems/TypedInterfaceRelabel.lean` |
| `∥` commutative and associative (Maurer/Jost treat it as such) | `ResourceSystem.par_comm`, `par_assoc` — plain equalities up to `reindex`, with `≈[0]` forms; the content is that `PFunDDS.par` is symmetric/associative under the swap and associator relabellings, lifted through the four-level tower | `Jost/SurfaceShuffle.lean`, `RandomSystems/TypedTensorShuffle.lean` |
| Jost Prop. 2.2.3 (1) at γ | `Converter.attachAlong_comm` — two connections commute when `img γ₂` misses `img γ₁`; a plain `=`, no transport.  A γ-attachment is *re-address then act*: the ACTIONS commute, the merges cannot (they change the interface set) | `Jost/SurfaceGamma.lean` |
| Jost Prop. 2.2.3 (2) and Thm 2.2.5 (2) at γ | `Converter.attachAlong_par_left`, `Converter.close_attachAlong_par_left` — up to one explicit renaming, at the same ε | `Jost/SurfaceGamma.lean` |
| the two kernel facts under the γ algebra | merging is LOCAL (`ResourceSystem.mergeAlong_attachAt_untouched`, via `PFunConverter.General.IsPullback`) and merging inside a factor is merging the factor (`ResourceSystem.mergeAlong_par_left`) | `Jost/SurfaceMergeLocality.lean` + `RandomSystems/TypedPullback.lean`, `Jost/SurfaceMergePar.lean` |
| Maurer11 Def. 1 completed: `id`, serial `∘`, blocking `⊣[i]`; MaRuTa12 Def. 2 two-condition `Constructs` + Thm 1; JosMau20 Prop. 1 | `SurfaceAlgebra` (`Σ` at an interface = the kernel converter monoid; `id•R=R` is `one_smul`) | `Jost/SurfaceAlgebra.lean` |
| the channel calculus: `—→`, `•—→`, `—→•`, `•—→•`, `•══•` (MaRuTa12 §1.3) | `Channels.*` with `cc_display` glyphs, roles, LaTeX forms | `Jost/SurfaceChannels.lean` |
| paper typography: display names, roles (Maurer11's palette), LaTeX export | `cc_display`/`cc_latex`/`cc_role`; `#cc_latex` emits the paper equation (`\equiv` for `=`) from checked terms; Fig-1 dashed-box diagrams | `Jost/SurfaceNames.lean`, `Jost/SurfaceLatex.lean`, `Jost/SurfaceWidgets.lean` |
| the visual design system (DESIGN §12 items 8–11): positioned-coordinate diagrams, visual test corpus, gallery generator (`.lake/cc_gallery.html`) + in-browser geometry audit | `Diagram.html` (fixed grid, geography, buses, boundary crossings), `#cc_gallery`, `Gallery.auditScript` | `Jost/SurfaceWidgets.lean`, `Jost/SurfaceGallery.lean` |
| §2.2.6 at the behavioral quotient | `CC.SecureChannel.real/ideal/game`, `construction` | `Jost/SecureChannel.lean` |

| the one-time pad (a resource identity that is NOT a law equality) | `CC.OTP.otp_real_eq_ideal` via `sampleInit_eq_of_flatten_equivalent`; creative core `otp_transcript` | `Jost/OTP.lean` |
| Maurer11 Def. 1's Φ: total attachment `α^i R`, plain-`=` order independence, `≈_ε`/eq.(3)/(4) | `CC.ResourceSystem`, `α •[i] R` (`Converter.attachAt`), `attachAt_comm`, `≈[ε]`, `close_par`/`close_attachAt` | `Jost/SurfaceCarrier.lean` |
| MauRen16 §3.3's neutral converter, at the converter (not the `Σ`-word) | `Converter.attachAt_id` — the `e = f = Equiv.refl` case of *a memoryless bijection converter is a relabelling* (`DependentDDS.flatten_attach_ofMaps_eq_relabel`, `TypedFraming.lean`) | `Jost/SurfaceCarrier.lean` |
| MaRuTa12 Def. 2's `⊥` / MauRen16 §3.4's `⊣` and its three laws | `ResourceSystem.block_idem`, `block_comm`, `close_block` — off `Converter.ofMaps_eq_of_no_input` (*a memoryless converter with an empty outer alphabet IS `ofMaps id id`*) and `ResourceSystem.layoutAt_eq_of_close` (*`≈[ε]` already fixes the layout*) | `Jost/SurfaceAlgebra.lean`, `Jost/SurfaceCarrier.lean` |
| Jost Fig. 2.3's π_ε^A: a converter reaching TWO interfaces (A of `Key` and A of `AuthChan`), inner side the PAIRED service | `CarrierDemo.encA`/`decB` with the connections `gammaU`/`gammaV`, and the flagship `constructedShape = dec^{γ^B} enc^{γ^A} [KEY, AUT] : ResourceSystem demoServices (Unit ⊕ Unit)` built from them | `Jost/SurfaceCarrier.lean` |

The OTP file is the surface's acid test: the real (XOR) and ideal (uniform
ciphertext) laws have disjoint supports over deterministic systems — no
coupling can close them — yet they are the *same resource*; the proof is
the classic argument (pre-send the worlds are indistinguishable; after the
first message `m₀` the seed pairing `k ↦ m₀ XOR k` matches transcripts),
finished by `Dist.fTransform_bijection_uniform`.

## What is proved

Both leaves are **law equalities** — the strongest possible form: under the
identity coupling of the shared seed `(key, tape)`, the composite packages
are pointwise bisimilar, hence denote equal distributions over
deterministic resources.  Consequently the headline needs no metric: every
functional Φ of the (real, ideal) pair equals its value on
`(c CPA_0, c CPA_1)`, which is the thesis's `ε(D) := Δ^{Dc}(CPA_0, CPA_1)`
transport with the distinguisher class left abstract and zero slack.
`dec_enc` (perfect correctness) is consumed exactly once, in leaf 1's
Bob clause — precisely where the thesis says "by correctness".

## Randomness discipline

The carrier is `Dist` over deterministic systems (CR18 Def 3.14), so all
sampling is eager: probabilistic encryption takes an explicit randomness
argument fed from a pre-sampled finite tape (`Fin cap → R`), totalized by
`default` past `cap` (`tapeAt`).  No machine carries a query cap or a guard
branch; past `cap` both sides of every identity reuse the same junk entry,
so the identities are unconditional — `cap` only calibrates for how many
challenge queries the CPA games mean real IND-CPA.

## Deliberate scope boundaries (bridge receipts, deferred)

* `Machine.par` / `Converter.attach` are the DSL's own composition
  operations.  Their agreement with the PFun-layer attachment
  (`ProtocolFn`, `PFunConverter.General.attachAt`, `TypedAttachment`) is a
  wiring receipt of the same kind as the RS↔AC ledger (STATUS.md §11) and
  is not claimed here.
* The protocol is one global converter with identity clauses at `E`/`F`
  rather than a per-party tuple; composition-order independence
  (Prop. 2.2.3) is therefore never invoked.
* π_B fetches the key per use instead of at initialization (converters
  have no init block); `Key` answers constantly, so the denotations agree.

The general ingredients live upstream, in place: `Dist.fTransform_congr`,
`Dist.fTransform_eq_of_coupling`, `Dist.mass_mono_on_support` (`Dist.lean`),
`HTechniqueDerivation.lawStatDist_fTransform_le_mass_ne`
(`HTechnique/Derivation.lean`), `JostFigure22.logLookup_map`
(`ResourceMachine.lean`).
-/

/-! The standing §10.11 gate: every build of this umbrella audits the tagged
surface statements for kernel-vocabulary leaks. -/
#cc_surface_audit
