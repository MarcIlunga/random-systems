# CR18 PFun Modeling Notes

Guidance for the CR18 PFun formalization in `random-systems`. The model is built
against Maurer's lecture notes `CR18_LN.pdf` (pdftotext at `papers/CR18_LN.txt`).
Keep this file synthesized — fold repeated corrections into the principles below
rather than appending a running log.

## Scope and process

- The PFun model lives in parallel to the existing CR18 files. Switch consumers
  over deliberately, not incidentally.
- `HCTR2/Proofs/CR18/Sketch.lean` is downstream context — do not edit it while
  building the PFun model.

## General modeling discipline

- **Stay close to the paper.** Check every modeling decision against `CR18_LN.pdf`.
  If the Lean proof stops resembling Maurer's, the *model* is wrong, not the proof.
- **A hard "constructed object = intended object" bridge means the model is wrong.**
  When a proof needs a painful lemma equating some built object with the target,
  re-model instead of grinding. Maurer's random-variable / sequence views usually
  make the event separable, or the equality definitional, for free (see the
  transcript under §3.6).
- **Algebraic, not operational.** Prefer equational definitions and notation over
  helper functions. No operational drivers, simulation loops, or fuel-bounded
  interpreters as the *public* model — finite internal transcripts/histories are
  private proof witnesses only.
- **No speculative scaffolding.** Do not add helper predicates, well-formedness
  conditions, or wrappers with no paper definition and no immediate consumer
  (definition, construction, or theorem). Delay them until the exact paper step is
  being formalized; delete them if they go unused.
- **Types carry the math.** Labels are labels only — put payloads in cartesian
  products, never in payload-carrying constructors. Prefer direct sum/union/product
  type expressions over helper abbrevs (`Input`, `Output`) when the paper expression
  is readable. Match lengths in the types.
- **Public APIs expose paper objects** — DDSs, DDCs, filters, resources, transcripts,
  behaviors — never execution traces, parser histories, or graph relations introduced
  as implementation devices.

## DDS, DDC, converters

- A **DDS** is a partial function with the paper's side conditions (nonempty domain,
  prefix closure), not an operational simulator.
- A **DDC** is just a DDS over converter alphabets. Do not introduce a separate
  converter structure, raw wrapper, or `toDDS` before it is requested. Use one small
  label type (`inside`/`outside`) and build alphabets as unions of cartesian products,
  with notation for the disjoint union; do not over-label.
- **Converter application is a DDS-level construction** `DDC.apply α S : DDS U V`
  (Def 3.9). Internal transcript / input-output relations stay private — used only to
  discharge the nonempty-domain and prefix-closure obligations.
- **Filters are converters** of type `DDC X Y X Y`; `Filter.apply φ S = DDC.apply φ S`.
  State filter theorems about the resulting DDS — e.g. the query-limit filter `[q]`
  forwards the first `q` outside queries and is undefined on the `(q+1)`-st, so
  `dom([q]S) = {l ∈ dom S | l.length ≤ q}` — not about the converter's internal history.
- **Paper-facing converter equations are extensional DDS equalities.** `casc[S,T]=S⊲T`,
  `comb⋆[S,T]=S⋆T`, and the like mean equality of the underlying partial functions,
  comparing the native DDS against the DDS obtained by `DDC.apply` of the *actual*
  converter. Do not redefine the converter side to be the native DDS to force `rfl`. A
  one-sided domain/output inclusion is not the paper statement unless explicitly marked.
- If such an equality degenerates into malformed raw-history parser cases, the fix is in
  the converter-description layer: give `casc`/`comb⋆` typed canonical prefix
  descriptions, prove the raw parser realizes them, then use the typed descriptions in
  the main proof. (Def 3.11 cascade and Def 3.12 output-combine — domain intersection,
  output `op (S l) (T l)` — both follow this shape, with parallel access to `[S,T]`.)
- **Keep notation roles distinct.** Native PFun cascade `⊲ₚ`; converter application `·ᶜ`;
  converter-side cascade/combine `cascᶜ[…]` / `comb⋆ᶜ[…]`. Expose `combine`, `⋆ₚ[…]`,
  `combineConverter`; keep phase parsers private. Cascade symbols are for cascade — do
  not reuse arrows/triangles that collide with `⊲`.

## §3.6 behavior and transcripts

- **Behavior and cumulative behavior are functions/kernels** over DDS samples
  (`p^S_{Yᵢ|XⁱYⁱ⁻¹}`, `p^S_{Yⁱ|Xⁱ}`), length-matched in the types. No transcript machines
  or operational stepping as the public model.
- **Reuse the `outSeq`/`prevOut` API.** The list↔conjunction converters
  (`outSeq_eq_map_iff`, `prevOut_take_eq_map_iff`) and structural lemmas (`outSeq_snoc`,
  `prevOut_eq_outSeq_dropLast`, `getElem_outSeq`, `outSeq_length`) are the reusable
  bridge between the `List`-valued behavior RVs and index-based reasoning. The
  list↔index impedance is real: when a new bridge is needed, add it as a NAMED API
  lemma — never inline it into a proof, never delete it as "dead code".
- **Telescoping uses `mass_biForall_lt_eq_prod`** (the generic NNReal chain rule). Do
  not re-derive the telescoping by induction (Mathlib's `Finset.prod_range_div` needs a
  `CommGroup`, which NNReal-with-division is not). On top of the API, Eq 3.2
  (`cumulativeBehaviorOf_eq_behaviorOf_prod`), its inverse the conditional/cumulative
  conversion (`behaviorOf_eq_cumulative_div`), and the consistency condition
  (`outSeq_take`) are all short.
- **Games/winners/distinguishers ride the exclusion chain — no structures, no side
  predicates.** The framework refines by *exclusion subtypes* and lifts to PDS by *codomain*:
  `Raw —Valid→ DDS —IsGame→ DDG`, with `PDS = RV valued in DDS`, `PDG = RV valued in DDG`.
  "Being refined" is carried by the type, not a free-floating predicate.
  - **Def 3.22 (game).** `IsMBO` is a property of a **`List (Y × Bool)`** — literally
    `Monotone (fun i : Fin l.length => (l.get i).2)` (the monotone-Bool subset; Mathlib
    `Monotone` + `Bool`'s `false ≤ true`). The *system never appears in it*. A game is then a
    DDS whose `outputHistory` along every in-domain input prefix is `IsMBO`:
    `DDS.IsGame g := ∀ l hl, IsMBO (outputHistory g l hl)`; `DDG := { g : DDS X (Y×Bool) // g.IsGame }`.
    `PDG Ω X Y := Dist.RV Ω (DDG X Y)` — an RV ranging over games, NOT a predicate `IsPDG` on
    an arbitrary PDS.
  - **Def 3.23 (winner).** A winner for an `(X,Y)`-game *is* a `(Y,X)`-environment (reads the
    visible `Y`-outputs, issues `X`-queries; MBO bit hidden) — so `Winner X Y := DDE X Y`, an
    alias, no new type.
  - **Def 3.24 (distinguisher).** `DDD X Y := { d : List (Option Y) → X ⊕ Bool // StopFinal d }`.
    Two stop symbols `⊣₀,⊣₁` → output `X ⊕ Bool` (query `inl`, verdict-stop `inr b`), the sum
    directly — no payload-carrying `Step` inductive. **DDE/DDD asymmetry:** a DDE's stop `⊣`
    carries no output so a bare function suffices; a DDD's stop carries a *verdict*, so it gets
    the carving predicate `StopFinal d := ∀ {h h'}, h <+: h' → ∀ b, d h = .inr b → d h' = .inr b`
    (once it emits a verdict it emits the same one on every extension — the answer is final).
  - Execution/winning (`Wins`, distinguisher output) lives on the record model in `CR18/Game.lean`;
    don't add those as free-floating predicates on the PFun side until a consumer needs them.
- **Model the transcript as Maurer's list of random variables** — `Yᵢ = S(x¹…xⁱ)`,
  `Xᵢ = E(y¹…yⁱ⁻¹)` — not as the law of the deterministic recurrence `PFunDDS.transcript`.
  Then the transcript event is separable by construction (system part on `ω₁`,
  environment part on `ω₂`) and Lemma 3.2 (`transcriptDist_eq_mul`) factors via
  `Dist.mass_prod_and` in one step. The recurrence model instead forces a hard
  separability induction — it is the wrong model. The environment is the dual system
  `E : RV Ω₂ Y X` (Def 3.21), one step behind the system (`xᵢ = E(yⁱ⁻¹)`, `yᵢ = S(xⁱ)`).

## Notation

- **PDS/PDE are uppercase** (`S`, `E` — the random variables); **DDS/DDE are lowercase**
  (`s`, `e` — the deterministic values).
- Notation roles stay separated (see converters): distinct symbols for native
  constructions, converter application, and converter-side constructions.
