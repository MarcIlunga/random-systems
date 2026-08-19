# A5 - R5 indifferentiability and the R3 discharge

## 0. Source correction and the theorem R5 can actually prove

The literal first sentence of the requested R5 goal is false. Plain
Merkle-Damgard is not indifferentiable from a random oracle: its public chaining
state gives the standard length-extension distinguisher. DRST say this
explicitly immediately before their positive result: the SHA family and other
Merkle-Damgard hashes are examples to which their random-oracle-HMAC theorem
does not apply ([DRST13, Section 4.4, p. 26](../2013-382.pdf#page=26)).
Therefore neither

$$
\operatorname{MD}[f]\approx\mathsf{RO}
$$

nor a Lean theorem named `mdHash_indifferentiable` is a sound R5 target.

The positive source theorem is HMAC-shaped. For R5 it must be adapted to the
canonical C2SP construction

$$
\operatorname{SequenceFunction}(\operatorname{MD}[f],K,S,F;M),
$$

not to `MD[f]` alone. SequenceHash is the instance $K=\emptyset,F=2$ and
SequenceMAC is the instance $K\ne\emptyset,F=1$. The R3 discharge uses the
second instance. This correction does not weaken R3: the frozen R3 hypothesis
already compares the complete SequenceMAC construction with its
role-separated random-oracle schedule, which is exactly the positive shape
that the DRST simulator can deliver.

There is a second important unit correction. DRST's $\sigma$ counts compression
primitive calls, whereas the frozen R3 expression $4q$ counts calls to the
fixed-output hash interface. The correct bound therefore contains an explicit
hash-call-to-compression-cost map. The paper does not justify
$13(4q)^2/2^n$ unless every hash call costs one compression call.

## 1. DRST Theorem 4.4 and its simulator

### 1.1 Exact source statement

Let $d,n>0$ with $d\ge n$, let

$$
f:\{0,1\}^n\times\{0,1\}^d\longrightarrow\{0,1\}^n
$$

be a random compression oracle, and let $\mathcal K\subseteq\{0,1\}^{\le d}$
be an allowed HMAC key set. Allowed means that the first HMAC block admits
functions `GetKey` and `IsOuter` which recover the key and distinguish the
inner and outer pads. For the keyed random oracle
$\mathcal R:\{0,1\}^*\times\{0,1\}^*\to\{0,1\}^n$, DRST Theorem 4.4 gives a
simulator $\sigma_{\rm DRST}$ such that, for total primitive cost
$\Sigma\le2^{n-2}$,

$$
\boxed{
\operatorname{Adv}^{\rm indiff}_{
  \operatorname{HMAC}_d[\operatorname{SMD}[f]],\mathcal R,
  \sigma_{\rm DRST}}
<\frac{13\Sigma^2}{2^n}.}
$$

The simulator makes at most one ideal-oracle query for each direct primitive
query and runs in $O(\Sigma^2\log\Sigma^2)$ time
([DRST13, Theorem 4.4, pp. 26-27](../2013-382.pdf#page=26)). The theorem's
cost is the cumulative compression cost of construction-interface queries plus
the number of direct primitive-interface queries, as defined in DRST Section 2.

Theorem 4.3 is not the needed theorem. It assumes that the underlying hash is
already a random oracle and gives $2\Sigma^2/2^n$. The MD-based result is
Theorem 4.4 with constant $13$.

### 1.2 The two simulator layers

Theorem 4.4 does not use the short table simulator of Theorem 4.3 verbatim. Its
proof composes two layers.

1. **The Lemma 4.5 router.** Replace the final compression call by an
   independent oracle $g$. Maintain a table $T$ of chaining values produced by
   recognized outer-prefix calls. A primitive query $(V,B)$ is sent to the
   $g$-table when $T[V]=1$ and otherwise to the $f$-table. A query from $IV$
   with `IsOuter(B)=1` colors its answer as an outer chaining value. The game
   sequence costs at most $10\Sigma^2/2^n$
   ([DRST13, Lemma 4.5 and Figures 11-12, pp. 27-30](../2013-382.pdf#page=27)).
2. **The Lemma 4.6 extractor.** The inner construction $F[f]$ is made
   preimage-aware. The extractor recovers the pad bits directly, applies
   `GetKey` to the recognized first block, and recovers the remaining MD
   message through the compression graph. DRST then applies the cited
   preimage-awareness-plus-random-oracle composition theorem. Lemma 4.6's
   displayed error is

   $$
   \frac{q_e\ell(q_f+\ell)}{2^n}
   +\frac{(q_f+\ell)^2}{2^n}
   +\frac{q_f}{2^n}.
   $$

   The final accounting is bounded by the remaining $3\Sigma^2/2^n$
   in Theorem 4.4
   ([DRST13, Lemma 4.6, p. 30](../2013-382.pdf#page=30)).

Schematically,

$$
\sigma_{\rm DRST}
=\sigma_{\rm route}[\sigma_{\rm PrA},E].
$$

It lazily samples the colored compression graph, recognizes complete logical
inner and outer chains, records the logical input behind an inner digest, and
uses the ideal keyed random oracle when a matching outer chain completes.
Unrecognized primitive queries remain ordinary lazy random compression points.

## 2. Adaptation to canonical C2SP `SequenceFunction`

### 2.1 The construction, written once

Start from the specification's general construction:

$$
\begin{aligned}
K'&=\operatorname{Derive}_H(K,b),\\
S'&=\operatorname{Derive}_H(S,b),\\
I_{F,K}(M)
  &=\operatorname{HeaderI}(b,F,K)\,\|\,K'\,\|\,
    \operatorname{EncodeItems}(M),\\
Z&=H(I_{F,K}(M)),\\
O_{F,K,S}(M,Z)
  &=\operatorname{HeaderO}(b,F,S,K)\,\|\,S'\,\|\,K'\,\|\\
  &\qquad\operatorname{MSBF}(|M|)\,\|\,
    \operatorname{MSBF}(L)\,\|\,Z,\\
\operatorname{SequenceFunction}(H,K,S,F;M)&=H(O_{F,K,S}(M,Z)).
\end{aligned}
$$

For R5, $H=\operatorname{MD}[f]$ with the actual C2SP-selected native MD
padding/codec. No R5 definition may separately re-spell the SequenceHash or
SequenceMAC inputs or step function. The future Lean model should introduce
one canonical `SequenceFunction` and make the existing instances corollaries,
as required by `PLAN.md`.

### 2.2 The adapted router and extractor

The C2SP simulator is the DRST colored-graph simulator with a richer role
parser.

- A codec-level parser recognizes the block stream of `HeaderI` or `HeaderO`,
  the function indicator $F$, the fixed-width length fields, and the following
  derived blocks. Headers may occupy more than one compression block, so the
  parser colors a recognized path, not merely one first block.
- A `deriveK` table records a long raw key input and its digest; a `deriveS`
  table does the same for the fixed customization. For a short input the padded
  value is read directly. These tables are the C2SP replacement for DRST's
  one-block `GetKey`.
- An `inner` table maps a completed logical tuple $(F,K,S,M)$ to its inner
  digest. A matching completed `outer` chain is answered consistently with the
  ideal logical function. Unrecognized compression queries are sampled from
  the ordinary $f$ table.
- The routing bit is set only after a complete recognized outer prefix. Random
  compression-state collisions remain bad exactly as in Lemma 4.5.

The new codec obligation is a streaming theorem saying that the block stream
recognized by this parser is exactly `codec.blockify` of the canonical byte
input. `MDCodec.blockify_padding` supplies the serialization equality, but the
complete header/parser theorem is not currently present and must be proved at
the canonical `SequenceFunction` layer.

### 2.3 Proven domain separation and the ideal law

The following steps are already proved and are reused, not re-derived.

1. `headerI_ne_headerO` and
   `sequenceMACInnerInput_ne_outerInput` make the complete inner and outer hash
   domains disjoint unconditionally. Thus restriction of one uniform random
   function to those two disjoint domains is a product of independent uniform
   restrictions. This costs **zero probability**. At Lean level this is a
   generic uniform-restriction/product fact; use `uniform_restrict` and the
   existing `Dist` product-map facts, or generalize the joint restriction fact
   publicly in `Dist` if its exact statement is absent.
2. `sequenceMACInnerInput_injective` gives within-inner-role injectivity.
   `sequenceMACSeparatedOuterCall_injective_of_innerTag_injective` and
   `sequenceMACSeparatedOuterInput_injective_of_innerTag_injective` give the
   corresponding conditional outer-role statement. These facts identify the
   logical role restrictions; the later inner-tag birthday event belongs to
   R3's already-proved encoding leg, not to a new R5 aliasing term.
3. `encodeItems_injective` and
   `sequenceHash_collision_of_distinct_inputs` eliminate alternative FIELD
   parses. No ambiguity or prefix-free bad event is added.

After fixing $F=1$, $S$, and the sampled key, the ideal marginal is exactly
`SM_RO_separated`:

$$
(K,U_K,U_S,R_I,R_O),
$$

where $U_K$ and $U_S$ are the two cached derivation answers, $R_I$ is the
uniform inner-tag function, and $R_O$ is the independent uniform function on
the finite active outer-call domain used by `seededHashThenURFGame`. Repeated
calls reuse the same sampled values. Inner/outer independence is therefore
free; only raw `Derive` overlap remains.

### 2.4 The exact Derive residual

The two public lemmas

- `sequenceMACDeriveInput_ne_innerInput_of_not_prefix`, and
- `sequenceMACDeriveInput_ne_outerInput_of_not_prefix`

give the honest conditional result. They do not say that raw $K$ or raw $S$
is always separated from framed inputs.

Write $\operatorname{Pref}(x,y)$ for `List.IsPrefix x y`, and let
$\mathsf{long}_b(X)$ mean $b<|X|$. For a sampled SequenceMAC key $K$, define

$$
\begin{aligned}
\mathsf{DerivePrefixHit}_{b,S}(K):={}&\mathsf{long}_b(K)\ \land\\
&\Bigl(
  (\mathsf{long}_b(S)\land K=S)\\
&\quad\lor\operatorname{Pref}(\operatorname{HeaderI}(b,1,K),K)\\
&\quad\lor\operatorname{Pref}(\operatorname{HeaderO}(b,1,S,K),K)
\Bigr).
\end{aligned}
$$

The first disjunct is the possible collision of the raw `Derive(K)` and
`Derive(S)` inputs. The other two are exactly the prefix hypotheses required
by the two proved domain-separation lemmas when the raw input is `K.val`.

The fixed customization is handled by the explicit side condition

$$
\begin{aligned}
\mathsf{DeriveSafeS}_{b,S}(D_K):={}&\ |S|\le b\ \lor\\
&\forall K\in\operatorname{supp}(D_K),\\
&\quad\neg\operatorname{Pref}(\operatorname{HeaderI}(b,1,K),S)\ \land\\
&\quad\neg\operatorname{Pref}(\operatorname{HeaderO}(b,1,S,K),S).
\end{aligned}
$$

Under that side condition, the precise residual is

$$
\boxed{
\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K)
=\Pr_{K\leftarrow D_K}
  [\mathsf{DerivePrefixHit}_{b,S}(K)].}
$$

This is a key-guessing/prefix-hit mass, not an invented birthday term. The key
is sampled once and reused, so the mass is not multiplied by $q$. If the key
law has a point-mass or min-entropy bound, the displayed mass may later be
bounded by counting the relevant prefix sets; R3 currently assumes only that
$D_K$ is normalized, so the exact event mass is the honest public quantity.
When $K$ and $S$ are both short the term is zero.

## 3. Term-by-term and event-by-event adaptation

`Killed` below means that a deterministic alias/event disappears by a named
SequenceFunction fact. It does not mean that random MD chaining states cannot
collide. Those cascade-inherent events remain.

| DRST term or bad event | SequenceFunction verdict | Reason and resulting contribution |
| --- | --- | --- |
| HMAC colliding/ambiguous key pairs from Sections 4.1-4.3; excluded in Theorem 4.4 by the allowed-key hypothesis | **Killed for the R3 specialization** | SequenceMAC has one internal sampled key, not an adversarial keyed-function interface. `headerI_ne_headerO` removes inner/outer role ambiguity. No related-ipad/opad term applies. |
| Alternative parsing of the logical message/key fields | **Killed** | FIELD framing, `encodeItems_injective`, and `sequenceHash_collision_of_distinct_inputs`; contribution $0$. |
| Lemma 4.5, $G_0\to G_1$: collision-free resampling, $(2\Sigma)^2/2^n=4\Sigma^2/2^n$ | **Remaining** | This is a collision among MD chaining values. Headers remove aliases, not functional-graph collisions. Retain inside the DRST $13\Sigma^2/2^n$ envelope. |
| Lemma 4.5 recoloring at line 10: an inner path reaches an outer-colored state | **Killed as a deterministic role alias; random meeting remains above** | Complete inner/outer inputs are disjoint by `sequenceMACInnerInput_ne_outerInput`. The codec streaming parser is a new proof obligation. |
| Lemma 4.5 line 11: an outer root is already colored as an external-final path | **Killed as role bookkeeping** | The adapted router colors only a completed `HeaderO` path. Multi-block recognition is new, but there is no probability term after recognition is proved. |
| Lemma 4.5 line 12: $K\oplus\mathsf{opad}=K'\oplus\mathsf{ipad}$ | **Killed / not applicable** | This is HMAC related-key ambiguity. SequenceFunction uses distinct header domains and one secret key. Raw derive overlap is not hidden here; it is charged by `DeriveCost_SEQ`. |
| Lemma 4.5 line 20: a primitive query is routed under the wrong inner/outer role | **Killed as a deterministic role alias** | `headerI_ne_headerO` and the role parser. Random chaining-state collision stays in the two $4\Sigma^2/2^n$ rows. |
| Lemma 4.5, line 21 hidden-state hit: $q_1q_2/(2^n-2\Sigma)\le2\Sigma^2/2^n$ | **Remaining in full R5; killed in the R3 marginal** | A full indifferentiability distinguisher may query the primitive directly. R3 exposes no $H/f$ interface, so $q_2=0$. Keeping the full $13\Sigma^2/2^n$ theorem is a safe, non-tight specialization. |
| Lemma 4.5, $G_4\to G_5$: relax collision-free resampling, another $4\Sigma^2/2^n$ | **Remaining** | Cascade-inherent random-state collision. |
| Lemma 4.6, $q_e\ell(q_f+\ell)/2^n$ | **Shrunk only in parsing bureaucracy; probabilistic core remains** | Canonical fields and `encodeItems_injective` make the logical parse unique, but extracting an MD preimage from the compression graph still has this inherent loss. |
| Lemma 4.6, $(q_f+\ell)^2/2^n$ | **Remaining** | Compression-graph/internal collision. |
| Lemma 4.6, $q_f/2^n$ | **Remaining** | Accidental root/output hit in the preimage-aware extractor. No proved C2SP property removes it. |
| Raw long `Derive(K)` and `Derive(S)`, absent from restricted-key HMAC | **New and explicit** | Under `DeriveSafeS`, add exactly `DeriveCost_SEQ`; without that side condition the fixed $S$ overlap is an unresolved structural case. |
| Inner-tag collision causing two logical outside inputs to share an outer call | **Remaining, but already isolated after R5** | It is not an inner/outer domain collision. It is exactly the birthday term proved by `sequenceMAC_separated_encoding_bound`, added by `sequenceMAC_prf_bound_indiff`. |

Thus the adaptation does not copy the HMAC constant blindly. It retains the
source's cascade/preimage-awareness envelope, deletes HMAC-specific ambiguity
bookkeeping, and adds the one C2SP-specific raw-derive mass.

## 4. Exact cost and error functions

For the concrete codec define the compression cost of one fixed-output hash
input by

$$
c_{\rm MD}(x)=|\operatorname{codec.blockify}(x)|.
$$

For at most $Q$ canonical SequenceFunction hash calls and $p$ direct primitive
queries, define

$$
\kappa_{b,S,L}(Q,p)
=p+\max_{\mathcal T:\,\#H(\mathcal T)\le Q}
  \sum_{x\in\mathcal T}c_{\rm MD}(x),
$$

where $\mathcal T$ ranges only over active calls of the canonical
`SequenceFunction` schedule. This maximum is finite in the current bounded
C2SP model. It includes the compression work of raw long derivations.

The source-faithful full R5 error, without attempting to re-optimize DRST's
constant, is

$$
\boxed{
\varepsilon_{\rm R5}(Q,p)
=\frac{13\,\kappa_{b,S,L}(Q,p)^2}{2^n}
 +\mathbf 1_{Q>0}\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K),}
$$

under

$$
\kappa_{b,S,L}(Q,p)\le2^{n-2}
\quad\text{and}\quad
\mathsf{DeriveSafeS}_{b,S}(D_K).
$$

The indicator makes the error zero at zero construction calls. For R3 there
are no direct primitive calls, so $p=0$. One SequenceMAC call makes at most
four calls to $H$:

| Case | Calls to $H$ |
| --- | ---: |
| $K,S$ both short | inner, outer: $2$ |
| exactly one is long | one derivation, inner, outer: $3$ |
| both long | `Derive(K)`, `Derive(S)`, inner, outer: $4$ |

Consequently $q$ outside calls give $Q\le4q$ and the exact R3 specialization
is

$$
\boxed{
\varepsilon_{\rm R5}(4q,0)
=\frac{13\,\kappa_{b,S,L}(4q,0)^2}{2^n}
 +\mathbf 1_{q>0}\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K).}
$$

If a later codec theorem proves $c_{\rm MD}(x)\le\ell_{\max}$ throughout the
active call domain, then
$\kappa(4q,0)\le4q\ell_{\max}$. Only when $\ell_{\max}=1$ does the paper reduce
to $13(4q)^2/2^n$.

## 5. Part (b): composition on the PDS/$\Delta$ surface

### 5.1 Source boundary and metric transport

> **API boundary (2026-07-20).** The direct PDS/`Δ` analysis in §§5.2--5.3
> and theorem shapes in §§7.2--7.3 remain operative. Within §§5--7, references
> to `ResP`, `probMetricAlgebra`, the `edistD_*` bridge names, gated
> `RandomSystemsCC/Sponge.lean`, and optional `ProtocolIndifferentiable`
> packaging are historical, non-importable design notes, not reuse receipts.
> Any future AC packaging requires a fresh audit against the flat AC API and a
> current faithful carrier/action realization.

At the optional AbstractCrypto packaging boundary, instantiate the existing
PDS carrier; do not create a SequenceHash carrier:

$$
\texttt{ResP}\;\sigma
=\texttt{PFunPDS}
  \left(\sum_i\sigma.\mathrm{In}_i\right)
  \left(\sum_i\sigma.\mathrm{Out}_i\right).
$$

`probMetricAlgebra` supplies the metric algebra. To turn an `edistD` upper
bound into R3's one-directional $\Delta$ bound, use
`ofReal_maxAdvantage_le_edistD`; `edistD_eq_maxAdvantage` records the complete
symmetrized equality. `edistD_le_maxAdvantage` points in the other direction
and cannot by itself extract the desired bound.

No `MetricResourceAlgebra`, `ProtocolIndifferentiable`, quotient resource, or
CC carrier appears in the public R3 corollary. Those are generic packaging
only. `RandomSystemsCC/Sponge.lean` is useful as a modeling pattern for a
tagged public primitive, a `ProtocolFn`, and a randomized simulator
`PFunPDC`; it is not a DRST theorem to reuse.

### 5.2 Hiding and converter DPI

Model the full R5 pair as tagged PDS resources exposing a construction
interface and a primitive interface. Apply a projection converter that exposes
only the construction interface. Converter monotonicity gives the marginal
bound; because R3 has no primitive access, the absorbed distinguisher makes
zero direct primitive queries.

For the construction schedule, extract the already-used `Bmax := 4` fact in
`sequenceMAC_ofStep_functionEvaluator` as the public lemma

```lean
theorem sequenceMACStep_answersWithin_four ... :
    PFunConverter.DDC.AnswersWithin (sequenceMACStep b S K) 4
```

and use `maxAdvantage_filterQueries_applyDDC_le` for the deterministic
converter. The sampled key is a common converter coin. If the needed
query-budgeted nonexpansion theorem for `PFunPDC.apply` is not already
available, generalize the deterministic DPI publicly in
`RandomSystems/AbsorbDPI.lean`; do not add a SequenceMAC-local bridge.

After DPI:

1. rewrite the real construction using the canonical `SequenceFunction`
   realization (and retain `sequenceMACSystem_realization` as its $F=1$
   corollary);
2. use `headerI_ne_headerO` and
   `sequenceMACInnerInput_ne_outerInput` to split the shared RO's inner and
   outer restrictions with no loss;
3. use the two conditional derive-separation lemmas, `DeriveSafeS`, and the
   complement of `DerivePrefixHit` to identify the remaining restrictions;
4. integrate the bad-key slice, costing exactly `DeriveCost_SEQ`;
5. rewrite the ideal marginal to the existing `SM_RO_separated` definition.

The PDS calculation is therefore

$$
\begin{aligned}
&\Delta(\lceil q\rceil\mathsf{SM}_{\rm MD[f]},
        \lceil q\rceil\mathsf{SM}_{\rm RO,sep})\\
&\quad\le
\frac{13\,\kappa_{b,S,L}(4q,0)^2}{2^n}
+\mathbf1_{q>0}\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K)\\
&\quad=\varepsilon_{\rm R5}(4q,0).
\end{aligned}
$$

Inner/outer separation contributes zero. The only C2SP schedule residual is
the displayed Derive term. The cascade/internal-collision loss is already
inside the DRST part of $\varepsilon_{\rm R5}$.

### 5.3 Exact frozen-hypothesis discharge

Let the function supplied to R3 satisfy

$$
\varepsilon_{\rm ind}(4q)\ge
\frac{13\,\kappa_{b,S,L}(4q,0)^2}{2^n}
+\mathbf1_{q>0}\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K).
$$

Then the preceding PDS inequality is exactly

$$
\boxed{
\texttt{h_indiff}:
\Delta(\lceil q\rceil\texttt{SM_H b S DK D_H},
       \lceil q\rceil\texttt{SM_RO_separated b S DK})
\le\varepsilon_{\rm ind}(4q).}
$$

It is passed directly to `sequenceMAC_prf_bound_indiff`; that theorem adds the
already-proved `pairCollisionUnionBound (HashOutput L) q` by one
`maxAdvantage_triangle`. No H-technique `Adv`/`advPRF`, game object, or CC
carrier is introduced.

## 6. Infrastructure map: reuse versus new

| Layer | Verdict | Exact item |
| --- | --- | --- |
| Canonical construction | **New/generalize in place** | One `SequenceFunction` model and converter; existing SequenceHash/SequenceMAC definitions become instances/corollaries. |
| FIELD separation | **Reuse** | `encodeItems_injective`, `sequenceHash_collision_of_distinct_inputs`. |
| Inner/outer separation | **Reuse** | `headerI_ne_headerO`, `sequenceMACInnerInput_ne_outerInput`; zero loss. |
| Within-role injectivity | **Reuse** | `sequenceMACInnerInput_injective`, `sequenceMACSeparatedOuterCall_injective_of_innerTag_injective`, `sequenceMACSeparatedOuterInput_injective_of_innerTag_injective`. |
| Derive separation | **Reuse plus one named event** | The two `sequenceMACDeriveInput_ne_*_of_not_prefix` lemmas; new public `DerivePrefixHit_SEQ`, `DeriveSafeS_SEQ`, and `DeriveCost_SEQ` definitions. |
| Concrete systems | **Reuse** | `SM_H`, `SM_RO_separated`, active-call domain, `sequenceMACSystem_realization`; refactor only through canonical `SequenceFunction`. |
| PDS DPI | **Reuse/generalize generically if needed** | `maxAdvantage_filterQueries_applyDDC_le`; a common-coin `PFunPDC.apply` extension belongs in `AbsorbDPI.lean`, never in SequenceHash. |
| Triangle and encoding leg | **Reuse** | `maxAdvantage_triangle`, `sequenceMAC_separated_encoding_bound`, `sequenceMAC_prf_bound_indiff`. |
| Uniform role restrictions | **Reuse/generalize generically if exact joint form is absent** | `uniform_restrict`, `Dist.prod`/product-map facts. |
| PDS metric packaging | **Reuse** | `probMetricAlgebra`, `ofReal_maxAdvantage_le_edistD`, `edistD_eq_maxAdvantage`; `edistD_le_maxAdvantage` only in its valid direction. |
| PDS indiff modeling pattern | **Reuse pattern** | `RandomSystemsCC/Sponge.lean` for tagged worlds, `ProtocolFn`, and `PFunPDC` simulator. |
| CR18 switching/counting | **Reuse where the DRST graph leaf matches** | Existing birthday/counting and mass-union facts; do not replace the weighted $\kappa$ accounting by an unweighted query bound. |
| C2SP DRST proof | **New application proof** | Codec streaming parser, colored role graph, derive tables, extractor, and the adapted Lemmas 4.5/4.6. |

The current `RandomSystemsCC.Conv` exposes only the simple memoryless fragment.
Packaging the multi-call construction as generic `ProtocolIndifferentiable`
therefore requires a generic full-DDC/`PFunPDC` converter extension. This is a
converter-fragment gap, not a resource-carrier gap, and it does not block the
plain PDS/$\Delta$ R3 corollary.

## 7. Proposed R5 Lean statement shapes

These are guardrail shapes for a later Lean task; no Lean definitions are
added by this sketch.

### 7.1 Full adapted indifferentiability theorem

The primary theorem must be about `SequenceFunction(MD[f])`, not `MD[f]`:

```lean
theorem sequenceFunction_md_indifferentiable
    (Q p : Nat)
    (hS : DeriveSafeS_SEQ b S DK)
    (hcost : sequenceFunctionCompressionCost codec b S L Q p <= 2 ^ (n - 2)) :
    exists simPDC,
      DeltaCost Q p
        (sequenceFunctionMDPublicWorld codec b S F DK Df)
        (sequenceFunctionROPublicWorld b S F DK simPDC)
      <= drstError (sequenceFunctionCompressionCost codec b S L Q p)
         + (if Q = 0 then 0 else DeriveCost_SEQ b S DK)
```

`DeltaCost` denotes the required generic weighted/tagged query filter. If the
implementation instead takes total primitive cost $\Sigma$ directly, the
right side is exactly $13\Sigma^2/2^n+\operatorname{DeriveCost}_{\rm SEQ}$.
An optional `ProtocolIndifferentiable` corollary may package this theorem after
the full-DDC converter generalization; it must not reprove it.

### 7.2 PDS theorem with the explicit Derive term

Let `mdHashDist codec Df iv` be the pushforward of the compression-function
law through `mdHash codec · iv`. The direct PDS specialization should have the
following conclusion:

```lean
theorem sequenceMAC_md_indiff_bound {L : U128}
    (q : Nat) (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (Df : RandomSystems.Dist (Compression State Block))
    (hDK : DK.isProbDist) (hDf : Df.isProbDist)
    (hS : DeriveSafeS_SEQ b S DK)
    (hcost : sequenceFunctionCompressionCost codec b S L (4 * q) 0
      <= 2 ^ (n - 2)) :
    Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
      ⌈q⌉ SM_RO_separated b S DK)
      <= drstError
          (sequenceFunctionCompressionCost codec b S L (4 * q) 0)
        + (if q = 0 then 0 else DeriveCost_SEQ b S DK)
```

The actual header will carry the codec/state finiteness premises required by
the existing PDS model, but the mathematical right-hand side must retain both
the compression-cost translation and the explicit Derive mass.

### 7.3 Corollary in the byte-for-byte R3 shape

```lean
theorem sequenceMAC_md_h_indiff {L : U128}
    (q : Nat) (b : BlockSize) (S : ByteString)
    (DK : RandomSystems.Dist SequenceMACKey)
    (Df : RandomSystems.Dist (Compression State Block))
    (epsilon_ind : Nat -> NNReal)
    (hDK : DK.isProbDist) (hDf : Df.isProbDist)
    (hS : DeriveSafeS_SEQ b S DK)
    (hcost : sequenceFunctionCompressionCost codec b S L (4 * q) 0
      <= 2 ^ (n - 2))
    (hepsilon :
      drstError (sequenceFunctionCompressionCost codec b S L (4 * q) 0)
          + (if q = 0 then 0 else DeriveCost_SEQ b S DK)
        <= epsilon_ind (4 * q)) :
    Δ(⌈q⌉ SM_H b S DK (mdHashDist codec Df iv),
      ⌈q⌉ SM_RO_separated b S DK)
      <= (epsilon_ind (4 * q) : Real)
```

This conclusion is the frozen `h_indiff` expected at
`SequenceMACIndiff.lean:324`. Passing it to
`sequenceMAC_prf_bound_indiff` is the G5 guardrail.

## 8. Conclusion

DRST do not prove plain MD indifferentiable from a random oracle. They prove
that a restricted-key HMAC-shaped construction over `SMD[f]` is
indifferentiable, using a colored routing simulator plus a preimage-aware MD
extractor. Canonical C2SP `SequenceFunction` has stronger FIELD and
inner/outer separation than HMAC, so ambiguity and related-pad events vanish
and inner/outer RO independence is free. Its extra raw derivation calls are
not unconditionally separated; their exact remnant is `DeriveCost_SEQ` under
the stated fixed-$S$ side condition. After the source theorem is transported
to PDS, hiding the primitive and applying converter DPI yields the frozen R3
$\Delta$ hypothesis at $4q$ hash calls, with the honest compression-cost map
inside $\varepsilon_{\rm ind}$.
