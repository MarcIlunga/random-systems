# R2 pen-and-paper sketch: SequenceMAC PRF security

The proof should be a SequenceMAC-to-framed-NMAC bridge followed by Gaži–Pietrzak–Rybár verbatim. The bridge cannot be omitted: Gaži proves two-key NMAC, while SequenceMAC derives its inner and outer states from one byte key. Gaži §1.2 explicitly requires data-input PRF security and a related-key assumption for single-key HMAC. Thus the Lean guardrail must expose a key-schedule loss rather than derive security from ordinary chaining-input PRF security alone.

## (a) OBJECTS

### MD and compression model

Let:

- `B` be the finite type of one compression block.
- `C` be the finite chaining/output type, with $N = |C|$. For an $L$-byte digest, $N=256^L$.
- $f : C \to B \to C$, keyed by its chaining input, exactly as in Gaži §2.2.
- `IV : C`.
- `blockify : List Byte → List B` be byte-to-block conversion including the hash’s native MD padding/strengthening.

Define

$$
\operatorname{Casc}_f(k,[m_1,\ldots,m_r])
  = \operatorname{foldl}(\lambda y\,m.\,f(y,m))\,k\,[m_1,\ldots,m_r]
$$

and

$$
MD[f](x)=\operatorname{Casc}_f(IV,\operatorname{blockify}(x)).
$$

The public MD model belongs in the planned `RandomSystems/MDHash.lean`. No public MD definition currently exists; local search found only the quarantined `RandomSystems.Applications.BonehShoup6_4.cascadeEval` in `RandomSystems/Legacy/Applications/BonehShoupCascade.lean`. The public definition should promote/generalize that fold rather than create a second specialized cascade.

Required codec laws:

1. `blockify` realizes the chosen byte-level MD padding.
2. Each result consists of full blocks.
3. MD strengthening is prefix-free, or the Gaži fresh-block transformation below is available.
4. Splitting at a block boundary commutes with iteration:
   $$
   \operatorname{Casc}_f(k,x\mathbin{+\!\!+}y)
   =\operatorname{Casc}_f(\operatorname{Casc}_f(k,x),y).
   $$

`REUSE:List.foldl_append`, `REUSE:List.foldl_concat`.

### SequenceMAC over MD

Reuse the concrete byte framing from [Spec.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/Spec.lean):

- `SequenceHash.pad`
- `SequenceHash.derive`
- `SequenceHash.headerI`
- `SequenceHash.headerO`

and from [Encoding.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/Encoding.lean):

- `encodeItems`
- `encodeMSBF`
- `encodeItems_injective`
- `encodeMSBF_injective`.

Use `F = fSeqMac = 1`. For a fixed key length $\kappa\ge 32$, take

$$
\mathrm{MacKey}_\kappa=\{K:\mathrm{List\ Byte}\mid |K|=\kappa\},
$$

sampled uniformly. A variable-length key distribution can be supported later, but fixed $\kappa$ gives the finite uniform key space expected by the current PRF surface.

For key $K$, customization $S$, and sequence $M$, set

$$
K'=\operatorname{derive}(K,MD[f],b),\qquad
S'=\operatorname{derive}(S,MD[f],b).
$$

The actual construction is

$$
\begin{aligned}
I(K,M)&=\operatorname{headerI}(b,1,K)\,\|\,K'\,\|\,\operatorname{encodeItems}(M),\\
Z(K,M)&=MD[f](I(K,M)),\\
O(K,S,M,Z)&=\operatorname{headerO}(b,1,S,K)\,\|\,S'\,\|\,K'\\
 &\qquad\|\,\operatorname{MSBF}(|M|)\,\|\,\operatorname{MSBF}(L)\,\|\,Z,\\
\operatorname{SequenceMAC}_{f,S}(K,M)&=MD[f](O(K,S,M,Z(K,M))).
\end{aligned}
$$

After splitting at the header/key block boundaries, define the derived chaining states

$$
\begin{aligned}
k_I(K)&=\operatorname{Casc}_f
  (IV,\operatorname{blockifyPrefix}(\operatorname{headerI}\|K')),\\
k_O(K,S)&=\operatorname{Casc}_f
  (IV,\operatorname{blockifyPrefix}(\operatorname{headerO}\|S'\|K')).
\end{aligned}
$$

The normalized framed-NMAC form is

$$
\operatorname{FNMAC}_{f}(k_I,k_O,M)
 =f\!\left(k_O,\operatorname{outerTag}
   \left(M,\operatorname{Casc}_f(k_I,\operatorname{innerBlocks}(M))\right)\right).
$$

`outerTag` contains the encoded item count, output length, and inner digest. Its required framing law is:

$$
M\ne M' \land
\operatorname{outerTag}(M,z)=\operatorname{outerTag}(M',z')
\Longrightarrow z=z'.
$$

If native MD padding makes the outer tail more than one compression call, the HMAC-to-NMAC bridge absorbs that fixed tail, as permitted by Gaži §2.2’s GNMAC/GHMAC padding discussion. Do not silently identify it with one call without this bridge.

### Random-system and advantage objects

Represent the keyed compression family as

$$
\mathrm{Comp}_f :=
\texttt{PFunPDS.Prob.functionEvaluator}
  (\texttt{Dist.uniform }C)\;(\lambda k\,m.\,f(k,m))
  : \texttt{ProbPDS }B\,C.
$$

Represent SequenceMAC similarly by sampling `MacKey κ` and evaluating the resulting function on `InputSequence`.

Use the H-technique security objects from [SecurityDefs.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/SecurityDefs.lean):

$$
\varepsilon_{\rm ad}
 =\texttt{advPRF}(q:=q)(\mathrm{Comp}_f),
\qquad
\varepsilon_{\rm na}
 =\texttt{advNPRF}(q:=q)(\mathrm{Comp}_f).
$$

The SequenceMAC goal is

$$
\texttt{advPRF}(q:=q)(\mathrm{SequenceMACSystem}_{f,S}).
$$

This is the law-level counterpart of `RandomSystems.CR18.Complexity.PRF.Advantage` in `RandomSystems/Complexity/PRF.lean`. The costed theorem should additionally package Gaži’s explicit reductions using `IsCostedReduction`.

Define the header/key-schedule bridge loss

$$
\varepsilon_{\rm KS}
 :=
\operatorname{Adv}_q
  (\mathrm{SequenceMACSystem}_{f,S},
   \mathrm{FramedNMACSystem}_f),
$$

where the second system samples independent uniform $k_I,k_O:C$. A theorem instantiating $\varepsilon_{\rm KS}$ must use the HMAC-to-NMAC assumptions identified in Gaži §1.2: data-input PRF security and, for the actual single byte key, the appropriate related-key security. It must also account for `derive(K)` when $|K|>b$.

## (b) FINAL THEOREM

Let $q,\ell\in\mathbb N$, where every normalized inner message has at most $\ell$ blocks. Assume:

1. $B,C$ are finite and nonempty, and $N=|C|$.
2. The key length is fixed at $\kappa\ge32$.
3. The MD realization and block-boundary laws above hold.
4. `outerTag` has the framing property above.
5. Either MD strengthening supplies prefix-free inner block strings, or the block domain admits Gaži’s fresh-block extension for every $q$-tuple of length-$\le\ell$ queries. A sufficient finite guard is $q\ell<|B|$.
6. The SequenceMAC-to-independent-framed-NMAC bridge is bounded by $\varepsilon_{\rm KS}$.
7. In the long-customization case, the raw derivation overlap probability is bounded by $\omega_S(q)$, defined below.

Then the Lean guardrail should have the shape

$$
\boxed{
\operatorname{advPRF}_q(\operatorname{SequenceMAC}_{f,S})
\le
\varepsilon_{\rm KS}
+\varepsilon_{\rm ad}
+(\ell+1)q\,\varepsilon_{\rm na}
+\frac{q^2}{N}
+\delta_S(q)
}
$$

where

$$
\delta_S(q)=
\begin{cases}
0,& |S|\le b,\\
\omega_S(q),& |S|>b.
\end{cases}
$$

Thus:

**Short customization**

$$
\boxed{
\operatorname{advPRF}_q(\operatorname{SequenceMAC}_{f,S})
\le
\varepsilon_{\rm KS}
+\varepsilon_{\rm ad}
+(\ell+1)q\,\varepsilon_{\rm na}
+\frac{q^2}{N}.
}
$$

**Long customization**

$$
\boxed{
\operatorname{advPRF}_q(\operatorname{SequenceMAC}_{f,S})
\le
\varepsilon_{\rm KS}
+\varepsilon_{\rm ad}
+(\ell+1)q\,\varepsilon_{\rm na}
+\frac{q^2}{N}
+\omega_S(q).
}
$$

The middle three terms are exactly Gaži Theorem 1, §3.1:

$$
\varepsilon_{\rm ad}+(\ell+1)q\varepsilon_{\rm na}+q^2/2^c,
$$

with $N=2^c$. The existing `bday q N = q(q-1)/(2N)` is tighter; weaken it arithmetically to $q^2/N$ to reproduce the paper’s displayed bound exactly.

For costed adversaries, the Gaži core has

$$
t=t_0+\widetilde O(\ell q).
$$

The composed SequenceMAC result adds the cost maps of the key-schedule bridge and, for long $S$, the one-time MD evaluation of $S$. Compose these with `IsCostedReduction.comp`; do not bake an informal runtime into the law-level theorem.

A theorem omitting $\varepsilon_{\rm KS}$ is valid only for a two-independent-key SequenceMAC variant or after separately proving that bridge. Ordinary PRF security of $k\mapsto f(k,\cdot)$ does not establish it.

## (c) PROOF SKELETON

### Hop 0: realize the concrete SequenceMAC law

Expose the exact short/long call schedule, following `sequenceHashSystem_realization` in [Converter.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/Converter.lean):

- short $S$: inner MD call, outer MD call;
- long $S$: raw `MD[f](S)`, inner MD call, outer MD call.

Then split the MD folds after the header/key prefixes using `List.foldl_append`.

- `REUSE:SequenceHash.pad`
- `REUSE:SequenceHash.derive`
- `REUSE:SequenceHash.headerI`
- `REUSE:SequenceHash.headerO`
- `REUSE:List.foldl_append`
- `REUSE:PFunPDS.applyDDC_ofFunDist`
- `NEW:sequenceMACSystem_realization` — construction-specific equality; adapt the existing SequenceHash realization rather than alter generic converter machinery.

### Hop 1: actual single-key SequenceMAC → independent framed NMAC

Replace the correlated states $(k_I(K),k_O(K,S))$ by independent uniform $C$-values, and normalize the fixed outer tail.

Loss: $\varepsilon_{\rm KS}$.

This is the black-box HMAC-to-NMAC step cited by Gaži §1.2 and §2.2, not part of Theorem 1’s NMAC proof.

- `REUSE:adaptiveTranscriptAdvantage_triangle`
- `REUSE:maxAdvantage_le_adjacent_sum` for the filtered/costed presentation.
- `NEW:sequenceMAC_to_framedNMAC` — genuinely SequenceMAC-specific because it mentions its two headers, `derive`, key-length encoding, and single-key relation. Its assumptions must expose data-input PRF/RKA security.

For $|K|>b$, the raw `MD[f](K)` call is included in this bridge. Alternatively it may be split into an analogous explicit $\omega_K$ term, but it must not disappear.

### Hop 2: outer compression PRF → random function

In framed NMAC, replace

$$
f(k_O,\cdot)
$$

by an independent uniform random function $r:B\to C$, while sampling $k_I$ unchanged.

Loss: $\varepsilon_{\rm ad}$.

This is the first reduction $T_1$ in Gaži §3.1.

- `REUSE:SecurityDefs.advPRF`
- `REUSE:statDist_fTransform_le`
- `REUSE:maxAdvantage_filterQueries_applyDDC_le` for the CR18 filtered formulation.
- `NEW:outerPRF_reduction` only if an `Adv`-level randomized-converter form is required; generalize the existing converter DPI rather than make an NMAC-only copy.

### Hop 3: random outer function is a URF until an inner collision

Let `Bad` say that two distinct transcript inputs $M_i\ne M_j$ produce the same framed outer input:

$$
\operatorname{outerTag}(M_i,Z_i)
 =\operatorname{outerTag}(M_j,Z_j),
\quad
Z_i=\operatorname{Casc}_f(k_I,\operatorname{innerBlocks}(M_i)).
$$

On `¬Bad`, distinct SequenceMAC queries reach distinct inputs of $r$, so their outputs are independent uniform values. Hence the framed-NMAC/random-outer world equals the ideal variable-input URF on good extended transcripts.

This is Gaži §3.1’s condition $C$ and Lemma 1(i) from §2.1.

- `REUSE:adv_le_of_extFixedQueryRep_eq_on_good`
- `REUSE:functionEvaluatorProb_KStepTotal`
- `REUSE:transcriptSystemEvent_functionEvaluatorRV_iff`
- `REUSE:SequenceHash.encodeItems_injective`
- `REUSE:SequenceHash.encodeMSBF_injective`
- `NEW:outerTag_eq_implies_inner_eq` — Sequence framing fact assembled from the two existing injectivity theorems.

The representative should reveal the dummy inner key $k_I$, exactly as `RectHashThenPRF` reveals its hash key. Therefore the ideal transcript remains independent of the revealed key, and the adaptive bad probability reduces to a fixed-query collision calculation. Generalize the representative bookkeeping in `RectHashThenPRF.extFixedQuery_eq_on_good`/`ideal_probBad_le`; do not duplicate that proof pattern.

### Hop 4: adaptive bad event → nonadaptive cascade collision

Conditioned on the ideal URF transcript, the adversary’s queries are fixed and independent of the revealed $k_I$. Thus the probability of `Bad` is bounded by the maximum fixed-query probability that the inner cascades collide.

This is the role of Gaži’s simulated nonadaptive adversary $A_{\rm na}$, equation (2) in §3.1. The extended-representative H-technique endpoint already performs the required adaptivity elimination.

- `REUSE:adv_le_of_extFixedQueryRep_eq_on_good`
- `REUSE:fixedQueryAdv`
- `REUSE:fixedQueryAdv_le_Adv`
- `REUSE:RectHashThenPRF.ideal_probBad_le` after generalizing its key-reveal pattern.
- No SequenceMAC-specific “adaptive-to-nonadaptive” theorem should be introduced.

### Hop 5: make the frozen queries prefix-free

Append one common block $d$ absent from every original query. Then:

1. the extended queries are prefix-free;
2. their lengths are at most $\ell+1$;
3. any collision before extension remains a collision afterward, because equal chaining states receive the same final block.

This is Gaži §3.1 immediately before $A^\*$.

- `REUSE:RandomSystems.CR18.PrefixFree`
- `REUSE:List.prefix_concat_iff`
- `REUSE:List.isPrefix_append_of_length`
- `REUSE:List.foldl_concat`
- `NEW:prefixFree_append_fresh` — generic list/cascade lemma; search found no existing theorem. Put it beside the canonical `CR18.PrefixFree`, not in SequenceMAC.
- `NEW:fresh_block_exists_of_total_length_lt_card` — generic finite counting fact, needed only if the theorem derives freshness from $q\ell<|B|$.

If native MD strengthening is already used as the prefix-free block former, this hop can be skipped and the factor improves from $\ell+1$ to the maximum padded length. Keep $\ell+1$ in the headline theorem to match Gaži exactly.

### Hop 6: distinguish cascade from URF using a collision tester

Let $A^\*$ issue the prefix-free frozen queries and output one iff two responses collide. Then

$$
\Pr[\text{cascade collision}]
 \le
 \operatorname{Adv}^{\rm NA\text{-}PF}
   (\operatorname{Casc}_f,\mathrm{URF})
 +\Pr[\text{URF collision}].
$$

For the ideal URF,

$$
\Pr[\text{collision}]
 \le \frac{q(q-1)}{2N}
 \le \frac{q^2}{N}.
$$

This is the last collision-tester paragraph of Gaži §3.1.

- `REUSE:probBad_urf_collision_le`
- `REUSE:Collision`
- `REUSE:statDist_triangle`
- `REUSE:fixedQueryAdv_le_of_pointwise`
- `REUSE:bday`
- `REUSE:bday_mono`

### Hop 7: apply Gaži Proposition 1

For nonadaptive prefix-free queries of length at most $\ell+1$,

$$
\operatorname{Adv}^{\rm NA\text{-}PF}
  (\operatorname{Casc}_f,\mathrm{URF})
\le
(\ell+1)q\,\varepsilon_{\rm na}.
$$

Copy Appendix A:

- Lemma 5: hybrid over block depth, loss $\ell+1$, reducing cascade security to $q$ independently keyed compression-function oracles.
- Lemma 6: hybrid over those $q$ oracle rows, loss $q$, reducing to ordinary nonadaptive PRF security of $f$.

- `REUSE:advantage_telescope`
- `REUSE:maxAdvantage_le_adjacent_sum`
- `REUSE:Dist.prodProbDist`
- `REUSE:Dist.fTransform_comp`
- `REUSE:SecurityDefs.advNPRF`
- `NEW:cascade_na_pf_adv_le` — general Gaži Proposition 1. Local search found only a legacy fixed-query statistical cascade theorem and an adaptive legacy scaffold containing `sorry`; neither is the nonadaptive computational reduction required here. This theorem must be public and generic over $B,C,f$, not SequenceMAC-specific.

Combining Hops 1–7 by triangle/telescoping gives the short bound.

## (d) SHORT vs LONG CUSTOMIZATION

### Short: $|S|\le b$

Here

$$
S'=\operatorname{pad}(S,b)
$$

is literal data. There is no extra hash query for customization.

After the key-schedule bridge, the construction has a domain-separated Hash-then-PRF shape:

$$
M
 \xrightarrow{\text{inner cascade under }k_I}
 Z
 \xrightarrow{\text{framed outer PRF under }k_O}
 \mathrm{tag}.
$$

The distinct `HeaderI`/`HeaderO` prefixes and the framing of count/output length discharge the structural separation obligations. The security proof is precisely the framed version of Gaži Theorem 1.

Do not apply `hashThenPRF_adaptive_tight_rect` as the cryptographic theorem: that endpoint assumes an epsilon-universal keyed hash, whereas R2 assumes compression-function PRF security. Reuse its representative/key-reveal machinery only.

### Long: $|S|>b$

Now

$$
S'=\operatorname{pad}(MD[f](S),b),
$$

so evaluating the construction includes a raw MD computation on $S$. This computation uses the same compression function as the header, inner, and outer paths.

Define `OverlapS` on the extended representative to mean that an MD compression-call coordinate $(\text{state},\text{block})$ on the raw $S$-path is also used by a non-derivation inner or outer call for one of the transcript queries. Equality of whole raw hash inputs is a special case; block-level overlap is the correct event for `H = MD[f]`.

Let

$$
\omega_S(q)
 =
 \sup_E
 \Pr[\operatorname{OverlapS}\mid
     \text{ideal extended transcript under }E].
$$

On `¬OverlapS`, the raw derivation path can be separated from the framed-NMAC path and the short-case proof applies. The representative equality-on-good endpoint adds exactly $\omega_S(q)$.

- `REUSE:adv_le_of_extFixedQueryRep_eq_on_good`
- `REUSE:adaptiveTranscriptAdvantage_triangle`
- `NEW:longDerive_eq_shortIdeal_on_noOverlap` — SequenceMAC/MD call-schedule fact; not an independent probability theorem.
- `NEW:OverlapS` — necessarily construction-specific because it refers to the concrete derivation, header, inner, and outer call sites.

There is no unconditional nontrivial numeric bound on $\omega_S(q)$ for arbitrary long $S$: an allowed $S$ can deliberately coincide with a construction input or compression prefix, making overlap certain. A useful corollary therefore needs either a syntactic/domain restriction on $S$, or a separate assumption bounding this event.

## (e) INFRA MAP

### Reuse directly

- `RandomSystems/HTechnique/SecurityDefs.lean`
  - `advPRF`
  - `advNPRF`
  - `fixedQueryAdv`
  - `fixedQueryAdv_le_Adv`
  - `advNPRF_le_advPRF`

- `RandomSystems/HTechnique/Derivation.lean`
  - `adv_le_of_extFixedQueryRep_eq_on_good`
  - `adv_le_of_extFixedQueryRep_ratio_of_good`
  - `adaptiveTranscriptAdvantage_triangle`
  - `Collision`
  - `probBad_urf_collision_le`
  - `bday`, `bday_mono`

- `RandomSystems/FunctionEvaluator.lean`
  - `PFunPDS.Prob.functionEvaluator`
  - `PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator`
  - `functionEvaluatorProb_KStepTotal`
  - `transcriptSystemEvent_functionEvaluatorRV_iff`

- `RandomSystems/PDS.lean`
  - `PFunPDS.URF`
  - `PFunPDS.ofFunDist`
  - `PFunPDS.RV.law`

- `RandomSystems/AbsorbDPI.lean`
  - `maxAdvantage_triangle`
  - `maxAdvantage_applyDDC_le`
  - `maxAdvantage_filterQueries_applyDDC_le`

- `RandomSystems/Complexity/AdvantageSeq.lean`
  - `advantage_telescope`
  - `maxAdvantage_le_adjacent_sum`
  - `maxAdvantage_three_hop_le`

- `RandomSystems/Complexity/Reduction.lean`
  - `IsCostedReduction`
  - `IsCostedReduction.comp`

- `RandomSystems/CBCMAC.lean`
  - canonical `RandomSystems.CR18.PrefixFree`
  - `PrefixFree.ne_nil`

- `sequence-hash/SequenceHash/Encoding.lean`
  - `encodeItems_injective`
  - `encodeMSBF_injective`

- `sequence-hash/SequenceHash/RandomSystems/RectHashThenPRF.lean`
  - generalize/reuse the revealed-key representative pattern behind `extFixedQuery_eq_on_good` and `ideal_probBad_le`.

- Mathlib/Lean core:
  - `List.foldl_append`
  - `List.foldl_concat`
  - `List.prefix_concat_iff`
  - `List.isPrefix_append_of_length`.

### Genuinely new, but generic where possible

- `MDHash` model and realization laws. Search found no public MD model. Promote/generalize the legacy `cascadeEval`; do not duplicate it in SequenceMAC.
- `cascade_na_pf_adv_le`, the public Gaži Proposition 1 reduction. Existing legacy cascade results prove a different fixed-query statistical statement; the adaptive legacy target is unfinished.
- Generic `prefixFree_append_fresh` and finite fresh-block existence. Search via local declarations, LeanSearch, and Loogle found only the underlying `List` prefix lemmas.
- SequenceMAC-to-framed-NMAC/key-schedule bridge. This cannot be an instance of an existing theorem because the two concrete C2SP headers, `derive`, key length, native MD padding, and single-key related-key relation are part of its statement.
- Sequence-specific `outerTag` framing and long-customization `OverlapS` call-schedule lemmas. Their algebraic components must be proved using the existing encoding injectivity and generic H-technique endpoints.

No AbstractCrypto construction theorem is needed in the R2 core: this is a one-interface PRF game and belongs on the RandomSystems law/game surface. `AbstractCrypto.Specifications.Indifferentiability` and its composition machinery enter R3/R5. Routing R2 through that layer would obscure, rather than reuse, the existing `advPRF`/H-technique infrastructure.