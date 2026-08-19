# R2 pen-and-paper sketch: SequenceMAC PRF security

The proof is a domain-separated SequenceMAC-to-framed-NMAC hop followed by the
classical Gaži–Pietrzak–Rybár proof. SequenceMAC is better than HMAC at the
first hop: it computes one derived key block $K' = \operatorname{Derive}(K,H,b)$
and absorbs that same block from two distinct header-prefixed run-up states.
The first eight bytes of `HeaderI` and `HeaderO` are respectively `SEQHSH_I`
and `SEQHSH_O`, so the two run-up inputs are distinct. Replacing their outputs
by independent uniform chaining values is therefore an ordinary data-input
PRF-to-URF hybrid for the compression function. It requires no related-key or
RKA assumption.

This distinction from HMAC is essential. HMAC forms $K\mathbin\oplus
\mathsf{ipad}$ and $K\mathbin\oplus\mathsf{opad}$, which are related keys;
Gaži §1.2 consequently cites an RKA assumption for the single-key HMAC bridge.
SequenceMAC was deliberately specified with distinct run-ups to obtain
independently keyed inner and outer hashes under ordinary PRF security instead.

R2 is not an H-technique proof. Gaži–Pietrzak–Rybár 2014 uses ordinary game
hops, explicit reductions, hybrids over block depth and oracle index, and a
birthday collision bound. No H-coefficient representative, revealed-key
extension, or equality-on-good H-technique endpoint belongs in this sketch.
The H-technique is reserved for R4, the Shen–Zhang–Wang–Gu 2025 route.

## (a) OBJECTS

### MD and compression model

Let:

- `B` be the finite type of one compression block.
- `C` be the finite chaining/output type, with $N = |C|$. For an $L$-byte
  digest, $N=256^L$.
- $f : C \to B \to C$, keyed by its chaining input, as in Gaži §2.2.
- `IV : C`.
- `blockify : List Byte → List B` convert a byte string, including the native
  MD padding/strengthening, into compression blocks.

Define

$$
\operatorname{Casc}_f(k,[m_1,\ldots,m_r])
  = \operatorname{foldl}(\lambda y\,m.\,f(y,m))\,k\,[m_1,\ldots,m_r]
$$

and

$$
MD[f](x)=\operatorname{Casc}_f(IV,\operatorname{blockify}(x)).
$$

Build the MD model directly on `SequenceHash.mdIterate` from
[MDHash.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/MDHash.lean),
which is already the canonical `List.foldl` object; the block-append/threading
law is `List.foldl_append`. (The legacy Boneh–Shoup cascade is not relevant to
this work and must not be pulled in.)

Required codec laws:

1. `blockify` realizes the chosen byte-level MD padding.
2. Its result consists of full blocks.
3. MD strengthening supplies prefix-free message block strings, or the Gaži
   fresh-block transformation below is available.
4. Splitting at a block boundary commutes with iteration:

   $$
   \operatorname{Casc}_f(k,x\mathbin{+\!+}y)
   =\operatorname{Casc}_f(\operatorname{Casc}_f(k,x),y).
   $$

`REUSE:List.foldl_append`, `REUSE:List.foldl_concat`.

### SequenceMAC over MD

Reuse the concrete byte framing from
[Spec.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/Spec.lean):

- `SequenceHash.pad`
- `SequenceHash.derive`
- `SequenceHash.headerI`
- `SequenceHash.headerO`

and from
[Encoding.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/Encoding.lean):

- `encodeItems`
- `encodeMSBF`
- `encodeItems_injective`
- `encodeMSBF_injective`.

Use `F = fSeqMac = 1`. For a fixed key length $\kappa\ge 32$, take

$$
\mathrm{MacKey}_\kappa
  =\{K:\mathrm{List\ Byte}\mid |K|=\kappa\},
$$

sampled uniformly. A variable-length key distribution can be added later;
fixed $\kappa$ provides the finite uniform key space expected by the current
PRF surface.

Compute the derived blocks once:

$$
K'=\operatorname{derive}(K,MD[f],b),\qquad
S'=\operatorname{derive}(S,MD[f],b).
$$

The concrete construction is

$$
\begin{aligned}
I(K,M)&=\operatorname{headerI}(b,1,K)\,\|\,K'\,\|\,
  \operatorname{encodeItems}(M),\\
Z(K,M)&=MD[f](I(K,M)),\\
O(K,S,M,Z)&=\operatorname{headerO}(b,1,S,K)\,\|\,S'\,\|\,K'\\
 &\qquad\|\,\operatorname{MSBF}(|M|)\,\|\,
   \operatorname{MSBF}(L)\,\|\,Z,\\
\operatorname{SequenceMAC}_{f,S}(K,M)&=MD[f](O(K,S,M,Z(K,M))).
\end{aligned}
$$

Let the complete block-aligned run-up strings be

$$
\begin{aligned}
R_I(K)&=\operatorname{blockifyPrefix}
  (\operatorname{headerI}(b,1,K)\,\|\,K'),\\
R_O(K,S)&=\operatorname{blockifyPrefix}
  (\operatorname{headerO}(b,1,S,K)\,\|\,S'\,\|\,K').
\end{aligned}
$$

The specification's different leading eight-byte indicators imply

$$
R_I(K)\ne R_O(K,S).
$$

After splitting the MD folds at those boundaries, define

$$
\begin{aligned}
k_I(K)&=\operatorname{Casc}_f(IV,R_I(K)),\\
k_O(K,S)&=\operatorname{Casc}_f(IV,R_O(K,S)).
\end{aligned}
$$

Thus $k_I$ and $k_O$ are outputs of the keyed compression cascade at two
distinct, domain-separated run-up inputs. They are not HMAC-style related
keys. In the ordinary PRF-to-URF hybrid, evaluations of the random function at
the two distinct inputs are independent uniform elements of $C$.

The normalized framed-NMAC form is

$$
\operatorname{FNMAC}_{f}(k_I,k_O,M)
 =f\!\left(k_O,\operatorname{outerTag}
   \left(M,\operatorname{Casc}_f(k_I,\operatorname{innerBlocks}(M))\right)
   \right).
$$

`outerTag` contains the encoded item count, output length, and inner digest.
Its framing obligation is

$$
M\ne M'\ \land\
\operatorname{outerTag}(M,z)=\operatorname{outerTag}(M',z')
\Longrightarrow z=z'.
$$

If native MD padding makes the outer suffix more than one compression call,
do not silently identify it with the displayed one-call form. Split the fixed
tail explicitly and use the GNMAC/GHMAC padding normalization discussed in
Gaži §2.2. This is an ordinary algebraic/game reduction over the fixed framed
tail, not an HMAC related-key bridge.

### Random-system and advantage objects

Represent the keyed compression family as

$$
\mathrm{Comp}_f :=
\texttt{PFunPDS.Prob.functionEvaluator}
  (\texttt{Dist.uniform }C)\;(\lambda k\,m.\,f(k,m))
  : \texttt{ProbPDS }B\,C.
$$

Represent SequenceMAC by sampling `MacKey κ` and evaluating the resulting
function on `InputSequence`. The scaffolding names already exist in
[SequenceMACPRF.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACPRF.lean):
`compSystem`, `sequenceMACSystem`, `framedNMACSystem`, `epsKS`, and `omegaS`.

Use the plain law-level adaptive and nonadaptive PRF advantages

$$
\varepsilon_{\rm ad}
 =\texttt{advPRF}(q:=q)(\mathrm{Comp}_f),\qquad
\varepsilon_{\rm na}
 =\texttt{advNPRF}(q:=q)(\mathrm{Comp}_f).
$$

Although these two method-neutral definitions currently live in
`RandomSystems/HTechnique/SecurityDefs.lean`, they are simply suprema of
ordinary adaptive and fixed-query transcript statistical distances. Their use
does not invoke the H-technique. No theorem from `HTechnique/Derivation.lean`
or the representative layer is part of R2.

Define the key-schedule game hop by

$$
\varepsilon_{\rm KS}
 :=\operatorname{Adv}_q(G_{\rm runup},G_{\rm independent}),
$$

where $G_{\rm runup}$ uses the actual $(k_I(K),k_O(K,S))$ and
$G_{\rm independent}$ samples $(u_I,u_O)\leftarrow C\times C$ uniformly and
then runs the identical framed-NMAC continuation. The theorem discharging this
term is the standard PRF/URF hybrid on the two distinct run-up inputs. Hence
$\varepsilon_{\rm KS}$ is the ordinary compression-PRF cost of the
domain-separated key schedule, including all run-up depths and the one-time
$MD[f](K)$ computation when $|K|>b$. It has no RKA component.

The SequenceMAC goal is

$$
\texttt{advPRF}(q:=q)(\mathrm{SequenceMACSystem}_{f,S}).
$$

The costed version packages the explicit Gaži reductions and the run-up
hybrid using `IsCostedReduction`; serial composition uses
`IsCostedReduction.comp`.

## (b) FINAL THEOREM

Let $q,\ell\in\mathbb N$, where every normalized inner message has at most
$\ell$ blocks. Assume:

1. $B,C$ are finite and nonempty, and $N=|C|$.
2. The key length is fixed at $\kappa\ge32$.
3. The MD realization and block-boundary laws above hold.
4. `outerTag` has the framing property above.
5. Either MD strengthening supplies prefix-free inner block strings, or the
   block domain admits Gaži's fresh-block extension for every $q$-tuple of
   length-at-most-$\ell$ queries. A sufficient finite guard is
   $q\ell<|B|$.
6. The domain-separated SequenceMAC run-up is replaced by independent uniform
   $(k_I,k_O)$ with loss at most $\varepsilon_{\rm KS}$ under ordinary
   data-input PRF security of $f$. No related-key assumption is present. If
   $|K|>b$, the reduction includes the one-time `derive(K)` hash call.
7. In the long-customization case, the raw customization-derivation overlap
   probability is bounded by $\omega_S(q)$ as defined below.

Then the Lean guardrail has the five-term shape

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

Thus the short-customization statement is

$$
\boxed{
\operatorname{advPRF}_q(\operatorname{SequenceMAC}_{f,S})
\le
\varepsilon_{\rm KS}
+\varepsilon_{\rm ad}
+(\ell+1)q\,\varepsilon_{\rm na}
+\frac{q^2}{N}
}
$$

and the long-customization statement is

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

The middle three terms are Gaži Theorem 1, §3.1:

$$
\varepsilon_{\rm ad}+ (\ell+1)q\varepsilon_{\rm na}+q^2/2^c,
$$

with $N=2^c$. The exact uniform-function collision probability is bounded by

$$
\operatorname{bday}(q,N)=\frac{q(q-1)}{2N}\le\frac{q^2}{N};
$$

the last weakening reproduces the paper's displayed term.

For costed adversaries, the Gaži core has

$$
t=t_0+\widetilde O(\ell q).
$$

The composed SequenceMAC reduction additionally accounts for the
domain-separated key-schedule hybrid and, for long $S$, the one-time MD
evaluation of $S$. Compose the cost maps using `IsCostedReduction.comp`; do
not put an informal runtime into the law-level theorem.

The $\varepsilon_{\rm KS}$ term remains necessary until the ordinary-PRF
run-up hop is proved, but its meaning is now precise: it is domain-separated
key-schedule cost, not an HMAC-to-NMAC RKA loss.

## (c) PROOF SKELETON

### Hop 0: realize the concrete SequenceMAC law

Expose the exact call schedule, following `sequenceHashSystem_realization` in
[Converter.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/Converter.lean):

- short $S$: inner MD call, then outer MD call;
- long $S$: raw `MD[f](S)`, then inner MD call, then outer MD call.

Compute $K'$ once, and thread that same block into both run-ups. Split the MD
folds after the header/key prefixes using `List.foldl_append`.

- `REUSE:SequenceHash.pad`
- `REUSE:SequenceHash.derive`
- `REUSE:SequenceHash.headerI`
- `REUSE:SequenceHash.headerO`
- `REUSE:SequenceHash.mdIterate`
- `REUSE:List.foldl_append`
- `REUSE:PFunPDS.applyDDC_ofFunDist`
- `NEW:sequenceMACSystem_realization` — construction-specific equality; adapt
  the existing SequenceHash realization and the canonical MD fold rather than
  changing generic converter machinery.

### Hop 1: domain-separated run-up to independent framed NMAC

Let $G_0$ use the actual pair

$$
(k_I(K),k_O(K,S))
$$

and let $G_1$ sample independent uniform $(u_I,u_O)\leftarrow C\times C$ and
use those as the framed-NMAC keys.

First prove from the concrete headers and block codec that the complete run-up
inputs are distinct:

$$
R_I(K)\ne R_O(K,S).
$$

Now replace the keyed compression evaluations in the run-up by uniform random
functions through an ordinary PRF hybrid. In the random-function world,
evaluations at the two distinct inputs are independent uniform values; use
`uniformFunction_eval_uniform` with the injective two-element query vector.
Telescope over any additional run-up depth. This is a normal data-input PRF
reduction and never presents related keys to the compression challenger.

Loss: $\varepsilon_{\rm KS}$.

If $|K|>b$, `derive(K)` first computes $MD[f](K)`. Put that raw hash schedule
inside the same ordinary-PRF hybrid and its cost map. It must not disappear and
it is not split out as an RKA term.

- `REUSE:RandomSystems.CR18.uniformFunction_eval_uniform`
- `REUSE:statDist_fTransform_le`
- `REUSE:advantage_telescope`
- `REUSE:maxAdvantage_le_adjacent_sum`
- `REUSE:IsCostedReduction.comp`
- `NEW:headerI_ne_headerO` — the local declaration search found the two
  concrete indicator definitions but no packaged distinct-header theorem;
  prove it once in the SequenceHash framing layer.
- `NEW:sequenceMAC_runup_inputs_ne` — block-codec consequence of the header
  theorem, kept construction-specific.
- `NEW:sequenceMAC_keySchedule_reduction` — the concrete run-up/`derive(K)`
  reduction. Its only cryptographic assumption is ordinary PRF security of
  $f$; its conclusion supplies the `epsKS` hop already named by the guardrail.

### Hop 2: outer compression PRF to random function

In the independent framed-NMAC game, replace

$$
f(k_O,\cdot)
$$

by an independent uniform random function $r:B\to C$, while leaving $k_I$
uniform and unchanged. This is Gaži's first reduction $T_1$ in §3.1.

Loss: $\varepsilon_{\rm ad}$.

- `REUSE:SecurityDefs.advPRF` as the ordinary adaptive PRF definition
- `REUSE:statDist_fTransform_le`
- `REUSE:maxAdvantage_applyDDC_le` or `AbstractCrypto.edist_smul_le` after
  transporting through the existing RandomSystems carrier bridge; do not
  reprove converter/context non-expansion.
- Generalize an existing randomized-converter reduction if the exact
  `Adv`-level wrapper is missing; do not create an NMAC-only DPI theorem.

### Hop 3: random outer function is a URF until an inner collision

Let `Bad` state that two distinct transcript queries $M_i\ne M_j$ produce the
same framed outer input:

$$
\operatorname{outerTag}(M_i,Z_i)
 =\operatorname{outerTag}(M_j,Z_j),\qquad
Z_i=\operatorname{Casc}_f(k_I,\operatorname{innerBlocks}(M_i)).
$$

By the framing law, `Bad` implies an inner cascade collision. On `¬Bad`, every
fresh SequenceMAC query reaches a fresh input of $r$, so lazy sampling returns
an independent uniform answer. Therefore the random-outer game and the ideal
variable-input URF are identical until `Bad`.

This is Gaži §3.1's condition $C$ and Lemma 1(i). Formalize it as a classical
bad-event game hop. On the RandomSystems surface, reuse `RandomSystems.CR18.gameOf`,
`CondEquiv`, and the existing conditional-equivalence/fundamental-lemma
endpoint; alternatively establish the pointwise transcript bound and take the
ordinary `Adv` supremum. Do not encode this as an extended fixed-query
representative.

- `REUSE:RandomSystems.CR18.gameOf`
- `REUSE:RandomSystems.CR18.CondEquiv`
- `REUSE:advantage_le_maxWinProb_of_condEquiv` for the per-adversary adaptive
  fundamental-lemma step, instantiated with `gameOf`
- `REUSE:ignoreMBO_gameOf`, `monotoneMBO_gameOf`
- `REUSE:statDist_triangle` for the law-level hop chain
- `REUSE:SequenceHash.encodeItems_injective`
- `REUSE:SequenceHash.encodeMSBF_injective`
- `NEW:outerTag_eq_implies_inner_eq` — Sequence framing fact assembled from
  the existing injectivity theorems.

No key is revealed. The state $k_I$ remains hidden sampled randomness in the
real game, exactly as in Gaži's reduction.

### Hop 4: adaptive bad event to a nonadaptive cascade collision

Construct Gaži's nonadaptive adversary $A_{\rm na}$ explicitly. It runs the
original adaptive adversary against a lazily sampled ideal URF: fresh queries
receive fresh uniform answers and repeated queries receive the cached answer.
After the simulation, it records the at most $q$ queries and submits that
fixed tuple to the inner cascade oracle.

Until `Bad`, this simulation is perfect, so

$$
\Pr[\mathrm{Bad}\text{ in the adaptive random-outer game}]
=
\Pr[\text{inner collision on the frozen }A_{\rm na}\text{ queries}].
$$

This is Gaži equation (2). It is an explicit classical adversary reduction,
not an adaptive-to-fixed-query H-coefficient theorem.

- `REUSE:PFunPDS.Prob.fixedQueryTranscriptDist`
- `REUSE:transcript_ofFunq_inputs_of_interact_eq` and
  `interact_ofFunq_eq_iff` as the existing deterministic adaptive-transcript
  replay core; generalize/transport these in place to the current PFun law
  surface rather than rebuilding transcript replay inside SequenceMAC.
- `REUSE:fixedQueryAdv` and `fixedQueryAdv_le_Adv` only as the plain
  nonadaptive/adaptive advantage notions
- `REUSE:IsCostedReduction` and `IsCostedReduction.comp`
- `NEW:recordedQueriesReduction` — local and AbstractCrypto searches found no
  generic lazy-URF adversary transformer that records an adaptive query list
  and replays it nonadaptively. Build the wrapper generically over finite
  input/output types on top of the existing transcript replay core;
  SequenceMAC supplies only the collision predicate and framing lemma.

### Hop 5: make the frozen queries prefix-free

Append one common block $d$ that appears in none of the original queries.
Then:

1. the extended queries are prefix-free;
2. their lengths are at most $\ell+1$;
3. a collision before extension remains a collision after extension, because
   equal chaining states receive the same final block.

This is the step immediately before $A^*$ in Gaži §3.1.

- `REUSE:RandomSystems.CR18.PrefixFree`
- `REUSE:List.prefix_concat_iff`
- `REUSE:List.isPrefix_append_of_length`
- `REUSE:List.foldl_concat`
- `REUSE:Finset.exists_not_mem_of_card_lt_enatCard` as the generic finite
  freshness core
- `NEW:prefixFree_append_fresh` — no packaged theorem with this statement was
  found in RandomSystems, AbstractCrypto, or Mathlib; place the generic list
  lemma beside the canonical `CR18.PrefixFree`.
- `NEW:fresh_block_exists_of_total_length_lt_card` — a thin finite-counting
  corollary, needed only when freshness is derived from $q\ell<|B|$.

If native MD strengthening already makes the block strings prefix-free, this
hop may be skipped and the factor can use the actual maximum padded length.
Keep $\ell+1$ in the headline theorem to match Gaži exactly.

### Hop 6: collision tester and the birthday term

Let $A^*$ issue the prefix-free frozen queries and return one exactly when two
responses collide. Then

$$
\Pr[\text{cascade collision}]
\le
\operatorname{Adv}^{\rm NA\text{-}PF}
  (\operatorname{Casc}_f,\mathrm{URF})
+\Pr[\text{URF collision}].
$$

For the ideal URF, use a pairwise union bound and the uniform-function
two-point evaluation lemma:

$$
\Pr[\text{collision}]
\le \operatorname{bday}(q,N)
=\frac{q(q-1)}{2N}
\le\frac{q^2}{N}.
$$

This is the final collision-tester paragraph of Gaži §3.1.

- `REUSE:RandomSystems.probBad_iUnion_le`
- `REUSE:RandomSystems.CR18.uniform_function_pair_eq_mass`
- `REUSE:pairCollisionUnionBound`
- `REUSE:pairCollisionUnionBound_le_birthday`
- `REUSE:statDist_triangle`
- `REUSE:fixedQueryAdv_le_of_pointwise`
- `REUSE:bday`, `bday_mono` after promoting/exporting these purely arithmetic
  declarations to a method-neutral counting module; do not import an
  H-technique proof to obtain them.

### Hop 7: Gaži Proposition 1 by two explicit hybrid families

For nonadaptive prefix-free queries of length at most $\ell+1$,

$$
\operatorname{Adv}^{\rm NA\text{-}PF}
  (\operatorname{Casc}_f,\mathrm{URF})
\le
(\ell+1)q\,\varepsilon_{\rm na}.
$$

Follow Appendix A verbatim:

1. Lemma 5 hybrids over block depth. At depth $i$, queries sharing their first
   $i-1$ blocks share one of at most $q$ independently keyed compression
   oracles. Telescoping over the $\ell+1$ depths loses the factor $\ell+1$.
2. Lemma 6 hybrids over the at most $q$ oracle rows. Replace one independently
   keyed compression oracle at a time and choose the challenged row uniformly.
   Telescoping loses the factor $q$ and produces an ordinary nonadaptive PRF
   adversary against $f$.

- `REUSE:advantage_telescope`
- `REUSE:maxAdvantage_le_adjacent_sum`
- `REUSE:Dist.prodProbDist`
- `REUSE:Dist.fTransform_comp`
- `REUSE:SecurityDefs.advNPRF` as the plain nonadaptive PRF definition
- `REUSE:IsCostedReduction.comp`
- `NEW:cascade_na_pf_adv_le` — repository and AbstractCrypto searches found
  only the legacy fixed-query statistical theorem
  `advantageOn_URFfunCascadeIdeal_URFfun_prefixFree_le_birthday` and an
  unfinished adaptive legacy scaffold. Neither is Gaži's computational
  Proposition 1. State the new theorem generically over $B,C,f$ and expose
  the two reduction families; do not specialize it to SequenceMAC.

Combine Hops 1–7 with the ordinary advantage triangle and trace telescoping.
This yields the short-customization bound.

## (d) SHORT vs LONG CUSTOMIZATION

### Short: $|S|\le b$

Here

$$
S'=\operatorname{pad}(S,b)
$$

is literal data; customization causes no extra hash query. After the ordinary
run-up PRF hop, the construction is the domain-separated framed-NMAC system

$$
M
 \xrightarrow{\text{inner cascade under }k_I}
 Z
 \xrightarrow{\text{framed outer PRF under }k_O}
 \mathrm{tag},
$$

with independent uniform $k_I,k_O$. The distinct headers discharge key-domain
separation; the count/output-length fields discharge outer framing. Hops 2–7
are then precisely the framed version of Gaži Theorem 1.

Do not apply `hashThenPRF_adaptive_tight_rect`: that theorem assumes an
epsilon-universal keyed hash and is an H-technique result. R2 instead assumes
ordinary adaptive and nonadaptive PRF security of the compression function.

### Long: $|S|>b$

Now

$$
S'=\operatorname{pad}(MD[f](S),b),
$$

so the construction performs a raw MD evaluation of $S$ using the same
compression function as the run-up, inner path, and outer path.

Define `OverlapS` on the explicit execution/call-schedule game: a compression
coordinate $(\text{state},\text{block})$ used on the raw $S$-derivation path
is reused by a non-derivation run-up, inner, or outer call for one of the
adversary's transcript queries. Equality of complete raw hash inputs is only a
special case; block-level overlap is the correct event for $H=MD[f]$.

Let

$$
\omega_S(q)
=\sup_E\Pr[\operatorname{OverlapS}
  \text{ in the idealized long-customization game against }E].
$$

On `¬OverlapS`, the raw derivation calls are disjoint from the framed-NMAC
calls, so the ordinary PRF hybrid separates them and the short-case games
apply. Add the bad-event probability with the classical fundamental lemma and
the advantage triangle:

$$
\operatorname{Adv}(G_{\rm long},G_{\rm separated})
\le \omega_S(q).
$$

- `REUSE:RandomSystems.CR18.gameOf`
- `REUSE:RandomSystems.CR18.CondEquiv`
- `REUSE:advantage_le_maxWinProb_of_condEquiv`
- `REUSE:ignoreMBO_gameOf`, `monotoneMBO_gameOf`
- `REUSE:statDist_triangle`
- `REUSE:maxAdvantage_le_adjacent_sum`
- `NEW:longDerive_eq_shortIdeal_on_noOverlap` — SequenceMAC/MD call-schedule
  fact, not an independent probability theorem.
- `NEW:OverlapS` — construction-specific because it refers to the actual
  derivation, run-up, inner, and outer call coordinates.

There is no unconditional nontrivial numeric bound on $\omega_S(q)$ for
arbitrary long $S$: an allowed customization can deliberately coincide with a
construction input or compression prefix, making overlap certain. A numeric
corollary therefore needs a syntactic/domain restriction on $S$ or a separate
assumption bounding this event.

## (e) INFRA MAP

### High-level algebra and classical advantage infrastructure

RandomSystems is the concrete random-system carrier for the sibling
AbstractCrypto algebra. R2 should consume the generic algebraic facts rather
than recreate them:

- `AbstractCrypto.edist_smul_le` for converter/context non-expansion.
- `AbstractCrypto.red_mul` and
  `AbstractCrypto.soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable`
  for the resource-level
  construction wrapper and any tree of local construction claims. The
  game-adversary cost maps remain in `IsCostedReduction.comp`; do not conflate
  the two composition layers.
- No current RS-to-AC carrier-quotient transport is available. Keep R2 on its
  proved direct `PFunPDS`/`maxAdvantage` (`Δ`) surface; any future AC packaging
  requires a fresh faithful carrier/action audit.
- `RandomSystems/AbsorbDPI.lean`: `maxAdvantage_triangle`,
  `maxAdvantage_applyDDC_le`, and
  `maxAdvantage_filterQueries_applyDDC_le`.
- `RandomSystems/Complexity/AdvantageSeq.lean`: `advantage_telescope`,
  `maxAdvantage_le_adjacent_sum`, and `maxAdvantage_three_hop_le`.
- `RandomSystems/Complexity/Reduction.lean`: `IsCostedReduction` and
  `IsCostedReduction.comp`.
- `RandomSystems/StatDist.lean`: `statDist_triangle`,
  `statDist_fTransform_le`, and `probBad_iUnion_le`.
- `RandomSystems/CondEquiv.lean` and `RandomSystems/GameOf.lean` for the
  classical identical-until-bad/fundamental-lemma presentation.

The concrete PRF games remain on the RandomSystems law surface:

- `RandomSystems/HTechnique/SecurityDefs.lean`: only the method-neutral
  definitions `Adv`, `fixedQueryAdv`, `advPRF`, `advNPRF`, and the inclusion
  `fixedQueryAdv_le_Adv`.
- `RandomSystems/FunctionEvaluator.lean`:
  `PFunPDS.Prob.functionEvaluator`, fixed-query evaluation laws, and
  `uniformFunction_eval_uniform`.
- `RandomSystems/PDS.lean`: `PFunPDS.URF`, `PFunPDS.ofFunDist`, and
  `PFunPDS.RV.law`.
- `RandomSystems/SwitchingLemma.lean`: `uniform_function_pair_eq_mass`,
  `pairCollisionUnionBound`, and
  `pairCollisionUnionBound_le_birthday`.
- `RandomSystems/CBCMAC.lean`: canonical `RandomSystems.CR18.PrefixFree`.
- `sequence-hash/SequenceHash/Encoding.lean`:
  `encodeItems_injective`, `encodeMSBF_injective`.
- Mathlib/core: `List.foldl_append`, `List.foldl_concat`,
  `List.prefix_concat_iff`, `List.isPrefix_append_of_length`, and
  `Finset.exists_not_mem_of_card_lt_enatCard`.

### Explicitly excluded from R2

Do not route any R2 hop through:

- `adv_le_of_extFixedQueryRep_eq_on_good` or any ratio/partition sibling;
- extended fixed-query representatives or transcript reveals;
- the `RectHashThenPRF` revealed-key construction;
- `hashThenPRF_adaptive_tight_rect`;
- H-coefficient good-transcript ratios.

Those are H-technique mechanisms and belong to R4. The location of the plain
`advPRF`/`advNPRF` definitions does not change this methodological boundary.

### Genuinely new after search, generic where possible

- Complete the public MD realization around the existing
  `SequenceHash.mdIterate`; do not duplicate the fold.
- `cascade_na_pf_adv_le`, the generic Gaži Proposition 1 reduction. The
  existing legacy cascade theorem is statistical and proves a different
  statement.
- Generic `recordedQueriesReduction`, implementing Gaži equation (2) by lazy
  URF simulation and nonadaptive replay, while reusing/generalizing the
  existing deterministic replay lemmas in `RandomSystems/Transcript.lean`.
- Generic `prefixFree_append_fresh` and the finite fresh-block corollary,
  built from the existing Mathlib prefix and finite-cardinality lemmas.
- The SequenceMAC domain-separated key-schedule reduction supplying
  $\varepsilon_{\rm KS}$ under ordinary PRF security, including long-key
  `derive(K)` accounting and no RKA assumption.
- Sequence-specific distinct-run-up, `outerTag` framing, and
  long-customization `OverlapS` call-schedule lemmas.

AbstractCrypto's indifferentiability specifications are for R3/R5, not the R2
PRF core. Its generic composition and non-expansion theorems still govern how
the R2 reductions are assembled; only the construction-specific probability
and reduction lemmas above are new.
