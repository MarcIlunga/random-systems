# A3 — concrete C2SP realization of the block-level PRF theorem

## Scope correction forced by the specification

There are two distinctions that the final guardrail must preserve.

First, the keyed construction with function indicator $F=1$ is **SequenceMAC**,
not literal SequenceHash. C2SP assigns $F_{\rm SEQMAC}=1$ and
$F_{\rm SEQHSH}=2$ ([`sequencehash.md`, lines 210–215](../sequencehash.md#L210-L215));
SequenceMAC has a nonempty key of at least 32 bytes
([lines 265–279](../sequencehash.md#L265-L279)), whereas SequenceHash fixes
$K=""$ and $F=2$ ([lines 294–300](../sequencehash.md#L294-L300)). Therefore:

- the keyed, $F=1$ PRF theorem requested here is semantically a concrete
  **SequenceMAC** theorem over `InputSequence`;
- the existing `sequenceHashStep`, `sequenceHashSystem`, and
  `sequenceHashSystem_realization` are the literal $F=2$, empty-key realization;
  they are a proof pattern for the keyed realization, not that realization
  itself;
- a theorem named `sequenceHash_prf_bound` with a secret $K$ and $F=1$ would
  misstate the C2SP construction. The honest guardrail name is
  `sequenceMAC_prf_bound_concrete`. If the project retains
  `sequenceHash_prf_bound` as a family-level name, its documentation must say
  explicitly that its subject is C2SP SequenceMAC.

Second, unique parsing is not prefix-freeness. This matters in part (c) below:
the prefix-free premise used inside the Gaži proof cannot be proved from
`encodeItems_injective`, and fortunately the frozen theorem does not require
such a premise from its caller.

Everything below stays on the pure CR18 surface: systems are `PFunPDS`, query
restriction is $\lceil q\rceil$, and comparison is $\Delta$.

## 1. The exact C2SP byte construction

Fix a block size $b$, an $L$-byte Merkle–Damgård hash
$H=MD[f]$, a customization string $S$, and a key $K$ satisfying the
SequenceMAC length rule. Write

$$
K'=\operatorname{Derive}(K,H,b),\qquad
S'=\operatorname{Derive}(S,H,b).
$$

For $M=(M_1,\ldots,M_n)$, C2SP defines

$$
\begin{aligned}
I_K(M)
  &=\operatorname{HeaderI}(b,1,K)\,\|\,K'\,\|\,
    \operatorname{encodeItems}(M),\\
Z_K(M)&=H(I_K(M)),\\
O_{K,S}(M,z)
  &=\operatorname{HeaderO}(b,1,S,K)\,\|\,S'\,\|\,K'\\
  &\quad\|\,\operatorname{EncodeMSBF}(n)
    \,\|\,\operatorname{EncodeMSBF}(L)\,\|\,z,\\
\operatorname{SequenceMAC}_{H,S}(K,M)
  &=H(O_{K,S}(M,Z_K(M))).
\end{aligned}
$$

This is exactly `SequenceFunction` in
[`sequencehash.md`, lines 241–261](../sequencehash.md#L241-L261), specialized
as required by [`lines 265–271`](../sequencehash.md#L265-L271). Individual
items use

$$
\operatorname{Encode}(x)
  =\operatorname{EncodeLSBF}(|x|)\,\|\,x,
$$

not MSBF ([`lines 163–180`](../sequencehash.md#L163-L180)); only the outer item
count and output length use fixed-width MSBF.

The headers are

$$
\begin{aligned}
\operatorname{HeaderI}(b,F,K)
 &=\operatorname{Pad}(
   \texttt{SEQHSH\_I}\,\|\,\operatorname{MSBF}(F)
   \,\|\,\operatorname{MSBF}(|K|),b),\\
\operatorname{HeaderO}(b,F,S,K)
 &=\operatorname{Pad}(
   \texttt{SEQHSH\_O}\,\|\,\operatorname{MSBF}(F)
   \,\|\,\operatorname{MSBF}(|S|)
   \,\|\,\operatorname{MSBF}(|K|),b).
\end{aligned}
$$

Their leading eight bytes differ; C2SP calls out this separation explicitly
([`lines 216–237`](../sequencehash.md#L216-L237)). Also, `Derive` hashes its
input only when it exceeds one hash block ([`lines 183–208`](../sequencehash.md#L183-L208)).
Thus an exact realization must account for the one-time $H(K)$ computation
when $|K|>b$ and the one-time $H(S)$ computation when $|S|>b$.

The generic theorem returns a chaining value in $C$, while `Spec.FixedHash L`
returns `HashOutput L`. For a literal instantiation, either take
$C=\texttt{HashOutput L}$ definitionally or supply an equivalence

$$
\mathsf{digestBytes}:C\simeq\texttt{HashOutput L}.
$$

A mere injection $C\hookrightarrow\texttt{HashOutput L}$ is enough to print a
digest but not enough to identify the block theorem's ideal uniform law on
$C$ with the literal uniform law on all $L$-byte outputs. The concrete
guardrail must make this output identification explicit.

## 2. The concrete real system over `InputSequence`

For a fixed key length $\kappa\ge 32$, let

$$
\mathcal K_\kappa
  =\{K:\texttt{ByteString}\mid |K|=\kappa\}
$$

with a specified probability distribution $D_K$ (uniform in the simplest
guardrail). The concrete keyed law is

$$
\mathsf{ConcreteReal}_{f,S}
 =\operatorname{ofFunDist}\!left(
   (K\mapsto(M\mapsto
     \operatorname{SequenceMAC}_{MD[f],S}(K,M)))_*D_K
   \right)
 :\texttt{PFunPDS InputSequence }C.
$$

This is a single sampled $K$ shared by every query. $K'$ and the fixed $S'$ may
therefore be computed once and stored in the sampled deterministic function;
recomputing either value per query is extensionally equal for a stateless
$MD[f]$, but gives the wrong internal-call accounting for a later quantitative
reduction.

### Relation to `Converter.lean`

`SequenceHash.RandomSystemsModel.sequenceHashStep` realizes the literal
SequenceHash call schedule over the hash resource:

- if $|S|\le b$, query the inner byte string and then the outer byte string;
- if $|S|>b$, first query $S$, then the inner byte string, then the outer byte
  string.

`SequenceHash.RandomSystemsModel.sequenceHashSystem_realization` proves the
resulting equality of `PFunPDS` laws. It hardcodes the definitions from
`Spec.sequenceHash`, hence $K=""$ and $F=2$.

More explicitly, for a distribution $D$ on `FixedHash L`, the existing law is

$$
\mathsf{SequenceHashReal}_D
 :=\texttt{sequenceHashSystem }b\,D
 :\texttt{PFunPDS (ByteString × InputSequence) (HashOutput L)},
$$

and the realization theorem rewrites it to the function law induced by

$$
H\longmapsto((S,M)\longmapsto\operatorname{SequenceHash}(H,S;M)).
$$

For a fixed customization, precompose by $M\mapsto(S,M)$. To instantiate
$H=MD[f]$, take the point law on the fixed hash obtained from `mdHash` and the
chosen $C\simeq\texttt{HashOutput L}$ identification. This is the exact
literal $F=2$ system; it still has no sampled SequenceMAC key.

The keyed realization is genuinely new. Define `sequenceMACStep` with $F=1$
and the sampled, precomputed $K'$. For fixed $K$ it has the same two/three-call
shape for customization derivation, and its realization statement is

$$
\mathsf{sequenceMACSystem}(b,f,S,D_K)
 =\mathsf{ConcreteReal}_{f,S}.
$$

Its proof should copy the structure of
`sequenceHashSystem_realization`, using `PFunPDS.applyDDC_ofFunDist` for the
per-function realization and then mixing over $D_K$. No new converter
semantics is required.

## 3. From an input sequence to compression blocks

Let $B$ be the compression-block type and $C$ the chaining/output type, and
let $f:C\to B\to C$. `MDCodec.blockify` includes the native final padding.
Because every header and every `Derive` result is padded to a positive multiple
of $b$, the two prefixes

$$
\begin{aligned}
P_I(K)&=\operatorname{HeaderI}(b,1,K)\,\|\,K',\\
P_O(K,S)&=\operatorname{HeaderO}(b,1,S,K)\,\|\,S'\,\|\,K'
\end{aligned}
$$

end on compression-block boundaries.

The concrete-to-generic map needed by the block theorem is the inner suffix
map

$$
\beta(M)
  :=\operatorname{blockify}(\operatorname{encodeItems}(M)).
$$

For an $\ell$ bounding all accepted encoded sequences, package it as

$$
\bar\beta(M)
  :=\langle\beta(M),\ |\beta(M)|\le\ell\rangle
  :\operatorname{BlockString}(B,\ell).
$$

The required MD boundary equation is

$$
\operatorname{blockify}(P_I(K)\,\|\,\operatorname{encodeItems}(M))
 =\operatorname{rawBlocks}(P_I(K))\,++\,\beta(M),
$$

and therefore, by `mdIterate_append`,

$$
MD[f](I_K(M))
 =\operatorname{Casc}_f(k_I(K),\beta(M)),
$$

where

$$
k_I(K)
 =\operatorname{Casc}_f(IV,\operatorname{rawBlocks}(P_I(K))).
$$

The current `MDCodec` does not expose `rawBlocks` or this boundary law. Its
existing `blockify_padding` and `blockify_full` fields do not imply the
equation. A construction-facing codec lemma is therefore new.

The outer suffix must be recorded separately:

$$
\tau(M,z)
 :=\operatorname{blockify}(
   \operatorname{MSBF}(|M|)\,\|\,\operatorname{MSBF}(L)
   \,\|\,\operatorname{digestBytes}(z)).
$$

After the outer boundary split,

$$
MD[f](O_{K,S}(M,z))
 =\operatorname{Casc}_f(k_O(K,S),\tau(M,z)),
$$

with $k_O$ obtained by iterating over `rawBlocks(P_O(K,S))`.

### Boundedness and injectivity

The frozen theorem has the finite carrier `BlockString B ℓ`; bare
`InputSequence` does not carry an $\ell$-block proof. The concrete guardrail
must therefore take either:

- a global proof $h_\ell:\forall M,|\beta(M)|\le\ell$ for the full C2SP
  `InputSequence` carrier; or
- a bounded subtype of `InputSequence` and state the theorem on that subtype.

The requested theorem over `InputSequence` uses the first form. The C2SP
128-bit bounds make some global finite bound possible, although a practical
theorem should normally use a much smaller implementation bound.

To transport the ideal block-string random function back to
`InputSequence`, $\bar\beta$ must be injective. `encodeItems_injective`
discharges the byte-level part. A further codec-faithfulness lemma is needed:

$$
\mathsf{blockifyEncodeItems\_injective}:
\operatorname{Injective}(M\mapsto
  \operatorname{blockify}(\operatorname{encodeItems}(M))).
$$

This may be proved from an injective native padding/serialization interface,
but it does not follow from the current `MDCodec` fields without
`blockify_prefixFree`. It should be added as the weakest exact codec premise;
prefix-freeness of every padded hash input is stronger than this realization
needs.

## 4. Prefix-freeness: what is and is not discharged

### The proposed encoding lemma is false

`encodeItems_injective` says that equal complete encodings have equal input
sequences. It does not say that two distinct complete encodings are
prefix-incomparable. Let $\epsilon$ denote the empty byte string and take

$$
M=[\epsilon],\qquad N=[\epsilon,\epsilon].
$$

Since `Encode(ε)` is the 16-byte zero length field,

$$
\operatorname{encodeItems}(M)=0^{16},\qquad
\operatorname{encodeItems}(N)=0^{32},
$$

so the former is a strict prefix of the latter. Appending the same fixed
`HeaderI || K'` prefix does not repair that fact. The outer count field occurs
in the second hash call and cannot make the first hash call's message blocks
prefix-free.

Consequently there is no sound lemma of the form

$$
\mathsf{PrefixFree}(M\mapsto\beta(M))
$$

derivable from `encodeItems_injective`, the outer count/length fields, and the
double-hash envelope alone. The sketch must not claim such a lemma.

### The exact prefix-free discharge used by the frozen theorem

The good news is that `sequenceMAC_prf_bound` has no prefix-free hypothesis.
Inside its proof, the only prefix-free premise is local to
`cascade_na_pf_fixedQuery_bound`. For every fixed $q$-tuple, the proof calls

`SequenceHash.MACPRF.exists_prefixFree_appendDelimiter`

to append one common delimiter block and obtain prefix-free block strings of
length at most $\ell+1$. If the block alphabet is too small for the fresh
delimiter branch, the theorem closes from the already-large birthday term.
Thus the actual prefix-free obligation is **already discharged by the proven
generic theorem**, not assumed of `MDCodec` and not supplied by C2SP's item
encoding.

The construction-specific fact supplied by C2SP is instead
**envelope unambiguity**:

1. `encodeItems_injective` makes $I_K(M)=I_K(N)$ imply $M=N$.
2. The fixed-width outer fields and fixed digest length make
   $O_{K,S}(M,z)=O_{K,S}(N,z')$ imply $|M|=|N|$ and $z=z'$.
3. Hence equal outer inputs for distinct $M,N$ force equality of inner
   digests on distinct inner byte strings.

For literal $F=2$ SequenceHash, the existing
`sequenceHash_collision_of_distinct_inputs` proves the stronger complete
collision disjunction, and its proof already uses `encodeItems_injective` and
the fixed-width outer fields. The keyed $F=1$ analogue is new, but it is an
unambiguity/collision lemma, not a prefix-free lemma.

C2SP's statement that final SequenceHash outputs resist length extension even
when the underlying hash is length-extendable
([`sequencehash.md`, lines 18–20](../sequencehash.md#L18-L20)) is consistent
with this distinction. The inner digest is placed inside a separately framed
outer hash. That double-hash envelope prevents extension of the *published
output*; it does not turn `encodeItems` into a prefix-free language.

## 5. The concrete key-schedule and envelope bridge

After splitting at the aligned prefixes, the concrete run-up states are

$$
\begin{aligned}
k_I(K)&=\operatorname{Casc}_f(IV,\operatorname{rawBlocks}(P_I(K))),\\
k_O(K,S)&=\operatorname{Casc}_f(IV,\operatorname{rawBlocks}(P_O(K,S))).
\end{aligned}
$$

The distinct `SEQHSH_I` and `SEQHSH_O` prefixes make the two complete run-ups
distinct. Replacing their resulting states by independent uniform
$(u_I,u_O)\leftarrow C\times C$ is an ordinary compression-PRF reduction:
the comparison is between the corresponding `PFunPDS` laws by $\Delta$.
There is no related-key premise. A complete proof must nevertheless include
all blocks of both run-ups and the $H(K)$ computation in the long-key branch;
distinct first blocks alone are not a proof that two multi-block cascades have
independent outputs. Any collision among internal compression coordinates is
part of this same bridge analysis.

Likewise, if $|S|>b$, $S'=\operatorname{Pad}(H(S),b)$ shares the same
compression family and must be included in the concrete bridge. A clean first
guardrail may assume $|S|\le b$; the unrestricted statement must absorb the
long-customization call into the bridge term rather than omit it.

Define input translation of a block system $P$ by the one-query simple
converter

$$
\bar\beta^*P
 :=\operatorname{applyDDC}(\operatorname{simple}(\bar\beta,\mathrm{id}),P).
$$

The concrete bridge term that is honest without further normalization claims
is

$$
\boxed{
\varepsilon_{\rm C2SP}(q)
 :=\Delta\!left(
   \lceil q\rceil\mathsf{ConcreteReal}_{f,S},
   \lceil q\rceil\bar\beta^*(\mathsf{nmacReal}_{\ell,f,\mathsf{pad}_C})
   \right).
}
$$

Here `nmacReal` is exactly the frozen theorem's independent-uniform pair, and
$\mathsf{pad}_C:C\hookrightarrow B$ is its injective final-block map.
This is the requested pure-CR18 distance between the concrete construction and
independent-key NMAC.

### The outer envelope is not definitionally NMAC

This is the main place where the concrete construction does not cleanly reduce
to Gaži's model. In `nmacReal` the outer computation is one call

$$
f(u_O,\mathsf{pad}_C(z)).
$$

The concrete outer computation after its run-up is

$$
\operatorname{Casc}_f(u_O,\tau(M,z)).
$$

The list $\tau(M,z)$:

- contains the item count before the digest;
- contains the output-length field;
- includes the hash's native final padding; and
- may contain several compression blocks.

It is therefore neither a fixed block nor generally a one-call function of
$z$. The outer suffix has fixed **byte length** for fixed $L$, but its count
field varies with $M$. Calling it a “fixed outer tail” without this
qualification would be incorrect.

There are two faithful ways forward.

1. Keep the frozen theorem unchanged and let $\varepsilon_{\rm C2SP}$ include
   both the domain-separated run-up replacement and the framed multi-block
   outer-envelope-to-NMAC normalization. Prove a separate bound

   $$
   \varepsilon_{\rm C2SP}
   \le \varepsilon_{\rm runup}+\varepsilon_{\rm outer}
   $$

   using ordinary compression-PRF distances and exact call accounting.

2. Prove a generalized framed-NMAC theorem whose outer map is

   $$
   (M,z)\mapsto\operatorname{Casc}_f(u_O,\tau(M,z)),
   $$

   using the envelope-unambiguity lemma in place of Gaži's one-block
   embedding. This is mathematically closer to C2SP but is a new theorem; it
   is not an instantiation of the already-frozen `sequenceMAC_prf_bound`.

For this task, option 1 is the exact reuse route. The phrase “absorb the fixed
outer tail” should mean proving the separate $\varepsilon_{\rm outer}$
reduction for this fixed-length framed cascade, not rewriting the concrete
outer hash definitionally to one compression call.

## 6. Pulling the generic theorem back to `InputSequence`

Let

$$
\mathsf{InputIdeal}
 :=\texttt{PFunPDS.URF (X := InputSequence) (Y := C)}.
$$

Once `blockifyEncodeItems_injective` is proved, uniform-function restriction
along $\bar\beta$ gives

$$
\bar\beta^*(\mathsf{macIdeal}_\ell)=\mathsf{InputIdeal}.
$$

This is the same finite-law fact as `uniform_restrict`, already wrapped in the
Gaži file as `gazi_uniform_restrict`. The simple converter makes exactly one
translated query per outside query, so query filtering is preserved, and the
$\Delta$ data-processing step gives

$$
\Delta(\lceil q\rceil\bar\beta^*P,
       \lceil q\rceil\bar\beta^*Q)
\le
\Delta(\lceil q\rceil P,\lceil q\rceil Q).
$$

Apply the $\Delta$ triangle law through
$\bar\beta^*(\mathsf{nmacReal})$, use this data-processing inequality, rewrite
the pulled-back ideal by injectivity, and invoke the proven block theorem.

Writing

$$
\varepsilon_f(q)
 :=\Delta(\lceil q\rceil\mathsf{compReal}_f,
          \lceil q\rceil\mathsf{compIdeal}),
$$

the result is

$$
\boxed{
\begin{aligned}
&\Delta(\lceil q\rceil\mathsf{ConcreteReal}_{f,S},
        \lceil q\rceil\mathsf{InputIdeal})\\
&\qquad\le
  \varepsilon_{\rm C2SP}(q)
  +\varepsilon_f(q)
  +((\ell+1)q)\,\varepsilon_{\rm na}
  +\frac{q^2}{|C|}.
\end{aligned}
}
$$

In Lean surface notation the semantically correct guardrail is:

```lean
-- GUARDRAIL: concrete C2SP SequenceMAC (F = 1), over InputSequence.
theorem sequenceMAC_prf_bound_concrete
    (q ℓ : ℕ) (f : C → B → C) (padC : C ↪ B)
    (S : ByteString) (DK : Dist MacKey)
    (hℓ : ∀ M : InputSequence,
      (codec.blockify (encodeItems M)).length ≤ ℓ)
    (hβ : Function.Injective
      (fun M : InputSequence => codec.blockify (encodeItems M)))
    (εna : NNReal) (hna : MACPRF.CompNASecure q f εna) :
    Δ(⌈q⌉ concreteSequenceMACReal codec iv f S DK,
      ⌈q⌉ PFunPDS.URF (X := InputSequence) (Y := C))
      ≤ epsC2SP q ℓ codec iv f padC S DK
        + Δ(⌈q⌉ MACPRF.compReal f, ⌈q⌉ MACPRF.compIdeal)
        + (((ℓ + 1) * q : ℕ) : ℝ) * (εna : ℝ)
        + ((q ^ 2 : ℕ) : ℝ) / (Fintype.card C : ℝ)
```

The displayed header is schematic about the finite key subtype and codec
boundary package, which do not yet exist. Its mathematical subject and every
term in the inequality are fixed. `epsC2SP` is the filtered $\Delta$ defined
above, not an unproved numeric constant.

There is no corresponding literal SequenceHash PRF guardrail from the current
premises: literal SequenceHash has $K=""$ and $F=2$. Its exact law-level
realization is already `sequenceHashSystem_realization`. To compare that
unkeyed construction with a uniform random function, one must separately
specify which hidden randomness is sampled in the underlying $H$; the frozen
independent-key NMAC theorem does not supply it.

## 7. Proof plan

1. **Exact byte-law realization.** Define the keyed $F=1$ pure construction
   and `sequenceMACStep`; prove `sequenceMACSystem_realization` by adapting the
   existing literal SequenceHash realization. Account for long $K$ and long
   fixed $S$ exactly.

2. **MD boundary realization.** Add the weakest raw-block/boundary API needed
   to split after `HeaderI || K'` and `HeaderO || S' || K'`. Use
   `mdIterate_append` to obtain the inner and outer cascade equations.

3. **Block map.** Define $\bar\beta:M\mapsto\operatorname{BlockString}B\ell$.
   Discharge its length field with $h_\ell$. Prove its injectivity from
   `encodeItems_injective` plus codec serialization/padding faithfulness.

4. **Ideal transport.** Apply `uniform_restrict` to prove
   $\bar\beta^*(\mathsf{macIdeal})=\mathsf{InputIdeal}$. Prove the one-query
   simple-converter/filter compatibility and the corresponding $\Delta$
   data-processing lemma if no exact packaged statement is available.

5. **Concrete bridge.** Define `epsC2SP` as the exact filtered $\Delta$ from
   concrete SequenceMAC to pulled-back `nmacReal`. Split its later proof into
   the ordinary-PRF run-up part and the framed outer-cascade normalization.
   Do not identify the latter with a single call.

6. **Generic theorem.** Instantiate `sequenceMAC_prf_bound` with the
   independent-uniform pair, for which its generic `epsKS` is zero, or invoke
   `nmac_prf_bound` directly. Pull the result back along $\bar\beta$.

7. **Assemble.** Use the $\Delta$ triangle law, rewrite the pulled-back ideal,
   and normalize the arithmetic. No extra concrete prefix-free premise enters
   this proof: `exists_prefixFree_appendDelimiter` has already discharged that
   step inside the generic theorem.

## 8. Reuse versus genuinely new work

### Reuse unchanged

- `SequenceHash.MACPRF.sequenceMAC_prf_bound`: the frozen abstract
  `BlockString B ℓ` theorem.
- `SequenceHash.MACPRF.nmac_prf_bound`: the independent-uniform specialization
  used under the concrete bridge.
- `SequenceHash.MACPRF.exists_prefixFree_appendDelimiter`: the actual
  prefix-free discharge.
- `SequenceHash.MACPRF.gazi_uniform_restrict` / `uniform_restrict`: ideal
  random-function restriction along an injection.
- `SequenceHash.encodeItems_injective`: unique parsing of LSBF-framed items.
- `SequenceHash.encodeMSBF_injective`: parsing the fixed-width outer count and
  length fields.
- `SequenceHash.sequenceHash_collision_of_distinct_inputs`: existing literal
  $F=2$ envelope-unambiguity/collision theorem and proof template for $F=1$.
- `SequenceHash.RandomSystemsModel.sequenceHashSystem_realization`: exact
  literal SequenceHash law and template for the keyed realization.
- `SequenceHash.mdIterate_append`: cascade splitting once the codec supplies
  the block-list append equation.
- `PFunPDS.applyDDC_ofFunDist`, `PFunPDS.applyDDC_simple_ofFunDist`, and the
  simple-converter realization laws: law-level translation and precomposition.
- the pure CR18 triangle and converter data-processing laws for $\Delta$.

### Genuinely new

- `sequenceMAC`/`sequenceMACStep`/`sequenceMACSystem_realization` for the
  keyed $F=1$ construction. The existing converter realizes only $F=2$ with an
  empty key.
- a raw-block/boundary extension of the codec, sufficient to prove the two
  append equations around the aligned C2SP prefixes.
- `blockifyEncodeItems_injective`, proved from `encodeItems_injective` and a
  minimal codec-faithfulness premise; this is injectivity, not prefix-freeness.
- the bounded map
  $\bar\beta:\texttt{InputSequence}\hookrightarrow\texttt{BlockString B ℓ}$
  and its ideal-transport equation.
- the keyed $F=1$ envelope-unambiguity lemma, adapted from
  `sequenceHash_collision_of_distinct_inputs`.
- `epsC2SP` and its later quantitative split into the domain-separated run-up
  reduction and the multi-block outer-envelope normalization.
- if option 2 is chosen instead, a generalized framed-NMAC theorem. That would
  not be a direct use of the frozen block theorem and should be scheduled as a
  separate result.

### Explicit assumptions in the concrete theorem

- finiteness/nonemptiness and decidable equality for $B$ and $C$;
- $C=\texttt{HashOutput L}$ or an explicit equivalence between them;
- the block-length bound $h_\ell$;
- the minimal codec boundary and injectivity laws until proved for a concrete
  MD padding;
- `CompNASecure q f εna` and the adaptive compression distance already present
  in the frozen theorem;
- a key distribution satisfying the C2SP key-length rule;
- either $|S|\le b$ for the clean first theorem, or inclusion of the long-$S$
  derivation in `epsC2SP`.

Nothing assumes `MDCodec.blockify_prefixFree`. Nothing assumes that
`encodeItems_injective` is prefix-free. The concrete theorem becomes a direct
corollary of the frozen block theorem only after the codec realization,
injective pullback, and exact C2SP-to-NMAC bridge have been supplied.

## 9. Obligation ledger

| Obligation | Status | Exact discharge or premise |
|---|---|---|
| Literal $F=2$ byte-law realization | **DISCHARGED** | `sequenceHashSystem_realization` |
| Keyed $F=1$ byte-law realization | **NEW** | `sequenceMACSystem_realization` |
| Unique parsing of item sequences | **DISCHARGED** | `encodeItems_injective` |
| Fixed-width parsing of outer count/length | **DISCHARGED** | `encodeMSBF_injective` plus the fixed digest length; the existing collision proof is the template |
| Prefix-free queries needed by Gaži Proposition 1 | **DISCHARGED** | internally by `exists_prefixFree_appendDelimiter`; no concrete codec premise |
| Prefix-freeness of `encodeItems` | **FALSE / NOT USED** | one empty item strictly prefixes two empty items |
| Split MD at C2SP's aligned prefixes | **NEW CODEC LAW** | raw-block append equations, then `mdIterate_append` |
| Injectivity of $M\mapsto\beta(M)$ | **PARTLY DISCHARGED** | `encodeItems_injective` plus a still-needed codec-faithfulness law |
| Bound $|\beta(M)|\le\ell$ | **ASSUMED** | explicit $h_\ell$ or a bounded input subtype |
| Output type identification | **ASSUMED / INSTANTIATED** | $C=\texttt{HashOutput L}$ or an equivalence |
| Compression nonadaptive term | **ASSUMED** | `CompNASecure q f εna`, exactly as in the frozen theorem |
| Compression adaptive term | **EXPLICIT RHS TERM** | $\Delta(\lceil q\rceil\mathsf{compReal},\lceil q\rceil\mathsf{compIdeal})$ |
| Concrete run-up and outer-envelope bridge | **EXPLICIT RHS TERM; BOUND NEW** | `epsC2SP`; later split into ordinary-PRF run-up and framed outer-cascade reductions |
| Long customization | **ASSUMED SHORT OR INCLUDED IN BRIDGE** | $|S|\le b$, or account for the one-time $H(S)$ path inside `epsC2SP` |
