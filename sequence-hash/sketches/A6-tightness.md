# A6 - Closing the Gaži reduction loss in the standard model

Pen-and-paper sketch only. Source: Backendal--Bellare--Günther--Scarlata,
*When Messages are Keys: Is HMAC a dual-PRF?* (2023), especially Lemmas 1--3,
Theorem 5, and Appendix B ([local PDF](../2023-861.pdf)). The eventual R6
statement is a pure RandomSystems PDS statement. The source's game and
adversary notation is quoted only to identify its theorem; it is not part of
the proposed model.

Every new C2SP object below starts from the canonical

$$
\operatorname{SequenceFunction}(MD[f],K,S,F;M),
\qquad F=F_{\rm SEQMAC}=1.
$$

The exact bridge already proved is
`sequenceMAC_eq_sequenceFunction`; no inner input, outer input, or converter
step is redefined here.

## 0. Source correction and what R6 can actually establish

Backendal et al. do not state a theorem in Gaži's notation and do not claim
that every factor in Gaži's NMAC analysis disappears. Their relevant new
result is a **strong multi-user, standard-model** PRF reduction for the
cascade and NMAC. It removes degradation in the number of active users. When
the transient cascade-prefix keys in Gaži's proof are viewed as users, that
is exactly the tool that removes Gaži's extra factor $q$.

The source still pays linearly for cascade depth. Its NMAC theorem has a
coefficient $m+2$, not a constant coefficient. Thus the honest R6 verdict is:

$$
\text{Gaži: }(\ell+1)q\,\varepsilon_{\rm na}
\quad\longrightarrow\quad
\text{Backendal: depth}\cdot\varepsilon_{\rm mu},
$$

where $\varepsilon_{\rm mu}$ is one adaptive strong multi-user compression-PRF
term. The query factor is removed; the cascade-depth factor remains.

This result is directly adaptable to the **independent-key, NMAC-normalized
core** already represented by `nmacReal`. It is not directly a theorem about
the complete C2SP construction. Canonical SequenceMAC additionally has:

1. one raw key whose framed run-ups induce the two effective roles, rather
   than two initially independent uniform $c$-bit NMAC keys;
2. a canonical multi-block outer `MD[f]` call, rather than NMAC's single final
   compression call;
3. optional raw `Derive(K)` and `Derive(S)` calls; and
4. a concrete byte-to-block codec whose current public law is injectivity,
   deliberately weaker than prefix-freeness.

Consequently R6 can prove a tight standard-model bound for C2SP SequenceMAC
only after a SequenceHash-specific **safe schedule normalization** theorem.
The existing `epsC2SP` is an exact $\Delta$ measuring this gap, but it hides
the raw-derivation residual. R6 should refine it into a safe schedule term plus
the already-defined, accountable `DeriveCost_SEQ`; it must not claim that
Backendal discharges this bridge.

This is analogous to A5 Section 0: the source theorem is useful and strong,
but its literal subject is not yet the complete C2SP object.

## 1. The exact loss in R2/Gaži

### 1.1 The current R2 bound

The proved R2 endpoint `sequenceMAC_prf_bound_concrete` has the form

$$
\Delta(\lceil q\rceil\,\mathsf{SequenceMAC},
       \lceil q\rceil\,\mathsf{URF})
\le
\varepsilon_{\rm C2SP}
+\varepsilon_{\rm comp}
+(\ell+1)q\,\varepsilon_{\rm na}
+\frac{q^2}{|C|}.
$$

Here $\varepsilon_{\rm comp}$ is the adaptive single-key compression-PRF
distance `epsComp`, while $\varepsilon_{\rm na}$ is the fixed-query
single-key hypothesis `CompNASecure`. The last term is a deliberately loose
version of the uniform-output collision probability.

### 1.2 The loss occurs at one identifiable composition

The factor $(\ell+1)q$ is not caused by C2SP framing, the outer random
function hop, or the birthday bound. It is the product of two separate
hybrids in Gaži Appendix A, visible by name in
`SequenceMACPRF.lean`.

1. `gazi_lemma6_row_hybrid` replaces $q$ independently keyed compression
   rows one at a time. A single-key non-adaptive assumption therefore gives

   $$
   \Delta_{\rm row}
   \le q\,\varepsilon_{\rm na}.
   $$

2. `gazi_lemma5_depth_hybrid` replaces the cascade at each of its $d$ block
   positions. It gives

   $$
   \Delta_{\rm casc}
   \le d\,\Delta_{\rm row}.
   $$

3. `cascade_na_pf_fixedQuery_bound` composes the two bounds:

   $$
   \Delta_{\rm casc}
   \le d q\,\varepsilon_{\rm na}.
   $$

4. The prefix-free collision reduction appends one block, so R2 instantiates
   $d=\ell+1$.

The exact loose step is therefore **the row hybrid's decision to pay the
single-key assumption independently for each of the $q$ live prefix states**.
Those states are not $q$ sequential attacks on one secret key. They are at
most $q$ dynamically created keys for the same compression family, precisely
the strong multi-user setting.

There are two lesser losses in the displayed R2 envelope:

- the adaptive outer hop and the cascade reduction are left as different
  assumptions, $\varepsilon_{\rm comp}$ and $\varepsilon_{\rm na}$; and
- `gazi_outer_random_collision_bound` weakens the exact pair-collision term
  to $q^2/|C|$.

Backendal addresses both in its NMAC theorem: all compression calls are
charged to one adaptive strong multi-user assumption, and the collision term
is $\binom q2/|C|$.

## 2. Backendal's improvement, exactly

### 2.1 The source bounds

The underlying two-tier statement is Backendal Lemma 1
([Section 4, Equation (1), p. 15](../2023-861.pdf#page=15)):

$$
\boxed{
\operatorname{Adv}^{\rm PRF}_{\rm 2CSC}(A_{\rm 2CSC})
\le
\operatorname{Adv}^{\rm PRF}_{f}(A_f)
+n\cdot\operatorname{Adv}^{\rm PRF}_{h}(A_h).
}
$$

The first tier supplies the initial key for the second-tier cascade. Lemma 2
instantiates that first tier by the family of all functions on the user index;
its PRF advantage is exactly zero. This turns many independently initialized
cascade users into one 2CSC key and gives the following corollary.

Backendal Lemma 2 states the strong multi-user cascade reduction
([Section 4, Equation (2), p. 15](../2023-861.pdf#page=15)):

$$
\boxed{
\operatorname{Adv}^{\rm PRF}_{h^*}(A_{h^*})
\le n\cdot\operatorname{Adv}^{\rm PRF}_{h}(A_h).
}
$$

The cascade adversary is prefix-free and its messages have at most $n$
blocks. The constructed compression adversary makes at most
$Q^{\rm Fn}(A_{h^*})$ `New` queries and the same number of `Fn` queries. In
particular, neither its resources nor its advantage bound contain the total
number of initialized cascade users.

The main NMAC theorem used by R6 is Backendal Theorem 5
([Section 5.2, Equation (14), pp. 20--22](../2023-861.pdf#page=21)). In the
paper's notation, let each NMAC query have bit length at most $L$, put

$$
m=1+\left\lceil\frac{L}{b}\right\rceil,
\qquad q_f=Q^{\rm Fn}(A),
$$

and assume $m q_f<2^b$. Then the theorem's bound is

$$
\boxed{
\operatorname{Adv}^{\rm PRF}_{\rm NMAC}(A)
\le
(m+2)\cdot\operatorname{Adv}^{\rm PRF}_{h}(A_h)
+\frac{q_f(q_f-1)}{2^{c+1}}.
}
$$

The constructed $A_h$ makes $Q^{\rm Fn}(A)$ `Fn` queries and
$\max(Q^{\rm New}(A),Q^{\rm Fn}(A))$ `New` queries, with approximately the
same running time. This is the bound R6 must preserve before adapting it; a
claim with no depth coefficient would not be Backendal's theorem.

Since $|C|=2^c$,

$$
\frac{q_f(q_f-1)}{2^{c+1}}
=\frac{\binom{q_f}{2}}{|C|}.
$$

### 2.2 How the factor is recovered

The tightening mechanism has four parts.

1. **Make the collision schedule non-adaptive.** In Theorem 5, games
   $G_2,G_3$ answer construction queries with independent random strings.
   The queried messages can then be recorded first and the cascade collision
   test performed afterward.
2. **Make the recorded cascade queries prefix-free.** For each actual NMAC
   user $i$, the reduction chooses a block $X_i$ absent from every recorded
   message block for that user and queries $M_{i,j}\|X_i$. Appending the same
   block preserves any existing cascade collision while ensuring the new
   queries are prefix-free. The source side condition $m q_f<2^b$ guarantees
   that $X_i$ exists.
3. **Treat prefix states as users.** Lemma 1 chooses a random depth
   $\omega\in\{1,\ldots,n\}$. Every live prefix
   $(i,A,S[1..\omega-1])$ receives a fresh user/key index in one strong
   multi-user PRF experiment for $h$. Hence a whole row is paid by one
   multi-user advantage, not by $q$ single-key hybrids. Telescoping over
   $\omega$ leaves the necessary depth factor $n$.
4. **Merge the outer and cascade reductions.** Theorem 5 has one outer-call
   reduction with weight $1$ and one cascade reduction with weight $m+1$.
   Lemma 3 merges them, giving the coefficient $m+2$ multiplying a single
   compression-PRF advantage.

Appendix B makes the key point explicit: unused initialized users disappear,
and at every non-first cascade layer there are at most $Q^{\rm Fn}$ keys that
are actually exercised ([Appendix B.1--B.2, pp. 46--49](../2023-861.pdf#page=46)).

Thus Backendal does not use a better estimate for each Gaži row. It changes
the **assumption and reduction interface** from $q$ separate single-key
non-adaptive instances to one adaptive strong multi-user instance.

## 3. Term-by-term and event-by-event C2SP adaptation

The table uses the required verdicts `KILLED`, `SHRUNK`, and `REMAINS`.
`KILLED` never means that the MD functional graph becomes collision-free; it
means only that the named source bookkeeping event is impossible or
unnecessary for canonical SequenceFunction.

| Backendal term, step, or event | Source role | C2SP verdict | SequenceHash reason and replacement |
| --- | --- | --- | --- |
| $n\operatorname{Adv}^{\rm PRF}_h(A_h)$ in Lemma 2 | One hybrid per cascade depth, with every live prefix at that depth represented as a user | **REMAINS** | Cascade depth is inherent. FIELD, role tags, and secret-bearing inputs do not remove random functional-graph transitions. Replace $n$ by the exact canonical role-local block-depth supplied by the `SequenceFunction`/codec trace theorem. |
| The missing factor in the number of users | Lemma 2 embeds all used cascade keys in one strong multi-user compression experiment | **KILLED** | This is Backendal's actual tightening. In the PDS translation, one `multiCompReal`/`multiCompIdeal` distance pays for the whole row. No factor $q$ multiplies the per-depth term. |
| Outer-call weight $1$ plus appended-cascade weight $m+1$ | Lemma 3 produces $(m+2)\operatorname{Adv}^{\rm PRF}_h(A_h)$ | **REMAINS, with canonical accounting** | INNER/OUTER separation removes related-key analysis, not the compression calls. For literal NMAC the coefficient stays $m+2$. For canonical SequenceFunction, the exact outer MD tail and safe run-up calls must be counted rather than silently called one compression step. |
| Collision event `bad`: two distinct construction queries for one user have the same inner cascade output | This is the only identical-until-bad event in Theorem 5 | **REMAINS** | `encodeItems_injective` and `sequenceHash_collision_of_distinct_inputs` show that distinct logical inputs are not aliases. They do not prevent two distinct same-role MD paths from meeting in $C$. This is the cascade-inherent event. |
| $q_f(q_f-1)/2^{c+1}=\binom{q_f}{2}/|C|$ | Collision probability for independent random construction answers in $G_4$ | **REMAINS** | Use the exact framework quantity `pairCollisionUnionBound (HashOutput L) q`. Do not weaken it back to $q^2/|C|$. |
| Fresh appended block $X_i$ and side condition $m q_f<2^b$ | Converts recorded colliding strings into prefix-free cascade queries | **SHRUNK to a deterministic proof device; no bad event** | FIELD framing (`encodeItems_injective`, `sequenceHash_collision_of_distinct_inputs`) kills ambiguity, but the current `MDCodec.blockify_encodeItems_injective` is explicitly weaker than prefix-freeness. Reuse R2's `exists_prefixFree_appendDelimiter` and its trivial-bound cardinality split, or later prove a stronger native-codec lemma. Do not invent a probabilistic C2SP prefix event. |
| Different initialized NMAC users | A naive single-user-to-multi-user hybrid would lose their number; Theorem 5 avoids it | **KILLED as a multiplier** | Strong multi-user compression security accounts for all active users in one term. C2SP's single outside key makes this no harder, although its transient prefix states still require the same multi-user interface. |
| Independent NMAC inner and outer keys | A premise of the source NMAC model | **SHRUNK to a schedule bridge** | Canonical SequenceMAC has one raw key, but `headerI_ne_headerO` and `sequenceMACInnerInput_ne_outerInput` prove distinct roles. Therefore the bridge is ordinary data-input/schedule PRF work, never an HMAC ipad/opad RKA term. It is not automatically zero and is named $\varepsilon_{\rm sched}^{\rm SEQ}$ below. |
| Any HMAC ipad/opad or related-key event | Relevant to HMAC reductions, absent from Backendal Theorem 5 itself | **KILLED / NOT APPLICABLE** | INNER/OUTER domain separation makes SequenceMAC NMAC-like. The effective role inputs have distinct leading bytes; no related-pad term may be imported into R6. |
| Inner/outer, derive/inner, derive/outer cross-role collision events that a literal transcription might add | Potential extra union terms when adapting NMAC to a shared construction | **KILLED outside the raw-prefix residual** | Proven CROSS-ROLE facts in `DomainSeparation.lean` make framed inner and outer inputs disjoint and give the exact conditional raw-derive separation. Hence there is no general cross-role union term. |
| Long raw `Derive(K)` overlap | Not present in Backendal's NMAC model | **SHRUNK, new and accountable** | The only unframed-key exception is `DerivePrefixHit_SEQ`. Charge its exact sampled-key mass `DeriveCost_SEQ b S DK`, once, because the key is sampled once and reused. Do not multiply it by $q$. |
| Long fixed `Derive(S)` | Not present in Backendal's NMAC model | **SHRUNK to a side condition plus call count** | Under `DeriveSafeS_SEQ`, `sequenceMAC_customizationDerive_separated_of_safe` kills cross-role overlap. Its compression work still belongs in the canonical schedule depth; it is not a new collision union term. |
| Fully offline steering of a cascade to a chosen state | A concern in generic ideal-compression analyses, not a separate event in Theorem 5 | **SHRUNK to key guessing / schedule security** | SECRET KEY IN THE INPUT prevents free steering of canonical secret-bearing run-ups. Any raw exception is already in `DeriveCost_SEQ`; the remaining computational cost is in $\varepsilon_{\rm sched}^{\rm SEQ}$ or the strong multi-user compression term. |

The table deliberately leaves the same-role collision and depth terms. Domain
separation collapses aliasing and cross-role bookkeeping; it does not erase
the Merkle--Damgård functional graph.

## 4. R2 versus R4 versus R6

Let $N=|C|=2^c$. Let $\varepsilon_{\rm mu}(q,f)$ denote the pure-PDS strong
multi-user compression distance defined in Section 5. Let
$B_{\rm SEQ}=B_{\rm cascade}+B_{\rm key}+\operatorname{DeriveCost}_{\rm SEQ}$
be A4's explicit ideal-compression bound.

| Rung | Model and surface | Bound shape | Tightness verdict | What it fixes |
| --- | --- | --- | --- | --- |
| **R2 / Gaži 2014** | Standard-model compression family; pure filtered PDS $\Delta$; single-key adaptive term plus a single-key non-adaptive assumption | $\varepsilon_{\rm C2SP}+\varepsilon_{\rm comp}+(\ell+1)q\varepsilon_{\rm na}+q^2/N$ | Loose by a factor $q$ in the cascade reduction and by a coarse birthday envelope | Establishes the first concrete SequenceMAC-to-NMAC standard-model route; isolates `epsC2SP` |
| **R4 / Shen 2025** | One public ideal compression function shared by `Prim` and `Eval`; H-technique extended transcripts | $B_{\rm SEQ}$, dominated by $\Theta((pq\lambda+q^2\lambda)/N)$, plus key and derive costs | Tight in the generic/ideal-compression sense up to constants and lower-order terms; no $(\ell+1)q\varepsilon_{\rm na}$ | Removes the Gaži reduction artifact by analyzing the ideal functional graph directly; identifies inherent cascade losses |
| **R6 / Backendal 2023 adapted** | Standard-model compression family; pure filtered PDS $\Delta$; one adaptive strong multi-user compression term | NMAC core: $(m+2)\varepsilon_{\rm mu}+\binom q2/N$. C2SP headline: safe schedule cost $+$ depth-weighted $\varepsilon_{\rm mu}$ $+$ exact birthday $+$ `DeriveCost_SEQ` | Removes Gaži's factor $q$ and all user-count degradation, but retains the necessary depth factor | Supplies the standard-model refinement absent from R4; it does not improve or replace Shen's ideal-compression $B_{\rm SEQ}$ |

The R4 and R6 bounds are not additive and neither dominates the other without
an extra theorem relating their models. R4 says what happens when the shared
compression primitive is ideal and directly queryable. R6 says how to reduce
the concrete standard-model NMAC core to strong multi-user PRF security of the
compression family. Backendal's contribution **on top of** Shen is therefore
a standard-model instantiation route with no query/user hybrid loss, not a
smaller version of $B_{\rm SEQ}$.

## 5. SequenceHash-specific R6 statement

### 5.1 The strong multi-user PDS term

The R2 file already has the right row laws:

- `multiCompReal u f` samples $u$ independent chaining keys and exposes
  $(i,x)\mapsto f(K_i,x)$;
- `multiCompIdeal u` is a uniform random function on the tagged domain.

Define the scheme-agnostic strong multi-user distance

$$
\varepsilon_{\rm mu}(q,u,f)
:=
\Delta\!\left(
  \lceil q\rceil\,\mathsf{multiCompReal}_{u,f},
  \lceil q\rceil\,\mathsf{multiCompIdeal}_{u}
\right).
$$

For the cascade row, $u=q$ is a safe finite address space; only used rows
matter. This is the PDS translation of Backendal's `New`/`Fn` resource bound,
with no game or adversary object.

Replacing `gazi_lemma6_row_hybrid` by this one row distance while reusing
`gazi_lemma5_depth_hybrid` yields the tight generic cascade endpoint

$$
\Delta_{\rm casc}^{\rm fixed}
\le d\,\varepsilon_{\rm mu}(q,q,f),
$$

not $dq\varepsilon_{\rm na}$.

For the literal R2 NMAC normalization, the Backendal-shaped PDS corollary is

$$
\boxed{
\Delta(\lceil q\rceil\,\mathsf{nmacReal}_{\ell,f},
       \lceil q\rceil\,\mathsf{macIdeal}_{\ell})
\le
(\ell+2)\,\varepsilon_{\rm mu}(q,q,f)
+\operatorname{pairCollisionUnionBound}(C,q).
}
$$

The $\ell+2$ is the R2 normalization of Backendal's $m+2$: at most $\ell$
inner blocks, one source/normalization depth needed for the prefix-free
cascade endpoint, and one outer compression hop. If the canonical codec's
strengthening proves that the extra normalization depth is unnecessary, the
trace theorem may reduce this coefficient; R6 must use the proved trace count,
not assume the improvement.

### 5.2 The honest C2SP headline

Let $d_{\rm body}^{\rm SEQ}$ be the proved maximum number of compression-PRF
layers in the normalized canonical inner/outer body. Let
$\varepsilon_{\rm sched}^{\rm SEQ}$ be the pure filtered $\Delta$ from the
**safe** canonical SequenceFunction schedule to the independent-role NMAC
normal form. It includes the exact framed run-up and multi-block outer-tail
normalization, but excludes the raw event already measured by
`DeriveCost_SEQ`.

The proposed R6 bound is

$$
\boxed{
\begin{aligned}
&\Delta(\lceil q\rceil\,
  \operatorname{SequenceFunction}(MD[f],K,S,1;\cdot),
  \lceil q\rceil\,\mathsf{URF})\\
&\qquad\le
\varepsilon_{\rm sched}^{\rm SEQ}
+\mathbf 1_{\{q>0\}}\operatorname{DeriveCost}_{\rm SEQ}(b,S,D_K)
+d_{\rm body}^{\rm SEQ}\,\varepsilon_{\rm mu}(q,q,f)
+\operatorname{pairCollisionUnionBound}(C,q).
\end{aligned}}
$$

For the present NMAC bridge,
$d_{\rm body}^{\rm SEQ}=\ell+2$. A future direct canonical trace proof may
replace it by a smaller exact count, but may not delete genuine outer or
cascade layers. The indicator on `DeriveCost_SEQ` matches the existing R5
surface: no construction query means the raw derive event is unobservable.

This statement is honest in two ways.

1. It exposes the SequenceHash-specific schedule gap rather than attributing
   it to Backendal.
2. It does not add A4's information-theoretic $B_{\rm SEQ}$ to a
   standard-model reduction. R4 and R6 are alternate theorem routes.

## 6. Proof skeleton in the pure PDS idiom

1. **Canonical realization.** Rewrite the real law through
   `sequenceMAC_eq_sequenceFunction` and
   `sequenceMACStep_eq_sequenceFunctionStep`. Use the existing converter
   realization; introduce no NMAC-shaped duplicate of the C2SP function.
2. **Raw-derive split.** Condition the sampled key on
   `DerivePrefixHit_SEQ`. Charge the bad key mass exactly by
   `DeriveCost_SEQ`. On the complement, reuse
   `sequenceMAC_keyDerive_separated_of_not_prefixHit`; use
   `sequenceMAC_customizationDerive_separated_of_safe` for long fixed $S$.
3. **Safe schedule normalization.** Use `headerI_ne_headerO`,
   `sequenceMACInnerInput_ne_outerInput`, and within-role injectivity to map
   the safe canonical call trace to the independent-role NMAC normal form.
   Bound this pure PDS hop by $\varepsilon_{\rm sched}^{\rm SEQ}$. No RKA or
   related-pad object appears.
4. **Outer compression replacement.** Charge the final outer role to the same
   strong multi-user compression distance used by the cascade. A one-user
   slice embeds into the $q$-row law; converter DPI supplies monotonicity.
5. **Collision reduction.** Reuse the R2 condition-equivalence/hash-then-URF
   endpoint. FIELD framing removes ambiguity. For the separate technical
   prefix-free premise, reuse `exists_prefixFree_appendDelimiter` and its
   nontrivial/trivial cardinality split; this is a deterministic reduction
   step, not an added bad event. On good transcripts, distinct outer calls
   receive independent uniform outputs.
6. **Strong multi-user cascade replacement.** At each depth, expose every
   live prefix state as one row of `multiCompReal`. Bound the entire row by
   $\varepsilon_{\rm mu}$ once, then reuse the existing depth telescope. This
   is Backendal Lemma 1's random-level analysis expressed as a PDS adjacent
   sum.
7. **Exact birthday leaf.** Use `pairCollisionUnionBound`, not the R2
   $q^2/N$ weakening.
8. **Assemble.** Apply `maxAdvantage_le_adjacent_sum` or the ready short-hop
   triangle theorem. The endpoint remains
   $\Delta(\lceil q\rceil\text{ real},\lceil q\rceil\text{ URF})$ throughout.

No H-technique theorem, `advPRF`, `advNPRF`, game, oracle, or adversary object
is introduced in this adapted proof.

## 7. Proposed G6 guardrail shape

The schematic Lean surface should have one generic strong-multi-user cascade
helper and one canonical SequenceFunction headline. Names may change when the
manager freezes G6, but the mathematical shape should not.

```lean
/-- Scheme-agnostic strong multi-user compression distance. -/
noncomputable def epsCompMU (q u : Nat) (f : CompressionFamily C B) : Real :=
  Δ(⌈q⌉ (multiCompReal u f).val, ⌈q⌉ (multiCompIdeal u).val)

/-- Backendal Lemma 2 / Theorem 5 core, on the existing PDS laws. -/
theorem nmac_prf_bound_strong_mu
    (q ell : Nat) (f : CompressionFamily C B) (pad : C ↪ B) :
    Δ(⌈q⌉ nmacReal ell f pad, ⌈q⌉ macIdeal ell) ≤
      (ell + 2 : Real) * epsCompMU q q f +
        (pairCollisionUnionBound C q : Real) := by
  sorry

-- GUARDRAIL (R6): canonical C2SP SequenceFunction, standard-model tight route.
theorem sequenceFunction_prf_bound_strong_mu
    (q ell dBody : Nat)
    (codec : MDCodec B) (iv : HashOutput L)
    (f : CompressionFamily (HashOutput L) B)
    (S : ByteString) (DK : Dist SequenceMACKey)
    (hDK : DK.isProbDist)
    (hSafeS : DeriveSafeS_SEQ b S DK)
    (hTrace : SequenceFunctionBodyDepth codec b S ell dBody)
    (epsSchedule : Real)
    (hSchedule : SequenceFunctionSafeScheduleBound
      codec iv f b S DK epsSchedule) :
    Δ(⌈q⌉ sequenceFunctionReal codec iv f b S DK,
      ⌈q⌉ PFunPDS.URF) ≤
        epsSchedule +
        (if q = 0 then 0 else (DeriveCost_SEQ b S DK : Real)) +
        (dBody : Real) * epsCompMU q q f +
        (pairCollisionUnionBound (HashOutput L) q : Real) := by
  sorry
```

`sequenceFunctionReal`, `SequenceFunctionBodyDepth`, and
`SequenceFunctionSafeScheduleBound` are schematic names, not permission to
re-spell the construction. The first must be built directly from canonical
`sequenceFunction`/`sequenceFunctionStep`; the latter two are trace/property
facades over those existing definitions.

The guardrail must not replace $\varepsilon_{\rm mu}$ by
`CompNASecure`, weaken the birthday term to $q^2/N$, hide
`DeriveCost_SEQ` inside an opaque `epsC2SP`, or state an H-technique
advantage.

## 8. Reuse versus new infrastructure

| Layer | Verdict | Exact infrastructure plan |
| --- | --- | --- |
| Canonical construction | **Reuse** | `sequenceFunction`, `sequenceFunctionStep`, `sequenceMAC_eq_sequenceFunction`, `sequenceMACStep_eq_sequenceFunctionStep` |
| C2SP law and existing R2 bridge | **Reuse/refine** | `concreteSequenceMACReal`, `epsC2SP`, `sequenceMAC_prf_bound_concrete`; refine the exact bridge so its raw residual is exposed rather than duplicating the law |
| Independent-key NMAC core | **Reuse** | `nmacReal`, `macIdeal`, `nmacOuterRandom`, `gazi_outer_prf_hop`, and `maxAdvantage_filterQueries_seededHashThenURF_le` for the condition-equivalence collision spine |
| Strong multi-user row laws | **Reuse objects** | `multiCompReal`, `multiCompIdeal`; they already model Backendal's active users as one tagged PDS |
| Strong multi-user PRF distance | **New generic public facade** | Add `epsCompMU`/a named multi-user PRF distance at the RandomSystems complexity layer, not as a `backendal_*` or SequenceHash-local generic helper |
| Cascade depth hybrid | **Reuse** | `gazi_lemma5_depth_hybrid` and the framework adjacent-sum theorem; replace only the loose row premise |
| Single-row to strong-MU row bound | **New generic lemma** | Fixed-query transcript distance is bounded by the filtered $\Delta$ of the tagged multi-user PDS; place it with general fixed-query/complexity infrastructure |
| Outer single-user slice to MU | **Generalize in place** | A tagged-domain embedding plus `maxAdvantage_filterQueries_applyDDC_le`; no NMAC-specific DPI lemma |
| Triangle/telescope | **Reuse** | `maxAdvantage_triangle`, `maxAdvantage_le_adjacent_sum`, and `maxAdvantage_three_hop_le` |
| Exact birthday | **Reuse** | `pairCollisionUnionBound`, `pairCollisionUnionBound_le_birthday`, and the existing collision-cover/condition-equivalence endpoints |
| Uniform tagged restrictions | **Reuse** | `uniform_restrict` and the existing `Dist` product-map facts; no row-specific uniformity helper |
| Costed companion theorem | **Reuse/new split** | Keep G6 law-level. A later complexity corollary reuses `IsCostedReduction.comp`; only the strong-MU cascade resource map is new, with Backendal's `Fn`/`New` counts translated explicitly |
| FIELD separation | **Reuse with exact scope** | `encodeItems_injective` and `sequenceHash_collision_of_distinct_inputs` kill ambiguity. `MDCodec.blockify_encodeItems_injective` does not imply prefix-freeness; reuse `exists_prefixFree_appendDelimiter` for that separate reduction premise. |
| INNER/OUTER and CROSS-ROLE separation | **Reuse** | `headerI_ne_headerO`, `sequenceMACInnerInput_ne_outerInput`, the within-role injectivity facts, and the conditional derive-separation theorems in `DomainSeparation.lean` |
| Derive residual | **Reuse exactly** | `DerivePrefixHit_SEQ`, `DeriveCost_SEQ`, `DeriveSafeS_SEQ`, `sequenceMAC_keyDerive_separated_of_not_prefixHit`, `sequenceMAC_customizationDerive_separated_of_safe` |
| Safe schedule normalization | **New SequenceHash-specific theorem** | Prove over canonical `SequenceFunction`; this is the genuine R6 application work not supplied by Backendal |
| R4 H-technique | **Not used** | R4 remains the separate ideal-compression route. No `advPRF`, extended transcript, or equality-on-good endpoint in R6 |
| R5 / AbstractCrypto | **Reuse facts only** | Reuse the canonical model and `DeriveCost_SEQ`; the DRST simulator, `Constructs`, and indifferentiability composition are irrelevant to this standard-model reduction |

No framework theorem is generalized by this sketch task itself. The future
implementation should generalize the multi-user PRF facade and tagged-slice
DPI in place because they are scheme-agnostic; only the safe schedule theorem
belongs to SequenceHash.

## 9. Final verdict

Gaži's exact avoidable loss is the factor $q$ introduced by the Appendix-A
row hybrid before the depth hybrid. Backendal's strong multi-user cascade
lemma pays one adaptive compression-PRF advantage for the entire row, so the
NMAC bound becomes $(m+2)\varepsilon_{\rm mu}+\binom q2/|C|$. It retains the
depth factor because that is genuine black-box reduction cost.

For C2SP SequenceMAC, FIELD separation removes ambiguity events, while the
existing deterministic delimiter lemma discharges the distinct technical
prefix-free obligation. INNER/OUTER and CROSS-ROLE separation prevent
related-key and cross-role union terms; same-role functional-graph collisions
remain. The paper directly proves only the independent-key NMAC core. The
canonical SequenceFunction headline additionally needs the safe schedule
normalization, with raw long-derive risk charged once by the existing
`DeriveCost_SEQ`.
