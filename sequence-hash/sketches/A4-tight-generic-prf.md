# A4 - Tight generic PRF security for C2SP SequenceMAC (R4)

Pen-and-paper sketch only. Source: Shen--Zhang--Wang--Gu, *Tight Generic
PRF Security of HMAC and NMAC* (2025), Theorem 2 and Section 4
([local PDF](../2025-2260.pdf)). The proposed Lean surface is only a future
guardrail shape; this task neither implements definitions nor touches a build.

The paper is used only as a proof template. The result below is for the
canonical C2SP construction

$$
\operatorname{SequenceFunction}(MD[h],K,S,F_{\rm SEQMAC};M),
\qquad F_{\rm SEQMAC}=1,
$$

not for a re-spelled NMAC or HMAC.

## 1. Reference only: Shen Theorem 2 and its model

This subsection is the single reference statement of the paper's NMAC result.
It is not the proposed SequenceMAC theorem.

The paper samples one ideal compression function

$$
h\xleftarrow{\$}\operatorname{Func}
  (\{0,1\}^{c}\times\{0,1\}^{b},\{0,1\}^{c}),
\qquad b>c.
$$

The adversary has a joint adaptive interface:

- `Prim(x,m)` returns $h(x,m)$ and may be called at most $p$ times;
- `Eval(i,M)` returns NMAC under user $i$ in the real world and an independent
  random-function value $f_i(M)$ in the ideal world; there are at most $q$
  such calls and every padded message has at most $\ell$ blocks;
- the same $h$ answers `Prim` and all real construction calls;
- keys and internal compression calls are revealed after the interaction,
  with independent dummy keys/calls in the ideal extension;
- the adversary is deterministic without loss of generality, computationally
  unbounded, and may choose users and both query classes adaptively.

If $u$ users occur then $u\le q$. Shen's NMAC Theorem 2 states, exactly,

$$
\begin{aligned}
\operatorname{Adv}^{\rm prf}_{\rm NMAC}(A)
\le B_{\rm N}:={}&
 \frac{pq\ell}{2^c}
 +\frac{4q^2\ell}{2^c}
 +\frac{4q^2}{2^c}
 +\frac{2pq}{2^c}
 +\frac{32q^2\ell^4}{2^{2c}}\\
&+\frac{q^2(b+c+3+\ln p)}{2^{b+1}}
 +\frac{q^2\ell(\ln p+1)}{2^b}.
\end{aligned}
$$

The proof augments the transcript, defines four bad events in Section 4.2,
proves an ideal-world bound on their union in Section 4.3, and obtains on every
good attainable transcript $\tau$

$$
\frac{\Pr[X_1=\tau]}{\Pr[X_0=\tau]}=1.
$$

Thus its H-coefficient ratio defect is zero; all source loss is bad-transcript
mass.

## 2. SequenceMAC parameters and already-proved facts

Let $u\le q$ be the number of active users. Keys are sampled once per user
from a fixed C2SP-valid key law. For the explicit information-theoretic bound,
assume every secret-bearing block has conditional point probability at most
$2^{-\kappa_*}$, where a safe fixed-length-uniform specialization is

$$
\kappa_*:=\min\{\kappa,b,c\},\qquad \kappa\ge256.
$$

This hypothesis is necessary: C2SP requires at least 32 key bytes, but does not
itself prescribe a probability law on keys.

The following quantities come from the call trace of the canonical
`SequenceFunction`; they do not re-specify its byte inputs.

- $\lambda$ is the maximum number of role-local MD compression transitions
  exposed by one `Eval`, excluding the separately counted long-input
  derivations. It includes the canonical inner and outer framing overhead, not
  merely the number of message payload blocks.
- $r_K$ is the maximum number of compression calls in `Derive(K)` for one long
  key, and is zero for short keys. Put $D_K:=u r_K$.
- $r_S$ is the number of compression calls in the one shared `Derive(S)` for a
  long customization string, and is zero for short $S$.

The adaptation reuses these established results by name.

1. **R1 / FIELD separation.** `encodeItems_injective` and
   `sequenceHash_collision_of_distinct_inputs` rule out byte-level ambiguity,
   prefix ambiguity, and collisions caused merely by alternative item parsing.
   No new prefix-free event is allowed in R4.
2. **R2 / INNER--OUTER separation.** `sequenceMACSystem_realization`,
   `sequenceMAC_prf_bound`, and `sequenceMAC_prf_bound_concrete`, together with
   the accepted A2 fact `HeaderI != HeaderO`, identify SequenceMAC as NMAC-like:
   the two effective role keys are independent under ordinary data-input PRF
   security. There is no HMAC related-ipad/opad assumption or event.
3. **R3 / separated schedule.** `sequenceMACInnerInput_injective`,
   `sequenceMACSeparatedOuterCall_collision`,
   `sequenceMACSeparatedOuterCollision_imp_innerTagCollision`, and
   `sequenceMAC_separated_encoding_bound` already isolate the only encoding
   collision that survives role separation. `sequenceMAC_prf_bound_indiff` is
   a consistency guard: its ideal schedule has independent derive, inner, and
   outer roles. R4 replaces the indifferentiability hypothesis by a direct
   ideal-compression transcript analysis; it does not reprove these lemmas.

Finally assume the announced **cross-role separation lemma**: compression
inputs belonging to `Derive(K)`, `Derive(S)`, inner, and outer roles are
pairwise disjoint. This is the only not-yet-formal premise used by this sketch.
It removes cross-role aliases, but it does not remove random-function cycles or
same-role cascade collisions.

## 3. SequenceMAC bad event: the paper's partition collapses

Reveal the sampled user keys and every construction-internal compression call
on both sides, using independent dummy data in the ideal world. Define
`Bad_SEQ` as the union of only the following SequenceMAC-specific events.

1. `KeyRepeat`: two users sampled the same raw key.
2. `KeyHit`: a direct `Prim` query guessed either of the two secret-bearing
   key-absorption inputs of some user's inner/outer run-up. For a long key this
   also includes guessing the first secret-bearing `Derive(K)` input.
3. `OfflineEntry`: after a fresh same-role cascade call, its random chaining
   output lands on a state/block continuation already fixed by `Prim`.
4. `SameRoleCollision`: two distinct canonical construction traces collide
   inside an inner or outer MD cascade, including the final-input freshness
   failure. Distinct outside inputs cannot enter this event by a framing alias,
   by R1.
5. `DeriveBad`: among the $D_K$ secret long-key derivation evaluations, a
   random continuation hits the public/offline table or two derivation
   continuations collide.

There is no separate ambiguity event, inner/outer collision event, or
last-call-versus-other-role event. On `not Bad_SEQ`, every final outer call is
fresh and distinct; after revealing the seed and internal trace, the real and
ideal extended fixed-query masses are equal. Hence

$$
\varepsilon_{\rm ratio}^{\rm SEQ}=0.
$$

### What happened to $E_A,E_B,E_C$

Shen partitions a same-user NMAC cascade collision according to how much of
the chain is in the offline table.

- $E_A$ becomes `OfflineEntry` and remains: a fresh random state can enter one
  of $p$ known continuations.
- The one-fresh-tail part of $E_B$ and the Gaži internal-collision part remain
  inside `SameRoleCollision`.
- $E_C$ no longer needs the paper's `mkeys` threshold enumeration. A fully
  offline-controlled SequenceMAC chain must first contain a secret-bearing
  compression input. That is `KeyHit`, bounded by key guessing. Thus the
  $E_B/E_C$ bookkeeping partition disappears even though its genuinely random
  same-role collision core remains.

This is the precise sense in which the bad-event partition collapses. It does
not claim that the cascade itself becomes collision-free.

## 4. Centerpiece: term-by-term and event-by-event adaptation

The table starts from the unloosened Section 4 event bounds when that exposes
the source of a displayed $B_{\rm N}$ term. `Killed` means the event is
impossible or unnecessary under a named established specificity; `shrunk`
means it is replaced by a smaller SequenceMAC event; `remaining` means it is
an inherent MD/random-function phenomenon.

| Paper event / displayed term | Source role | SequenceMAC verdict and named reason | Contribution to $B_{\rm SEQ}$ |
| --- | --- | --- | --- |
| Section 4 `bad1`: $K_{1,i}=K_{1,j}$ or $K_{2,i}=K_{2,j}$; contributes to $4q^2/2^c$ after loosening | Two independent NMAC key families and cross-user final-input separation | **Shrunk.** R2 gives two independent *effective roles* from one sampled C2SP key, so the raw-key bookkeeping is a single `KeyRepeat`, not a union over two stored NMAC keys. Same-role random-state collisions are charged to the cascade row. Long-key digest collisions are charged to `DeriveBad`. | $\binom{u}{2}/2^{\kappa_*}$ plus the derive-collision part of `DeriveCost_SEQ` |
| Section 4 `bad2`: $K_{1,i}=u_j$ or $K_{2,i}=u_j$ for an offline query; source envelope $2pq/2^c$ | Offline query directly names an NMAC chaining key | **Shrunk.** In canonical SequenceMAC the secret is in a framed compression *input*. The adversary must guess the secret-bearing block; this is `KeyHit`. INNER/OUTER separation leaves two absorption positions but no related-key event. | $2up/2^{\kappa_*}$ |
| Section 4 `bad3`, $E_A$; displayed $pq\ell/2^c$ | A fresh cascade output enters one of $p$ offline continuations at one of $q\ell$ transitions | **Remaining (inherent).** FIELD and role tags do not change a random functional graph. Replace the paper's message length by the exact canonical trace budget $\lambda$. | $pq\lambda/2^c$ |
| Section 4 `bad3`, $E_B^1/E_B^2$; the $2/2^c$ part per construction-query pair, folded into $4q^2/2^c$ | One cascade tail is fresh and the other is already fixed | **Remaining (inherent), but no coarse paper envelope.** A fresh $c$-bit value still hits one fixed value with probability $2^{-c}$. | $\binom q2\,2/2^c$ |
| Section 4 `bad3`, $E_B^3$; the $\ell/2^c$ part per pair, folded into $4q^2\ell/2^c$ | Gaži same-role cascade collision with neither tail queried offline | **Remaining (inherent).** R1 proves the starting byte strings are distinct; it cannot stop their MD state paths from meeting. | $\binom q2\,\lambda/2^c$ |
| Section 4 `bad3`, $E_B^3$; displayed $32q^2\ell^4/2^{2c}$ | Lower-order internal random-functional-graph collision structure; source has $64\ell^4/2^{2c}$ per pair | **Remaining (inherent).** Domain separation removes aliases, not random-function cycles. Use the source per-pair form with $\lambda$. | $\binom q2\,64\lambda^4/2^{2c}$ |
| Section 4 `bad3`, $E_C$ / `mkeys`; displayed $q^2(b+c+3+\ln p)/2^{b+1}$ | Counts many fully offline-determined NMAC chains and chooses a threshold over candidate starting keys | **Killed as a separate event; shrunk to `KeyHit`.** SECRET KEY IN THE INPUT means a fully controlled canonical chain first guesses a secret-bearing block. No candidate-message/key threshold or Stirling term is needed. | Included in $B_{\rm key}$ and, for a long key, the initial-guess part of `DeriveCost_SEQ`; zero logarithmic term |
| Section 4 `bad3`, remainder of $E_C`; contributes to $q^2\ell(\ln p+1)/2^b$ | Same threshold enumeration, length-amplified | **Killed as a separate event** for the same `KeyHit` reason. | $0$ beyond `KeyHit` |
| Section 4 `bad4`: last outer call collides with an internal call; contributes to the coarse $4q^2\ell/2^c$ envelope | NMAC's raw outer chaining key can equal an inner state | **Killed across roles** by the assumed CROSS-ROLE separation lemma. A within-outer-role cycle is not killed; it is already in `SameRoleCollision`. | $0$ as a separate union term |
| Any ambiguity/prefix-free event that a literal C2SP transcription would add | Two different item sequences or field tuples encode the same hash input | **Killed.** FIELD separation, `encodeItems_injective`, and `sequenceHash_collision_of_distinct_inputs`. | $0$ |
| HMAC ipad/opad, related-key, final/offline, and final/internal bookkeeping | HMAC-only key schedule and six-event partition | **Killed / not applicable.** R2 says SequenceMAC is NMAC-like, not HMAC-like. The template is $B_{\rm N}$, never $B_{\rm H}$. | $0$ |
| Long `Derive(K)` / `Derive(S)` evaluations, absent from NMAC | Additional calls to the shared $h$ | **New and accountable.** Public long-$S$ work enlarges the offline table by $r_S$; secret long-key derivations contribute offline-entry and birthday terms over $D_K=ur_K$ calls. CROSS-ROLE separation removes their intersections with inner/outer roles, not their same-role random collisions. | `DeriveCost_SEQ` below |

Equivalently, the verdict on the seven displayed terms of $B_{\rm N}$ is:

| $B_{\rm N}$ term | Verdict | SequenceMAC replacement |
| --- | --- | --- |
| $pq\ell/2^c$ | **Remaining** | $pq\lambda/2^c$ |
| $4q^2\ell/2^c$ | **Shrunk** | $\binom q2\lambda/2^c$; NMAC `bad4` and threshold slack drop |
| $4q^2/2^c$ | **Shrunk** | $\binom q2 2/2^c+\binom u2/2^{\kappa_*}$ |
| $2pq/2^c$ | **Shrunk** | $2up/2^{\kappa_*}$ |
| $32q^2\ell^4/2^{2c}$ | **Remaining** | $\binom q2 64\lambda^4/2^{2c}$ |
| $q^2(b+c+3+\ln p)/2^{b+1}$ | **Killed as threshold bookkeeping** | absorbed by `KeyHit`; no $\ln p$ term |
| $q^2\ell(\ln p+1)/2^b$ | **Killed as threshold/cross-role bookkeeping** | $0$ beyond `KeyHit` |

## 5. The SequenceMAC-specific bound

Separate the unavoidable cascade term, the single-key term, and the one extra
C2SP derivation cost:

$$
\begin{aligned}
B_{\rm cascade}(p,q,\lambda;c)
:={}&\frac{pq\lambda}{2^c}
+\binom q2\left(
  \frac{\lambda+2}{2^c}
  +\frac{64\lambda^4}{2^{2c}}
\right),\\
B_{\rm key}(p,u;\kappa_*)
:={}&\frac{\binom u2+2up}{2^{\kappa_*}},\\
\operatorname{DeriveCost}_{\rm SEQ}
:={}&\frac{\mathbf 1_{\{r_K>0\}}\,up}{2^{\kappa_*}}
+\frac{r_Sq\lambda}{2^c}
 +\frac{(p+r_S)D_K+\binom{D_K}{2}}{2^c},
\qquad D_K=ur_K.
\end{aligned}
$$

The first derivation summand charges a direct guess of the initial
secret-bearing long-key derivation input. The $r_Sq\lambda/2^c$ summand is
exactly the increase caused by treating the public `Derive(S)` trace as $r_S$
additional primitive-table entries. The last summand is a union bound for
offline entry and same-role collision among secret long-key derivation calls.
The entire cost is zero when key/customization are short: $r_K=r_S=0$.

The proposed R4 bound is

$$
\boxed{
B_{\rm SEQ}
=B_{\rm cascade}(p,q,\lambda;c)
 +B_{\rm key}(p,u;\kappa_*)
 +\operatorname{DeriveCost}_{\rm SEQ}
}
$$

for $u\le q$. Expanded,

$$
\boxed{
\begin{aligned}
B_{\rm SEQ}={}&
\frac{pq\lambda}{2^c}
+\binom q2\left(
  \frac{\lambda+2}{2^c}
  +\frac{64\lambda^4}{2^{2c}}
\right)
+\frac{\binom u2+2up}{2^{\kappa_*}}\\
&+\frac{\mathbf 1_{\{r_K>0\}}\,up}{2^{\kappa_*}}
+\frac{r_Sq\lambda+(p+r_S)ur_K+\binom{ur_K}{2}}{2^c}.
\end{aligned}}
$$

This is not Shen's constant with renamed variables. Its $pq\lambda/2^c$ and
$q^2\lambda/2^c$ behavior is retained because the matching attacks exercise
the MD cascade itself. The logarithmic and cross-role union terms disappear
for stated SequenceMAC reasons. A future sharper count may reduce the
lower-order constants or `DeriveCost_SEQ`, but G4 must not delete either
dominant cascade term.

## 6. Proof skeleton on the H-technique surface

1. **Joint law.** Sample $h$ and the $u$ keys once. The real tagged oracle
   answers `Prim` with $h$ and `Eval(i,M)` with the canonical
   `SequenceFunction(MD[h],K_i,S,1;M)`. The ideal tagged oracle keeps the same
   independent $h$ at `Prim` and replaces each user's `Eval` side by an
   independent random function.
2. **Budget facade.** Restrict to environments with at most $p$ `Prim` calls,
   at most $q$ `Eval` calls, and canonical trace cost at most $\lambda$ per
   `Eval`. This is a tagged-query generalization of `EnvRespects`, not a local
   `SequenceMACEnvRespects` definition.
3. **Extended transcript.** Reveal keys and the role-tagged internal calls.
   Use `extendedTranscriptDistRep` /
   `extFixedQueryTranscriptDistRep`; projection back is already supplied by
   the H-technique extension/data-processing layer.
4. **Good ratio.** R1/R3 injectivity plus CROSS-ROLE separation imply that on
   `not Bad_SEQ`, every final outer input is fresh and distinct. The real and
   ideal extended fixed-query masses are equal. Apply
   `adv_le_of_extFixedQueryRep_eq_on_good`; ratio epsilon is exactly zero.
5. **Bad mass.** Bound `OfflineEntry` by $pq\lambda/2^c$; apply the source's
   same-role Gaži tail bound to each of $\binom q2$ pairs; bound `KeyRepeat`
   and `KeyHit` by min-entropy; add the explicit derivation union bound. This
   gives precisely $B_{\rm SEQ}$.

### Where `hashThenPRF_adaptive_tight` applies

Reuse its spine, not its final numeric theorem:

- reveal the hash/inner seed;
- show extended masses equal off a collision predicate;
- project the extension and conclude with the equality-on-good endpoint.

The R3 lemmas
`sequenceMACSeparatedOuterCall_collision` and
`sequenceMACSeparatedOuterCollision_imp_innerTagCollision` are the
SequenceMAC realization of its collision step.

`hashThenPRF_adaptive_tight` does **not** supply the conditional collision
leaf here. It assumes an independent epsilon-universal hash and an independent
outer URF; it has no public shared `Prim(h)`, no $p/q/\lambda$ filter, no
multi-user key law, and no long-derive trace. Those missing pieces are exactly
the application-specific bad-mass proof above.

## 7. Infrastructure map: reuse versus new

| Layer | Verdict | Exact plan |
| --- | --- | --- |
| H-technique equality on good | **Reuse** | `adv_le_of_extFixedQueryRep_eq_on_good` (or ratio sibling at epsilon zero) |
| Extended representative and projection | **Reuse** | `extendedTranscriptDistRep`, `extFixedQueryTranscriptDistRep`, `statDist_le_of_extension` |
| Adaptive/fixed-query factorization | **Reuse** | Existing `Adv_le_of_pointwise`, fixed-query and system-factor spine; no new fundamental theorem |
| Hash-then-PRF structure | **Reuse spine only** | `hashThenPRF_adaptive_tight`, plus the named R3 collision lemmas above |
| FIELD / canonical construction | **Reuse** | `encodeItems_injective`, `sequenceHash_collision_of_distinct_inputs`, `sequenceMACSystem_realization`; start only from `SequenceFunction` |
| Query restriction | **Generalize in place** | Extend `EnvRespects` with a reusable tagged budget/cost predicate: `Prim` count, `Eval` count, and per-`Eval` trace cost. Do not define a local copy. |
| Joint ideal-compression oracle | **New generic facade** | One public law-level object with tagged `Prim`/`Eval`, one shared ideal $h$, and independent per-user ideal functions. It contains no SequenceHash byte encoding. |
| `Bad_SEQ`, trace classifier, and $B_{\rm SEQ}$ count | **New application layer** | Lives with the future R4 SequenceMAC proof because it names canonical SequenceFunction roles and `DeriveCost_SEQ`. |
| Birthday/union arithmetic | **Reuse** | Existing `probBad_iUnion_le`, mass union bounds, `bday`/counting toolbox; no local generic helper |
| Coupling / indifferentiability / StrongPRP | **Not used** | R4 is the direct H-technique route. R3/R5 and permutation switching are separate. |

## 8. Proposed R4 Lean statement - G4 guardrail

The facade should expose a tagged query alphabet with `Prim` and `Eval`, while
the construction argument is the canonical SequenceFunction realization. In
schematic Lean surface notation:

```lean
-- GUARDRAIL (R4): direct ideal-compression generic PRF bound.
theorem sequenceMAC_generic_prf_tight
    (p q u lambda rK rS : Nat) (kappaStar : Nat)
    (huq : u <= q)
    (hkey : KeyPointMassBound DK kappaStar)
    (htrace : SequenceFunctionTraceBound b S lambda rK rS)
    (hroles : SequenceFunctionCrossRoleSeparated b S) :
    filteredAdaptiveTranscriptAdvantage
        (TaggedBudgetRespects p q lambda)
        (sequenceFunctionICReal b S u DK)
        (sequenceFunctionICIdeal b S u) <=
      (B_SEQ p q u lambda rK rS c kappaStar : Real) := by
  sorry
```

The names of the new facade may change when G4 is frozen, but five statement
features may not:

1. the real construction is canonical `SequenceFunction`, never a duplicate
   NMAC-shaped definition;
2. the shared `Prim` interface is present in both worlds;
3. the $p$, $q$, and $\lambda$ budgets are separately enforced by the
   generalized `EnvRespects` facade;
4. key min-entropy and cross-role separation are explicit hypotheses;
5. the right-hand side is $B_{\rm SEQ}$ including `DeriveCost_SEQ`, not
   $B_{\rm N}$ and not an unspecified normalization epsilon.

The intended proof closes directly with
`adv_le_of_extFixedQueryRep_eq_on_good`. No triangle hop to literal NMAC is
part of G4.

## 9. Tightness relative to R2/Gazi and what remains for R6

R2's standard-model result `sequenceMAC_prf_bound_concrete` has the shape

$$
\varepsilon_{\rm C2SP}+\varepsilon_{\rm comp}
+(\ell+1)q\,\varepsilon_{\rm na}+q^2/2^c.
$$

R4 answers a different question. It replaces compression-PRF assumptions by
one public ideal compression function and measures offline work explicitly.
Its dominant part is

$$
\Theta\!\left(
\frac{pq\lambda+q^2\lambda}{2^c}
\right).
$$

The paper's functional-graph and aligned-suffix attacks still apply to the
role-local MD cascade after canonical framing; R1 prevents encoding aliases
but does not prevent those attacks. Therefore these two terms are genuine
generic loss, not proof slack. INNER/OUTER and CROSS-ROLE separation remove
bookkeeping terms around them, not the attacks themselves.

R6 must still connect this ideal-compression characterization to the
standard-model compression assumptions and decide which R2 losses can be
closed using the Backendal et al. route. In particular R6 must address the
real key schedule and long-derive analysis under a concrete compression
family. R4 neither proves indifferentiability (R5) nor removes
`DeriveCost_SEQ` by fiat.

## 10. Six-line handoff summary

1. Source template: Shen NMAC Theorem 2, joint adaptive `Eval`/`Prim` model, good-transcript ratio exactly one.
2. Killed: FIELD ambiguity/prefix events, HMAC ipad/opad events, NMAC cross-role `bad4`, and the $E_C$ threshold/logarithmic terms.
3. Shrunk: NMAC `bad1`/`bad2` become one-key `KeyRepeat` and secret-input `KeyHit`, bounded at $2^{-\kappa_*}$.
4. Remaining: functional-graph $pq\lambda/2^c$, same-role $q^2\lambda/2^c$, and the lower-order $q^2\lambda^4/2^{2c}$ internal-collision term.
5. Final shape: $B_{\rm SEQ}=B_{\rm cascade}+B_{\rm key}+\operatorname{DeriveCost}_{\rm SEQ}$ with the explicit boxed formula in Section 5.
6. Infra: reuse the extended-representative/hash-then-PRF spine; add only a generic joint ideal-compression oracle and a tagged $p/q/\lambda$ generalization of `EnvRespects`.
