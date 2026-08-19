# Augmented observations as random variables -- pen-and-paper sketch

An augmented transcript is a richer observation of the same underlying experiment.  The
ordinary transcript and the augmented transcript are random variables on one master sample
space; the ordinary transcript is recovered pointwise by forgetting information from the
augmented observation.  The law-level marginal identity is therefore functoriality of
pushforward, and the distance comparison is data processing.  H is applied only to the two
augmented laws and remains independent of transcripts.

## Objects

- A source distribution on a master sample space.
- An ordinary observation from that sample space to an arbitrary base carrier.
- A richer observation from that sample space to an arbitrary augmented carrier.
- A deterministic stripping map from the augmented carrier to the base carrier.
- The pointwise identity saying that stripping the richer observation gives the ordinary
  observation.

Fresh coins are included in the master sample space.  The ordinary observation ignores
them, while the augmented observation may use them.  Thus deterministic and randomized
augmentation have the same mathematical form once all randomness is exposed in the source.

## Claim

Pushing the augmented law through the stripping map gives exactly the law of the ordinary
observation.  Consequently, stripping cannot increase the distance between two augmented
laws.  Combining this data-processing step with H on the augmented laws bounds the distance
between the corresponding ordinary observation laws.

## Argument

For every source outcome, stripping after augmentation equals the ordinary observation.
Pushforward along equal functions gives equal laws, while composition of two pushforwards is
the pushforward along the composite function.  These two facts prove the marginal identity.
Data processing then compares the stripped laws to the augmented laws.  No product carrier,
transcript type, PDS, law-extension structure, or separate augmented H theorem is needed.

The existing product-transcript result should remain, if useful to callers, only as a thin
specialization with the first projection as the stripping map.

## Technique and rejected alternative

Technique: observation refinement followed by data processing, then the existing
carrier-independent H ratio theorem.

Rejected: packaging an abstract relation between an augmented law and a base law.  It loses
the stronger pointwise random-variable identity already available in the intended model and
creates proof data that pushforward composition derives automatically.

## Obligation DAG

`marginal_identity`

- Statement: stripping the pushed-forward augmented observation equals the pushed-forward
  ordinary observation.
- Class: library/generalization.
- Depends on: pushforward composition and equality of the two observation functions.
- Reuse verdict: ADAPT the product/transcript-specific marginal theorem by replacing it
  with one public carrier-independent pushforward theorem in the distribution layer.  The
  proof reuses pushforward composition and congruence; repository and local declaration
  search found no existing arbitrary stripping theorem.

`transcript_specialization`

- Statement: the existing product-valued augmented transcript theorem follows from the
  carrier-independent marginal identity.
- Class: routine.
- Depends on: `marginal_identity`.
- Reuse verdict: remove the standalone product/transcript bridge; its application receipts
  invoke `marginal_identity` directly.

`H_after_stripping`

- Statement: H on two augmented laws bounds the distance of their stripped laws.
- Class: library.
- Depends on: data processing and the existing carrier-independent H theorem.
- Reuse verdict: REUSE the arbitrary-map H-through-pushforward theorem.  Remove its
  first-projection-only wrapper and instantiate the arbitrary map with first projection at
  the sole application caller.
