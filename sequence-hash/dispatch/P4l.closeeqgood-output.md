Stopped under the explicit framework-gap valve. The final representative-mass equality and packaged R4 lemma are not yet proved.

Completed additively in [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:52):

- Exact evaluation-request/tag-count correspondence.
- Exact `p`/`q` budget saturation.
- Idempotence of terminal programming.
- `sequenceFunctionTerminalFreeSkeleton_terminalShift` ([line 1246](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:1246)), proving the terminal shift preserves every non-terminal representative coordinate and only translates the terminal coordinate.

The genuinely missing framework lemma is a product-uniform coordinate-exchange theorem, preferably in `RandomSystems/HTechnique/Derivation.lean` or `IdealCompression.lean`:

```lean
theorem Dist.mass_prod_uniform_coordinate_exchange
    [Fintype F] [Nonempty F]
    [Fintype K] [Nonempty K]
    [Fintype G] [Nonempty G]
    [Fintype A] [Nonempty A]
    (DK : Dist K)
    (R : F → K → Prop)
    (I : F → K → G → Prop)
    (P : K → F → Prop)
    (coordF : F → A) (coordG : G → A) (a : A)
    (hR : ∀ f k, R f k ↔ coordF f = a ∧ P k f)
    (hI : ∀ f k g, I f k g ↔ coordG g = a ∧ P k f)
    (hF : ∀ k,
      (Finset.univ.filter fun f => coordF f = a ∧ P k f).card *
          Fintype.card A =
        (Finset.univ.filter fun f => P k f).card)
    (hG :
      (Finset.univ.filter fun g => coordG g = a).card *
          Fintype.card A =
        Fintype.card G) :
    (Dist.prod (Dist.uniform F) DK).mass (fun fk => R fk.1 fk.2) =
      (Dist.prod (Dist.uniform F)
        (Dist.prod DK (Dist.uniform G))).mass
          (fun fkg => I fkg.1 fkg.2.1 fkg.2.2)
```

This is the general step needed to integrate `sequenceFunction_fiber_card_of_not_Bad_SEQ` through an arbitrary key law and exchange the real terminal compression coordinate with the independent ideal-function coordinate. Existing `uniform_mass_eq_mass_mul_mass_of_card_mul_eq` handles only one uniform carrier and does not relate these two representative coin spaces.

Reuse in the completed shift proof includes:

- `not_Bad_SEQ_iff_compressionFresh`
- `sequenceFunctionRevealedTerminalInputs_sublist_constructionInputs`
- `sequenceFunctionTerminalShift_eq_of_not_mem`
- `sequenceFunctionCompressionTrace_terminalShift`
- `sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint`
- The ideal transcript/reveal definitions and honest-prefix programming laws

Verification:

- Focused build: green, 8327 jobs.
- Whole-repository `lake build`: green, 8441 jobs.
- Added code is free of `sorry`, `private`, games, `condEquiv`, `B_SEQ`, and `h_badmass`.
- Axioms: `{propext, Classical.choice, Quot.sound}`.

Therefore step 4 is not yet the only remaining R4-spine work: the framework coordinate-exchange lemma must land, followed by its SequenceFunction event characterizations and endpoint packaging.