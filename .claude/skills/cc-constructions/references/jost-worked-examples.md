# The two worked CC workflows (Jost §2.2.6 and OTP)

Every step is tagged with its floor and its owner:
`[MODEL]` pen-and-paper modeling (this skill's stages 1–2), `[DEF]` surface
definitions, `[RS]` a leaf handed to `random-systems-proofs`, `[CC]`
algebra/rewriting at the resource floor, `[SET]` set-level/functional
transport, `[RCPT]` receipts.

---

## §1  Secure channel from [AuthChan, Key] — Jost §2.2.6, Prop 2.2.17

The rung-1 workflow: every leaf is a **law equality** (identity coupling of
a shared seed), so the construction costs two bisimulations and a rewrite.
Files: `Jost/Systems.lean` (boxes), `Jost/Construction.lean` (leaves),
`Jost/SecureChannel.lean` (the statement at the resource floor).

**Step 1 [MODEL] — derandomize the scheme.**  Probabilistic `Enc` becomes
`enc : K → R → M → C` with an explicit randomness argument; one run's
randomness is the seed `(k, tape : Fin cap → R)`, tape read totally via
`tapeAt` (junk past `cap` cancels because both sides of every leaf read the
same tape).  Perfect correctness (`dec_enc`) and the length functional
(`len`/`zeroOf`, `len_zeroOf`) are the only scheme laws.  Decision recorded:
NO capacity guards in any machine.

**Step 2 [MODEL] — place the objects.**  Boxes (L1): `authChan` (reused,
`JostFigure22`), `secChan` (leak reveals `len` only), `cpaMachine b`
(Fig. 2.4b — a game IS a resource; the `require |m₀|=|m₁|` guard answers an
error VALUE).  Converters (L1): protocol `piConv` (encrypt/decrypt,
identity clauses at E and F), simulator `sigmaConv` (encrypts `zeroOf ℓ`
under its OWN key — which is a seed coordinate), reduction `cConv`
(plaintext/ciphertext store; plays `(m, zeroOf (len m))` at the game).
Claims (L4): three resources over ONE interface declaration
(`constructedInterfaces M C`).

**Step 3 [MODEL] — the identity ladder test.**  Leaf 1 pairs
`π·[AuthChan,Key]` with `c·CPA₀` at the SAME seed `(k, tape)`: at every
history both answer with `enc k (tapeAt tape i) mᵢ` at Eve and (by
`dec_enc`) the stored plaintext at Bob — observer-free pointwise agreement
⇒ **rung 1**.  Leaf 2 pairs `σ·SecChan` with `c·CPA₁`: the simulator's own
key IS `CPA₁`'s key under the identity coupling; both answer
`enc k (tapeAt tape (i-1)) (zeroOf (len mᵢ))` — rung 1 again, and NO
correctness assumption is consumed.

**Step 4 [DEF] — resources.**  `real := Resource.sampleInit (realMachine E)
(uniform (Seed K R cap)) …`, likewise `ideal`, `game b`.  The families are
functions into realizations; how each fibre was assembled is authoring
detail with no proof obligation.

**Step 5 [RS] — the two leaves.**  Handed to `random-systems-proofs` as
`toDDS` equalities per seed, discharged by `Machine.toDDS_eq_of_bisim`:

- `realMachine_toDDS_eq_gameMachine` — relation `realGameRel`: the three
  counters track the store length; the channel buffer is the ciphertext
  column (`logLookup`-based, never positional `getElem`); Bob's pending
  ciphertext decrypts to the stored plaintext (`dec_enc` fires HERE and
  only here — exactly where the thesis says "by correctness"); every
  stored ciphertext is honest w.r.t. its tape position.
- `idealMachine_toDDS_eq_gameMachine` — `idealGameRel`: plaintext column =
  SecChan log; stored ciphertexts are zero-string encryptions at their
  positions.

Tactic notes that saved hours (STATUS §7): unfold `Option.map`/`Option.bind`
in the simp sets and close moves with `injection`, never `some.injEq`+`subst`
(defeq-but-not-syntactic state types); never `rintro -`; `dsimp only`
before `rw` when tuple projections block the pattern.

**Step 6 [CC] — lift to resources.**  `real_eq_game`/`ideal_eq_game` are
one application each of `Resource.sampleInit_congr` (the identity
coupling).  No probability appears.

**Step 7 [SET] — Prop 2.2.17.**  Because the leaves are equalities,
`construction : Φ (real, ideal) = Φ (c·CPA₀, c·CPA₁)` for EVERY functional
Φ, by `rw`.  Instantiating Φ with a distinguisher's advantage is the
thesis's `ε(D) = Δ^{Dc}(CPA₀, CPA₁)` — the reduction is inside the game
laws, so distinguisher absorption is definitional, zero slack, no metric
machinery consumed.

**Step 8 [RCPT].**  `#print axioms` on every headline: the three standard
axioms only.  `ScheduleAgnostic` not claimed (none of the statements
quantify a rushing adversary).  Sketch updated with deviations.

**What changes for a weaker scheme** (the escalation pattern): statistical
correctness demotes leaf 1 to rung 2 — same relation, bad set = "some tape
entry triggers a decryption failure", endpoint
`Machine.lawOf_lawStatDist_le_of_coupling`; the CC skeleton (steps 4, 6, 7)
does not change by one symbol.

---

## §2  One-time pad — the rung-3 workflow (`Jost/OTP.lean`)

The acid test: an identity that is FALSE at the law floor and TRUE at the
resource floor.  Single-use channel; real = leak answers `m ⊕ k` (key `k`
uniform); ideal = leak answers a fresh uniform `c`, message-independently.

**Step 1 [MODEL] — ladder test fails rungs 1–2.**  Real fibres answer
message-DEPENDENTLY (`k=0` is the identity function on the message), ideal
fibres constantly ⇒ the two laws have disjoint supports over deterministic
systems.  No seed coupling can pair them observer-free: the right pairing
is `k ↔ m₀ ⊕ k` where `m₀` is the first message the ENVIRONMENT sends.
Rung 3: the identity enters through
`Resource.sampleInit_eq_of_flatten_equivalent`, and the leaf is
`StrictContext.Equivalent` of the flattened laws.

**Step 2 [DEF] — boxes.**  `realM k` (state = first stored message,
`Option.or s (some m)` on send; leak answers `s.map (· ⊕ k)`), `idealM c`
(state = sent flag; leak answers `if s then some c else none`).  TOTAL
machines; single-use = later sends ignored (a modeling decision the
invariant depends on: repeated leaks must be constant in both worlds).

**Step 3 [RS] — the leaf, routed per the RS skill.**  Family I (exact),
transcript route.  Structure that made it tractable:

1. Closed forms first: `runFrom` closed forms via `firstSend : List Query →
   Option Bool`; then snoc-history output forms for the flattened systems
   (`flatten_output_concat`, `output_fullyDefined_of_total` — generic,
   migration candidates).  After these, the transcript induction never
   touches machines.
2. The four-worlds invariant `otp_transcript`, by induction on the
   transcript length, for every deterministic environment `e`:
   EITHER no send has occurred and all four transcripts are LITERALLY
   equal (pre-send, leaks answer `none` in every world — the environment
   has learned nothing, so its queries agree), OR the first message `m₀`
   is fixed and `tr(SR k) = tr(SI (m₀ ⊕ k))` for both `k`, with
   `firstSend` persisting.  The observer-dependence of the pairing is
   captured by `m₀` being a function of the (common) transcript prefix.
3. Per-(e, n) law equality `transcriptDist_flat_eq`: left branch — both
   pushforwards are constant on the seed support (`fTransform_congr`);
   right branch — the seed bijection `k ↦ m₀ ⊕ k` moves one pushforward
   onto the other, closed by `Dist.fTransform_bijection_uniform` (the
   library's own "OTP-style argument" lemma).
4. The metric chain collapsed to ONE existing endpoint:
   `StrictContextAdvantage.strict_equivalent_of_equivalent` (CR18
   transcript equivalence → strict contextual equivalence).  Reuse-search
   before building the chain saved the planned
   maxAdvantage/maxEDist manipulation entirely.

**Step 4 [CC] — the headline.**  `otp_real_eq_ideal : real = ideal` is the
bridge applied to the leaf.  One line.

**Step 5 [RCPT].**  Axiom audit; the sketch records the route AND the
rejected alternative (coupling — with the reason: any coupling of the laws
has positive disagreement mass).

**The general lesson**: when the seed pairing needs information only the
observer has, you are at rung 3 by necessity, not by failure of technique —
and the transcript induction's shape is always "common prefix until the
observer commits, then a per-observer bijection of seeds".
