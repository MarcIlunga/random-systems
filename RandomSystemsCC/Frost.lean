/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Frost.Group
import RandomSystemsCC.Frost.Model
import RandomSystemsCC.Frost.Instantiation
import RandomSystemsCC.Frost.EndToEnd
import RandomSystemsCC.Frost.Dkg
import RandomSystemsCC.Frost.Reduction

/-!
# FROST at the random-systems carrier

The concrete side of the FROST development: everything that *instantiates*
the abstract layers lives here, so the sibling `abstract-crypto` repository
stays carrier-free and its AC/CC.MPC theorems fire by application.  The
files are organized by protocol phase:

* `Group` — `FrostGroup`: the structural group obligations (prime order,
  torsion/module, generator), the dlog-trivial witness, and the named
  secp256k1 carrier obligations.
* `Model` — the concrete FROST signature universe: one interface per party,
  the assumed `[NET, BC, RO, COIN]` bundle (broadcast assumed, its
  construction out of scope), the intermediate key ideal, and the
  gated-real-signer final ideal.
* `Instantiation` — the abstract epsilon-relaxed FROST theorem specialized
  to the typed random-systems carrier; the cryptographic leaves remain
  explicit hypotheses.
* `EndToEnd` — the concrete FROST security theorem at the threshold
  structure (no honest majority): the `Setup` bundle, the three leaf
  predicates, the two reusable stage constructions, `Setup.secure`, and
  availability.
* `Dkg` — key generation: the key ideal as a carrier resource
  (`keyResource`) with VSS consistency and reconstruction, the multi-dealer
  DKG reconstruction (`dkg_key_reconstruct`), the simulator's key
  programming (`key_matches`), and the Gennaro–Jarecki–Krawczyk–Rabin bias
  impossibility (`uniform_key_dkg_impossible`).  The RO-programming coupling
  (`DkgIndistinguishable`) is the residual.
* `Reduction` — the security reduction: the generic Problem⟶`gameSpec`
  bridge, AOMDL as a CR18 `Problem` with the tight forking reduction
  (`reduction_winProb`), the AOMDL instantiation, and the final
  `Setup.secure_of_aomdl` (only cryptographic inputs: the two statistical
  simulators, AOMDL hardness, and the reduction contract).
-/
