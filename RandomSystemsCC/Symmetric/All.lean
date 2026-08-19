/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.OTP
import RandomSystemsCC.Symmetric.FreshOTP
import RandomSystemsCC.Symmetric.AffineOneTimeMAC
import RandomSystemsCC.Symmetric.BoundedURFMAC
import RandomSystemsCC.Symmetric.UHFThenURF
import RandomSystemsCC.Symmetric.UHFURFMAC
import RandomSystemsCC.Symmetric.MACThenOTP
import RandomSystemsCC.Symmetric.SpongeIndifferentiability
import RandomSystemsCC.Symmetric.SpongeBDPV
import RandomSystemsCC.Symmetric.SpongeLemma4

/-!
# CC-first symmetric-cryptography construction surface

This module exports the statement-first construction suite specified by
`DESIGN.md` §11.  During the statement phase its public construction proofs
are deliberately deferred; no standalone security theorem is exported here.
-/
