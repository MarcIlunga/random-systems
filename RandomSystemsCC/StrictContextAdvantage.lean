/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContextAdvantage

/-!
# Compatibility shim

`StrictContextAdvantage` is pure random-systems content and now lives at
`RandomSystems.StrictContextAdvantage` (namespace
`RandomSystems.CR18.StrictContextAdvantage`).  This shim keeps the old module
path and the one fully-qualified name consumed by `Symmetric/OTP.lean` alive
until that file's owner switches to the new home; nothing else should import
this module.
-/

namespace RandomSystemsCC.StrictContextAdvantage

export RandomSystems.CR18.StrictContextAdvantage (edist_acceptMass_le_maxAdvantage)

end RandomSystemsCC.StrictContextAdvantage
