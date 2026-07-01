import Lake
open System Lake DSL

-- Presentation layer (SEPARATE from the import-Lean-only core): reuse Verso's
-- reveal.js slide genre. Toolchain v4.32.0-rc1 to match verso-slides.
require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"main"

package «informalization-slides» where
  version := v!"0.1.0"

lean_lib InformalizationSlides

@[default_target] lean_exe «informalization-slides» where root := `Main

-- SwissCryptoDay 2026 talk deck (separate output dir `_scd`)
lean_lib SwissCryptoDay

lean_exe «scd-slides» where root := `MainSCD
