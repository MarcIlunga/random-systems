/-
Copyright (c) 2026 Trail of Bits. Apache 2.0.
-/
import Informalization
open Informalization
open Lean Elab Command

theorem inj_comp' {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  fun a b h => hf (hg h)

/-- `#informalizeVerso ident` — informalize a declaration, then emit VersoSlides
markup (the bridge that lets Verso host our informalization text). -/
syntax (name := informalizeVersoCmd) "#informalizeVerso " ident : command

@[command_elab informalizeVersoCmd]
def elabIV : CommandElab := fun stx => do
  match stx with
  | `(#informalizeVerso $i:ident) => do
    let nm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    let doc ← liftTermElabM <| Frontend.informalizeConst nm
    logInfo m!"{(FTL.realizeDocument doc).toVerso}"
  | _ => throwUnsupportedSyntax

#informalizeVerso inj_comp'
