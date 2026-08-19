/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import Lean

/-!
# Random-systems semantic declaration registry

This Mathlib-independent registry lets pure RandomSystems declarations expose
their machine-facing role without importing the AC/CC integration layer.
-/

open Lean

namespace RandomSystems.SemanticRegistry

/-- The stable semantic coordinates carried by `@[rs_rule]`. -/
structure Entry where
  declaration : Name
  id : String
  kind : String
  layer : String
  deriving BEq, Hashable

initialize entries : SimplePersistentEnvExtension Entry (Array (Array Entry)) <-
  registerSimplePersistentEnvExtension {
    addImportedFn imported := imported
    addEntryFn state _ := state
  }

/-- All random-systems semantic entries visible in an environment. -/
def allEntries (environment : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState entries environment
  state.2.flatten ++ state.1

syntax (name := rsRuleAttr) "rs_rule" str ident ident : attr

/-- Mark a declaration as a semantic rule available to proof tooling. -/
initialize registerBuiltinAttribute {
  name := `rsRuleAttr
  descr := "register a declaration and its semantic role for random-systems proof tooling"
  add := fun declaration stx _ => do
    let `(attr| rs_rule $id:str $kind:ident $layer:ident) := stx
      | throwError "invalid rs_rule annotation"
    let entry : Entry := {
      declaration
      id := id.getString
      kind := kind.getId.toString
      layer := layer.getId.toString
    }
    let environment <- getEnv
    if (allEntries environment).any (fun old => old.id = entry.id) then
      throwError "duplicate semantic rule id {entry.id}"
    modifyEnv fun environment => entries.addEntry environment entry
}

end RandomSystems.SemanticRegistry
