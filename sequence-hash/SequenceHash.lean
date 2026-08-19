import SequenceHash.Spec
import SequenceHash.RandomSystems.Converter

/-!
# SequenceHash

Formalization of the C2SP SequenceHash construction. `Encoding` and `Spec`
form a pure, Mathlib-only layer; `RandomSystems.Converter` realizes the same
function as a two- or three-call CR18 protocol converter. Security and
constructive-cryptography instantiations live in later modules.
-/
