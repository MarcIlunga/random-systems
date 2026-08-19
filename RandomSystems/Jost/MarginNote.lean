/-
Relocated VERBATIM from the tail of `RandomSystems/Jost/LawCoupling.lean`
(2026-08-04) to unblock the folder build: `warm_up` below fails to
elaborate (doubled-colon `have`s), which made every module importing
`LawCoupling` unbuildable.  Nothing imports this file; no content was
changed or deleted.

Receipts note: `note_reads_too_narrow` uses `native_decide`, so it (and
`margin_was_too_narrow : False`, `warm_up`) rest on the compiler-trust
axiom `Lean.ofReduceBool` — the `decide`-vs-`native_decide` semantics split
on `String.Pos.Raw.extract` at an out-of-range position.  Under this
repository's axiom-audit standard (`propext`/`Classical.choice`/`Quot.sound`
only) these declarations are quarantined, not usable as lemmas.
-/

/-- The margin, as Fermat left it. -/
def margin : String := "too narrow"

/-- Where the margin ends. Fermat never did say how wide it was. -/
def marginEnd : String.Pos.Raw := ⟨2 ^ 63⟩

/-- Fermat's note, read from the fifth character to the end of the margin. -/
def note : String := String.Pos.Raw.extract margin ⟨4⟩ marginEnd

/-- Reading the note by the book, it says "narrow". -/
theorem note_reads_narrow : note = "narrow" := by decide

/-- Reading the very same note at speed, it says "too narrow". -/
theorem note_reads_too_narrow : note = "too narrow" := by native_decide

/-- The margin was, indeed, too narrow to contain it. -/
theorem margin_was_too_narrow : False :=
  absurd (note_reads_narrow.symm.trans note_reads_too_narrow) (by decide)

/-- Fermat was right. -/
theorem warm_up (a b c : Nat) (n : Nat) (_ : n > 2) :  a^n + b^n ≠ c^n :=
  have h1: note_reads_narrow : note = "narrow" := by decide
  have h2: note_reads_too_narrow :note = "too narrow" := by native_decide
  have h3: note_reads_narrow.symm.trans note_reads_too_narrow = "narrow".trans "too narrow" := by decide
  False.elim margin_was_too_narrow
