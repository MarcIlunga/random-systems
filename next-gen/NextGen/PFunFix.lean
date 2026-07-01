import Mathlib.Data.PFun

/-!
# A bisimulation principle for `PFun.fix`

`PFun.fix_bisim` is generic least-fixed-point theory with no dependency on the
random-systems development. It is stated in the `PFun` namespace so that it can
be upstreamed to `Mathlib.Data.PFun` verbatim.

UPSTREAM-CANDIDATE.
-/

namespace PFun

/-- A bisimulation principle for `PFun.fix`: if a state relation `R` and an
output relation `Q` are preserved by single steps — `f`-stops map to `Q`-related
`g`-stops, `f`-steps map to `R`-related `g`-steps — then `R`-related states have
`Q`-related fixed-point results. -/
theorem fix_bisim {σ τ β β' : Type*} {f : σ →. β ⊕ σ} {g : τ →. β' ⊕ τ}
    {R : σ → τ → Prop} {Q : β → β' → Prop}
    (hstop : ∀ a a', R a a' → ∀ b, Sum.inl b ∈ f a →
        ∃ b', Sum.inl b' ∈ g a' ∧ Q b b')
    (hstep : ∀ a a', R a a' → ∀ a₁, Sum.inr a₁ ∈ f a →
        ∃ a₁', Sum.inr a₁' ∈ g a' ∧ R a₁ a₁')
    {a : σ} {b : β} (hb : b ∈ f.fix a) :
    ∀ a', R a a' → ∃ b', b' ∈ g.fix a' ∧ Q b b' := by
  refine PFun.fixInduction hb
    (C := fun a₀ => ∀ a', R a₀ a' → ∃ b', b' ∈ g.fix a' ∧ Q b b') ?_
  intro a₀ hb₀ IH a' hR
  rw [PFun.mem_fix_iff] at hb₀
  rcases hb₀ with hl | ⟨a₁, hr, _⟩
  · obtain ⟨b', hb', hQ⟩ := hstop a₀ a' hR b hl
    exact ⟨b', PFun.fix_stop hb', hQ⟩
  · obtain ⟨a₁', hr', hR₁⟩ := hstep a₀ a' hR a₁ hr
    obtain ⟨b', hb', hQ⟩ := IH a₁ hr a₁' hR₁
    exact ⟨b', by rw [PFun.fix_fwd_eq hr']; exact hb', hQ⟩

end PFun
