/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.ResourceLift
import RandomSystems.CBCMAC

/-!
# CBC model setup (formalization, settled once)

The ambient formalization data for the CBC development — the interfaces and
the instances that let pure PDS/converters find their place
on the carrier.  Nothing here is mathematics; it is imported by
`RandomSystemsCC.CBC`, which reads like the paper because this lives here.
-/

namespace RandomSystemsCC.CBCMAC

open RandomSystems.CR18.TypedResource
open RandomSystemsCC.CR18

universe u

/-- The two interfaces: the round function `X → X` and the variable-input
function `M → X`. -/
inductive Interface where
  | roundFunction
  | variableInputFunction
  deriving DecidableEq

/-- CBC's two-interface universe. -/
abbrev interfaces (X M : Type u) : InterfaceUniverse.{0, u, u} where
  Code := Interface
  input
    | .roundFunction => X
    | .variableInputFunction => M
  output _ := X

/-- The CBC resource carrier.  Its interface universe is model plumbing and
does not appear in construction statements. -/
abbrev Resource (X M : Type u) :=
  RandomSystemsCC.CR18.Resource (interfaces X M)

section

variable {X M : Type u}
variable [Fintype X] [DecidableEq X] [Nonempty X]
variable [Fintype M] [DecidableEq M]

instance : DecidableEq (interfaces X M).Code := by
  change DecidableEq Interface; infer_instance

/-- The round function lives at the `roundFunction` interface (input `X`). -/
instance : HasResourceCode (interfaces X M) X X where
  code := .roundFunction
  input_eq := rfl
  output_eq := rfl

/-- The variable-input function lives at the `variableInputFunction` interface
(input `M`).  The priority resolves an overlap: the two instance heads unify
when `M = X`, and there priority — not the alphabets — picks the code.

That overlap is **sound but silently relabelling**.  Instance resolution is
deterministic and cached per head, so at `M = X` *every* occurrence collapses
to `variableInputFunction` together; the resulting statement is the same
mathematics carried by the other of two labels for one and the same signature,
not a false one.  What it is not is what the author wrote.  Since placement is
observable (`liftProbAt_roundFunction_ne_liftVIF`), the resolution is pinned by
`overlap_resolves_to_variableInputFunction` below, and every statement boundary
whose intent matters names its code with `liftProbAt` / `liftVIF` instead of
relying on this instance. -/
instance (priority := 1100) : HasResourceCode (interfaces X M) M X where
  code := .variableInputFunction
  input_eq := rfl
  output_eq := rfl

/-- The explicit placement of a variable-input law, for use at statement
boundaries.  Definitionally the coercion whenever `M ≠ X`, and unlike the
coercion it still says `variableInputFunction` when `M = X`. -/
noncomputable abbrev liftVIF (system : RandomSystems.CR18.PFunPDS.Prob M X) :
    Resource X M :=
  liftProbAt (U := interfaces X M) Interface.variableInputFunction system

/-- Placement is **observable**: the two placements of one and the same law are
distinct resources.  This is why the overlap above has to be pinned rather than
dismissed — resolution decides which of two provably different resources a
statement is about. -/
theorem liftProbAt_roundFunction_ne_liftVIF
    (system : RandomSystems.CR18.PFunPDS.Prob X X) :
    liftProbAt (U := interfaces X X) Interface.roundFunction system ≠
      liftVIF (X := X) (M := X) system := by
  intro contradiction
  have codes : Interface.roundFunction = Interface.variableInputFunction :=
    congrArg RandomSystemsCC.CR18.Resource.code contradiction
  exact Interface.noConfusion codes

/-- **Resolution pin.** At `M = X` both `HasResourceCode` instances apply, and
this records which one wins.  Changing either priority — or adding a third
instance — flips this and breaks the build here rather than silently moving
every CBC statement to the other interface. -/
theorem overlap_resolves_to_variableInputFunction :
    (inferInstance : HasResourceCode (interfaces Bool Bool) Bool Bool).code =
      Interface.variableInputFunction :=
  rfl

/-- Away from the overlap there is nothing to pin: a round function can only
land at `roundFunction`. -/
theorem roundFunction_placement :
    (inferInstance : HasResourceCode (interfaces X M) X X).code =
      Interface.roundFunction :=
  rfl

/-! ### The pure converters, bundled with their DDC proofs

Each is the raw CR18 converter paired with its determinism proof — the
converter analogue of `PFunPDS.Prob.URF`.  `RandomSystemsCC.CBC` uses these
directly as typed DDCs; the proofs never appear there. -/

open RandomSystems.CR18

variable [AddCommGroup X]

/-- `CBC` bundled with its DDC proof — the pure `CBC bf`.  The block bound that
CBC's DDC-ness needs is *free* for the finite message space (a `Finset.sup`),
so it is discharged here, not threaded as a hypothesis. -/
noncomputable abbrev Converter.cbc (bf : M → List X) : DDConverter M X X X :=
  ⟨CBC bf, cbc_is_deterministic_discrete_converter bf
    ⟨Finset.univ.sup fun m => (bf m).length,
      fun m => Finset.le_sup (f := fun m => (bf m).length) (Finset.mem_univ m)⟩⟩

/-- The restriction `θ_r`, polymorphic in its answer alphabet. -/
noncomputable abbrev Converter.restriction {Y : Type u}
    (bf : M → List X) (r : ℕ) : DDConverter M Y M Y :=
  ⟨RandomSystems.CR18.θ bf r,
    theta_is_deterministic_discrete_converter bf r⟩

/-- The restriction `θ_r` at the CBC resource alphabet. -/
noncomputable abbrev Converter.θ
    (bf : M → List X) (r : ℕ) : DDConverter M X M X :=
  Converter.restriction bf r

/-- The round-limit `[r]` bundled with its DDC proof — the pure `queryLimitFn r`. -/
noncomputable abbrev Converter.roundLimit (r : ℕ) : DDConverter X X X X :=
  ⟨PFunConverter.queryLimitFn r, PFunConverter.isDDC_queryLimitFn r⟩

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X] in
/-- Applying the bundled round-limit converter is exactly the canonical `⌈r⌉`
query filter. -/
theorem Converter.roundLimit_apply (r : ℕ) (S : PFunPDS X X) :
    Converter.roundLimit (X := X) r * S = PFunPDS.filterQueries r S :=
  StrictContext.apply_law_queryLimitFn r S

omit [DecidableEq M] in
/-- Applying the bundled CBC converter to the uniform round function is the
real CBC system. -/
theorem Converter.cbc_URF_eq_cbcReal (bf : M → List X) :
    Converter.cbc bf * PFunPDS.URF (X := X) (Y := X) = cbcReal bf := by
  simpa only [DDConverter.mul_system] using
    apply_cbc_to_uniform_random_function_eq_real_system bf

omit [Fintype X] [DecidableEq X] [Nonempty X] [DecidableEq M] in
/-- CR18 equation (6.1) on the bundled converter surface. -/
theorem Converter.theta_cbc_eq_theta_cbc_round_limit
    (bf : M → List X) (r : ℕ) :
    Converter.θ bf r * Converter.cbc bf =
      Converter.θ bf r *
        (Converter.cbc bf * Converter.roundLimit (X := X) r) := by
  apply DDConverter.ext
  simp only [DDConverter.run_mul]
  exact theta_comp_cbc_eq_theta_comp_query_limited_cbc bf r

end

end RandomSystemsCC.CBCMAC
