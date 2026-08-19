/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictParallel
import RandomSystems.StrictRelabel
import RandomSystemsCC.ResourceLift

/-!
# The parallel-composition axis on the strict resource carrier

This module installs Abstract Cryptography's parallel operators on the
`ResourceLift` carrier:

* `Par (Resource U)` — parallel composition of heterogeneous resources,
  from `StrictContext.System.parallel` under a `⊕`-closed signature
  universe (`HasSumCode`);
* `IsNonexpandingPar (Resource U)` — MauRen11 §4.4 Definition 3 / eq. (3)
  on the carrier, from the strict `System.edist_parallel_le`;
* `ParProtocol U` — a **syntactic** protocol monoid (the free `{1, ∘, ‖}`
  algebra over the carrier's primitives, modulo the monoid laws), acting
  on resources, with `Par` and `SMulParClass`.

**Why this is a second monoid and not a `par` on `Protocol U`.**  Both
monoids are syntactic — `Protocol U` is converter words modulo the serial
monoid laws, `ParProtocol U` is protocol terms modulo the same laws — so
the difference is not representation.  It is the *codomain of the
interpretation*, and with it the metric claim.  `Protocol U` interprets
into `nonexpandingEnd (Resource U)` and therefore asserts MauRen16
Definition 2 for every element; adding a `par` constructor there would
assert something **false** (the parallel action is not non-expanding — mix
a product law with a correlating one at weight `δ` and the mixture does not
decompose, so the action pins it while moving the product) and would break
`IsNonexpandingSMul`, hence `SecurelyConstructs.trans`, for every endpoint
on this carrier.  `ParProtocol U` escapes exactly by acting into plain
functions and asserting no metric law at all.

Its parallel element acts componentwise on `‖`-shaped resources —
well-defined because the parallel decomposition of a strict behavior is
*unique* (`System.parallel_inj`, itself the strict cancellation theorem)
and sum codes are injective — and as the identity elsewhere, the freedom
MauRen11 fn. 23 grants.

Only the resource side carries a metric claim (`IsNonexpandingPar`);
`ParProtocol` makes no non-expansion claim, and AC's ordered parallel
calculus (`Constructs.par_left`, `Constructs.eball_par`, simulator
extension) needs none.  Deliberately absent, per AC's own modeling rule:
associativity, commutativity, and unit laws for `‖`.
-/

namespace RandomSystemsCC.CR18

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.StrictContext
open scoped AbstractCrypto Classical

noncomputable section

universe c u v

variable {U : SignatureUniverse.{c, u, v}} [DecidableEq U.Code]
  [HasSumCode U]

/-! ## Parallel composition of resources -/

/-- The sum code's alphabets are only *equivalent* to the tagged sums
(`HasSumCode.inputEquiv` / `outputEquiv`), so the flat parallel behavior is
carried to the sum-code fibre by the relabelling of `RandomSystems.StrictRelabel`
— an isometry (`System.edist_relabel`) and a bijection (`System.relabel_inj`),
which is everything the two facts below need. -/
instance Resource.instPar : Par (Resource U) where
  par R S :=
    ⟨HasSumCode.sumCode R.code S.code,
      System.relabel (HasSumCode.inputEquiv R.code S.code).symm
        (HasSumCode.outputEquiv R.code S.code).symm
        (System.parallel R.system S.system)⟩

namespace Resource

omit [DecidableEq U.Code] in
theorem par_def (R S : Resource U) :
    R ∥ S =
      ⟨HasSumCode.sumCode R.code S.code,
        System.relabel (HasSumCode.inputEquiv R.code S.code).symm
          (HasSumCode.outputEquiv R.code S.code).symm
          (System.parallel R.system S.system)⟩ :=
  rfl

omit [DecidableEq U.Code] in
@[simp]
theorem par_code (R S : Resource U) :
    (R ∥ S).code = HasSumCode.sumCode R.code S.code :=
  rfl

omit [DecidableEq U.Code] in
/-- **The parallel decomposition of a resource is unique**: sum codes are
injective and the parallel decomposition of a strict behavior is unique
(`System.parallel_inj`). -/
theorem par_inj {R S R' S' : Resource U} (h : R ∥ S = R' ∥ S') :
    R = R' ∧ S = S' := by
  rcases R with ⟨a, rs⟩
  rcases R' with ⟨a', rs'⟩
  rcases S with ⟨b, ss⟩
  rcases S' with ⟨b', ss'⟩
  have hcode : HasSumCode.sumCode a b = HasSumCode.sumCode a' b' :=
    congrArg Resource.code h
  obtain ⟨rfl, rfl⟩ := HasSumCode.sumCode_inj hcode
  rw [par_def, par_def, Resource.mk.injEq] at h
  have hsys : System.relabel (HasSumCode.inputEquiv a b).symm
        (HasSumCode.outputEquiv a b).symm (System.parallel rs ss)
      = System.relabel (HasSumCode.inputEquiv a b).symm
        (HasSumCode.outputEquiv a b).symm (System.parallel rs' ss') :=
    eq_of_heq h.2
  obtain ⟨rfl, rfl⟩ := System.parallel_inj (System.relabel_inj _ _ hsys)
  exact ⟨rfl, rfl⟩

omit [DecidableEq U.Code] in
/-- Distinct components produce distinct compositions — the non-vacuity
receipt for `Par`: the operation genuinely remembers both components. -/
theorem par_ne_left {R R' S : Resource U} (h : R ≠ R') :
    R ∥ S ≠ R' ∥ S :=
  fun hc => h (par_inj hc).1

end Resource

/-- Within one pair of component codes, resource-level parallel distance
is fibre-level parallel distance. -/
theorem Resource.edist_par_par_same (ca cb : U.Code)
    (sa sa' : System (U.input ca) (U.output ca))
    (sb sb' : System (U.input cb) (U.output cb)) :
    edist ((⟨ca, sa⟩ : Resource U) ∥ ⟨cb, sb⟩)
        ((⟨ca, sa'⟩ : Resource U) ∥ ⟨cb, sb'⟩)
      = edist (System.parallel sa sb) (System.parallel sa' sb') := by
  rw [Resource.par_def, Resource.par_def]
  dsimp only
  rw [Resource.edist_same, System.edist_relabel]

/-- **Maurer11 §4.4 Definition 3 (eq. (3)) on the resource carrier**: the
strict contextual metric is `‖`-non-expanding.  Distinct sum codes sit at
distance `⊤` on both sides, and within one sum code the strict
`System.edist_parallel_le` applies. -/
instance : IsNonexpandingPar (Resource U) where
  edist_par_par_le a a' b b' := by
    rcases a with ⟨ca, sa⟩
    rcases a' with ⟨ca', sa'⟩
    rcases b with ⟨cb, sb⟩
    rcases b' with ⟨cb', sb'⟩
    by_cases hcodes : ca = ca' ∧ cb = cb'
    · obtain ⟨rfl, rfl⟩ := hcodes
      rw [Resource.edist_par_par_same]
      exact (System.edist_parallel_le sa sa' sb sb').trans
        (by rw [Resource.edist_same, Resource.edist_same])
    · have hcode : HasSumCode.sumCode ca cb ≠ HasSumCode.sumCode ca' cb' :=
        fun hc => hcodes (HasSumCode.sumCode_inj hc)
      rw [Resource.par_def, Resource.par_def]
      dsimp only
      rw [Resource.edist_ne hcode]
      rcases not_and_or.mp hcodes with h | h
      · rw [Resource.edist_ne h]
        simp
      · rw [Resource.edist_ne h]
        simp

/-! ## The syntactic protocol monoid, its action, and `SMulParClass` -/

/-- MauRen11 Definition 5's constructor set for this carrier, as syntax:
the free `{1, ∘, ‖}`-algebra over the primitive converters. -/
inductive ProtocolTerm (U : SignatureUniverse.{c, u, v}) :
    Type (max c u v)
  | prim (p : Primitive U)
  | one
  | mul (a b : ProtocolTerm U)
  | par (a b : ProtocolTerm U)

namespace ProtocolTerm

/-- The action of a protocol term.  A primitive acts natively; serial
composition composes (right factor first, the mathlib action order); a
parallel term acts componentwise on `‖`-shaped resources — well-defined
by uniqueness of the parallel decomposition — and as the identity
elsewhere (the fn. 23 freedom). -/
noncomputable def act : ProtocolTerm U → Resource U → Resource U
  | prim p => p.act
  | one => id
  | mul a b => a.act ∘ b.act
  | par a b => fun A =>
      if h : ∃ R S : Resource U, R ∥ S = A then
        a.act h.choose ∥ b.act h.choose_spec.choose
      else A

/-- The monoid-law congruence on protocol terms: associativity and the
two unit laws for serial composition, closed under both operations.  No
law mentions `‖` itself — AC's modeling rule. -/
inductive Rel : ProtocolTerm U → ProtocolTerm U → Prop
  | refl (a) : Rel a a
  | symm {a b} : Rel a b → Rel b a
  | trans {a b c} : Rel a b → Rel b c → Rel a c
  | assoc (a b c) : Rel (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a) : Rel (mul one a) a
  | mul_one (a) : Rel (mul a one) a
  | mul_congr {a a' b b'} : Rel a a' → Rel b b' → Rel (mul a b) (mul a' b')
  | par_congr {a a' b b'} : Rel a a' → Rel b b' → Rel (par a b) (par a' b')

theorem act_congr {a b : ProtocolTerm U} (h : Rel a b) : a.act = b.act := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | assoc a b c => rfl
  | one_mul a => rfl
  | mul_one a => rfl
  | mul_congr _ _ ih₁ ih₂ =>
      show _ ∘ _ = _ ∘ _
      rw [ih₁, ih₂]
  | par_congr _ _ ih₁ ih₂ =>
      funext A
      show (if h : ∃ R S : Resource U, R ∥ S = A then _ else A) = _
      rw [ih₁, ih₂]
      rfl

instance setoid (U : SignatureUniverse.{c, u, v}) [DecidableEq U.Code]
    [HasSumCode U] : Setoid (ProtocolTerm U) :=
  ⟨Rel, ⟨Rel.refl, Rel.symm, Rel.trans⟩⟩

end ProtocolTerm

/-- The carrier's parallel-capable protocol monoid: protocol terms modulo
the serial monoid laws. -/
def ParProtocol (U : SignatureUniverse.{c, u, v}) [DecidableEq U.Code]
    [HasSumCode U] : Type (max c u v) :=
  Quotient (ProtocolTerm.setoid U)

namespace ParProtocol

/-- Display a protocol term. -/
def mk (a : ProtocolTerm U) : ParProtocol U :=
  Quotient.mk (ProtocolTerm.setoid U) a

/-- A primitive as a parallel-capable protocol. -/
def ofPrimitive (p : Primitive U) : ParProtocol U :=
  mk (ProtocolTerm.prim p)

instance : One (ParProtocol U) :=
  ⟨mk ProtocolTerm.one⟩

instance : Mul (ParProtocol U) :=
  ⟨Quotient.map₂ ProtocolTerm.mul
    (fun _ _ ha _ _ hb => ProtocolTerm.Rel.mul_congr ha hb)⟩

instance : Par (ParProtocol U) :=
  ⟨Quotient.map₂ ProtocolTerm.par
    (fun _ _ ha _ _ hb => ProtocolTerm.Rel.par_congr ha hb)⟩

@[simp]
theorem mk_mul (a b : ProtocolTerm U) :
    mk a * mk b = mk (ProtocolTerm.mul a b) :=
  rfl

@[simp]
theorem mk_par (a b : ProtocolTerm U) :
    mk a ∥ mk b = mk (ProtocolTerm.par a b) :=
  rfl

instance instMonoid : Monoid (ParProtocol U) where
  mul_assoc a b c := by
    induction a using Quotient.inductionOn with
    | _ a =>
        induction b using Quotient.inductionOn with
        | _ b =>
            induction c using Quotient.inductionOn with
            | _ c => exact Quot.sound (ProtocolTerm.Rel.assoc a b c)
  one_mul a := by
    induction a using Quotient.inductionOn with
    | _ a => exact Quot.sound (ProtocolTerm.Rel.one_mul a)
  mul_one a := by
    induction a using Quotient.inductionOn with
    | _ a => exact Quot.sound (ProtocolTerm.Rel.mul_one a)

noncomputable instance : SMul (ParProtocol U) (Resource U) :=
  ⟨fun q => Quotient.lift ProtocolTerm.act
    (fun _ _ h => ProtocolTerm.act_congr h) q⟩

@[simp]
theorem mk_smul (a : ProtocolTerm U) (A : Resource U) :
    mk a • A = a.act A :=
  rfl

noncomputable instance instMulAction :
    MulAction (ParProtocol U) (Resource U) where
  one_smul A := rfl
  mul_smul q r A := by
    induction q using Quotient.inductionOn with
    | _ a =>
        induction r using Quotient.inductionOn with
        | _ b => rfl

/-- The native primitive action is the term action. -/
@[simp]
theorem ofPrimitive_smul (p : Primitive U) (A : Resource U) :
    ofPrimitive p • A = p.act A :=
  rfl

/-- **MauRen11 §6.2, `(α‖β)(R‖S) = αR ‖ βS`** on the strict resource
carrier: the parallel protocol acts componentwise on parallel resources.
Well-definedness is exactly the uniqueness of the parallel decomposition
(`Resource.par_inj`). -/
instance : SMulParClass (ParProtocol U) (Resource U) where
  smul_par α β R S := by
    induction α using Quotient.inductionOn with
    | _ a =>
        induction β using Quotient.inductionOn with
        | _ b =>
            show (ProtocolTerm.par a b).act (R ∥ S) = a.act R ∥ b.act S
            show (if h : ∃ R' S' : Resource U, R' ∥ S' = R ∥ S then
                a.act h.choose ∥ b.act h.choose_spec.choose
              else R ∥ S) = a.act R ∥ b.act S
            have hex : ∃ R' S' : Resource U, R' ∥ S' = R ∥ S := ⟨R, S, rfl⟩
            rw [dif_pos hex]
            obtain ⟨hR, hS⟩ :=
              Resource.par_inj hex.choose_spec.choose_spec
            exact congrArg₂ (fun x y => a.act x ∥ b.act y) hR hS

end ParProtocol

end

end RandomSystemsCC.CR18
