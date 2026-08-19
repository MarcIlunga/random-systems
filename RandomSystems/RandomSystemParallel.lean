/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CompatibleMetric
import RandomSystems.RandomSystemQuotient

/-!
# Typed parallel composition of random systems

This module lifts the deterministic tagged-parallel law through independent
products, probabilistic systems, normalized probability systems, and the
behavioral random-system quotient.  Signatures remain explicit throughout:
parallel composition sends `(X,Y)` and `(X',Y')` to
`(X ⊕ X',Y ⊕ Y')`.

The algebraic interchange law retains the two `AnswersInY` hypotheses of the
deterministic theorem.  Descending heterogeneous converter application to the
behavioral quotient additionally requires the precise `Emulable` witnesses
used by `equivalent_apply`; in particular, this module does not assert that
parallel composition preserves emulability.
-/

namespace RandomSystems

namespace Dist

variable {A B C D : Type*}

/-- Pushing an independent product through componentwise maps gives the
independent product of the two pushforwards. -/
theorem pushforward_product_eq_product_pushforwards
    (f : A → C) (g : B → D) (S : Dist A) (T : Dist B) :
    fTransform (fun p : A × B => (f p.1, g p.2)) (prod S T) =
      prod (fTransform f S) (fTransform g T) := by
  apply Finsupp.ext
  intro p
  rw [fTransform_apply_eq_mass, prod_apply,
    fTransform_apply_eq_mass, fTransform_apply_eq_mass]
  rw [mass_congr (prod S T) (fun q => Prod.ext_iff)]
  simpa only [Prod.fst, Prod.snd] using
    mass_prod_and S T (fun a => f a = p.1) (fun b => g b = p.2)

end Dist

end RandomSystems

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v u' v' w z w' z'

namespace PFunPDS

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
variable {U : Type w} {V : Type z} {U' : Type w'} {V' : Type z'}

/-- Applying a tagged parallel converter to an independent parallel PDS is
the same as applying both component converters before parallel composition. -/
theorem apply_parallel_eq_parallel_apply
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (beta : PFunConverter.ProtocolFn U' V' X' Y')
    (S : PFunPDS X Y) (T : PFunPDS X' Y')
    (halpha : PFunConverter.AnswersInY alpha)
    (hbeta : PFunConverter.AnswersInY beta) :
    apply (PFunConverter.par alpha beta) (par S T) =
      par (apply alpha S) (apply beta T) := by
  unfold apply par
  rw [Dist.fTransform_comp]
  rw [← RandomSystems.Dist.pushforward_product_eq_product_pushforwards]
  rw [Dist.fTransform_comp]
  congr 1
  funext p
  exact PFunConverter.apply_parallel_eq_parallel_apply
    alpha beta p.1 p.2 halpha hbeta

namespace Prob

/-- Independent tagged parallel composition of normalized probabilistic
systems. -/
noncomputable def parallel
    (S : PFunPDS.Prob X Y) (T : PFunPDS.Prob X' Y') :
    PFunPDS.Prob (X ⊕ X') (Y ⊕ Y') :=
  ⟨PFunPDS.par S.val T.val,
    PFunPDS.isProbDist_par S.property T.property⟩

/-- Apply a typed converter to a normalized probabilistic system. -/
noncomputable def applyConverter
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (S : PFunPDS.Prob X Y) : PFunPDS.Prob U V :=
  ⟨PFunPDS.apply alpha S.val,
    (PFunPDS.isProbDist_apply_iff alpha S.property.nonNeg).2 S.property⟩

/-- The tagged parallel converter law preserves normalization and holds on
normalized probabilistic systems. -/
theorem apply_parallel_eq_parallel_apply
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (beta : PFunConverter.ProtocolFn U' V' X' Y')
    (S : PFunPDS.Prob X Y) (T : PFunPDS.Prob X' Y')
    (halpha : PFunConverter.AnswersInY alpha)
    (hbeta : PFunConverter.AnswersInY beta) :
    applyConverter (PFunConverter.par alpha beta) (parallel S T) =
      parallel (applyConverter alpha S) (applyConverter beta T) := by
  apply Subtype.ext
  exact PFunPDS.apply_parallel_eq_parallel_apply
    alpha beta S.val T.val halpha hbeta

end Prob

end PFunPDS

namespace RandomSystem

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
variable {U : Type w} {V : Type z} {U' : Type w'} {V' : Type z'}

/-- Tagged parallel composition descends to behavioral random-system
classes. -/
noncomputable def parallel
    (R : RandomSystem X Y) (S : RandomSystem X' Y') :
    RandomSystem (X ⊕ X') (Y ⊕ Y') :=
  Quotient.liftOn₂ R S
    (fun R S => ofProb (PFunPDS.Prob.parallel R S))
    (fun _ _ _ _ hR hS => by
      apply Quotient.sound
      exact equivalent_par hR hS)

/-- Parallel composition of displayed classes is the class of the
probability-level parallel composition. -/
@[simp]
theorem parallel_classes_eq_class_of_parallel
    (S : PFunPDS.Prob X Y) (T : PFunPDS.Prob X' Y') :
    parallel (ofProb S) (ofProb T) =
      ofProb (PFunPDS.Prob.parallel S T) :=
  rfl

/-- An emulable typed converter acts between behavioral quotients with its
source and target signatures. -/
noncomputable def applyConverter
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (halpha : PFunConverter.Emulable alpha)
    (R : RandomSystem X Y) : RandomSystem U V :=
  Quotient.liftOn R
    (fun S => ofProb (PFunPDS.Prob.applyConverter alpha S))
    (fun _ _ h => by
      apply Quotient.sound
      exact equivalent_apply alpha halpha h)

/-- Converter application to a displayed class is the class of application
to its normalized representative. -/
@[simp]
theorem converter_application_of_class_eq_class_of_application
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (halpha : PFunConverter.Emulable alpha)
    (S : PFunPDS.Prob X Y) :
    applyConverter alpha halpha (ofProb S) =
      ofProb (PFunPDS.Prob.applyConverter alpha S) :=
  rfl

/-- Serial converter application on behavioral random systems is the AC
action law already proved at the deterministic and probability-law levels:
the right converter acts first.  This theorem is signature-polymorphic, so
application modules never have to re-prove the quotient lift. -/
theorem apply_converter_serial
    {A B C D E F : Type*}
    (outer : PFunConverter.ProtocolFn A B C D)
    (inner : PFunConverter.ProtocolFn C D E F)
    (outerAnswers : PFunConverter.AnswersInY outer)
    (outerEmulable : PFunConverter.Emulable outer)
    (innerEmulable : PFunConverter.Emulable inner)
    (resource : RandomSystem E F) :
    applyConverter (PFunConverter.comp outer inner)
        (PFunConverter.emulable_comp outer inner outerAnswers
          outerEmulable innerEmulable) resource =
      applyConverter outer outerEmulable
        (applyConverter inner innerEmulable resource) := by
  induction resource using Quotient.inductionOn with
  | _ system =>
      apply Quotient.sound
      change Equivalent
        (PFunPDS.apply (PFunConverter.comp outer inner) system.val)
        (PFunPDS.apply outer (PFunPDS.apply inner system.val))
      have applicationEquation :
          PFunPDS.apply (PFunConverter.comp outer inner) system.val =
            PFunPDS.apply outer (PFunPDS.apply inner system.val) := by
        unfold PFunPDS.apply
        rw [RandomSystems.Dist.fTransform_comp]
        congr 1
        funext deterministic
        exact PFunConverter.apply_comp outer inner deterministic outerAnswers
      rw [applicationEquation]
      exact equivalent_refl _

/-- The tagged parallel converter law holds on behavioral random-system
classes whenever the two components and their tagged parallel converter have
the emulation witnesses required to descend application. -/
theorem apply_parallel_eq_parallel_apply
    (alpha : PFunConverter.ProtocolFn U V X Y)
    (beta : PFunConverter.ProtocolFn U' V' X' Y')
    (halpha_answers : PFunConverter.AnswersInY alpha)
    (hbeta_answers : PFunConverter.AnswersInY beta)
    (halpha_emulable : PFunConverter.Emulable alpha)
    (hbeta_emulable : PFunConverter.Emulable beta)
    (hparallel_emulable :
      PFunConverter.Emulable (PFunConverter.par alpha beta))
    (R : RandomSystem X Y) (S : RandomSystem X' Y') :
    applyConverter (PFunConverter.par alpha beta) hparallel_emulable
        (parallel R S) =
      parallel (applyConverter alpha halpha_emulable R)
        (applyConverter beta hbeta_emulable S) := by
  induction R using Quotient.inductionOn with
  | _ R =>
      induction S using Quotient.inductionOn with
      | _ S =>
          change ofProb
              (PFunPDS.Prob.applyConverter (PFunConverter.par alpha beta)
                (PFunPDS.Prob.parallel R S)) =
            parallel
              (ofProb (PFunPDS.Prob.applyConverter alpha R))
              (ofProb (PFunPDS.Prob.applyConverter beta S))
          rw [PFunPDS.Prob.apply_parallel_eq_parallel_apply
            alpha beta R S halpha_answers hbeta_answers]
          exact (parallel_classes_eq_class_of_parallel
            (PFunPDS.Prob.applyConverter alpha R)
            (PFunPDS.Prob.applyConverter beta S)).symm

end RandomSystem

end RandomSystems.CR18
