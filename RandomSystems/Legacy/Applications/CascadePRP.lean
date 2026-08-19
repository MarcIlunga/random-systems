/-
Cascade for permutations (easy case).

This is the `∘` composition operator from MauPie04 (Definition 10) specialized
to *uniform random permutations*: composing two independent uniform permutations
is again a uniform permutation.

We implement this in the PDS model used in this repo by sampling permutations
uniformly and embedding them as stateless DDS via `Instances.ofPerm`.
-/
import RandomSystems.Legacy.Instances.URP
import RandomSystems.Dist

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

namespace MauPie04CascadePerm

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : ℕ}

/-- Uniform random permutation as a PDS: sample `π : Perm X` uniformly and use it as a stateless DDS. -/
def URPfun : PDS X X q where
  dist := Dist.fTransform (fun π : Equiv.Perm X => Instances.ofPerm (X := X) (q := q) π)
    (Dist.uniform (Equiv.Perm X))

/-- Cascade/composition operator on permutations: `(π₁, π₂) ↦ π₂ * π₁`. -/
private def permCompose (p : Equiv.Perm X × Equiv.Perm X) : Equiv.Perm X :=
  p.2 * p.1

/-- Bijection `(π,σ) ↦ (π, σ*π)` with inverse `(π,τ) ↦ (π, τ*π⁻¹)`. -/
private def pairToMul : (Equiv.Perm X × Equiv.Perm X) ≃ (Equiv.Perm X × Equiv.Perm X) where
  toFun p := (p.1, p.2 * p.1)
  invFun p := (p.1, p.2 * p.1⁻¹)
  left_inv p := by
    rcases p with ⟨π, σ⟩
    ext <;> simp [mul_assoc]
  right_inv p := by
    rcases p with ⟨π, τ⟩
    ext <;> simp [mul_assoc]

/-- Helper: `snd` marginal of uniform is uniform (same as in `CascadePRF`). -/
private theorem fTransform_snd_uniform (A B : Type*)
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    Dist.fTransform (Prod.snd : A × B → B) (Dist.uniform (A × B)) = Dist.uniform B := by
  classical
  have hsnd : (Prod.snd : A × B → B) = Prod.fst ∘ (Equiv.prodComm A B) := by
    rfl
  calc
    Dist.fTransform (Prod.snd : A × B → B) (Dist.uniform (A × B))
        = Dist.fTransform (Prod.fst : B × A → B)
            (Dist.fTransform (Equiv.prodComm A B) (Dist.uniform (A × B))) := by
            simp [hsnd, Dist.fTransform_comp]
    _ = Dist.fTransform (Prod.fst : B × A → B) (Dist.uniform (B × A)) := by
            rw [Dist.fTransform_equiv_uniform (Equiv.prodComm A B)]
    _ = Dist.uniform B := by
            simpa using (Dist.fTransform_fst_uniform (A' := B) (B' := A))

/-- Uniformity of permutation multiplication: if `(π,σ)` is uniform on the product,
then `σ*π` is uniform on `Perm X`. -/
private theorem permCompose_uniform :
    Dist.fTransform permCompose (Dist.uniform (Equiv.Perm X × Equiv.Perm X)) =
      Dist.uniform (Equiv.Perm X) := by
  classical
  have hcomp : permCompose (X := X) = Prod.snd ∘ pairToMul (X := X) := by
    rfl
  calc
    Dist.fTransform permCompose (Dist.uniform (Equiv.Perm X × Equiv.Perm X))
        = Dist.fTransform Prod.snd
            (Dist.fTransform (pairToMul (X := X))
              (Dist.uniform (Equiv.Perm X × Equiv.Perm X))) := by
            simp [hcomp, Dist.fTransform_comp]
    _ = Dist.fTransform Prod.snd (Dist.uniform (Equiv.Perm X × Equiv.Perm X)) := by
            simp [Dist.fTransform_equiv_uniform]
    _ = Dist.uniform (Equiv.Perm X) := by
            simpa using (fTransform_snd_uniform (A := Equiv.Perm X) (B := Equiv.Perm X))

/-- Cascade of two independent uniform permutations is uniform. -/
def URPfunCascade : PDS X X q where
  dist :=
    Dist.fTransform
      (fun p : Equiv.Perm X × Equiv.Perm X =>
        Instances.ofPerm (X := X) (q := q) (permCompose (X := X) p))
      (Dist.uniform (Equiv.Perm X × Equiv.Perm X))

theorem URPfunCascade_eq_URPfun :
    URPfunCascade (X := X) (q := q) = URPfun (X := X) (q := q) := by
  apply PDS.ext
  classical
  -- Push uniform pairs through multiplication, then through `ofPerm`.
  simp [URPfun, URPfunCascade]
  -- Make the composition explicit to match `Dist.fTransform_comp`.
  have hcomp :
      (fun p : Equiv.Perm X × Equiv.Perm X =>
          Instances.ofPerm (X := X) (q := q) (permCompose (X := X) p))
        =
      (fun π : Equiv.Perm X => Instances.ofPerm (X := X) (q := q) π) ∘ permCompose (X := X) := by
    rfl
  rw [hcomp]
  -- Regroup the pushforward through `permCompose`.
  rw [(Dist.fTransform_comp
    (g := fun π : Equiv.Perm X => Instances.ofPerm (X := X) (q := q) π)
    (f := permCompose (X := X))
    (X := Dist.uniform (Equiv.Perm X × Equiv.Perm X))).symm]
  -- `permCompose` maps uniform pairs to uniform permutations.
  simpa [hcomp] using congrArg
    (fun D => Dist.fTransform (fun π : Equiv.Perm X => Instances.ofPerm (X := X) (q := q) π) D)
    (permCompose_uniform (X := X))

end MauPie04CascadePerm

end RandomSystems.Applications
