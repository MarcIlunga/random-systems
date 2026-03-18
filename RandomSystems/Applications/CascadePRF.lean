/-
Maurer–Pietrzak (2004) warmup: simplest composition for random functions.

This file implements the easiest "composition operator" from MauPie04:
the pointwise group operation (paper Definition 10, operator `⋆`).

In game-based terms this is the classic fact:
  XOR-of-two-independent-random-oracles is a random oracle.

We prove it in the random-systems/PDS model used in this repo:
  (URFfun ⋆ URFfun) = URFfun

Notes:
- This is intentionally the *simplest* example to validate our modeling choices.
- This file is not yet imported by `RandomSystems.lean`.
- Later, the cascade operator `∘` (permutations / chaining) is the next step.
-/
import RandomSystems.Instances.URF
import RandomSystems.Advantage
import RandomSystems.Dist

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

namespace MauPie04Warmup

variable {X Y : Type*} {q : ℕ}
  [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [AddCommGroup Y]
  [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]

/-! ### Helper: `snd` marginal of uniform is uniform -/

private theorem fTransform_snd_uniform (A B : Type*)
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    Dist.fTransform (Prod.snd : A × B → B) (Dist.uniform (A × B)) = Dist.uniform B := by
  classical
  -- `snd = fst ∘ swap`
  have hsnd : (Prod.snd : A × B → B) = Prod.fst ∘ (Equiv.prodComm A B) := by
    rfl
  -- Push uniform through the swap equivalence, then project with `fst`.
  calc
    Dist.fTransform (Prod.snd : A × B → B) (Dist.uniform (A × B))
        = Dist.fTransform (Prod.fst : B × A → B)
            (Dist.fTransform (Equiv.prodComm A B) (Dist.uniform (A × B))) := by
            simp [hsnd, Dist.fTransform_comp]
    _ = Dist.fTransform (Prod.fst : B × A → B) (Dist.uniform (B × A)) := by
            -- `prodComm` is an equivalence, so it preserves uniform.
            rw [Dist.fTransform_equiv_uniform (Equiv.prodComm A B)]
    _ = Dist.uniform B := by
            simpa using (Dist.fTransform_fst_uniform (A' := B) (B' := A))

/-! ### The `⋆` operator on (uniform) random functions -/

private def starFun (p : (X → Y) × (X → Y)) : X → Y :=
  fun x => p.1 x + p.2 x

/-- Bijection `(f,g) ↦ (f, f+g)` (and inverse `(f,h) ↦ (f, h-f)`). -/
private def pairToFH : ((X → Y) × (X → Y)) ≃ ((X → Y) × (X → Y)) where
  toFun p := (p.1, fun x => p.1 x + p.2 x)
  invFun p := (p.1, fun x => p.2 x - p.1 x)
  left_inv p := by
    cases p with
    | mk f g =>
      ext x
      · rfl
      · simp [add_sub_cancel_left]
  right_inv p := by
    cases p with
    | mk f h =>
      ext x
      · rfl
      · -- `f + (h - f) = h`
        calc
          f x + (h x - f x) = (f x + h x) - f x := by
            simp [sub_eq_add_neg, add_assoc]
          _ = h x := by
            simp [add_sub_cancel_left]

private theorem starFun_uniform :
    Dist.fTransform starFun (Dist.uniform ((X → Y) × (X → Y))) =
      Dist.uniform (X → Y) := by
  classical
  -- `starFun = snd ∘ pairToFH`
  have hstar : starFun = Prod.snd ∘ pairToFH (X := X) (Y := Y) := by
    rfl
  calc
    Dist.fTransform starFun (Dist.uniform ((X → Y) × (X → Y)))
        = Dist.fTransform Prod.snd
            (Dist.fTransform (pairToFH (X := X) (Y := Y))
              (Dist.uniform ((X → Y) × (X → Y)))) := by
            simp [hstar, Dist.fTransform_comp]
    _ = Dist.fTransform Prod.snd (Dist.uniform ((X → Y) × (X → Y))) := by
            simp [Dist.fTransform_equiv_uniform]
    _ = Dist.uniform (X → Y) := by
            simpa using (fTransform_snd_uniform (A := X → Y) (B := X → Y))

/-! ### A PDS model of `URFfun ⋆ URFfun` -/

/-!
We make independence explicit using `Dist.prod`:
sample `f` and `g` independently from their respective distributions.

This generalizes the warmup `⋆` operator beyond uniform distributions, which is
what we need for keyed-function (non-uniform) distributions.
!-/

/-- Sample two independent functions `f,g : X → Y` (according to `Df` and `Dg`)
and answer each query `x` with `f(x)+g(x)`. -/
def URFfunStarOf (Df Dg : Dist (X → Y)) : PDS X Y q where
  dist :=
    Dist.fTransform
      (fun p : (X → Y) × (X → Y) => DDS.ofFunq (q := q) (starFun (X := X) (Y := Y) p))
      (Dist.prod Df Dg)

/-- Sample two independent uniform functions `f,g : X → Y` and answer each query `x` with `f(x)+g(x)`.

This is the MauPie04 `⋆`-composition operator instantiated with the additive group on `Y`. -/
def URFfunStar : PDS X Y q :=
  URFfunStarOf (X := X) (Y := Y) (q := q) (Dist.uniform (X → Y)) (Dist.uniform (X → Y))

omit [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)] in
/-- **Warmup theorem** (MauPie04 Definition 10, `⋆`): `URFfun ⋆ URFfun = URFfun`.

In other words, XOR/sum of two independent random function oracles is again a random function oracle. -/
theorem URFfunStar_eq_URFfun :
    URFfunStar (X := X) (Y := Y) (q := q) =
      Instances.URFfun (X := X) (Y := Y) (q := q) := by
  apply PDS.ext
  classical
  -- Push the uniform pair distribution through `starFun`, then through `DDS.ofFunq`.
  -- `URFfun.dist` is exactly `DDS.ofFunq` applied to a uniform `X → Y`.
  show
    Dist.fTransform
        (fun p : (X → Y) × (X → Y) =>
          DDS.ofFunq (q := q) (starFun (X := X) (Y := Y) p))
        (Dist.prod (Dist.uniform (X → Y)) (Dist.uniform (X → Y)))
      =
      Dist.fTransform
        (fun f : X → Y => DDS.ofFunq (q := q) f)
        (Dist.uniform (X → Y))
  -- Rewrite LHS as a composed pushforward: `DDS.ofFunq` after `starFun`.
  change
    Dist.fTransform
        ((fun f : X → Y => DDS.ofFunq (q := q) f) ∘ (starFun (X := X) (Y := Y)))
        (Dist.prod (Dist.uniform (X → Y)) (Dist.uniform (X → Y)))
      =
      Dist.fTransform
        (fun f : X → Y => DDS.ofFunq (q := q) f)
        (Dist.uniform (X → Y))
  rw [← Dist.fTransform_comp
    (g := fun f : X → Y => DDS.ofFunq (q := q) f)
    (f := starFun (X := X) (Y := Y))
    (X := Dist.prod (Dist.uniform (X → Y)) (Dist.uniform (X → Y)))]
  -- Reduce to the warmup uniformity fact: `starFun` maps independent uniforms to uniform.
  simp [Dist.prod_uniform (A := (X → Y)) (B := (X → Y)), starFun_uniform]

/-- Corollary: the distinguishing advantage between the two ideal descriptions is 0. -/
theorem advantage_URFfunStar_URFfun :
    advantage (URFfunStar (X := X) (Y := Y) (q := q))
      (Instances.URFfun (X := X) (Y := Y) (q := q)) = 0 := by
  -- They are definitionally equal as PDS, so advantage is self-advantage.
  simp [URFfunStar_eq_URFfun, advantage_self]

end MauPie04Warmup

end RandomSystems.Applications
