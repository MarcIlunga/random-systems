/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Counting
import RandomSystems.CR18Tactics
import RandomSystems.Instances.URFfunEval
import RandomSystems.SemanticRegistry

/-!
# CR18 §4.11.3 — the URP–URF "switching lemma" (Def 4.22, Lemma 4.18, Lemma 4.19)

A single collision notion and the §4.11.3 statements:

* **`Collides`** — the one collision predicate: a tuple of values contains a value twice.
* **`pcoll`** (Def 4.22) — the genuine *probability* that `q` iid uniform values from a size-`t`
  alphabet collide (a `Dist.mass` of `Collides`, NOT a closed-form number).
* **`pcoll_eq_one_sub_descFactorial_div`** — the closed form `pcoll(t,q) = 1 - (t)_q/t^q`, the bridge
  to the falling-factorial arithmetic of `RandomSystems/Counting.lean`.
* **`pcoll_le_birthday`** — the birthday bound `pcoll(t,q) ≤ ½q²/t`, a corollary of the sharp
  `pcoll_le_birthday_tight` (`≤ q(q-1)/(2t)`), itself `Counting.birthday_bound` transported.
* **`min_le_pcoll` / `one_sub_exp_le_pcoll` / `pcoll_le_one_sub_exp`** — Boneh–Shoup Theorem B.1's
  two-sided form, including the collision *lower* bound an attack argument needs.
* **`collisionCond` / `Rhat`** — Example 4.15's collision MBO and the resulting collision-enhanced game
  `R̂ₙ,ₙ := gameOf Rₙ,ₙ collisionCond` (constructed from the base URF, not taken as a free `Ŝ`).
* **`urf_urp_switching`** — the switching lemma in Maurer's *filtered* form
  `∆([q]Rₙ,ₙ, [q]Pₙ) ≤ ½q²2⁻ⁿ`, i.e.
  `maxAdvantage ([q]Rₙ,ₙ) ([q]Pₙ) ≤ q²/(2·2ⁿ)` over the concrete URF/URP under the query filter `[q]`.

The proof follows Maurer's construction: build the collision game from the base URF, apply
Theorem 4.17 to the filtered systems, and discharge the blind collision game by a proved birthday
bound. The sharper paper sentence identifying the optimal blind collision game exactly with
`pcoll(|X|, q)` is not kept as a theorem-shaped TODO here; it should be added only when proved.

Sources: Maurer's CR18 notes §4.11.3, and Boneh–Shoup, *A Graduate Course in Applied
Cryptography*, Appendix B (`papers/BonehShoup.pdf`, book pp. 1101–1103) for the two-sided
birthday bound and the non-uniform statement.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open scoped RandomSystems.CR18.CondEquiv
open scoped RandomSystems.CR18

/-- **CR18 Definition 4.22 — the collision event.** A length-`q` tuple of values "contains a value
twice": two distinct positions carry equal values. This is the single collision notion of §4.11.3. -/
def Collides {α : Type*} {q : ℕ} (v : Fin q → α) : Prop := ∃ i j : Fin q, i ≠ j ∧ v i = v j

/-- **CR18 Definition 4.22 — `pcoll(t, q)`.** The *probability* that `q` independent, uniformly chosen
values from an alphabet of size `t` contain a collision — the `Dist.mass` of `Collides` over `q` iid
uniform draws from `Fin t`. (For the empty alphabet `t = 0` there are no values to draw, so `pcoll 0 q
:= 0`.) Faithful to Maurer's "the probability that …"; the closed form `1 − (t)_q/t^q` is a theorem,
not the definition. -/
noncomputable def pcoll (t q : ℕ) : ℝ :=
  if h : 0 < t then
    haveI : Nonempty (Fin t) := ⟨⟨0, h⟩⟩
    Dist.mass (Dist.iidPow (Dist.uniform (Fin t)) q) Collides
  else 0

/-- **Finite union (subadditivity) bound for `Dist.mass`** (UPSTREAM-CANDIDATE): the mass of "some
event in `s` holds" is at most the sum of the individual masses. The measure-theoretic union bound,
specialized to a finite index `Finset`. -/
theorem mass_biUnion_le {A ι : Type*} [Fintype A] [Nonempty A]
    (X : Dist A) (hX : X.NonNeg) (s : Finset ι) (E : ι → A → Prop) :
    X.mass (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, X.mass (E i) := by
  classical
  rw [Dist.mass_eq_sum]
  have hrhs : (∑ i ∈ s, X.mass (E i)) = ∑ i ∈ s, ∑ a, (if E i a then X a else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [Dist.mass_eq_sum]
  rw [hrhs, Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : ∃ i ∈ s, E i a
  · rw [if_pos ha]
    obtain ⟨i, hi, hEi⟩ := ha
    calc X a = (if E i a then X a else 0) := (if_pos hEi).symm
      _ ≤ _ := Finset.single_le_sum (f := fun i => if E i a then X a else 0)
                  (fun i _ => by by_cases h : E i a <;> simp [h, hX a]) hi
  · rw [if_neg ha]
    exact Finset.sum_nonneg fun i _ => by
      by_cases h : E i a <;> simp [h, hX a]

/-- **Counting tuples with two coordinates equal**: the number of `v : Fin q → α` with
`v i = v j` (for `i ≠ j`) is `|α|^{q-1}` — coordinate `j` is forced to equal coordinate `i`,
leaving `q-1` free coordinates. Via the drop-`j` equivalence to `({k // k ≠ j} → α)`.

UPSTREAM-CANDIDATE: reusable pair-equality fiber count for iid birthday bounds. -/
theorem card_pair_eq_type {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (i j : Fin q) (hij : i ≠ j) :
    (Finset.univ.filter (fun v : Fin q → α => v i = v j)).card =
      Fintype.card α ^ (q - 1) := by
  classical
  rw [← Fintype.card_subtype]
  have e : {v : Fin q → α // v i = v j} ≃ ({k : Fin q // k ≠ j} → α) :=
    { toFun := fun v k => v.1 k.1
      invFun := fun w => ⟨fun k => if hk : k = j then w ⟨i, hij⟩ else w ⟨k, hk⟩, by
        dsimp only
        rw [dif_pos rfl, dif_neg hij]⟩
      left_inv := fun v => by
        apply Subtype.ext; funext k
        dsimp only
        by_cases hk : k = j
        · rw [dif_pos hk, hk]; exact v.2
        · rw [dif_neg hk]
      right_inv := fun w => by
        funext k
        dsimp only
        rw [dif_neg k.2] }
  rw [Fintype.card_congr e, Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

/-- Independent uniform samples over a finite type are the uniform distribution over tuples.

UPSTREAM-CANDIDATE: iid/uniform bridge for finite products. -/
theorem iidPow_uniform_eq_uniform_fun {α : Type*} [Fintype α] [Nonempty α] (q : ℕ) :
    Dist.iidPow (Dist.uniform α) q = Dist.uniform (Fin q → α) := by
  classical
  ext v
  rw [Dist.iidPow_apply, Dist.uniform_apply]
  have hu : ∀ i : Fin q, (Dist.uniform α) (v i) = 1 / (Fintype.card α : ℝ) := by
    intro i; rw [Dist.uniform_apply]
  simp_rw [hu]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
  rw [div_pow]
  simp

/-- In an iid uniform tuple, any two distinct coordinates agree with probability `1 / |α|`.

UPSTREAM-CANDIDATE: pairwise collision marginal for birthday union bounds. -/
theorem iid_uniform_pair_eq_mass {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {q : ℕ} (i j : Fin q) (hij : i ≠ j) :
    (Dist.iidPow (Dist.uniform α) q).mass (fun v : Fin q → α => v i = v j) =
      1 / (Fintype.card α : ℝ) := by
  classical
  have hq1 : 1 ≤ q := by have := i.2; omega
  rw [Dist.mass_eq_sum]
  have hconst : ∀ v : Fin q → α,
      Dist.iidPow (Dist.uniform α) q v = (1 / (Fintype.card α : ℝ)) ^ q := by
    intro v
    rw [Dist.iidPow_apply]
    have hu : ∀ i : Fin q, (Dist.uniform α) (v i) = 1 / (Fintype.card α : ℝ) := by
      intro i; rw [Dist.uniform_apply]
    simp_rw [hu]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hconst]
  rw [← Finset.sum_filter, Finset.sum_const, card_pair_eq_type i j hij, nsmul_eq_mul,
    div_pow, one_pow, mul_one_div]
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul]
  push_cast
  rw [← pow_succ, Nat.sub_add_cancel hq1]

/-- A heterogeneous uniform random function evaluated at two distinct inputs
collides with probability `1 / |Y|`. -/
theorem uniform_function_pair_eq_mass_of_codomain
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {a b : X} (hab : a ≠ b) :
    (Dist.uniform (X → Y)).mass (fun f => f a = f b) =
      1 / (Fintype.card Y : ℝ) := by
  classical
  let nonces : Fin 2 → X := fun i => if i = 0 then a else b
  have hinj : Function.Injective nonces := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [nonces, hab] at hij ⊢
    · exact False.elim (hab hij.symm)
  have heval : Dist.fTransform (fun f : X → Y => fun i => f (nonces i))
      (Dist.uniform (X → Y)) = Dist.uniform (Fin 2 → Y) :=
    RandomSystems.Instances.eval_nonces_uniform nonces hinj
  have hevent :
      (Dist.uniform (X → Y)).mass (fun f => f a = f b) =
        (Dist.uniform (X → Y)).mass
          (fun f => (fun i => f (nonces i)) (0 : Fin 2) =
            (fun i => f (nonces i)) (1 : Fin 2)) := by
    apply Dist.mass_congr
    intro f
    simp [nonces]
  rw [hevent, ← Dist.mass_fTransform
    (fun f : X → Y => fun i => f (nonces i)) (Dist.uniform (X → Y))
    (fun v : Fin 2 → Y => v 0 = v 1), heval,
    ← iidPow_uniform_eq_uniform_fun (α := Y) 2]
  exact iid_uniform_pair_eq_mass (α := Y) (i := 0) (j := 1) (by decide)

/-- A uniform random function evaluated at two distinct inputs collides with probability `1 / |X|`.

UPSTREAM-CANDIDATE: two-point URF marginal for birthday union bounds. -/
theorem uniform_function_pair_eq_mass {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {a b : X} (hab : a ≠ b) :
    (Dist.uniform (X → X)).mass (fun f => f a = f b) =
      1 / (Fintype.card X : ℝ) :=
  uniform_function_pair_eq_mass_of_codomain hab

/-- Uniform event mass as a cardinality ratio.

Compatibility wrapper over `RandomSystems.Dist.uniform_mass_eq_card_filter`.
Keep this CR18-local spelling while downstream switching code is migrated to
the shared distribution API. -/
theorem uniform_mass_eq_card_filter {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) [DecidablePred P] :
    (Dist.uniform A).mass P =
      (((Finset.univ : Finset A).filter P).card : ℝ) / (Fintype.card A : ℝ) := by
  exact Dist.uniform_mass_eq_card_filter P

/-- Uniform distributions do not depend on the particular `Fintype`/`Nonempty` instance presentation.

UPSTREAM-CANDIDATE: generic bridge for definitions, such as `URP`, that synthesize a hidden classical
finite instance while local counting lemmas use an explicit instance from the theorem context. -/
theorem uniform_eq_of_fintype_instances {A : Type*}
    (FA FB : Fintype A) (NA NB : Nonempty A) :
    @Dist.uniform A FA NA = @Dist.uniform A FB NB := by
  ext a
  rw [@Dist.uniform_apply A FA NA a, @Dist.uniform_apply A FB NB a]
  have hcard : @Fintype.card A FA = @Fintype.card A FB := by
    exact @Fintype.card_congr A A FA FB (Equiv.refl A)
  rw [hcard]

/-- The number of permutations fixing prescribed values on a finite injective input tuple.

UPSTREAM-CANDIDATE: reusable permutation-fiber count for PRP/URP transcript arguments. -/
theorem card_perm_fiber {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_ys_inj : Function.Injective ys)
    (h_q_le : q ≤ Fintype.card X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card =
    (Fintype.card X - q).factorial := by
  exact Counting.card_perm_fiber inputs h_inj ys h_ys_inj h_q_le

/-- The permutation fiber count over an actual finite input set, rather than an injective tuple.

UPSTREAM-CANDIDATE: finite-set form of `card_perm_fiber`, suited to transcript arguments with repeated
queries. The queried set is `S`; the prescribed outputs are an embedding `S ↪ X`. -/
theorem card_perm_fiber_finset {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (g : S ↪ X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter (fun π => ∀ x : S, π x.1 = g x)).card =
      (Fintype.card X - S.card).factorial := by
  exact Counting.card_perm_fiber_finset S g

/-- The number of functions agreeing with a prescribed map on a finite input subset.

UPSTREAM-CANDIDATE: reusable function-fiber count for transcript arguments. -/
theorem card_function_fiber_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X) (g : S → Y) :
    (Finset.univ.filter (fun f : X → Y => ∀ x : S, f x.1 = g x)).card =
      Fintype.card Y ^ (Fintype.card X - S.card) := by
  exact Counting.card_function_fiber_finset S g

/-- The number of functions that are injective on a finite set of inputs.

UPSTREAM-CANDIDATE: generic finite-function count for no-collision transcript normalizers. A function
injective on `S` is equivalently an embedding `S ↪ Y` plus arbitrary values on `Sᶜ`. -/
theorem card_function_injOn_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X)
    [DecidablePred (fun f : X → Y => Set.InjOn f (fun x => x ∈ S))] :
    ((Finset.univ : Finset (X → Y)).filter (fun f => Set.InjOn f (fun x => x ∈ S))).card =
      (Fintype.card Y).descFactorial S.card * Fintype.card Y ^ (Fintype.card X - S.card) := by
  exact Counting.card_function_injOn_finset S

/-- Uniform functions conditioned to be injective on the actual queried set have the same finite
transcript fiber law as uniform permutations.

UPSTREAM-CANDIDATE: generic finite-set H-coefficient identity for Example-4.15 conditional
equivalence. The statement is tight in the queried set `S`, with no default input. -/
theorem uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (S : Finset X) (g : S → X) :
    (Dist.uniform (X → X)).mass
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S)) =
      (Dist.uniform (Equiv.Perm X)).mass (fun σ => ∀ x : S, σ x.1 = g x) *
        (Dist.uniform (X → X)).mass (fun f => Set.InjOn f (fun x => x ∈ S)) := by
  classical
  rw [uniform_mass_eq_card_filter, uniform_mass_eq_card_filter, uniform_mass_eq_card_filter]
  by_cases hg : Function.Injective g
  · have hleft_set : ((Finset.univ : Finset (X → X)).filter
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S))) =
      ((Finset.univ : Finset (X → X)).filter (fun f => ∀ x : S, f x.1 = g x)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact h.1
      · intro h
        refine ⟨h, ?_⟩
        intro a ha b hb hab
        have hgab : g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
          rw [← h ⟨a, ha⟩, ← h ⟨b, hb⟩, hab]
        exact congrArg Subtype.val (hg hgab)
    have hperm_card : ((Finset.univ : Finset (Equiv.Perm X)).filter
          (fun σ => ∀ x : S, σ x.1 = g x)).card =
        (Fintype.card X - S.card).factorial := by
      simpa using card_perm_fiber_finset S ⟨g, hg⟩
    rw [hleft_set, card_function_fiber_finset S g, hperm_card, card_function_injOn_finset S]
    rw [Fintype.card_fun, Fintype.card_perm]
    have hle : S.card ≤ Fintype.card X := Finset.card_le_univ S
    have hfact : (Fintype.card X - S.card).factorial * (Fintype.card X).descFactorial S.card =
        (Fintype.card X).factorial := Nat.factorial_mul_descFactorial hle
    have hfact_ne : (((Fintype.card X - S.card).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos (Fintype.card X - S.card)).ne'
    have hdesc_ne : (((Fintype.card X).descFactorial S.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hle).ne'
    rw [← hfact]
    field_simp [hfact_ne, hdesc_ne]
    push_cast
    ring
  · have hnoneF : ∀ f : X → X,
        ¬ ((∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S)) := by
      intro f hf
      apply hg
      intro x y hxy
      apply Subtype.ext
      exact hf.2 x.2 y.2 (by rw [hf.1 x, hf.1 y, hxy])
    have hL : ((Finset.univ : Finset (X → X)).filter
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S))).card = 0 := by
      rw [Finset.card_eq_zero]
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hf
        exact False.elim (hnoneF f hf)
      · intro hf
        simp at hf
    have hnoneP : ∀ σ : Equiv.Perm X, ¬ (∀ x : S, σ x.1 = g x) := by
      intro σ hσ
      apply hg
      intro x y hxy
      apply Subtype.ext
      exact σ.injective (by rw [hσ x, hσ y, hxy])
    have hP : ((Finset.univ : Finset (Equiv.Perm X)).filter
        (fun σ => ∀ x : S, σ x.1 = g x)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hσ
        exact False.elim (hnoneP σ hσ)
      · intro hσ
        simp at hσ
    rw [hL, hP]
    simp

/-- A repeated-input transcript is consistent when equal inputs are assigned equal outputs.
Stated for heterogeneous input/output types so VIL constructions (`M → X`, e.g. the CBC-MAC) reuse it.

UPSTREAM-CANDIDATE: finite tuple consistency predicate for quotienting a concrete transcript by its
actual queried input set. -/
def tupleConsistent {I O : Type*} {n : ℕ} (xs : Fin n → I) (ys : Fin n → O) : Prop :=
  ∀ i j, xs i = xs j → ys i = ys j

/-- A transcript has no output collision when distinct inputs are assigned distinct outputs.

UPSTREAM-CANDIDATE: finite tuple no-collision predicate for the Example-4.15 condition. -/
def tupleNoCollision {X : Type*} {n : ℕ} (xs ys : Fin n → X) : Prop :=
  ∀ i j, xs i ≠ xs j → ys i ≠ ys j

/-- An inconsistent transcript has no seed that agrees with all input/output pairs.

UPSTREAM-CANDIDATE: generic zero-mass fact for repeated-input transcript normalization. It is stated
over an arbitrary distribution and evaluator, with no finiteness or nonemptiness assumptions on the
seed type beyond the finite support already carried by `Dist`. -/
theorem mass_tuple_agree_eq_zero_of_not_consistent
    {A I O : Type*} {n : ℕ} (D : Dist A) (eval : A → I → O)
    (xs : Fin n → I) (ys : Fin n → O) (hcons : ¬ tupleConsistent xs ys) :
    D.mass (fun a => ∀ k, eval a (xs k) = ys k) = 0 := by
  classical
  unfold Dist.mass Finsupp.sum
  apply Finset.sum_eq_zero
  intro a _ha
  dsimp
  rw [if_neg]
  intro hagree
  apply hcons
  intro i j hx
  calc
    ys i = eval a (xs i) := (hagree i).symm
    _ = eval a (xs j) := by rw [hx]
    _ = ys j := hagree j

/-- An inconsistent transcript also has zero mass after intersecting agreement with any side event.

UPSTREAM-CANDIDATE: side-condition form of `mass_tuple_agree_eq_zero_of_not_consistent`, used when the
seed must both agree with a transcript and satisfy a no-bad/injectivity event. -/
theorem mass_tuple_agree_and_event_eq_zero_of_not_consistent
    {A I O : Type*} {n : ℕ} (D : Dist A) (eval : A → I → O)
    (xs : Fin n → I) (ys : Fin n → O) (E : A → Prop) (hcons : ¬ tupleConsistent xs ys) :
    D.mass (fun a => (∀ k, eval a (xs k) = ys k) ∧ E a) = 0 := by
  classical
  unfold Dist.mass Finsupp.sum
  apply Finset.sum_eq_zero
  intro a _ha
  dsimp
  rw [if_neg]
  intro h
  apply hcons
  intro i j hx
  calc
    ys i = eval a (xs i) := (h.1 i).symm
    _ = eval a (xs j) := by rw [hx]
    _ = ys j := h.1 j

/-- The finite set of entries in a vector's list form is exactly the image of its index map.

UPSTREAM-CANDIDATE: exact vector/list finite-set bridge for transcript quotienting. -/
theorem vector_toList_toFinset_eq_image_get {X : Type*} [DecidableEq X] {n : ℕ}
    (xs : Vector X n) :
    xs.toList.toFinset = (Finset.univ : Finset (Fin n)).image (fun k => xs.get k) := by
  classical
  ext x
  rw [List.mem_toFinset]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
    rw [Finset.mem_image]
    refine ⟨⟨k.1, by simpa [Vector.length_toList] using k.2⟩, Finset.mem_univ _, ?_⟩
    rw [← hk]
    simp [Vector.get_eq_getElem, Vector.getElem_toList]
  · intro hx
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
    rw [List.mem_iff_get]
    refine ⟨⟨k.1, by simp [Vector.length_toList, k.2]⟩, ?_⟩
    simp [Vector.get_eq_getElem, Vector.getElem_toList]

/-- Transport a per-query transcript condition from list indexing to vector indexing.

UPSTREAM-CANDIDATE: vector/list index bridge for transcript quotienting. -/
theorem forall_toList_iff {I O : Type*} {i : ℕ} (xs : Vector I (i + 1)) (ys : Vector O (i + 1))
    (hbk : ∀ k : Fin ys.toList.length, k.1 < xs.toList.length) (F : I → O) :
    (∀ k : Fin ys.toList.length, F (xs.toList.get ⟨k.1, hbk k⟩) = ys.toList.get k) ↔
      ∀ k : Fin (i + 1), F (xs.get k) = ys.get k := by
  constructor
  · intro h k
    have hk : k.1 < ys.toList.length := by simpa using k.2
    have := h ⟨k.1, hk⟩
    simpa [List.get_eq_getElem, Vector.get_eq_getElem, Vector.getElem_toList] using this
  · intro h k
    have hk : k.1 < i + 1 := by simpa using k.2
    have := h ⟨k.1, hk⟩
    simpa [List.get_eq_getElem, Vector.get_eq_getElem, Vector.getElem_toList] using this

/-- **Last-query specialization** of `CondEquiv.massY_fTransform_historyEvaluator`: for a
seed-indexed family of last-query evaluators, the transcript law is agreement at the queried
points, indexed over the transcript vector.

UPSTREAM-CANDIDATE: transcript law for seed-indexed `functionEvaluator`-style systems. -/
theorem massY_fTransform_lastQuery {A I O : Type*} (D : Dist A) (F : A → I → O) {i : ℕ}
    (ys : Vector O (i + 1)) (xs : Vector I (i + 1)) :
    CondEquiv.massY (Dist.fTransform
        (fun a => PFunDDS.historyEvaluator fun l h => F a (l.getLast h)) D) i ys xs
      = D.mass fun a => ∀ k : Fin (i + 1), F a (xs.get k) = ys.get k := by
  have hbk : ∀ k : Fin ys.toList.length, k.1 < xs.toList.length := fun k => by simpa using k.2
  refine (CondEquiv.massY_fTransform_historyEvaluator D
    (fun a l h => F a (l.getLast h)) ys xs).trans ?_
  refine Dist.mass_congr _ fun a =>
    Iff.trans (forall_congr' fun k => ?_) (forall_toList_iff xs ys hbk (F a))
  rw [getLast_take_succ xs.toList k.1 (hbk k)]

/-- **Last-query specialization** of `CondEquiv.massYAfalse_fTransform_historyEvaluator`: the
joint "outputs match ∧ Aᵢ = 0" law of a last-query game with a per-seed monotone bit.

UPSTREAM-CANDIDATE: joint law for seed-indexed monitored `functionEvaluator`-style games. -/
theorem massYAfalse_fTransform_lastQuery {A I O : Type*} (D : Dist A) (F : A → I → O)
    (bit : A → List I → Bool)
    (hmono : ∀ a, ∀ {l₁ l₂ : List I}, l₁ <+: l₂ → bit a l₁ = true → bit a l₂ = true) {i : ℕ}
    (ys : Vector O (i + 1)) (xs : Vector I (i + 1)) :
    CondEquiv.massYAfalse (Dist.fTransform
        (fun a => PFunDDS.historyEvaluator fun l h => (F a (l.getLast h), bit a l)) D) i ys xs
      = D.mass fun a =>
          (∀ k : Fin (i + 1), F a (xs.get k) = ys.get k) ∧ bit a xs.toList = false := by
  have hbk : ∀ k : Fin ys.toList.length, k.1 < xs.toList.length := fun k => by simpa using k.2
  refine (CondEquiv.massYAfalse_fTransform_historyEvaluator D
    (fun a l h => F a (l.getLast h)) bit hmono ys xs).trans ?_
  refine Dist.mass_congr _ fun a => and_congr ?_ Iff.rfl
  refine Iff.trans (forall_congr' fun k => ?_) (forall_toList_iff xs ys hbk (F a))
  rw [getLast_take_succ xs.toList k.1 (hbk k)]

/-- The assignment induced by a consistent transcript on the finite set of actual queried inputs.
No default value is used: every element of the finite set carries a representative occurrence proof. -/
noncomputable def tupleAssignment {X : Type*} {n : ℕ} [DecidableEq X]
    (xs ys : Fin n → X) : ((Finset.univ : Finset (Fin n)).image xs) → X :=
  fun x => ys (Classical.choose (Finset.mem_image.mp x.2))

/-- The finite-set assignment agrees with any chosen transcript representative.

UPSTREAM-CANDIDATE: quotient-map API for repeated-input transcript counting. -/
theorem tupleAssignment_eq {X : Type*} [DecidableEq X] {n : ℕ}
    (xs ys : Fin n → X) (hcons : tupleConsistent xs ys)
    (x : ((Finset.univ : Finset (Fin n)).image xs))
    {i : Fin n} (hi : xs i = x.1) :
    tupleAssignment xs ys x = ys i := by
  classical
  dsimp [tupleAssignment]
  have hchoose := (Classical.choose_spec (Finset.mem_image.mp x.2)).2
  exact hcons (Classical.choose (Finset.mem_image.mp x.2)) i (hchoose.trans hi.symm)

/-- Tuple agreement is the same as agreeing with the induced finite-set assignment.

UPSTREAM-CANDIDATE: generic repeated-input transcript normalization for uniform-function fibers. -/
theorem tuple_agree_iff_assignment {X : Type*} [DecidableEq X] {n : ℕ}
    (xs ys : Fin n → X) (hcons : tupleConsistent xs ys) (f : X → X) :
    (∀ i, f (xs i) = ys i) ↔
      ∀ x : ((Finset.univ : Finset (Fin n)).image xs), f x.1 = tupleAssignment xs ys x := by
  classical
  constructor
  · intro hf x
    obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp x.2
    dsimp [tupleAssignment]
    have hchoose := (Classical.choose_spec (Finset.mem_image.mp x.2)).2
    calc
      f x.1 = f (xs i) := by rw [hix]
      _ = ys i := hf i
      _ = ys (Classical.choose (Finset.mem_image.mp x.2)) :=
          hcons i (Classical.choose (Finset.mem_image.mp x.2)) (hix.trans hchoose.symm)
  · intro hf i
    have hmem : xs i ∈ (Finset.univ : Finset (Fin n)).image xs :=
      Finset.mem_image_of_mem xs (Finset.mem_univ i)
    have hfi := hf ⟨xs i, hmem⟩
    dsimp [tupleAssignment] at hfi
    have hchoose := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    calc
      f (xs i) = ys (Classical.choose (Finset.mem_image.mp hmem)) := hfi
      _ = ys i := hcons (Classical.choose (Finset.mem_image.mp hmem)) i hchoose

/-- The transcript assignment targeted at a *given* finset `S` of the queried inputs (via `hS`), so
consumers avoid subtype transport along `univ.image xs = S`.  Heterogeneous (`I → O`) for VIL
constructions (e.g. the CBC-MAC's `M → X`).

UPSTREAM-CANDIDATE: quotient-map API for repeated-input transcript counting. -/
noncomputable def tupleAssignmentOn {I O : Type*} [DecidableEq I] {n : ℕ} {S : Finset I}
    (xs : Fin n → I) (ys : Fin n → O) (hS : Finset.univ.image xs = S) : ↥S → O :=
  fun s => ys (Classical.choose (Finset.mem_image.mp (show s.1 ∈ Finset.univ.image xs by
    rw [hS]; exact s.2)))

/-- Tuple agreement is agreement with the finset-targeted assignment. -/
theorem tuple_agree_iff_assignmentOn {I O : Type*} [DecidableEq I] {n : ℕ} {S : Finset I}
    (xs : Fin n → I) (ys : Fin n → O) (hS : Finset.univ.image xs = S)
    (hcons : tupleConsistent xs ys) (F : I → O) :
    (∀ k, F (xs k) = ys k) ↔ ∀ s : ↥S, F s.1 = tupleAssignmentOn xs ys hS s := by
  classical
  constructor
  · intro hf s
    have hs' : s.1 ∈ Finset.univ.image xs := by rw [hS]; exact s.2
    have hchoose := (Classical.choose_spec (Finset.mem_image.mp hs')).2
    show F s.1 = ys (Classical.choose (Finset.mem_image.mp hs'))
    exact (congrArg F hchoose.symm).trans (hf _)
  · intro hf i
    have hmem : xs i ∈ S := hS ▸ Finset.mem_image_of_mem xs (Finset.mem_univ i)
    have hmi : xs i ∈ Finset.univ.image xs := by rw [hS]; exact hmem
    have hchoose := (Classical.choose_spec (Finset.mem_image.mp hmi)).2
    rw [hf ⟨xs i, hmem⟩]
    show ys (Classical.choose (Finset.mem_image.mp hmi)) = ys i
    exact hcons _ i hchoose

/-- **The eq. (4.38) transcript-mass template.** A game `Ŝ` is conditionally equivalent to a total
probability system `T` once each transcript mass reads off as a seed-distribution mass — `Ŝ`'s over a
seed `F` with evaluator `out` and no-MBO event `E`, `T`'s over a seed `A` with evaluator `outT` — and,
per assignment `a` on the distinct queried inputs, the game's joint (agree ∧ no-MBO) mass factors as
`T`'s agree mass times the no-MBO normalizer.  The template supplies the rest of eq. (4.38) for free:
`T`'s normalizer is `1` by totality, repeated queries quotient to the distinct-input assignment
(`tuple_agree_iff_assignmentOn`), and inconsistent transcripts vanish on both sides.  (`[q]`-filtered
games, whose mass reductions hold only on kept histories, are out of scope — see `urf_urp_switching`.)

UPSTREAM-CANDIDATE: protocol-independent skeleton of a conditional-equivalence proof.
-/
theorem condEquiv_of_transcript_mass_reductions {In Out F A : Type*} [DecidableEq In]
    (Shat : PFunPDS In (Out × Bool)) (T : PFunPDS In Out)
    (D₁ : Dist F) (D₂ : Dist A) (out : F → In → Out) (outT : A → In → Out)
    (E : F → List In → Prop)
    (hAf : ∀ {xs : List In}, xs ≠ [] →
      CondEquiv.massAfalse Shat xs = D₁.mass fun f => E f xs)
    (hY : ∀ {i : ℕ} (ys : Vector Out (i + 1)) (xs : Vector In (i + 1)),
      CondEquiv.massY T i ys xs
        = D₂.mass fun g => ∀ k : Fin (i + 1), outT g (xs.get k) = ys.get k)
    (hYAf : ∀ {i : ℕ} (ys : Vector Out (i + 1)) (xs : Vector In (i + 1)),
      CondEquiv.massYAfalse Shat i ys xs
        = D₁.mass fun f => (∀ k : Fin (i + 1), out f (xs.get k) = ys.get k) ∧ E f xs.toList)
    (hprod : ∀ {i : ℕ} (xs : Vector In (i + 1)) (a : ↥xs.toList.toFinset → Out),
      D₁.mass (fun f => (∀ s : ↥xs.toList.toFinset, out f s.1 = a s) ∧ E f xs.toList)
        = D₂.mass (fun g => ∀ s : ↥xs.toList.toFinset, outT g s.1 = a s)
          * D₁.mass fun f => E f xs.toList)
    (hT : T.isProbDist := by cr18_standing)
    (hTot : CondEquiv.TotalOnNonempty T := by cr18_standing) :
    Shat |≡ T := by
  classical
  intro i xs ys hA hD
  have hne : xs.toList ≠ [] := by simp
  rw [CondEquiv.massDom_eq_one_of_totalOnNonempty T hT hTot hne, mul_one, hY ys xs, hAf hne,
    hYAf ys xs]
  by_cases hcons : tupleConsistent (fun k : Fin (i + 1) => xs.get k) (fun k => ys.get k)
  · -- consistent: quotient both agreement events to the distinct queried inputs, then factor
    have hS : Finset.univ.image (fun k : Fin (i + 1) => xs.get k) = xs.toList.toFinset :=
      (vector_toList_toFinset_eq_image_get xs).symm
    rw [Dist.mass_congr _ fun f => and_congr_left'
        (tuple_agree_iff_assignmentOn _ _ hS hcons (out f)),
      Dist.mass_congr _ fun g => tuple_agree_iff_assignmentOn _ _ hS hcons (outT g)]
    exact hprod xs (tupleAssignmentOn _ _ hS)
  · -- inconsistent: both sides vanish (the outputs are functions of the inputs)
    rw [mass_tuple_agree_and_event_eq_zero_of_not_consistent D₁ out _ _ _ hcons,
      mass_tuple_agree_eq_zero_of_not_consistent D₂ outT _ _ hcons, zero_mul]

/-- A no-collision transcript induces an injective finite-set assignment.

UPSTREAM-CANDIDATE: finite quotient bridge from transcript no-collision to an embedding. -/
theorem tupleAssignment_injective {X : Type*} [DecidableEq X] {n : ℕ}
    (xs ys : Fin n → X) (hcons : tupleConsistent xs ys)
    (hnc : tupleNoCollision xs ys) :
    Function.Injective (tupleAssignment xs ys) := by
  classical
  intro a b hab
  apply Subtype.ext
  obtain ⟨i, _hi, hia⟩ := Finset.mem_image.mp a.2
  obtain ⟨j, _hj, hjb⟩ := Finset.mem_image.mp b.2
  by_contra hne
  have hxsne : xs i ≠ xs j := by
    intro hxs
    exact hne (hia ▸ hxs ▸ hjb)
  have hysne := hnc i j hxsne
  have hai : tupleAssignment xs ys a = ys i := tupleAssignment_eq xs ys hcons a hia
  have hbj : tupleAssignment xs ys b = ys j := tupleAssignment_eq xs ys hcons b hjb
  exact hysne (hai.symm.trans (hab.trans hbj))

/-! ### The birthday bound on `pcoll`

**CR18 Lemma 4.18** `pcoll(t, q) ≤ ½ q²/t` (the PDF leaves it "as an exercise"),
and the two-sided form of Boneh–Shoup Theorem B.1 (`papers/BonehShoup.pdf`,
book p. 1101).

Everything here goes through one identity, `pcoll_eq_one_sub_descFactorial_div`:
`pcoll(t,q) = 1 - (t)_q/t^q`.  The tree used to carry two unrelated birthday
bounds — this probabilistic one, proved by a union bound over pairs, and the
falling-factorial arithmetic in `RandomSystems/Counting.lean`.  They are the
same fact, and the closed form is what says so; the arithmetic side is canonical
and everything below transports it.

Boneh–Shoup's Corollary B.2 (the i.i.d. **non-uniform** birthday bound at general
`k`) is *not* here.  Its proof needs "uniform maximizes `∑_{distinct tuples} ∏
p_{bⱼ}`", i.e. Maclaurin's inequality on elementary symmetric polynomials, which
mathlib does not carry.  Its `k = 2` case — the chance that two i.i.d. draws
agree is at least the uniform value `1/n` — is `Counting.inv_card_le_sum_sq`. -/

/-- `2 · #{(i,j) : i < j} ≤ q²` over `Fin q × Fin q`: the strict-upper and strict-lower triangles are
disjoint, equinumerous (swap), and together sit inside the `q²` cell grid. -/
theorem pair_card_le (q : ℕ) :
    2 * (Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2)).card ≤ q ^ 2 := by
  classical
  set P := Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2) with hP
  set P' := Finset.univ.filter (fun p : Fin q × Fin q => p.2 < p.1) with hP'
  have himg : P' = P.image (fun p => (p.2, p.1)) := by
    ext p
    simp only [hP, hP', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp; exact ⟨(p.2, p.1), hp, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ha
  have hcard : P'.card = P.card := by
    rw [himg, Finset.card_image_of_injective]
    intro a b hab
    simp only [Prod.ext_iff] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  have hdisj : Disjoint P P' := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [hP, hP', Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact absurd (hp.trans hp') (lt_irrefl _)
  have hle : P.card + P'.card ≤ q ^ 2 := by
    calc P.card + P'.card = (P ∪ P').card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin q × Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = q ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  omega

/-- **`pcoll` in closed form** — `pcoll(t,q) = 1 - (t)_q/t^q`.

`¬ Collides v` is exactly injectivity of the tuple, the injective tuples
`Fin q → Fin t` number `(t)_q = t.descFactorial q` (`Fintype.card_embedding_eq`),
and each carries iid-uniform mass `t^{-q}`.

This is the identity CR18 §4.11.3 appeals to when it identifies the optimal blind
collision game with `pcoll`, and it is the bridge to the falling-factorial
arithmetic of `RandomSystems/Counting.lean`, every statement of which is about
`1 - (N)_q/N^q`. -/
theorem pcoll_eq_one_sub_descFactorial_div (t q : ℕ) (h_pos : 0 < t) :
    pcoll t q = 1 - ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
  classical
  haveI : Nonempty (Fin t) := ⟨⟨0, h_pos⟩⟩
  set X := Dist.iidPow (Dist.uniform (Fin t)) q with hX
  have hconst : ∀ v : Fin q → Fin t, X v = (1 / (t : ℝ)) ^ q := by
    intro v
    rw [hX, Dist.iidPow_apply]
    have hu : ∀ i : Fin q, (Dist.uniform (Fin t)) (v i) = 1 / (t : ℝ) := by
      intro i; rw [Dist.uniform_apply, Fintype.card_fin]
    simp_rw [hu]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcompl : X.mass (fun v => ¬ Collides v)
      = ((t.descFactorial q : ℕ) : ℝ) / (t : ℝ) ^ q := by
    have hcong : X.mass (fun v : Fin q → Fin t => ¬ Collides v)
        = X.mass (fun v : Fin q → Fin t => Function.Injective v) := by
      refine Dist.mass_congr X fun v => ?_
      constructor
      · intro h i j hij
        by_contra hne
        exact h ⟨i, j, hne, hij⟩
      · rintro h ⟨i, j, hne, hv⟩
        exact hne (h hv)
    have hcard : (Finset.univ.filter (fun v : Fin q → Fin t => Function.Injective v)).card
        = t.descFactorial q := by
      rw [← Fintype.card_subtype,
        Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin q) (Fin t)),
        Fintype.card_embedding_eq]
      simp
    rw [hcong, Dist.mass_eq_sum]
    simp_rw [hconst]
    rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul, div_pow, one_pow,
      mul_one_div]
  have hsplit := Dist.mass_add_compl X Collides
  rw [(Dist.iidPow_isProbDist Dist.uniform_isProbDist q).weight_eq, hcompl] at hsplit
  rw [pcoll, dif_pos h_pos]
  linarith

/-- Beyond `t` draws a collision is certain: `pcoll(t,q) = 1` for `t < q`.
Pigeonhole, read off the closed form — `(t)_q = 0` once `q` exceeds `t`.
`0 < t` is needed because `pcoll 0 q` is `0` by convention, not `1`. -/
theorem pcoll_eq_one_of_lt {t q : ℕ} (h_pos : 0 < t) (h : t < q) : pcoll t q = 1 := by
  rw [pcoll_eq_one_sub_descFactorial_div t q h_pos,
    Nat.descFactorial_eq_zero_iff_lt.mpr h]
  simp

/-- **CR18 Lemma 4.18, sharp** — `pcoll(t,q) ≤ q(q-1)/(2t)`.

`Counting.birthday_bound` transported along `pcoll_eq_one_sub_descFactorial_div`.
The arithmetic form needs `q ≤ t`; this one does not, because past `q = t` the
right-hand side already exceeds `1`. -/
theorem pcoll_le_birthday_tight (t q : ℕ) (h_pos : 0 < t) :
    pcoll t q ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * t) := by
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr h_pos
  rcases le_or_gt q t with hqt | hqt
  · rw [pcoll_eq_one_sub_descFactorial_div t q h_pos,
      Counting.cast_descFactorial_eq_prod hqt]
    exact Counting.birthday_bound hqt h_pos
  · rw [pcoll_eq_one_of_lt h_pos hqt]
    have h1 : (t : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hqt
    have h2 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h_pos
    rw [le_div_iff₀ (by linarith)]
    nlinarith

/-- **CR18 Lemma 4.18** — `pcoll(t,q) ≤ ½ q²/t`, the rounded form the switching
lemma quotes.  `pcoll_le_birthday_tight` is sharper by `q(q-1)` versus `q²`. -/
theorem pcoll_le_birthday (t q : ℕ) (h_pos : 0 < t) :
    pcoll t q ≤ (q : ℝ) ^ 2 / (2 * t) := by
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr h_pos
  refine (pcoll_le_birthday_tight t q h_pos).trans ?_
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

/-- **Boneh–Shoup Theorem B.1(i)** on `pcoll` (`papers/BonehShoup.pdf` p. 1101):
`1 - e^{-q(q-1)/(2t)} ≤ pcoll(t,q)`.

The first collision *lower* bound in the tree.  An upper bound proves security;
this is the direction an attack argument needs. -/
theorem one_sub_exp_le_pcoll (t q : ℕ) (h_pos : 0 < t) :
    1 - Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * t))) ≤ pcoll t q := by
  rcases le_or_gt q t with hqt | hqt
  · rw [pcoll_eq_one_sub_descFactorial_div t q h_pos,
      Counting.cast_descFactorial_eq_prod hqt]
    exact Counting.one_sub_exp_le_one_sub_prod_sub_div_pow hqt h_pos
  · rw [pcoll_eq_one_of_lt h_pos hqt]
    linarith [Real.exp_pos (-((q : ℝ) * ((q : ℝ) - 1) / (2 * t)))]

/-- **Boneh–Shoup Theorem B.1(i)**, in the explicit form an attack argument
quotes: `min {q(q-1)/(4t), 0.63} ≤ pcoll(t,q)`. -/
theorem min_le_pcoll (t q : ℕ) (h_pos : 0 < t) :
    min ((q : ℝ) * ((q : ℝ) - 1) / (4 * t)) 0.63 ≤ pcoll t q := by
  rcases le_or_gt q t with hqt | hqt
  · rw [pcoll_eq_one_sub_descFactorial_div t q h_pos,
      Counting.cast_descFactorial_eq_prod hqt]
    exact Counting.min_le_one_sub_prod_sub_div_pow hqt h_pos
  · rw [pcoll_eq_one_of_lt h_pos hqt]
    exact le_trans (min_le_right _ _) (by norm_num)

/-- **Boneh–Shoup Theorem B.1(ii)** on `pcoll`: `pcoll(t,q) ≤ 1 - e^{-q(q-1)/t}`
when `2q ≤ t` (the paper's `q < t/2`).  The side condition is real: the termwise
step `e^{-2k/t} ≤ 1 - k/t` holds only while `2k ≤ t`. -/
theorem pcoll_le_one_sub_exp {t q : ℕ} (h : 2 * q ≤ t) (h_pos : 0 < t) :
    pcoll t q ≤ 1 - Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / t)) := by
  have hqt : q ≤ t := le_trans (by omega) h
  rw [pcoll_eq_one_sub_descFactorial_div t q h_pos,
    Counting.cast_descFactorial_eq_prod hqt]
  exact Counting.one_sub_prod_sub_div_pow_le_one_sub_exp h h_pos

/-- **Uniformity minimises the collision probability**, at two draws — the `k = 2`
case of Boneh–Shoup Corollary B.2 (`papers/BonehShoup.pdf` p. 1103): two i.i.d.
draws from *any* law on a finite alphabet agree with probability at least
`1/|A|`, which is the uniform value (`pcoll |A| 2 = 1/|A|`).

So non-uniformity only helps a collision-finding attacker, and the uniform
birthday bounds above are the attacker's worst case rather than a special case.
The general-`k` Corollary B.2 is not formalized; see the section note. -/
theorem inv_card_le_iidPow_two_mass_collides {A : Type*} [Fintype A]
    (X : Dist A) (hX : X.isProbDist) :
    1 / (Fintype.card A : ℝ) ≤ (Dist.iidPow X 2).mass Collides := by
  classical
  have hiff : ∀ v : Fin 2 → A, Collides v ↔ v 0 = v 1 := by
    intro v
    constructor
    · rintro ⟨i, j, hij, hv⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · intro h; exact ⟨0, 1, by decide, h⟩
  have hmass : (Dist.iidPow X 2).mass Collides = ∑ a, (X a) ^ 2 := by
    rw [Dist.mass_eq_sum]
    rw [Fintype.sum_equiv (piFinTwoEquiv (fun _ => A))
      (fun v => if Collides v then Dist.iidPow X 2 v else 0)
      (fun p => if p.1 = p.2 then X p.1 * X p.2 else 0) ?_]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [sq]
    · intro v
      dsimp only [piFinTwoEquiv, Equiv.coe_fn_mk]
      rw [Dist.iidPow_apply, Fin.prod_univ_two]
      by_cases h : v 0 = v 1
      · rw [if_pos ((hiff v).mpr h), if_pos h]
      · rw [if_neg (fun hc => h ((hiff v).mp hc)), if_neg h]
  rw [hmass]
  have hsum : ∑ a, X a = 1 := by
    rw [← Dist.weight_eq_sum]; exact hX.weight_eq
  simpa using Counting.inv_card_le_sum_sq (Finset.univ : Finset A) (fun a => X a) hsum

/-! ### Collision-game infrastructure for the switching lemma -/

/-- **CR18 Example 4.15 — input/output collision.** A transcript contains an output collision when
two distinct inputs in the visible `(input, output)` transcript have the same output. This is a `Prop`
version of Maurer's MBO condition, kept separate from the Boolean wrapper below.

UPSTREAM-CANDIDATE: this is the reusable collision predicate for transcript-defined MBOs. -/
def ioCollision {X Y : Type*} (t : List (X × Y)) : Prop :=
  ∃ p ∈ t, ∃ p' ∈ t, p.1 ≠ p'.1 ∧ p.2 = p'.2

/-- **CR18 Example 4.15 — collision MBO condition.** The Boolean MBO bit attached by `gameOf`: true
exactly when the visible input/output transcript has an output collision among distinct inputs.

UPSTREAM-CANDIDATE: canonical Boolean wrapper for the Example-4.15 collision MBO. -/
noncomputable def collisionCond {X Y : Type*} (t : List (X × Y)) : Bool := by
  classical
  exact decide (ioCollision (X := X) (Y := Y) t)

/-- `collisionCond` is monotone in transcript prefixes: once an input/output collision appears, later
transcript extensions preserve the same two witnesses.

UPSTREAM-CANDIDATE: the standing monotonicity fact for the Example-4.15 MBO. -/
theorem monotone_collisionCond {X Y : Type*} :
    PFunDDS.MonotoneCond (collisionCond (X := X) (Y := Y)) := by
  classical
  intro t₁ t₂ hpre
  rw [Bool.le_iff_imp]
  intro h
  simp only [collisionCond, decide_eq_true_eq] at h ⊢
  obtain ⟨p, hp, p', hp', hne, heq⟩ := h
  exact ⟨p, hpre.subset hp, p', hpre.subset hp', hne, heq⟩

/-- Collision among the outputs of a concrete function on a concrete input list: two list positions
with distinct inputs receive the same function value.

UPSTREAM-CANDIDATE: list-level bridge target for `ioTranscript` collision proofs. -/
def outputCollisionOn {X Y : Type*} (f : X → Y) (xs : List X) : Prop :=
  ∃ i j : Fin xs.length, i ≠ j ∧ xs.get i ≠ xs.get j ∧ f (xs.get i) = f (xs.get j)

/-- The tight no-collision event on a concrete input list is exactly injectivity on the list's finite
set of actual queried inputs.

UPSTREAM-CANDIDATE: list-to-finset event bridge for collision MBO normalizers. -/
theorem not_outputCollisionOn_iff_injOn_toFinset {X : Type*} [DecidableEq X]
    (f : X → X) (xs : List X) :
    ¬ outputCollisionOn f xs ↔ Set.InjOn f (fun x => x ∈ xs.toFinset) := by
  classical
  constructor
  · intro h a ha b hb hab
    change a ∈ xs.toFinset at ha
    change b ∈ xs.toFinset at hb
    rw [List.mem_toFinset] at ha hb
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
    by_contra hne
    apply h
    refine ⟨i, j, ?_, ?_, ?_⟩
    · intro hij
      apply hne
      rw [← hi, ← hj, hij]
    · intro hxs
      exact hne (hi.symm.trans (hxs.trans hj))
    · calc
        f (xs.get i) = f a := congrArg f hi
        _ = f b := hab
        _ = f (xs.get j) := (congrArg f hj).symm
  · intro h hc
    obtain ⟨i, j, _hij, hne, heq⟩ := hc
    exact hne (h (List.mem_toFinset.mpr (List.get_mem xs i))
      (List.mem_toFinset.mpr (List.get_mem xs j)) heq)

/-- The fixed `q`-round optional query schedule induced by a blind winner. A stopped round remains
`none`; we do not fill it with an artificial input.

UPSTREAM-CANDIDATE: exact optional vector form of the blind query schedule for filtered games. -/
def blindQueryVector {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) : Fin q → Option X :=
  fun i => w (List.replicate i.1 (none : Option Y))

/-- The exact collision event for a blind winner's actual issued queries against a function `f`. Both
witnessed rounds must be `some` queries. Stopped rounds (`none`) do not contribute, and no default input
is inserted. Repeated scheduled inputs do not count as a bad event; only distinct issued inputs with
equal function outputs do.

UPSTREAM-CANDIDATE: probability leaf event for the filtered switching bound. -/
def blindQueryCollision {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) (f : X → Y) : Prop :=
  ∃ i j : Fin q, i ≠ j ∧ ∃ xᵢ xⱼ : X,
    blindQueryVector w q i = some xᵢ ∧
    blindQueryVector w q j = some xⱼ ∧
    xᵢ ≠ xⱼ ∧ f xᵢ = f xⱼ

/-- The fixed issued-query list of a blind winner: the schedule's `some`-entries in round order. -/
def blindQueryList {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) : List X :=
  ((List.finRange q).map fun k => blindQueryVector w q k).reduceOption

theorem blindQueryList_length_le {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) :
    (blindQueryList w q).length ≤ q :=
  le_trans (List.reduceOption_length_le _) (by simp)

/-- Every schedule-consistent accepted query list is a prefix of the winner's fixed schedule list.
With a monotone MBO this moves any blind win to the single history `blindQueryList w q`.

UPSTREAM-CANDIDATE: schedule-list normalization for blind run-reductions. -/
theorem isPrefix_blindQueryList {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) (xs : List X)
    (hlen : xs.length ≤ q)
    (hsched : ∀ k : Fin xs.length,
      blindQueryVector w q ⟨k.1, lt_of_lt_of_le k.2 hlen⟩ = some (xs.get k)) :
    xs <+: blindQueryList w q := by
  classical
  have htake : ((List.finRange q).map fun k => blindQueryVector w q k).take xs.length
      = xs.map some := by
    apply List.ext_getElem
    · simp [hlen]
    · intro n h1 h2
      have hn : n < xs.length := by simpa using h2
      have := hsched ⟨n, hn⟩
      simp only [List.getElem_take, List.getElem_map, List.getElem_finRange]
      simpa [List.get_eq_getElem] using this
  have hmapsome : (xs.map some).reduceOption = xs := by
    simp [List.reduceOption, List.filterMap_map]
  refine ⟨(((List.finRange q).map fun k => blindQueryVector w q k).drop xs.length).reduceOption, ?_⟩
  unfold blindQueryList
  conv_rhs => rw [← List.take_append_drop xs.length ((List.finRange q).map _)]
  rw [List.reduceOption_append, htake, hmapsome]

/-- The strict unordered query-pair index set used by the birthday union bound.

UPSTREAM-CANDIDATE: canonical query-pair set for birthday-style arguments. -/
def queryPairSet (q : ℕ) : Finset (Fin q × Fin q) :=
  Finset.univ.filter (fun p : Fin q × Fin q => p.1 < p.2)

/-- The standard pair-count/cardinality collision union-bound scalar. -/
noncomputable def pairCollisionUnionBound (X : Type*) [Fintype X] (q : ℕ) : NNReal :=
  ((queryPairSet q).card : NNReal) / (Fintype.card X : NNReal)

/-- **Birthday union bound, packaged as a descriptor-cover principle**: if a bad event on a
distribution `D` is covered by a family `E` on any finite descriptor set `P` that embeds into the
strict query pairs, each leaf of mass `≤ 1/|X|`, then `D`'s bad mass is at most the pair-union bound.
Protocol events stay in their native coordinates; the code arithmetic is confined to the embedding.

UPSTREAM-CANDIDATE: reusable birthday-cover combinator for blind collision games. -/
theorem mass_le_pairCollisionUnionBound_of_cover_injOn {A : Type*} [Fintype A] [Nonempty A]
    (X : Type*) [Fintype X] (D : Dist A) (hD : D.NonNeg)
    (n : ℕ) {ι : Type*} (P : Finset ι)
    (E : ι → A → Prop) (Bad : A → Prop) (enc : ι → Fin n × Fin n)
    (hcover : ∀ a, Bad a → ∃ p ∈ P, E p a)
    (hleaf : ∀ p ∈ P, D.mass (E p) ≤ 1 / (Fintype.card X : ℝ))
    (hmem : ∀ p ∈ P, enc p ∈ queryPairSet n) (henc : Set.InjOn enc ↑P) :
    D.mass Bad ≤ pairCollisionUnionBound X n := by
  classical
  calc D.mass Bad
      ≤ D.mass (fun a => ∃ p ∈ P, E p a) := mass_mono hD hcover
    _ ≤ ∑ p ∈ P, D.mass (E p) := mass_biUnion_le D hD P E
    _ ≤ ∑ _p ∈ P, 1 / (Fintype.card X : ℝ) := Finset.sum_le_sum hleaf
    _ = (P.card : ℝ) * (1 / (Fintype.card X : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((queryPairSet n).card : ℝ) * (1 / (Fintype.card X : ℝ)) := by
        gcongr
        exact_mod_cast Finset.card_le_card_of_injOn enc hmem henc
    _ = (pairCollisionUnionBound X n : ℝ) := by
      simp only [pairCollisionUnionBound, NNReal.coe_div, NNReal.coe_natCast]
      rw [one_div]
      exact (div_eq_mul_inv _ _).symm

/-- The cover principle at the trivial descriptor set — the strict query pairs themselves. -/
theorem mass_le_pairCollisionUnionBound_of_cover {A : Type*} [Fintype A] [Nonempty A]
    (X : Type*) [Fintype X] (D : Dist A) (hD : D.NonNeg)
    (n : ℕ) (E : Fin n × Fin n → A → Prop) (Bad : A → Prop)
    (hcover : ∀ a, Bad a → ∃ p ∈ queryPairSet n, E p a)
    (hleaf : ∀ p ∈ queryPairSet n, D.mass (E p) ≤ 1 / (Fintype.card X : ℝ)) :
    D.mass Bad ≤ pairCollisionUnionBound X n :=
  mass_le_pairCollisionUnionBound_of_cover_injOn X D hD n
    (queryPairSet n) E Bad id hcover hleaf
    (fun _ hp => hp) Function.injective_id.injOn

/-- For a total function evaluator under the `[q]` filter, the fully-defined completion keeps exactly
the first `q` raw queries. The `gameOfDDS` wrapper does not change the domain, so this follows from the
generic domain-level `[q]` fact above.

UPSTREAM-CANDIDATE: specialization of the generic `[q]`/`fullyDefined` API lemma. -/
theorem keptPrefix_gameOfDDS_filterQueries_functionEvaluator
    {X Y : Type*} (cond : List (X × Y) → Bool) (q : ℕ) (f : X → Y) (l : List X) :
    PFunDDS.keptPrefix
      (PFunDDS.gameOfDDS cond (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) l
      = l.take q := by
  cr18_filter

/-- A nonempty prefix of the `[q]`-filtered function evaluator returns `f` applied to the last input
in that prefix. Stated for `l.take (k+1)`, the prefixes used by `ioTranscript`.

UPSTREAM-CANDIDATE: output-normalization API for `[q]` over `functionEvaluator`. -/
theorem PFunDDS.output_filterQueries_functionEvaluator_take_succ
    {X Y : Type*} (q : ℕ) (f : X → Y) (l : List X) (k : Fin l.length)
    (htake : l.take (k.1 + 1) ∈ PFunDDS.dom
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) :
    PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
      (l.take (k.1 + 1)) htake = f (l.get k) := by
  rw [PFunDDS.output_filterQueries]
  have hseq : l.take (k.1 + 1) = l.take k.1 ++ [l.get k] :=
    take_succ_get' l k.1 k.2
  have hdom : l.take k.1 ++ [l.get k] ∈ PFunDDS.dom (PFunDDS.functionEvaluator f) := by
    have hlne : l ≠ [] := by
      intro hl
      have hk := k.2
      simp [hl] at hk
    rw [PFunDDS.dom_functionEvaluator]
    change l.take k.1 ++ [l.get k] ≠ []
    simp [hlne]
  calc
    PFunDDS.output (PFunDDS.functionEvaluator f) (l.take (k.1 + 1)) htake.1
        = PFunDDS.output (PFunDDS.functionEvaluator f) (l.take k.1 ++ [l.get k]) hdom := by
            exact PFunDDS.output_congr (PFunDDS.functionEvaluator f) hseq htake.1 hdom
    _ = f (l.get k) := by
            exact PFunDDS.functionEvaluator_output f (l.take k.1) (l.get k) hdom

/-- The input/output transcript of `[q]` over a function evaluator is the pointwise graph of `f` on
the accepted input list.

UPSTREAM-CANDIDATE: transcript-normalization API for `[q]` over `functionEvaluator`. -/
theorem PFunDDS.ioTranscript_filterQueries_functionEvaluator_eq
    {X Y : Type*} (q : ℕ) (f : X → Y) (l : List X)
    (h : l ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) :
    PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) l h
      = List.ofFn (fun k : Fin l.length => (l.get k, f (l.get k))) := by
  rw [List.ext_get_iff]
  constructor
  · simp [PFunDDS.ioTranscript]
  · intro n hn hn'
    simp only [PFunDDS.ioTranscript, List.get_ofFn]
    have hnl : n < l.length := by simpa using hn'
    have htake : l.take (n + 1) ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := by
      exact PFunDDS.prefix_closed (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
        (List.take_prefix (n + 1) l)
        (by rw [← List.length_pos_iff_ne_nil, List.length_take]; omega) h
    refine Prod.ext ?_ ?_
    · rfl
    · exact PFunDDS.output_filterQueries_functionEvaluator_take_succ q f l ⟨n, hnl⟩ htake

/-- The generic `ioTranscript` collision condition for the filtered function evaluator is exactly the
list-level collision event on the accepted input history.

UPSTREAM-CANDIDATE: bridge from transcript-defined MBOs to function-output collision events. -/
theorem ioCollision_ioTranscript_filterQueries_functionEvaluator_iff
    {X Y : Type*} (q : ℕ) (f : X → Y) (l : List X)
    (h : l ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) :
    ioCollision (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) l h)
      ↔ outputCollisionOn f l := by
  classical
  rw [PFunDDS.ioTranscript_filterQueries_functionEvaluator_eq]
  constructor
  · intro hc
    obtain ⟨p, hp, p', hp', hne, heq⟩ := hc
    rw [List.mem_ofFn] at hp hp'
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, rfl⟩ := hp'
    refine ⟨i, j, ?_, ?_, heq⟩
    · intro hij
      subst j
      exact hne rfl
    · exact hne
  · intro hc
    obtain ⟨i, j, hij, hne, heq⟩ := hc
    refine ⟨(l.get i, f (l.get i)), ?_, (l.get j, f (l.get j)), ?_, hne, heq⟩
    · rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · rw [List.mem_ofFn]
      exact ⟨j, rfl⟩

namespace PFunDDS

/-- A positive output in an interaction with an arbitrary game comes from one
actual in-domain query history whose output bit is true.  This is the generic
run-extraction fact; constructions such as `gameOfDDS` only have to identify
what that bit means on the extracted history. -/
theorem true_output_mem_exists_query_output_true {X Y : Type*}
    (S : DDS X (Y × Bool)) (w : Winner X Y) (n : ℕ) (y : Y)
    (hmem : (some (y, true) : Option (Y × Bool)) ∈
      transcriptOutputs (transcript S (winnerView w) n)) :
    ∃ m : ℕ, ∃ x : X,
      winnerView w (transcript S (winnerView w) m)↓ᵧ = some x ∧
      let xs := keptPrefix S
          (transcript S (winnerView w) m)↓ₓ ++ [x]
      ∃ hxs : xs ∈ dom S, (output S xs hxs).2 = true := by
  induction n with
  | zero =>
      simp [transcriptOutputs, transcript] at hmem
  | succ n ih =>
      by_cases hnone :
          winnerView w (transcript S (winnerView w) n)↓ᵧ = none
      · rw [transcript_succ_stall hnone] at hmem
        exact ih hmem
      · rcases hval :
          winnerView w (transcript S (winnerView w) n)↓ᵧ with _ | x
        · exact False.elim (hnone hval)
        · rw [transcript_succ_fire hval] at hmem
          simp only [transcriptOutputs_append, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hprev | hlast
          · exact ih hprev
          · let t := transcript S (winnerView w) n
            let xs := keptPrefix S t↓ₓ ++ [x]
            rw [output_fullyDefined] at hlast
            have hdrop : (t↓ₓ ++ [x]).dropLast = t↓ₓ := by simp
            have hlastx : (t↓ₓ ++ [x]).getLast (by simp) = x := by simp
            rw [hdrop, hlastx] at hlast
            dsimp only [xs] at hlast
            split at hlast
            · rename_i hxs
              have hout : output S xs hxs = (y, true) :=
                (Option.some.inj hlast).symm
              exact ⟨n, x, hval, hxs, congrArg Prod.snd hout⟩
            · simp at hlast

/-- Every concrete input that appears in a generic transcript is exactly the environment query issued
after the preceding output prefix.

UPSTREAM-CANDIDATE: index-level transcript/environment alignment for Def 3.7. -/
theorem transcript_input_get?_eq_env {X Y : Type*} (s : DDS X Y) (e : DDE X Y) (n k : ℕ)
    {x : X} (hget : ((transcript s e n)↓ₓ)[k]? = some x) :
    e ((transcript s e n).take k)↓ᵧ = some x := by
  induction n generalizing k with
  | zero =>
      simp at hget
  | succ n ih =>
      by_cases hnone : e (transcript s e n)↓ᵧ = none
      · rw [transcript_succ_stall hnone] at hget ⊢
        exact ih k hget
      · rcases hval : e (transcript s e n)↓ᵧ with _ | x'
        · exact False.elim (hnone hval)
        · rw [transcript_succ_fire hval] at hget ⊢
          by_cases hk : k < (transcript s e n).length
          · have hget' : ((transcript s e n)↓ₓ)[k]? = some x := by
              rw [transcriptInputs_append] at hget
              rw [List.getElem?_append_left (by simpa [transcriptInputs_length] using hk)] at hget
              exact hget
            have htake :
                (transcript s e n ++
                      [(x', output (s⊥) ((transcript s e n)↓ₓ ++ [x'])
                        (by simp [fullyDefined, dom]))]).take k =
                  (transcript s e n).take k := by
              rw [List.take_append_of_le_length]
              exact hk.le
            rw [htake]
            exact ih k hget'
          · have hk' : k = (transcript s e n).length := by
              have hlen : k < (transcript s e n).length + 1 := by
                obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hget
                simpa [transcriptInputs_append, transcriptInputs_length] using hbound
              omega
            subst hk'
            have hx_eq : x' = x := by
              simpa [transcriptInputs_append, transcriptInputs_length] using hget
            simpa [hx_eq] using hval

/-- If a true MBO output appears in a `gameOfDDS cond S` run, it was produced by an accepted base
history whose `ioTranscript` satisfies `cond`.

The witness keeps the exact raw prefix and issued query that produced the true bit, so consumers can
relate the accepted history back to the environment schedule without re-opening the transcript
recursion.

UPSTREAM-CANDIDATE: positive-output extraction for constructed MBO games. -/
theorem true_output_mem_gameOfDDS_exists_query_cond_true {X Y : Type*}
    (cond : List (X × Y) → Bool) (S : DDS X Y) (w : Winner X Y) (n : ℕ) (y : Y)
    (hmem : (some (y, true) : Option (Y × Bool)) ∈
      transcriptOutputs (transcript (gameOfDDS cond S) (winnerView w) n)) :
    ∃ m : ℕ, ∃ x : X,
      winnerView w (transcript (gameOfDDS cond S) (winnerView w) m)↓ᵧ = some x ∧
      let xs := keptPrefix (gameOfDDS cond S)
          (transcript (gameOfDDS cond S) (winnerView w) m)↓ₓ ++ [x]
      ∃ hxs : xs ∈ dom S, cond (ioTranscript S xs hxs) = true := by
  induction n with
  | zero =>
      simp [transcriptOutputs, transcript] at hmem
  | succ n ih =>
      by_cases hnone : winnerView w (transcript (gameOfDDS cond S) (winnerView w) n)↓ᵧ = none
      · rw [transcript_succ_stall hnone] at hmem
        exact ih hmem
      · rcases hval : winnerView w (transcript (gameOfDDS cond S) (winnerView w) n)↓ᵧ with _ | x
        · exact False.elim (hnone hval)
        · rw [transcript_succ_fire hval] at hmem
          simp only [transcriptOutputs_append, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hprev | hlast
          · exact ih hprev
          · let t := transcript (gameOfDDS cond S) (winnerView w) n
            let xs := keptPrefix (gameOfDDS cond S) t↓ₓ ++ [x]
            rw [output_fullyDefined] at hlast
            have hdrop : (t↓ₓ ++ [x]).dropLast = t↓ₓ := by simp
            have hlastx : (t↓ₓ ++ [x]).getLast (by simp) = x := by simp
            rw [hdrop, hlastx] at hlast
            dsimp only [xs] at hlast
            split at hlast
            · rename_i hcand
              have hS : xs ∈ dom S := by
                exact hcand
              have hpair : output (gameOfDDS cond S) xs hcand = (y, true) := by
                exact (Option.some.inj hlast).symm
              refine ⟨n, x, hval, hS, ?_⟩
              have hbit : (output (gameOfDDS cond S) xs hcand).2 = true := by
                simp [hpair]
              simpa [outputBit_gameOfDDS cond S xs hcand hS] using hbit
            · simp at hlast

end PFunDDS

/-- **Generic positive-run extraction** for a blind winner against *any* transcript-MBO game over the
`[q]`-filtered function evaluator: a win yields an accepted, schedule-consistent query list whose
`ioTranscript` satisfies `cond`.  The collision consequence below and the CBC-MAC birthday bound
(`RandomSystems.CBCMAC`) both consume this single run-reduction.

UPSTREAM-CANDIDATE: operational run-reduction for `Γ(b[q]·)` over constructed MBO games. -/
theorem winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list
    {X Y : Type*} (cond : List (X × Y) → Bool) (w : PFunDDS.Winner X Y) (q : ℕ)
    (hblind : IsBlind w) (f : X → Y)
    (hwin : winsDDS w
      (PFunDDS.gameOfDDS cond (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))) :
    ∃ (xs : List X) (hlen : xs.length ≤ q),
      (∀ k : Fin xs.length,
        blindQueryVector w q ⟨k.1, lt_of_lt_of_le k.2 hlen⟩ = some (xs.get k)) ∧
      ∃ hdom : xs ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)),
        cond (PFunDDS.ioTranscript
          (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hdom) = true := by
  classical
  let G := PFunDDS.gameOfDDS cond
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
  obtain ⟨n, y, hmem⟩ := hwin
  obtain ⟨m, x, hquery, hdom, hcond⟩ :=
    PFunDDS.true_output_mem_gameOfDDS_exists_query_cond_true
      cond (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) w n y hmem
  let t := PFunDDS.transcript G (PFunDDS.winnerView w) m
  let raw := PFunDDS.transcriptInputs t
  let xs := PFunDDS.keptPrefix G raw ++ [x]
  change xs ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) at hdom
  change
    cond (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hdom) =
      true at hcond
  have hxs_take : xs = raw.take q ++ [x] := by
    dsimp [xs, raw, G]
    rw [keptPrefix_gameOfDDS_filterQueries_functionEvaluator]
  have hlen_le_q : xs.length ≤ q := hdom.2
  have hraw_lt_q : raw.length < q := by
    have htake_len : (raw.take q).length + 1 ≤ q := by
      simpa [hxs_take] using hlen_le_q
    have htake_lt : (raw.take q).length < q := by omega
    rw [List.length_take] at htake_lt
    omega
  have hxs_raw : xs = raw ++ [x] := by
    rw [hxs_take, List.take_of_length_le hraw_lt_q.le]
  have hblindAt : ∀ k : Fin xs.length,
      blindQueryVector w q ⟨k.1, lt_of_lt_of_le k.2 hlen_le_q⟩ = some (xs.get k) := by
    intro k
    by_cases hkraw : k.1 < raw.length
    · have hgetRaw : raw[k.1]? = some (xs.get k) := by
        have hxs_get : xs.get k = (raw ++ [x]).get ⟨k.1, by simpa [hxs_raw] using k.2⟩ := by
          exact List.get_of_eq hxs_raw k
        rw [List.getElem?_eq_getElem hkraw]
        rw [hxs_get, List.get_eq_getElem, List.getElem_append_left hkraw]
      have hactual :=
        PFunDDS.transcript_input_get?_eq_env G (PFunDDS.winnerView w) m k.1 hgetRaw
      have hactualY :
          w ((PFunDDS.transcriptOutputs (t.take k.1)).map (Option.map Prod.fst)) =
            some (xs.get k) := by
        simpa [PFunDDS.winnerView, t, G] using hactual
      have hk_t : k.1 ≤ t.length := by
        have := hkraw.le
        simpa [raw, transcriptInputs_length] using this
      have hlen_view : ((PFunDDS.transcriptOutputs (t.take k.1)).map (Option.map Prod.fst)).length =
          (List.replicate k.1 (none : Option Y)).length := by
        simp [transcriptOutputs_length, List.length_take, Nat.min_eq_left hk_t]
      unfold blindQueryVector
      change w (List.replicate k.1 (none : Option Y)) = some (xs.get k)
      rw [← hblind ((PFunDDS.transcriptOutputs (t.take k.1)).map (Option.map Prod.fst))
        (List.replicate k.1 (none : Option Y)) hlen_view]
      exact hactualY
    · have hk_eq : k.1 = raw.length := by
        have hk_len : k.1 < raw.length + 1 := by
          simpa [hxs_raw] using k.2
        omega
      have hxget : xs.get k = x := by
        have hxs_get : xs.get k = (raw ++ [x]).get ⟨k.1, by simpa [hxs_raw] using k.2⟩ := by
          exact List.get_of_eq hxs_raw k
        rw [hxs_get, List.get_eq_getElem]
        rw [List.getElem_append_right (by rw [hk_eq])]
        have hsub : k.1 - raw.length = 0 := by omega
        simp [hsub]
      have hqueryY : w ((PFunDDS.transcriptOutputs t).map (Option.map Prod.fst)) = some x := by
        simpa [PFunDDS.winnerView, t, G] using hquery
      have hlen_view : ((PFunDDS.transcriptOutputs t).map (Option.map Prod.fst)).length =
          (List.replicate k.1 (none : Option Y)).length := by
        simp [transcriptOutputs_length, raw, transcriptInputs_length, hk_eq]
      unfold blindQueryVector
      change w (List.replicate k.1 (none : Option Y)) = some (xs.get k)
      rw [hxget]
      rw [← hblind ((PFunDDS.transcriptOutputs t).map (Option.map Prod.fst))
        (List.replicate k.1 (none : Option Y)) hlen_view]
      exact hqueryY
  exact ⟨xs, hlen_le_q, hblindAt, hdom, hcond⟩

/-- If a blind winner wins the collision MBO game built from the `[q]`-filtered function evaluator,
then the function has a collision on the winner's fixed `q`-round blind query schedule.  Consumer of
the generic schedule-list extraction plus the `ioTranscript`/function-output collision bridge.

UPSTREAM-CANDIDATE: operational run-reduction for `Γ(b[q]R̂)`. -/
theorem winsDDS_gameOfDDS_filterQueries_functionEvaluator_imp_blindQueryCollision
    {X Y : Type*} (w : PFunDDS.Winner X Y) (q : ℕ) (hblind : IsBlind w) (f : X → Y) :
    winsDDS w
        (PFunDDS.gameOfDDS (collisionCond (X := X) (Y := Y))
          (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))) →
      blindQueryCollision w q f := by
  classical
  intro hwin
  obtain ⟨xs, hlen, hsched, hdom, hcond⟩ :=
    winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list
      (collisionCond (X := X) (Y := Y)) w q hblind f hwin
  have hxsColl : outputCollisionOn f xs :=
    (ioCollision_ioTranscript_filterQueries_functionEvaluator_iff q f xs hdom).mp
      (by simpa [collisionCond] using hcond)
  obtain ⟨i, j, hij, hne, heq⟩ := hxsColl
  refine ⟨⟨i.1, lt_of_lt_of_le i.2 hlen⟩, ⟨j.1, lt_of_lt_of_le j.2 hlen⟩, ?_,
    xs.get i, xs.get j, hsched i, hsched j, hne, heq⟩
  intro hijq
  apply hij
  apply Fin.ext
  simpa using congrArg (fun z : Fin q => z.1) hijq

/-- A uniform random function collides on an arbitrary fixed blind schedule with probability at most
the birthday pair-union bound. Repeated scheduled inputs are excluded from the event, stopped rounds
are absent, and only issued distinct inputs are counted.

UPSTREAM-CANDIDATE: reusable collision marginal for arbitrary non-adaptive optional schedules. The
`[DecidableEq X]` instance is Lean infrastructure for finite filtering and uniform distributions, not
an extra paper assumption. -/
theorem uniform_mass_blindQueryCollision_le_pairCollisionUnionBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (w : PFunDDS.Winner X X) (q : ℕ) :
    (Dist.uniform (X → X)).mass (fun f => blindQueryCollision w q f)
      ≤ pairCollisionUnionBound X q := by
  classical
  set P : Finset (Fin q × Fin q) := queryPairSet q with hP
  let E : Fin q × Fin q → (X → X) → Prop := fun p f =>
    ∃ xᵢ xⱼ : X,
      blindQueryVector w q p.1 = some xᵢ ∧
      blindQueryVector w q p.2 = some xⱼ ∧
      xᵢ ≠ xⱼ ∧ f xᵢ = f xⱼ
  have htoUnion : ∀ f, blindQueryCollision w q f → ∃ p ∈ P, E p f := by
    intro f hf
    obtain ⟨i, j, hij, xᵢ, xⱼ, hi, hj, hne, heq⟩ := hf
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine ⟨(i, j), ?_, xᵢ, xⱼ, hi, hj, hne, heq⟩
      simp [hP, queryPairSet, hlt]
    · refine ⟨(j, i), ?_, xⱼ, xᵢ, hj, hi, hne.symm, heq.symm⟩
      simp [hP, queryPairSet, hgt]
  calc
    (Dist.uniform (X → X)).mass (fun f => blindQueryCollision w q f)
        ≤ (Dist.uniform (X → X)).mass (fun f => ∃ p ∈ P, E p f) :=
          mass_mono Dist.uniform_nonNeg htoUnion
    _ ≤ ∑ p ∈ P, (Dist.uniform (X → X)).mass (E p) :=
          mass_biUnion_le (Dist.uniform (X → X)) Dist.uniform_nonNeg P E
    _ ≤ ∑ _p ∈ P, (1 / (Fintype.card X : ℝ)) := by
          refine Finset.sum_le_sum fun p _hp => ?_
          by_cases hpair : ∃ xᵢ xⱼ : X,
              blindQueryVector w q p.1 = some xᵢ ∧
              blindQueryVector w q p.2 = some xⱼ ∧ xᵢ ≠ xⱼ
          · obtain ⟨xᵢ, xⱼ, hi, hj, hne⟩ := hpair
            have hmono : ∀ f, E p f → f xᵢ = f xⱼ := by
              intro f hf
              obtain ⟨a, b, ha, hb, _hab, heq⟩ := hf
              have hai : a = xᵢ := Option.some.inj (ha.symm.trans hi)
              have hbj : b = xⱼ := Option.some.inj (hb.symm.trans hj)
              simpa [hai, hbj] using heq
            exact (mass_mono Dist.uniform_nonNeg hmono).trans_eq
              (uniform_function_pair_eq_mass (X := X) hne)
          · have hnone : ∀ f, ¬ E p f := by
              intro f hf
              obtain ⟨xᵢ, xⱼ, hi, hj, hne, _heq⟩ := hf
              exact hpair ⟨xᵢ, xⱼ, hi, hj, hne⟩
            have hzero : (Dist.uniform (X → X)).mass (E p) = 0 := by
              rw [Dist.mass_eq_sum]
              simp [hnone]
            rw [hzero]
            exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    _ = (P.card : ℝ) / (Fintype.card X : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ = (pairCollisionUnionBound X q : ℝ) := by
          simp [pairCollisionUnionBound, hP]

/-- Per-blind-winner filtered collision bound. This is the small assembled leaf used by the supremum
argument: winning the constructed filtered collision game implies the fixed-schedule collision event,
whose uniform-function mass is bounded by the pair-union birthday expression.

UPSTREAM-CANDIDATE: per-winner form of the `Γ(b[q]R̂)` birthday-bound step. -/
theorem blind_winner_filtered_collision_mass_le_pairCollisionUnionBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (w : PFunDDS.Winner X X) (q : ℕ) (hblind : IsBlind w) :
    (Dist.uniform (X → X)).mass
        (fun f => winsDDS w
          (PFunDDS.gameOfDDS (collisionCond (X := X) (Y := X))
            (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))))
      ≤ pairCollisionUnionBound X q := by
  classical
  calc
    (Dist.uniform (X → X)).mass
        (fun f => winsDDS w
          (PFunDDS.gameOfDDS (collisionCond (X := X) (Y := X))
            (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))))
        ≤ (Dist.uniform (X → X)).mass (fun f => blindQueryCollision w q f) := by
          exact mass_mono Dist.uniform_nonNeg fun f hf =>
            winsDDS_gameOfDDS_filterQueries_functionEvaluator_imp_blindQueryCollision
              w q hblind f hf
    _ ≤ pairCollisionUnionBound X q :=
          uniform_mass_blindQueryCollision_le_pairCollisionUnionBound w q

/-- `𝖱 X` — the uniform random function oThen `X` (`URF X X`); Maurer's URF `R` (§4.11.3). -/
scoped notation:max "𝖱 " X:max => PFunPDS.URF (X := X) (Y := X)
/-- `𝖯 X` — the uniform random permutation on `X` (`URP X`); Maurer's URP `P`. -/
scoped notation:max "𝖯 " X:max => PFunPDS.URP X

/-- The filtered blind collision game for the URF is bounded by the birthday pair-union expression.
The statement keeps the base object in the protocol statement and constructs the complex object there:
`gameOf (⌈q⌉ 𝖱 X) collisionCond`.

UPSTREAM-CANDIDATE: supremum-level `Γ(b[q]R̂)` birthday-bound bridge for Lemma 4.19. -/
theorem blindMaxWinProb_filterURF_collisionCond_le_pairCollisionUnionBound
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    (Γᵇ (gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))) : ℝ)
      ≤ (pairCollisionUnionBound X q : ℝ) := by
  unfold gameOf PFunPDS.filterQueries PFunPDS.URF PFunPDS.ofFunDist
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  exact blindMaxWinProb_fTransform_le _ _ _ fun w hblind =>
    blind_winner_filtered_collision_mass_le_pairCollisionUnionBound w q hblind

/-- The domain normalizer for `[q]URP` is `1` on any nonempty history of length at most `q`.

UPSTREAM-CANDIDATE: concrete `[q]`/URP `massDom` normalizer for conditional-equivalence proofs. -/
theorem massDom_filterURP_eq_one_of_length_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (q : ℕ) {xs : List X} (hne : xs ≠ []) (hlen : xs.length ≤ q) :
    CondEquiv.massDom (⌈q⌉ 𝖯 X) xs = 1 := by
  classical
  unfold CondEquiv.massDom PFunPDS.filterQueries PFunPDS.URP PFunPDS.ofPermDist
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  rw [show (fun a : Equiv.Perm X => xs ∈ PFunDDS.dom
        (PFunDDS.filterQueries q (PFunDDS.functionEvaluator a.toFun))) = (fun _ => True) from by
    funext σ
    rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator]
    simp [hne, hlen]]
  rw [Dist.mass_true]
  convert Dist.weight_uniform using 2

/-- The domain normalizer for `[q]URP` is `0` once the queried history exceeds the filter budget.

UPSTREAM-CANDIDATE: concrete `[q]`/URP `massDom` zero normalizer for conditional-equivalence proofs. -/
theorem massDom_filterURP_eq_zero_of_length_gt
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (q : ℕ) {xs : List X} (hlen : q < xs.length) :
    CondEquiv.massDom (⌈q⌉ 𝖯 X) xs = 0 := by
  classical
  unfold CondEquiv.massDom PFunPDS.filterQueries PFunPDS.URP PFunPDS.ofPermDist
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  rw [show (fun a : Equiv.Perm X => xs ∈ PFunDDS.dom
        (PFunDDS.filterQueries q (PFunDDS.functionEvaluator a.toFun))) = (fun _ => False) from by
    funext σ
    apply propext
    constructor
    · intro hσ
      rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator] at hσ
      exact (not_le_of_gt hlen) hσ.2
    · intro hfalse
      exact False.elim hfalse]
  rw [Dist.mass]
  simp

/-- The not-yet-won normalizer of the filtered URF collision game is the tight no-collision event on
the actual queried input set.

UPSTREAM-CANDIDATE: concrete `massAfalse` normalizer for Example-4.15 conditional equivalence. -/
theorem massAfalse_filterURF_collisionCond_eq_uniform_injOn
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (q : ℕ) {xs : List X} (hne : xs ≠ []) (hlen : xs.length ≤ q) :
    CondEquiv.massAfalse (gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))) xs =
      (Dist.uniform (X → X)).mass (fun f => Set.InjOn f (fun x => x ∈ xs.toFinset)) := by
  classical
  unfold CondEquiv.massAfalse gameOf PFunPDS.filterQueries PFunPDS.URF PFunPDS.ofFunDist
  rw [Dist.mass_fTransform, Dist.mass_fTransform, Dist.mass_fTransform]
  refine Dist.mass_congr _ fun f => ?_
  constructor
  · rintro ⟨h, hfalse⟩
    have hbase : xs ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := h
    have hbit : collisionCond
          (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hbase) =
        false := by
      simpa [PFunDDS.outputBit_gameOfDDS (collisionCond (X := X) (Y := X))
        (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs h hbase] using hfalse
    have hnoio : ¬ ioCollision
        (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hbase) := by
      simpa [collisionCond] using hbit
    have hnoout : ¬ outputCollisionOn f xs := by
      exact mt (ioCollision_ioTranscript_filterQueries_functionEvaluator_iff q f xs hbase).mpr hnoio
    exact (not_outputCollisionOn_iff_injOn_toFinset f xs).mp hnoout
  · intro hinj
    have hbase : xs ∈ PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := by
      rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator]
      exact ⟨hne, hlen⟩
    refine ⟨hbase, ?_⟩
    have hnoout : ¬ outputCollisionOn f xs :=
      (not_outputCollisionOn_iff_injOn_toFinset f xs).mpr hinj
    have hnoio : ¬ ioCollision
        (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hbase) := by
      exact mt (ioCollision_ioTranscript_filterQueries_functionEvaluator_iff q f xs hbase).mp hnoout
    have hbit : collisionCond
          (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hbase) =
        false := by
      simpa [collisionCond] using hnoio
    simpa [PFunDDS.outputBit_gameOfDDS (collisionCond (X := X) (Y := X))
      (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) xs hbase hbase] using hbit

/-- The visible transcript mass of a filtered permutation-seeded system is the seed mass of the
corresponding tuple-agreement event.

UPSTREAM-CANDIDATE: generic `massY` normalizer for filtered stateless permutation systems. -/
theorem massY_filterPermDist_eq_perm_tuple_agree
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (Dσ : Dist (Equiv.Perm X)) (q i : ℕ) (ys xs : Vector X (i + 1))
    (hlen : xs.toList.length ≤ q) :
    CondEquiv.massY (PFunPDS.filterQueries q (PFunPDS.ofPermDist X Dσ)) i ys xs =
      Dσ.mass
        (fun σ => ∀ k : Fin (i + 1), σ (xs.get k) = ys.get k) := by
  classical
  unfold CondEquiv.massY PFunPDS.cumulativeBehavior PFunPDS.filterQueries PFunPDS.ofPermDist
  rw [Dist.mass_fTransform, Dist.mass_fTransform]
  refine Dist.mass_congr _ fun σ => ?_
  constructor
  · intro h k
    let kx : Fin xs.toList.length := ⟨k.1, by simpa [Vector.length_toList] using k.2⟩
    let ky : Fin ys.toList.length := ⟨k.1, by simpa [Vector.length_toList] using k.2⟩
    obtain ⟨hdom, hout⟩ := h ky
    have hbase : xs.toList.take (kx.1 + 1) ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator σ.toFun)) := hdom
    have hout' := PFunDDS.output_filterQueries_functionEvaluator_take_succ q σ.toFun xs.toList kx hbase
    calc
      σ (xs.get k) = σ (xs.toList.get kx) := by
        simp [kx, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
      _ = PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator σ.toFun))
            (xs.toList.take (kx.1 + 1)) hbase := hout'.symm
      _ = ys.toList.get ky := hout
      _ = ys.get k := by
        simp [ky, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
  · intro h k
    let kx : Fin xs.toList.length := ⟨k.1, by
      have hk := k.2
      simpa [Vector.length_toList] using hk⟩
    let kv : Fin (i + 1) := ⟨k.1, by
      have hk := k.2
      simpa [Vector.length_toList] using hk⟩
    have htake_ne : xs.toList.take (k.1 + 1) ≠ [] := by
      rw [← List.length_pos_iff_ne_nil, List.length_take]
      have hkx_lt := kx.2
      omega
    have htake_len : (xs.toList.take (k.1 + 1)).length ≤ q := by
      rw [List.length_take]
      have hkx_lt := kx.2
      omega
    have hdom : xs.toList.take (k.1 + 1) ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator σ.toFun)) := by
      rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator]
      exact ⟨htake_ne, htake_len⟩
    refine ⟨hdom, ?_⟩
    have hout := PFunDDS.output_filterQueries_functionEvaluator_take_succ q σ.toFun xs.toList kx hdom
    calc
      PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator σ.toFun))
          (xs.toList.take (k.1 + 1)) hdom
          = σ (xs.toList.get kx) := hout
      _ = σ (xs.get kv) := by
        simp [kx, kv, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
      _ = ys.get kv := h kv
      _ = ys.toList.get k := by
        simp [kv, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]

/-- The visible transcript mass of `[q]URP` is the uniform-permutation tuple-agreement mass.

UPSTREAM-CANDIDATE: concrete `massY` normalizer for `[q]URP`. The proof isolates the hidden
classical finite instance used inside `URP` and transports it back to the theorem-context uniform
distribution with `uniform_eq_of_fintype_instances`. -/
theorem massY_filterURP_eq_uniform_perm_tuple_agree
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (q i : ℕ) (ys xs : Vector X (i + 1)) (hlen : xs.toList.length ≤ q) :
    CondEquiv.massY (⌈q⌉ 𝖯 X) i ys xs =
      (Dist.uniform (Equiv.Perm X)).mass
        (fun σ => ∀ k : Fin (i + 1), σ (xs.get k) = ys.get k) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  have hclass : CondEquiv.massY (⌈q⌉ 𝖯 X) i ys xs =
      (Dist.uniform (Equiv.Perm X)).mass
        (fun σ => ∀ k : Fin (i + 1), σ (xs.get k) = ys.get k) := by
    exact massY_filterPermDist_eq_perm_tuple_agree
      (Dσ := Dist.uniform (Equiv.Perm X)) q i ys xs hlen
  rw [hclass]
  rw [uniform_eq_of_fintype_instances]

/-- The not-yet-won transcript mass of the filtered URF collision game is the uniform-function mass
of exact tuple agreement plus injectivity on the actual queried set.

UPSTREAM-CANDIDATE: concrete `massYAfalse` normalizer for Example-4.15 conditional equivalence. -/
theorem massYAfalse_filterURF_collisionCond_eq_uniform_function_tuple_agree_and_injOn
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (q i : ℕ) (ys xs : Vector X (i + 1)) (hlen : xs.toList.length ≤ q) :
    CondEquiv.massYAfalse (gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))) i ys xs =
      (Dist.uniform (X → X)).mass
        (fun f => (∀ k : Fin (i + 1), f (xs.get k) = ys.get k) ∧
          Set.InjOn f (fun x => x ∈ xs.toList.toFinset)) := by
  classical
  unfold CondEquiv.massYAfalse gameOf PFunPDS.filterQueries PFunPDS.URF PFunPDS.ofFunDist
  rw [Dist.mass_fTransform, Dist.mass_fTransform, Dist.mass_fTransform]
  refine Dist.mass_congr _ fun f => ?_
  constructor
  · intro h
    constructor
    · intro k
      let kx : Fin xs.toList.length := ⟨k.1, by simpa [Vector.length_toList] using k.2⟩
      let ky : Fin ys.toList.length := ⟨k.1, by simpa [Vector.length_toList] using k.2⟩
      obtain ⟨hdom, hout, _hbit⟩ := h ky
      have hbase : xs.toList.take (kx.1 + 1) ∈
          PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := hdom
      have hout' := PFunDDS.output_filterQueries_functionEvaluator_take_succ q f xs.toList kx hbase
      calc
        f (xs.get k) = f (xs.toList.get kx) := by
          simp [kx, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
        _ = PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
              (xs.toList.take (kx.1 + 1)) hbase := hout'.symm
        _ = ys.toList.get ky := by simpa [PFunDDS.output_gameOfDDS] using hout
        _ = ys.get k := by
          simp [ky, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
    · let last : Fin ys.toList.length := ⟨i, by simp [Vector.length_toList]⟩
      obtain ⟨hdom, _hout, hbitFalse⟩ := h last
      have htake_full : xs.toList.take (last.1 + 1) = xs.toList := by
        simp [last, Vector.length_toList]
      have hbase : xs.toList.take (last.1 + 1) ∈
          PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := hdom
      have hbit : collisionCond
            (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
              (xs.toList.take (last.1 + 1)) hbase) = false := by
        simpa [PFunDDS.outputBit_gameOfDDS (collisionCond (X := X) (Y := X))
          (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
          (xs.toList.take (last.1 + 1)) hdom hbase] using hbitFalse
      have hnoio : ¬ ioCollision
          (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
            (xs.toList.take (last.1 + 1)) hbase) := by
        simpa [collisionCond] using hbit
      have hnoout_take : ¬ outputCollisionOn f (xs.toList.take (last.1 + 1)) := by
        exact mt (ioCollision_ioTranscript_filterQueries_functionEvaluator_iff q f
          (xs.toList.take (last.1 + 1)) hbase).mpr hnoio
      have hnoout : ¬ outputCollisionOn f xs.toList := by
        simpa [htake_full] using hnoout_take
      exact (not_outputCollisionOn_iff_injOn_toFinset f xs.toList).mp hnoout
  · rintro ⟨hagree, hinj⟩ k
    let kx : Fin xs.toList.length := ⟨k.1, by
      have hk := k.2
      simpa [Vector.length_toList] using hk⟩
    let kv : Fin (i + 1) := ⟨k.1, by
      have hk := k.2
      simpa [Vector.length_toList] using hk⟩
    have htake_ne : xs.toList.take (k.1 + 1) ≠ [] := by
      rw [← List.length_pos_iff_ne_nil, List.length_take]
      have hkx_lt := kx.2
      omega
    have htake_len : (xs.toList.take (k.1 + 1)).length ≤ q := by
      rw [List.length_take]
      have hkx_lt := kx.2
      omega
    have hbase : xs.toList.take (k.1 + 1) ∈
        PFunDDS.dom (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)) := by
      rw [PFunDDS.mem_dom_filterQueries, PFunDDS.dom_functionEvaluator]
      exact ⟨htake_ne, htake_len⟩
    refine ⟨hbase, ?_, ?_⟩
    · have hout := PFunDDS.output_filterQueries_functionEvaluator_take_succ q f xs.toList kx hbase
      calc
        (PFunDDS.output
            (PFunDDS.gameOfDDS (collisionCond (X := X) (Y := X))
              (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f)))
            (xs.toList.take (k.1 + 1)) hbase).1
            = PFunDDS.output (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
                (xs.toList.take (k.1 + 1)) hbase := rfl
        _ = f (xs.toList.get kx) := hout
        _ = f (xs.get kv) := by
          simp [kx, kv, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
        _ = ys.get kv := hagree kv
        _ = ys.toList.get k := by
          simp [kv, Vector.get_eq_getElem, Vector.getElem_toList, List.get_eq_getElem]
    · have hinj_take : Set.InjOn f (fun x => x ∈ (xs.toList.take (k.1 + 1)).toFinset) := by
        intro a ha b hb hab
        apply hinj
        · change a ∈ (xs.toList.take (k.1 + 1)).toFinset at ha
          change a ∈ xs.toList.toFinset
          rw [List.mem_toFinset] at ha ⊢
          exact List.mem_of_mem_take ha
        · change b ∈ (xs.toList.take (k.1 + 1)).toFinset at hb
          change b ∈ xs.toList.toFinset
          rw [List.mem_toFinset] at hb ⊢
          exact List.mem_of_mem_take hb
        · exact hab
      have hnoout : ¬ outputCollisionOn f (xs.toList.take (k.1 + 1)) :=
        (not_outputCollisionOn_iff_injOn_toFinset f (xs.toList.take (k.1 + 1))).mpr hinj_take
      have hnoio : ¬ ioCollision
          (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
            (xs.toList.take (k.1 + 1)) hbase) := by
        exact mt (ioCollision_ioTranscript_filterQueries_functionEvaluator_iff q f
          (xs.toList.take (k.1 + 1)) hbase).mp hnoout
      have hbit : collisionCond
            (PFunDDS.ioTranscript (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
              (xs.toList.take (k.1 + 1)) hbase) = false := by
        simpa [collisionCond] using hnoio
      simpa [PFunDDS.outputBit_gameOfDDS (collisionCond (X := X) (Y := X))
        (PFunDDS.filterQueries q (PFunDDS.functionEvaluator f))
        (xs.toList.take (k.1 + 1)) hbase hbase] using hbit

/-- **CR18 Example 4.15 under Maurer's `[q]` filter.**

This is the filtered instance needed by the filtered Theorem-4.17 route. It packages the finite
transcript-counting argument for exactly the object used by Lemma 4.19: `gameOf ([q]R) collisionCond`.
The unfiltered Example 4.15 and the generic "`[q]` preserves `|≡`" theorem should be upstreamed only
when proved, not left as theorem-shaped scaffolding here. -/
theorem filterURF_collisionCond_condEquiv_filterURP
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X)) |≡ ⌈q⌉ 𝖯 X := by
  intro i xs ys hA hD
  have hne : xs.toList ≠ [] := by
    simp
  have hlen : xs.toList.length ≤ q := by
    by_contra hlen
    apply hD
    exact massDom_filterURP_eq_zero_of_length_gt (X := X) q (Nat.lt_of_not_ge hlen)
  rw [massDom_filterURP_eq_one_of_length_le (X := X) q hne hlen, mul_one]
  have hYA :=
    massYAfalse_filterURF_collisionCond_eq_uniform_function_tuple_agree_and_injOn
      (X := X) q i ys xs hlen
  have hAfalse := massAfalse_filterURF_collisionCond_eq_uniform_injOn (X := X) q hne hlen
  have hY := massY_filterURP_eq_uniform_perm_tuple_agree (X := X) q i ys xs hlen
  let xfun : Fin (i + 1) → X := fun k => xs.get k
  let yfun : Fin (i + 1) → X := fun k => ys.get k
  let S : Finset X := (Finset.univ : Finset (Fin (i + 1))).image xfun
  let g : S → X := tupleAssignment xfun yfun
  by_cases hcons : tupleConsistent xfun yfun
  · have hSlist : xs.toList.toFinset = S := by
      simpa [S, xfun] using vector_toList_toFinset_eq_image_get xs
    rw [hYA, hAfalse, hY, hSlist]
    have hFconv : (Dist.uniform (X → X)).mass
        (fun f => (∀ k : Fin (i + 1), f (xfun k) = yfun k) ∧
          Set.InjOn f (fun x => x ∈ S)) =
        (Dist.uniform (X → X)).mass
          (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S)) := by
      refine Dist.mass_congr _ fun f => ?_
      constructor
      · intro hf
        exact ⟨(tuple_agree_iff_assignment xfun yfun hcons f).mp hf.1, hf.2⟩
      · intro hf
        exact ⟨(tuple_agree_iff_assignment xfun yfun hcons f).mpr hf.1, hf.2⟩
    have hPconv : (Dist.uniform (Equiv.Perm X)).mass
        (fun σ => ∀ k : Fin (i + 1), σ (xfun k) = yfun k) =
        (Dist.uniform (Equiv.Perm X)).mass
          (fun σ => ∀ x : S, σ x.1 = g x) := by
      refine Dist.mass_congr _ fun σ => ?_
      exact tuple_agree_iff_assignment xfun yfun hcons σ
    rw [hFconv, hPconv]
    exact uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn S g
  · rw [hYA, hAfalse]
    have hYA0 : (Dist.uniform (X → X)).mass
        (fun f => (∀ k : Fin (i + 1), f (xs.get k) = ys.get k) ∧
          Set.InjOn f (fun x => x ∈ xs.toList.toFinset)) = 0 := by
      exact mass_tuple_agree_and_event_eq_zero_of_not_consistent
        (D := Dist.uniform (X → X)) (eval := fun f x => f x)
        xfun yfun (fun f => Set.InjOn f (fun x => x ∈ xs.toList.toFinset)) hcons
    rw [hYA0]
    rw [hY]
    have hY0 : (Dist.uniform (Equiv.Perm X)).mass
        (fun σ => ∀ k : Fin (i + 1), σ (xs.get k) = ys.get k) = 0 := by
      exact mass_tuple_agree_eq_zero_of_not_consistent
        (D := Dist.uniform (Equiv.Perm X)) (eval := fun σ x => σ x) xfun yfun hcons
    rw [hY0, zero_mul]

/-- **CR18 Lemma 4.18, packaged**: the pair-union expression at `r` draws is at most the birthday
bound `½ r² / |X|`.  The whole `#pairs ≤ ½r²` and cast arithmetic lives here, once. -/
theorem pairCollisionUnionBound_le_birthday (X : Type*) [Fintype X] (r : ℕ) :
    (pairCollisionUnionBound X r : ℝ) ≤ (1 / 2 : ℝ) * (r : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
  have hpair : (2 * ((queryPairSet r).card : ℝ)) ≤ (r : ℝ) ^ 2 := by
    unfold queryPairSet
    exact_mod_cast pair_card_le r
  calc (pairCollisionUnionBound X r : ℝ)
      = ((queryPairSet r).card : ℝ) / (Fintype.card X : ℝ) := by
        unfold pairCollisionUnionBound
        push_cast
        ring
    _ ≤ ((r : ℝ) ^ 2 / 2) / (Fintype.card X : ℝ) := by
        gcongr
        cr18_arith
    _ = (1 / 2 : ℝ) * (r : ℝ) ^ 2 / (Fintype.card X : ℝ) := by cr18_algebra

/-- The blind collision game for `[q]R̂` satisfies the final birthday bound.

This is the proved version of Lemma 4.19's "It remains to analyze `Γ(b[q]R̂)`" step: the exact
queried-pair union bound closed by the packaged Lemma 4.18. -/
theorem blindMaxWinProb_filterURF_collisionCond_le_birthday
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    (Γᵇ (gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))) : ℝ)
      ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
  le_trans (blindMaxWinProb_filterURF_collisionCond_le_pairCollisionUnionBound X q)
    (pairCollisionUnionBound_le_birthday X q)

/-- The condition-C leg of the URF/URP switching proof: filtered
distinguishing advantage is bounded by the blind collision game.  The
finite-query normalization used by CR18 Theorem 4.17 is discharged here so
paper-facing proofs can cite precisely this edge of the argument. -/
theorem filtered_urf_urp_advantage_le_blind_collision_game
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    (Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) : ℝ) ≤
      (Γᵇ (gameOf (⌈q⌉ 𝖱 X)
        (collisionCond (X := X) (Y := X))) : ℝ) := by
  classical
  let dummy : X := Classical.choice ‹Nonempty X›
  have hRtot : CondEquiv.TotalOnNonempty (𝖱 X) :=
    PFunPDS.URF_totalOnNonempty
  have hPtot : CondEquiv.TotalOnNonempty (𝖯 X) :=
    PFunPDS.URP_totalOnNonempty X
  have hNorm : DeltaFilteredFiniteQueryNormalization q (𝖱 X) (𝖯 X) :=
    deltaFilteredFiniteQueryNormalization_of_totalOnNonempty
      dummy q (𝖱 X) (𝖯 X) hRtot hPtot
  exact
    maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization_all
      q (𝖱 X) (𝖯 X) (collisionCond (X := X) (Y := X))
      monotone_collisionCond (by cr18_prob) (by cr18_prob)
      hRtot hPtot hNorm
      (filterURF_collisionCond_condEquiv_filterURP X q)

/-- **CR18 Lemma 4.19 — the URP–URF "switching lemma", general-alphabet form.**
`Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤ ½ q² / |X|`: over *any* finite alphabet `X`, the URF `𝖱 X : X → X`
is indistinguishable from the URP `𝖯 X`, both limited to `q` queries by the filter `⌈q⌉`
(Maurer's `[q]`), up to the birthday bound `½q²/|X|`. Maurer states it for `X = {0,1}ⁿ`
(`|X| = 2ⁿ`), i.e. `½q²2⁻ⁿ`; this is the same statement over a general size-`|X|` alphabet.
(Hypothesis-instance form — no `open Classical`: downstream citations from `[DecidableEq X]`
contexts must not cross a classical-instance boundary, which is exponential at `isDefEq`.) -/
@[rs_rule "rs.switching.urf_urp" distance_bound random_systems]
lemma urf_urp_switching (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
  calc Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X)
      ≤ (Γᵇ (gameOf (⌈q⌉ 𝖱 X)
          (collisionCond (X := X) (Y := X))) : ℝ) :=
        filtered_urf_urp_advantage_le_blind_collision_game X q
    _ ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
        blindMaxWinProb_filterURF_collisionCond_le_birthday X q

open Classical in
/-- **Maurer's overlined-angle-bracket form of the switching lemma is the *same statement*** (CR18
§4.11.3: "the lemma can also be stated as `〈[q]Rₙ,ₙ | [q]Pₙ〉 ≤ …`"). Both `〈· | ·〉` and `Δ(·,·)` are
notations for `maxAdvantage`, so the two forms are *definitionally equal* — proved by `rfl`. -/
example (X : Type*) [Fintype X] [Nonempty X] (q : ℕ) :
    (〈 ⌈q⌉ 𝖱 X | ⌈q⌉ 𝖯 X 〉) = Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) := rfl

/-- **`Γᵇ` of a monitored last-query game is bounded by any per-schedule mass bound.**  For a
seed-indexed family of last-query evaluators carrying a per-seed, prefix-monotone bad predicate
`bad`, if every blind winner's fixed schedule `blindQueryList w q` provokes `bad` with mass `≤ ε`,
then the filtered game's non-adaptive advantage `Γᵇ` is `≤ ε`.  Absorbs the game/`gameOfDDS` bridge,
the schedule-list run-reduction, and the monotone lift, leaving a protocol only its mass leaf.

UPSTREAM-CANDIDATE: `Γᵇ`-bound for seed-indexed monitored games (the reusable Step-2 of a CR18
MBO-game security proof — cf. the CBC-MAC in `RandomSystems.CBCMAC`). -/
theorem blindMaxWinProb_filterQueries_monitored_le {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop) [∀ a l, Decidable (bad a l)]
    (hD : D.NonNeg)
    (hmono : ∀ a, ∀ {l₁ l₂ : List I}, l₁ <+: l₂ → bad a l₁ → bad a l₂) (q : ℕ) (ε : NNReal)
    (hleaf : ∀ w : PFunDDS.Winner I O, IsBlind w →
      D.mass (fun a => bad a (blindQueryList w q)) ≤ ε) :
    Γᵇ (⌈q⌉ Dist.fTransform
        (fun a => PFunDDS.historyEvaluator fun l h => (F a (l.getLast h), decide (bad a l))) D)
      ≤ ε := by
  classical
  -- the filtered game per seed is a `gameOfDDS` over the filtered function evaluator
  have hbridge : ∀ a,
      PFunDDS.filterQueries q
          (PFunDDS.historyEvaluator fun l h => (F a (l.getLast h), decide (bad a l)))
        = PFunDDS.gameOfDDS (fun tr => decide (bad a (tr.map Prod.fst)))
          (PFunDDS.filterQueries q (PFunDDS.functionEvaluator (F a))) := by
    intro a
    apply Subtype.ext; funext l; apply Part.ext'
    · exact Iff.rfl
    · intro h₁ h₂
      refine Prod.ext rfl ?_
      show decide (bad a l)
        = decide (bad a ((PFunDDS.ioTranscript
          (PFunDDS.filterQueries q (PFunDDS.functionEvaluator (F a))) l h₂).map Prod.fst))
      rw [PFunDDS.ioTranscript_map_fst]
  unfold PFunPDS.filterQueries
  rw [Dist.fTransform_comp]
  refine blindMaxWinProb_fTransform_le _ _ _ fun w hblind =>
    le_trans (mass_mono hD fun a ha => ?_) (hleaf w hblind)
  simp only [Function.comp] at ha
  rw [hbridge a] at ha
  obtain ⟨xs, hlen, hsched, hdom, hcond⟩ :=
    winsDDS_gameOfDDS_filterQueries_functionEvaluator_exists_schedule_list _ w q hblind _ ha
  rw [PFunDDS.ioTranscript_map_fst] at hcond
  exact hmono a (isPrefix_blindQueryList w q xs hlen hsched) (of_decide_eq_true hcond)

/-! ## Seed-indexed condition C

The CBC randomness-expander proof and Gażi's random-outer NMAC hop share the
same CR18 argument.  The following public wrapper is the single source of
truth for that argument: a seed determines a function and a monotone bad
predicate; conditional equivalence identifies the good world; and the blind
reduction leaves only a fixed-schedule seed event.
-/

/-- A seed-indexed last-query evaluator carrying a monotone condition-C
failure bit. -/
noncomputable def seededConditionCGame {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)] : PFunPDS I (O × Bool) :=
  Dist.fTransform
    (fun a => PFunDDS.historyEvaluator fun l h =>
      (F a (l.getLast h), decide (bad a l))) D

/-- Prefix-monotonicity of the seed event makes `seededConditionCGame` a
monotone-MBO game. -/
theorem seededConditionCGame_monotoneMBO {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)]
    (hmono : ∀ a, ∀ {l₁ l₂ : List I}, l₁ <+: l₂ → bad a l₁ → bad a l₂) :
    MonotoneMBO (seededConditionCGame D F bad) :=
  CondEquiv.monotoneMBO_fTransform_historyEvaluator D
    (fun a l h => F a (l.getLast h)) (fun a l => decide (bad a l))
    (fun a l₁ l₂ hpre hb => by
      simpa using hmono a hpre (by simpa using hb))

/-- A seed-indexed condition-C game is total on every nonempty history. -/
theorem seededConditionCGame_totalOnNonempty {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)] :
    CondEquiv.TotalOnNonempty (seededConditionCGame D F bad) :=
  CondEquiv.totalOnNonempty_fTransform_historyEvaluator D
    (fun a l h => (F a (l.getLast h), decide (bad a l)))

/-- A probability seed law induces a probability condition-C game. -/
theorem seededConditionCGame_isProbDist {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)] (hD : D.isProbDist) :
    (seededConditionCGame D F bad).isProbDist := by
  unfold seededConditionCGame
  exact Dist.fTransform_isProbDist _ hD

/-- **Stripping the monitor bit** from a seed-indexed condition-C game returns the plain
seed-evaluator system: the `historyEvaluator` last-query output is a `functionEvaluator`.
The instance-level `seededHashThenURFGame_ignoreMBO` and `CBCMAC.cbcGame_ignoreMBO` are
this lemma. -/
theorem seededConditionCGame_ignoreMBO {A I O : Type*}
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop) [∀ a l, Decidable (bad a l)] :
    PFunPDS.ignoreMBO (seededConditionCGame D F bad) =
      PFunPDS.ofFunDist (Dist.fTransform F D) := by
  unfold PFunPDS.ignoreMBO PFunPDS.stripMBO seededConditionCGame PFunPDS.ofFunDist
  simp only [dist_simp]
  rw [show (PFunDDS.stripMBO ∘ fun a : A =>
      PFunDDS.historyEvaluator fun l h => (F a (l.getLast h), decide (bad a l))) =
      (fun a : A => PFunDDS.functionEvaluator (F a)) from by
    funext a
    rfl]
  rfl

/-- **Public condition-C / first-bad endpoint.**  Conditional equivalence
handles the good world; the monitored-game blind reduction handles Gażi's
Eq. (2); the only scheme-specific obligation is the seed mass of `bad` on a
blind winner's fixed query schedule. -/
theorem maxAdvantage_filterQueries_seededConditionCGame_le
    {A I O : Type*} [Nonempty I]
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)]
    (hmono : ∀ a, ∀ {l₁ l₂ : List I}, l₁ <+: l₂ → bad a l₁ → bad a l₂)
    (q : ℕ) (T : PFunPDS I O) (ε : NNReal)
    (hCE : seededConditionCGame D F bad |≡ T)
    (hD : D.isProbDist) (hT : T.isProbDist)
    (hTtot : CondEquiv.TotalOnNonempty T)
    (hleaf : ∀ w : PFunDDS.Winner I O, IsBlind w →
      D.mass (fun a => bad a (blindQueryList w q)) ≤ ε) :
    Δ(⌈q⌉ PFunPDS.ignoreMBO (seededConditionCGame D F bad), ⌈q⌉ T) ≤ (ε : ℝ) := by
  calc
    Δ(⌈q⌉ PFunPDS.ignoreMBO (seededConditionCGame D F bad), ⌈q⌉ T)
        ≤ (Γᵇ (⌈q⌉ seededConditionCGame D F bad) : ℝ) :=
      maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv q
        (seededConditionCGame D F bad) hCE rfl
        (seededConditionCGame_monotoneMBO D F bad hmono)
        (seededConditionCGame_isProbDist D F bad hD) hT
        (seededConditionCGame_totalOnNonempty D F bad) hTtot
    _ ≤ (ε : ℝ) := by
      exact_mod_cast blindMaxWinProb_filterQueries_monitored_le
        D F bad hD.nonNeg hmono q ε hleaf

/-- A collision of a seed-indexed hash on two distinct queries. -/
def seededHashCollision {A I J : Type*} (H : A → I → J)
    (a : A) (l : List I) : Prop :=
  ∃ x ∈ l, ∃ y ∈ l, x ≠ y ∧ H a x = H a y

instance seededHashCollision_decidable {A I J : Type*}
    [DecidableEq I] [DecidableEq J] (H : A → I → J) (a : A) (l : List I) :
    Decidable (seededHashCollision H a l) := by
  unfold seededHashCollision
  infer_instance

/-- Hash collisions are monotone in the query history. -/
theorem seededHashCollision_monotone {A I J : Type*} (H : A → I → J)
    (a : A) {l₁ l₂ : List I} (hpre : l₁ <+: l₂)
    (h : seededHashCollision H a l₁) : seededHashCollision H a l₂ := by
  obtain ⟨x, hx, y, hy, hxy, hH⟩ := h
  exact ⟨x, hpre.subset hx, y, hpre.subset hy, hxy, hH⟩

/-- **A uniform random function collides on a fixed query list with birthday probability.**

The `List` form of `uniform_mass_blindQueryCollision_le_pairCollisionUnionBound`, which is
stated for a `blindQueryVector`-style optional schedule.  A `List` is what the seed-indexed
condition-C endpoint's leaf hands you (`blindQueryList`) and what `seededHashCollision`
consumes, so this is the shape every hash-collision leaf over a *uniform* hash needs.

UPSTREAM-CANDIDATE: fixed-list birthday leaf for uniform-hash condition-C games. -/
theorem uniform_mass_listCollision_le_pairCollisionUnionBound
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (l : List X) (q : ℕ) (hlen : l.length ≤ q) :
    (Dist.uniform (X → Y)).mass
        (fun f => seededHashCollision (fun g : X → Y => g) f l)
      ≤ pairCollisionUnionBound Y q := by
  classical
  refine mass_le_pairCollisionUnionBound_of_cover Y (Dist.uniform (X → Y))
    Dist.uniform_nonNeg q
    (fun p f => ∃ x y : X, l[p.1.1]? = some x ∧ l[p.2.1]? = some y ∧ x ≠ y ∧ f x = f y)
    _ ?_ ?_
  · -- cover: a collision on `l` is a collision at two ordered positions of `l`
    rintro f ⟨x, hx, y, hy, hne, heq⟩
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    have hij : i ≠ j := by rintro rfl; exact hne (hix.symm.trans hjy)
    have hxi : l[i]? = some x := by rw [List.getElem?_eq_getElem hi, hix]
    have hyj : l[j]? = some y := by rw [List.getElem?_eq_getElem hj, hjy]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨(⟨i, lt_of_lt_of_le hi hlen⟩, ⟨j, lt_of_lt_of_le hj hlen⟩),
        by simp [queryPairSet, hlt], x, y, hxi, hyj, hne, heq⟩
    · exact ⟨(⟨j, lt_of_lt_of_le hj hlen⟩, ⟨i, lt_of_lt_of_le hi hlen⟩),
        by simp [queryPairSet, hgt], y, x, hyj, hxi, hne.symm, heq.symm⟩
  · -- leaf: a single ordered position pair is a single uniform coincidence
    intro p _hp
    by_cases hpair : ∃ x y : X, l[p.1.1]? = some x ∧ l[p.2.1]? = some y ∧ x ≠ y
    · obtain ⟨x, y, hx, hy, hne⟩ := hpair
      refine (Dist.mass_mono Dist.uniform_nonNeg ?_).trans_eq
        (uniform_function_pair_eq_mass_of_codomain (X := X) (Y := Y) hne)
      rintro f ⟨u, v, hu, hv, _, huv⟩
      rw [show u = x from Option.some.inj (hu.symm.trans hx),
        show v = y from Option.some.inj (hv.symm.trans hy)] at huv
      exact huv
    · refine le_of_eq_of_le (Dist.mass_eq_zero_of_forall_not _ ?_)
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
      rintro f ⟨x, y, hx, hy, hne, _⟩
      exact hpair ⟨x, y, hx, hy, hne⟩

/-- Restricting a uniform random function along an embedding gives a uniform
random function on the smaller domain. -/
theorem uniform_restrict {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Nonempty O] (e : I ↪ J) :
    Dist.fTransform (fun F : J → O => fun i => F (e i)) (Dist.uniform (J → O)) =
      Dist.uniform (I → O) := by
  classical
  let fi := Fintype.equivFin I
  let nonce : Fin (Fintype.card I) → J := fun n => e (fi.symm n)
  have hn : Function.Injective nonce := e.injective.comp fi.symm.injective
  have hu := RandomSystems.Instances.eval_nonces_uniform (X := J) (Y := O)
    (n := Fintype.card I) nonce hn
  let E : (Fin (Fintype.card I) → O) ≃ (I → O) :=
    Equiv.arrowCongr fi.symm (Equiv.refl O)
  have hE : Dist.fTransform E (Dist.uniform (Fin (Fintype.card I) → O)) =
      Dist.uniform (I → O) := Dist.fTransform_equiv_uniform E
  rw [← hE, ← hu, Dist.fTransform_comp]
  congr 1
  funext F i
  simp [E, nonce, fi]

/-- **Fubini for an independent product.**  The mass of an event coupling the two
coordinates integrates the second coordinate's fiber mass against the first.

UPSTREAM-CANDIDATE: the general product-mass fiber decomposition; `mass_prod_good_eq_mass_mul`
(constant fiber on a good set) and `mass_prod_congr_fiber` (proportional fibers) are its two
specializations. -/
theorem mass_prod_eq_sum_fiber {A B : Type*} (P : Dist A) (Q : Dist B) (R : A → B → Prop) :
    (Dist.prod P Q).mass (fun p => R p.1 p.2) = P.sum fun a wa => wa * Q.mass (R a) := by
  classical
  rw [Dist.mass_prod_eq_double_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  unfold Dist.mass
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun b _ => ?_
  by_cases hr : R a b <;> simp [hr]

/-- **Fiberwise comparison of two independent products.**  If at every value of the shared
first coordinate the second coordinate's fiber masses differ by a *constant* factor, then so
do the two coupled masses.  This is how a per-seed conditional-equivalence factorization is
integrated over an independent seed component. -/
theorem mass_prod_congr_fiber {A B B' : Type*} (P : Dist A) (Q : Dist B) (Q' : Dist B')
    (R : A → B → Prop) (R' : A → B' → Prop) (c : ℝ)
    (hfiber : ∀ a, Q.mass (R a) = Q'.mass (R' a) * c) :
    (Dist.prod P Q).mass (fun p => R p.1 p.2)
      = (Dist.prod P Q').mass (fun p => R' p.1 p.2) * c := by
  rw [mass_prod_eq_sum_fiber, mass_prod_eq_sum_fiber, Finsupp.sum_mul]
  exact Finsupp.sum_congr fun a _ => by rw [hfiber a, ← mul_assoc]

/-- Integrate a seed-dependent event whose conditional mass is constant on a
good seed set. -/
theorem mass_prod_good_eq_mass_mul {A B : Type*}
    (P : Dist A) (Q : Dist B) (Good : A → Prop) (R : A → B → Prop)
    (c : ℝ) (hfiber : ∀ a, Good a → Q.mass (R a) = c) :
    (Dist.prod P Q).mass (fun p => Good p.1 ∧ R p.1 p.2) = P.mass Good * c := by
  classical
  have hR : P.mass Good * c = P.sum fun a wa => (if Good a then wa else 0) * c := by
    unfold Dist.mass
    rw [Finsupp.sum_mul]
  rw [mass_prod_eq_sum_fiber P Q (fun a b => Good a ∧ R a b), hR]
  refine Finsupp.sum_congr fun a _ => ?_
  by_cases hgood : Good a
  · rw [if_pos hgood, Dist.mass_congr Q fun b => and_iff_right hgood, hfiber a hgood]
  · rw [if_neg hgood, zero_mul,
      Dist.mass_eq_zero_of_forall_not (P := fun b => Good a ∧ R a b) Q
        (fun b hb => hgood hb.1), mul_zero]

/-- The uniform outer function has the same assignment-fiber mass after an
injective hash restriction as a VIL uniform random function. -/
theorem uniform_hash_assignment_mass_eq {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (S : Finset I) (h : I → J) (a : ↑S → O)
    (hinj : Set.InjOn h {x | x ∈ S}) :
    (Dist.uniform (J → O)).mass (fun r => ∀ s : ↑S, r (h s.1) = a s) =
      (Dist.uniform (I → O)).mass (fun r => ∀ s : ↑S, r s.1 = a s) := by
  classical
  let eh : ↑S ↪ J :=
    ⟨fun s => h s.1, fun s t hst => Subtype.ext (hinj s.2 t.2 hst)⟩
  let ei : ↑S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  calc
    (Dist.uniform (J → O)).mass (fun r => ∀ s : ↑S, r (h s.1) = a s)
        = (Dist.uniform (J → O)).mass
            (fun r => (fun s : ↑S => r (eh s)) = a) := by
          apply Dist.mass_congr
          intro r
          simp only [eh]
          exact ⟨fun hr => funext hr, fun hr s => congrFun hr s⟩
    _ = Dist.fTransform (fun r : J → O => fun s : ↑S => r (eh s))
          (Dist.uniform (J → O)) a :=
      Dist.mass_preimage_eq_fTransform_apply _ _ _
    _ = Dist.uniform (↑S → O) a := by rw [uniform_restrict eh]
    _ = Dist.fTransform (fun r : I → O => fun s : ↑S => r (ei s))
          (Dist.uniform (I → O)) a := by rw [uniform_restrict ei]
    _ = (Dist.uniform (I → O)).mass
          (fun r => ∀ s : ↑S, r s.1 = a s) := by
      rw [Dist.fTransform_apply_eq_mass]
      apply Dist.mass_congr
      intro r
      exact ⟨fun hr s => congrFun hr s, fun hr => funext hr⟩

/-- The seed-indexed hash-then-URF condition-C game.  The seed law and the
outer random function are independent; the bit records the first collision of
hash values at distinct queried inputs. -/
noncomputable def seededHashThenURFGame {A I J O : Type*}
    [Fintype J] [Fintype O] [Nonempty O] [DecidableEq I] [DecidableEq J]
    (D : Dist A) (H : A → I → J) : PFunPDS I (O × Bool) :=
  seededConditionCGame (Dist.prod D (Dist.uniform (J → O)))
    (fun p i => p.2 (H p.1 i))
    (fun p l => seededHashCollision H p.1 l)

/-- Stripping the condition-C bit recovers the hash-then-URF function law. -/
theorem seededHashThenURFGame_ignoreMBO {A I J O : Type*}
    [Fintype J] [Fintype O] [Nonempty O] [DecidableEq I] [DecidableEq J]
    (D : Dist A) (H : A → I → J) :
    PFunPDS.ignoreMBO (seededHashThenURFGame (O := O) D H) =
      PFunPDS.ofFunDist (Dist.fTransform
        (fun p : A × (J → O) => fun i => p.2 (H p.1 i))
        (Dist.prod D (Dist.uniform (J → O)))) :=
  seededConditionCGame_ignoreMBO _ _ _

/-- **Hash-then-URF condition C.**  Until two distinct queried inputs collide
under the sampled hash, independent outer random-function answers are exactly
those of the VIL URF. -/
theorem seededHashThenURF_condEquiv {A I J O : Type*}
    [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (D : Dist A) (H : A → I → J) :
    seededHashThenURFGame (O := O) D H |≡ PFunPDS.URF := by
  classical
  let Shat := seededHashThenURFGame (O := O) D H
  let seed : Dist (A × (J → O)) := Dist.prod D (Dist.uniform (J → O))
  let out : (A × (J → O)) → I → O := fun p i => p.2 (H p.1 i)
  let good : (A × (J → O)) → List I → Prop :=
    fun p l => ¬ seededHashCollision H p.1 l
  refine condEquiv_of_transcript_mass_reductions Shat PFunPDS.URF
    seed (Dist.uniform (I → O)) out (fun r i => r i) good
    (fun {xs} hne => ?_) (fun ys xs => massY_fTransform_lastQuery _ _ ys xs)
    (fun ys xs => ?_) (fun xs a => ?_)
    (hT := PFunPDS.URF_isProbDist) (hTot := PFunPDS.URF_totalOnNonempty)
  · unfold Shat seededHashThenURFGame seededConditionCGame seed good
    rw [CondEquiv.massAfalse_fTransform_historyEvaluator _ _ _ hne]
    apply Dist.mass_congr
    intro p
    simp
  · unfold Shat seededHashThenURFGame seededConditionCGame seed out good
    refine (massYAfalse_fTransform_lastQuery
      (Dist.prod D (Dist.uniform (J → O)))
      (fun p i => p.2 (H p.1 i))
      (fun p l => decide (seededHashCollision H p.1 l)) ?_ ys xs).trans ?_
    · intro p l₁ l₂ hpre hb
      simpa using seededHashCollision_monotone H p.1 hpre (by simpa using hb)
    · apply Dist.mass_congr
      intro p
      simp
  · let S : Finset I := xs.toList.toFinset
    let c : ℝ := (Dist.uniform (I → O)).mass
      (fun r => ∀ s : ↑S, r s.1 = a s)
    have hfiber : ∀ h : A, ¬ seededHashCollision H h xs.toList →
        (Dist.uniform (J → O)).mass
          (fun r => ∀ s : ↑S, r (H h s.1) = a s) = c := by
      intro h hgood
      apply uniform_hash_assignment_mass_eq S (H h) a
      intro x hx y hy hxy
      by_contra hne
      exact hgood ⟨x, by simpa [S] using hx, y, by simpa [S] using hy, hne, hxy⟩
    change (Dist.prod D (Dist.uniform (J → O))).mass
        (fun p => (∀ s : ↑S, p.2 (H p.1 s.1) = a s) ∧
          ¬ seededHashCollision H p.1 xs.toList) = _
    rw [Dist.mass_congr _ fun p => and_comm]
    calc
      (Dist.prod D (Dist.uniform (J → O))).mass
          (fun p => ¬ seededHashCollision H p.1 xs.toList ∧
            ∀ s : ↑S, p.2 (H p.1 s.1) = a s)
          = D.mass (fun h => ¬ seededHashCollision H h xs.toList) * c :=
        mass_prod_good_eq_mass_mul D (Dist.uniform (J → O))
          (fun h => ¬ seededHashCollision H h xs.toList)
          (fun h r => ∀ s : ↑S, r (H h s.1) = a s) c hfiber
      _ = (Dist.uniform (I → O)).mass
            (fun r => ∀ s : ↑S, r s.1 = a s) *
          (Dist.prod D (Dist.uniform (J → O))).mass
            (fun p => ¬ seededHashCollision H p.1 xs.toList) := by
        have hfst : (Dist.prod D (Dist.uniform (J → O))).mass
            (fun p => ¬ seededHashCollision H p.1 xs.toList) =
            D.mass (fun h => ¬ seededHashCollision H h xs.toList) := by
          calc
            (Dist.prod D (Dist.uniform (J → O))).mass
                (fun p => ¬ seededHashCollision H p.1 xs.toList) =
                D.mass (fun h => ¬ seededHashCollision H h xs.toList) *
                  (Dist.uniform (J → O)).weight :=
              Dist.mass_prod_fst D (Dist.uniform (J → O))
                (fun h => ¬ seededHashCollision H h xs.toList)
            _ = D.mass (fun h => ¬ seededHashCollision H h xs.toList) := by
              rw [Dist.weight_uniform,
                mul_one]
        rw [show c = (Dist.uniform (I → O)).mass
          (fun r => ∀ s : ↑S, r s.1 = a s) from rfl, hfst, mul_comm]

/-- **Seeded hash-then-URF condition-C / first-collision bound.**  The
adaptive filtered distance is reduced to the collision mass of the sampled
hash on each blind fixed schedule. -/
theorem maxAdvantage_filterQueries_seededHashThenURF_le
    {A I J O : Type*} [Nonempty I]
    [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (D : Dist A) (H : A → I → J) (q : ℕ) (ε : NNReal)
    (hD : D.isProbDist)
    (hleaf : ∀ w : PFunDDS.Winner I O, IsBlind w →
      D.mass (fun a => seededHashCollision H a (blindQueryList w q)) ≤ ε) :
    Δ(⌈q⌉ PFunPDS.ignoreMBO (seededHashThenURFGame (O := O) D H),
      ⌈q⌉ PFunPDS.URF) ≤ (ε : ℝ) := by
  apply maxAdvantage_filterQueries_seededConditionCGame_le
    (Dist.prod D (Dist.uniform (J → O)))
    (fun p i => p.2 (H p.1 i))
    (fun p l => seededHashCollision H p.1 l)
    (fun p => seededHashCollision_monotone H p.1)
    q PFunPDS.URF ε (seededHashThenURF_condEquiv D H)
    (Dist.prod_isProbDist D (Dist.uniform (J → O)) hD Dist.uniform_isProbDist)
    PFunPDS.URF_isProbDist PFunPDS.URF_totalOnNonempty
  intro w hw
  calc
    (Dist.prod D (Dist.uniform (J → O))).mass
        (fun p => seededHashCollision H p.1 (blindQueryList w q)) =
        D.mass (fun a => seededHashCollision H a (blindQueryList w q)) *
          (Dist.uniform (J → O)).weight :=
      Dist.mass_prod_fst D (Dist.uniform (J → O))
        (fun a => seededHashCollision H a (blindQueryList w q))
    _ = D.mass (fun a => seededHashCollision H a (blindQueryList w q)) := by
      rw [Dist.weight_uniform, mul_one]
    _ ≤ ε := hleaf w hw

end RandomSystems.CR18
