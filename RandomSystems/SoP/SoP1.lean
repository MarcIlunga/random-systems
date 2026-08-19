/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.Common
import RandomSystems.Coupling
import RandomSystems.Counting

/-!
# SoP1: one permutation on an ordered-pair partition

This file formalizes the separate paired-input construction developed in
`RandomSystems/SoP/SoP1.md`.  It does not import or depend on the
two-independent-permutation proof in `RandomSystems/SoP/SoP2.lean`.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18

namespace RandomSystems.SoP

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open Common

/-!
## One permutation on an ordered-pair partition

This file formalizes a construction separate from the sum of two
independent permutations: one uniform permutation is evaluated on
the two members of each block of a fixed ordered-pair partition.  The public
surface is deliberately law-level.  Endpoint tapes, hidden matchings, fiber
counts, and coupling kernels are introduced only inside the proof layers
that need them.

The paper proof's headline graph is written from its public conclusion
downward.  The current formalization below reaches the exact adaptive
finite-count characterization and the exact one-query theorem.  The Boolean
online-coupling layers shown above it in the graph remain to be appended at
the bottom of this file.

```text
ordered_pair_advantage_eq_zero_event_closed_range
├── lower bound: fixed fresh-query zero test
│   ├── real Boolean matching colors are nonzero
│   └── ideal zero-event probability
└── upper bound: coupling disagreement
    ├── explicit online coupling
    │   ├── coupling normalization
    │   ├── real marginal is a uniform ordered matching
    │   ├── ideal marginal is a uniform function tape
    │   └── disagreement iff an ideal fresh answer is zero
    └── honest-representative transport
        ├── fresh-rank cache handles repeats
        ├── uniform restriction of a permutation
        └── CR18 system-factor transcript transport
            ├── ordered_pair_real
            └── ordered_pair_ideal
```

The arbitrary-group exact count and the one-query formula are separately
required publication audit results; they are not ancestors of the headline
closed-range proof.  Normalization, domain, and totality declarations are
likewise semantic certificates.  Every private declaration must feed either
the headline graph or one of those named audit results; a final reference
audit enforces that rule.
-/

section OrderedPairPartition

variable {X H : Type*} [Fintype X] [Fintype H] [AddGroup H]

section PublicModel

/-- Paper Definition 27.  An ordered partition of the permutation domain
into blocks indexed by `X`.  Encoding the partition as an equivalence makes
disjointness, coverage, and the order of both endpoints structural. -/
def ordered_pair_partition (X H : Type*) :=
  X × Fin 2 ≃ H

/-- The concrete function sampled in the real ordered-pair experiment.  Its
output is visibly the sum of the two permutation values in the block. -/
def ordered_pair_function
    (P : ordered_pair_partition X H) (π : Equiv.Perm H) : X → H :=
  fun x =>
    π ((show X × Fin 2 ≃ H from P) (x, 0)) +
      π ((show X × Fin 2 ≃ H from P) (x, 1))

/-- Paper Definition 27, real law-level oracle. -/
noncomputable def ordered_pair_real
    (P : ordered_pair_partition X H) : PFunPDS.Prob X H :=
  PFunPDS.Prob.functionEvaluator
    ⟨Dist.uniform (Equiv.Perm H), Dist.uniform_isProbDist⟩
    (ordered_pair_function P)

/-- Paper Definition 27, ideal law-level oracle. -/
noncomputable def ordered_pair_ideal : PFunPDS.Prob X H :=
  PFunPDS.Prob.urf (X := X) (Y := H)

/-- An ordered-pair partition forces the permutation carrier to have twice
as many elements as the oracle input space. -/
theorem ordered_pair_partition_card
    (P : ordered_pair_partition X H) :
    Fintype.card H = 2 * Fintype.card X := by
  rw [← Fintype.card_congr P]
  simp [Nat.mul_comm]

/-- The real public system is a normalized probability law. -/
theorem ordered_pair_real_is_prob_dist
    (P : ordered_pair_partition X H) :
    (ordered_pair_real P).val.isProbDist :=
  (ordered_pair_real P).property

/-- The ideal public system is a normalized probability law. -/
theorem ordered_pair_ideal_is_prob_dist :
    (ordered_pair_ideal (X := X) (H := H)).val.isProbDist :=
  (ordered_pair_ideal (X := X) (H := H)).property

/-- The real oracle answers every nonempty history up to every finite query
bound. -/
theorem ordered_pair_real_k_step_total
    (P : ordered_pair_partition X H) (q : Nat) :
    PFunPDS.Prob.KStepTotal (ordered_pair_real P) q :=
  functionEvaluatorProb_KStepTotal
    ⟨Dist.uniform (Equiv.Perm H), Dist.uniform_isProbDist⟩
    (ordered_pair_function P) q

/-- The ideal oracle answers every nonempty history up to every finite query
bound. -/
theorem ordered_pair_ideal_k_step_total (q : Nat) :
    PFunPDS.Prob.KStepTotal
      (ordered_pair_ideal (X := X) (H := H)) q :=
  PFunPDS.Prob.urf_KStepTotal q

/-- The real oracle is total on every nonempty history in every system in its
support. -/
theorem ordered_pair_real_total_on_nonempty
    (P : ordered_pair_partition X H) :
    CondEquiv.TotalOnNonempty (ordered_pair_real P).val :=
  functionEvaluatorProb_totalOnNonempty
    ⟨Dist.uniform (Equiv.Perm H), Dist.uniform_isProbDist⟩
    (ordered_pair_function P)

/-- The ideal oracle is total on every nonempty history in every system in
its support. -/
theorem ordered_pair_ideal_total_on_nonempty :
    CondEquiv.TotalOnNonempty
      (ordered_pair_ideal (X := X) (H := H)).val := by
  change
    CondEquiv.TotalOnNonempty
      (PFunPDS.Prob.functionEvaluator
        (PFunPDS.uniformP (X := X) (Y := H))
        (fun f : X → H => f)).val
  exact
    functionEvaluatorProb_totalOnNonempty
      (PFunPDS.uniformP (X := X) (Y := H))
      (fun f : X → H => f)

end PublicModel

/-!
### Fresh ordered-matching tapes

The adaptive proof is driven by fresh query rank.  On a fixed injective
schedule, the real tape is obtained by restricting one uniform permutation
to the two endpoints of each queried block and summing within each block.
The ideal tape is uniform.  These definitions are honest pushforwards of the
two public experiments; no compatible-count formula is used at this stage.
-/

section FreshTape

/-- The `2m` distinct permutation-domain points exposed by `m` distinct
ordered-pair queries. -/
private def ordered_pair_endpoint_inputs {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    Fin (m * 2) ↪ H where
  toFun k :=
    let ib := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).symm k
    (show X × Fin 2 ≃ H from P) (xs ib.1, ib.2)
  inj' i j h := by
    let ib := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).symm i
    let jb := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).symm j
    have hp :
        (xs ib.1, ib.2) = (xs jb.1, jb.2) :=
      (show X × Fin 2 ≃ H from P).injective h
    apply
      (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).symm.injective
    exact Prod.ext
      (xs.injective (congrArg Prod.fst hp))
      (congrArg (fun p : X × Fin 2 => p.2) hp)

/-- The finite slot encoding preserves the displayed block and endpoint. -/
@[simp] private theorem ordered_pair_endpoint_inputs_fin_prod {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X)
    (i : Fin m) (b : Fin 2) :
    ordered_pair_endpoint_inputs P xs (finProdFinEquiv (i, b)) =
      (show X × Fin 2 ≃ H from P) (xs i, b) := by
  change
    (show X × Fin 2 ≃ H from P)
        (xs ((finProdFinEquiv :
          Fin m × Fin 2 ≃ Fin (m * 2)).symm
            (finProdFinEquiv (i, b))).1,
          ((finProdFinEquiv :
            Fin m × Fin 2 ≃ Fin (m * 2)).symm
              (finProdFinEquiv (i, b))).2) =
      _
  rw [Equiv.symm_apply_apply]

/-- Sum the two endpoint values of every block in an endpoint embedding. -/
private def ordered_pair_endpoint_sums {m : Nat}
    (a : Fin (m * 2) ↪ H) : Fin m → H :=
  fun i =>
    a (finProdFinEquiv (i, 0)) +
      a (finProdFinEquiv (i, 1))

/-- Paper Lemma 28, real fresh-output tape on a fixed injective schedule. -/
noncomputable def ordered_pair_real_fresh_tape {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    Dist.ProbDist (Fin m → H) :=
  ⟨Dist.fTransform
      (fun π : Equiv.Perm H =>
        fun i => ordered_pair_function P π (xs i))
      (Dist.uniform (Equiv.Perm H)),
    Dist.fTransform_isProbDist _ Dist.uniform_isProbDist⟩

/-- Paper Lemma 28, ideal fresh-output tape. -/
noncomputable def ordered_pair_ideal_fresh_tape
    (m : Nat) : Dist.ProbDist (Fin m → H) :=
  ⟨Dist.uniform (Fin m → H), Dist.uniform_isProbDist⟩

/-- Restrict a permutation to the ordered endpoints exposed by a fresh
query schedule. -/
private def ordered_pair_restrict_perm {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X)
    (π : Equiv.Perm H) : Fin (m * 2) ↪ H :=
  (ordered_pair_endpoint_inputs P xs).trans π.toEmbedding

/-- Uniform law on endpoint embeddings.  The displayed schedule supplies
nonemptiness constructively, avoiding a cardinality side condition in every
subsequent statement. -/
private noncomputable def ordered_pair_uniform_endpoint_embedding {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    Dist (Fin (m * 2) ↪ H) :=
  letI : Nonempty (Fin (m * 2) ↪ H) :=
    ⟨ordered_pair_endpoint_inputs P xs⟩
  Dist.uniform (Fin (m * 2) ↪ H)

/-- The public real fresh tape factors through its endpoint embedding. -/
private theorem ordered_pair_real_fresh_tape_factor {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    (ordered_pair_real_fresh_tape P xs).val =
      Dist.fTransform ordered_pair_endpoint_sums
        (Dist.fTransform (ordered_pair_restrict_perm P xs)
          (Dist.uniform (Equiv.Perm H))) := by
  change
    Dist.fTransform
        (fun π : Equiv.Perm H =>
          fun i => ordered_pair_function P π (xs i))
        (Dist.uniform (Equiv.Perm H)) = _
  rw [Dist.fTransform_comp]
  congr 1
  funext π i
  simp [ordered_pair_endpoint_sums, ordered_pair_restrict_perm,
    ordered_pair_function]

/-- Restricting a uniform permutation to the endpoints of distinct queried
blocks gives a uniform endpoint embedding.  This is the finite counting core
of the real marginal in Paper Lemma 28. -/
private theorem ordered_pair_restrict_perm_uniform {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    Dist.fTransform (ordered_pair_restrict_perm P xs)
        (Dist.uniform (Equiv.Perm H)) =
      ordered_pair_uniform_endpoint_embedding P xs := by
  letI : Nonempty (Fin (m * 2) ↪ H) :=
    ⟨ordered_pair_endpoint_inputs P xs⟩
  unfold ordered_pair_uniform_endpoint_embedding
  apply Dist.fTransform_uniform_eq_uniform_of_card_fiber_mul
  intro a
  have hle : m * 2 ≤ Fintype.card H := by
    simpa using
      (Fintype.card_le_of_injective
        (ordered_pair_endpoint_inputs P xs)
        (ordered_pair_endpoint_inputs P xs).injective)
  have hfiber :=
    RandomSystems.CR18.Counting.card_perm_fiber
      (ordered_pair_endpoint_inputs P xs)
      (ordered_pair_endpoint_inputs P xs).injective
      a a.injective hle
  have hfilter :
      ((Finset.univ : Finset (Equiv.Perm H)).filter
          (fun π => ordered_pair_restrict_perm P xs π = a)) =
        (Finset.univ.filter
          (fun π : Equiv.Perm H =>
            ∀ i, π (ordered_pair_endpoint_inputs P xs i) = a i)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Function.Embedding.ext_iff
  rw [hfilter, hfiber, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_perm]
  exact Nat.factorial_mul_descFactorial hle

/-- Canonical form of the real fresh tape: sum the pairs in a uniform
ordered endpoint embedding.  In particular, its law is independent of the
names and geometry of the ordered blocks. -/
theorem ordered_pair_real_fresh_tape_eq_uniform_matching {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X) :
    (ordered_pair_real_fresh_tape P xs).val =
      Dist.fTransform ordered_pair_endpoint_sums
        (ordered_pair_uniform_endpoint_embedding P xs) := by
  rw [ordered_pair_real_fresh_tape_factor,
    ordered_pair_restrict_perm_uniform]

end FreshTape

/-!
### The fresh-rank lazy representative

This is the concrete bounded-system representative from Paper Lemma 28.
Unlike an absolute-position tape, a fresh query consumes the next unused
coordinate and a repeat reuses the coordinate assigned at its first
occurrence.  The definitions are private; the semantic marginal theorems
below are the interface consumed by the coupling proof.
-/

section FreshRankRepresentative

/-- Distinct query names in order of first appearance. -/
private def first_occurrences (l : List X) : List X :=
  l.reverse.dedup.reverse

/-- First-occurrence lists are duplicate-free. -/
private theorem first_occurrences_nodup (l : List X) :
    (first_occurrences l).Nodup := by
  simpa only [first_occurrences, ne_comm] using
    (List.nodup_dedup l.reverse).reverse

/-- Taking first occurrences preserves the prefix order. -/
private theorem first_occurrences_prefix_of_prefix
    {l₁ l₂ : List X} (h : l₁ <+: l₂) :
    first_occurrences l₁ <+: first_occurrences l₂ := by
  obtain ⟨tail, rfl⟩ := h
  induction tail generalizing l₁ with
  | nil => simp
  | cons x tail ih =>
      rw [show l₁ ++ x :: tail = (l₁ ++ [x]) ++ tail by simp]
      have hstep :
          first_occurrences l₁ <+:
            first_occurrences (l₁ ++ [x]) := by
        by_cases hx : x ∈ l₁
        · simp [first_occurrences, hx]
        · rw [show first_occurrences (l₁ ++ [x]) =
              first_occurrences l₁ ++ [x] by
              simp [first_occurrences, hx]]
          exact List.prefix_append _ _
      exact hstep.trans (ih (l₁ := l₁ ++ [x]))

/-- Fresh-query rank of the current query in a nonempty bounded history. -/
private def fresh_rank_index {q : Nat}
    (l : List X) (h : l ≠ [] ∧ l.length ≤ q) : Fin q := by
  let x := l.getLast h.1
  have hx : x ∈ first_occurrences l := by
    simp [x, first_occurrences, List.getLast_mem]
  refine ⟨(first_occurrences l).idxOf x, ?_⟩
  have hidx :
      (first_occurrences l).idxOf x <
        (first_occurrences l).length :=
    List.idxOf_lt_length_of_mem hx
  have hlen : (first_occurrences l).length ≤ l.length := by
    simpa [first_occurrences] using
      (List.dedup_sublist l.reverse).length_le
  exact lt_of_lt_of_le hidx (hlen.trans h.2)

/-- Input prefix ending at a specified position. -/
private def input_prefix {q : Nat}
    (inputs : Fin q → X) (i : Fin q) : List X :=
  List.take (i.1 + 1) (List.ofFn inputs)

private theorem input_prefix_ne_nil {q : Nat}
    (inputs : Fin q → X) (i : Fin q) :
    input_prefix inputs i ≠ [] := by
  have hlen :
      (input_prefix inputs i).length = i.1 + 1 := by
    simp [input_prefix]
  intro h
  rw [h] at hlen
  simp at hlen

private theorem input_prefix_length_le {q : Nat}
    (inputs : Fin q → X) (i : Fin q) :
    (input_prefix inputs i).length ≤ q := by
  simp [input_prefix]

/-- Rank consumed by the query at absolute position `i`. -/
private def fresh_rank_at {q : Nat}
    (inputs : Fin q → X) (i : Fin q) : Fin q :=
  fresh_rank_index (input_prefix inputs i)
    ⟨input_prefix_ne_nil inputs i, input_prefix_length_le inputs i⟩

/-- Number of distinct queries in a complete fixed input vector. -/
private def fresh_query_count {q : Nat}
    (inputs : Fin q → X) : Nat :=
  (first_occurrences (List.ofFn inputs)).length

/-- Distinct fixed queries, ordered by first appearance. -/
private def fresh_input_embedding {q : Nat}
    (inputs : Fin q → X) : Fin (fresh_query_count inputs) ↪ X where
  toFun := (first_occurrences (List.ofFn inputs)).get
  inj' :=
    (first_occurrences_nodup
      (List.ofFn inputs)).injective_get

/-- Every consumed rank lies inside the final distinct-query prefix. -/
private theorem fresh_rank_at_lt_count {q : Nat}
    (inputs : Fin q → X) (i : Fin q) :
    (fresh_rank_at inputs i).1 < fresh_query_count inputs := by
  let pref := input_prefix inputs i
  let x := pref.getLast (input_prefix_ne_nil inputs i)
  have hx : x ∈ first_occurrences pref := by
    simp [x, first_occurrences, List.getLast_mem]
  have hidx :
      (first_occurrences pref).idxOf x <
        (first_occurrences pref).length :=
    List.idxOf_lt_length_of_mem hx
  have hpref :
      first_occurrences pref <+:
        first_occurrences (List.ofFn inputs) :=
    first_occurrences_prefix_of_prefix
      (List.take_prefix (i.1 + 1) (List.ofFn inputs))
  exact lt_of_lt_of_le hidx hpref.length_le

/-- Looking up an absolute position through its fresh rank recovers the
original query name. -/
private theorem fresh_input_embedding_fresh_rank_at {q : Nat}
    (inputs : Fin q → X) (i : Fin q) :
    fresh_input_embedding inputs
        ⟨(fresh_rank_at inputs i).1,
          fresh_rank_at_lt_count inputs i⟩ =
      inputs i := by
  let pref := input_prefix inputs i
  let x := pref.getLast (input_prefix_ne_nil inputs i)
  have hx : x ∈ first_occurrences pref := by
    simp [x, first_occurrences, List.getLast_mem]
  have hpref :
      first_occurrences pref <+:
        first_occurrences (List.ofFn inputs) :=
    first_occurrences_prefix_of_prefix
      (List.take_prefix (i.1 + 1) (List.ofFn inputs))
  have hidx :
      (first_occurrences pref).idxOf x =
        (first_occurrences (List.ofFn inputs)).idxOf x :=
    hpref.idxOf_eq_of_mem hx
  have hmem : x ∈ first_occurrences (List.ofFn inputs) :=
    hpref.mem hx
  have hval :
      (fresh_rank_at inputs i).val =
        (first_occurrences (List.ofFn inputs)).idxOf x := by
    change (first_occurrences pref).idxOf x = _
    exact hidx
  calc
    fresh_input_embedding inputs
        ⟨(fresh_rank_at inputs i).1,
          fresh_rank_at_lt_count inputs i⟩ =
        (first_occurrences (List.ofFn inputs)).get
          ⟨(first_occurrences (List.ofFn inputs)).idxOf x,
            List.idxOf_lt_length_of_mem hmem⟩ := by
              apply congrArg
                (first_occurrences (List.ofFn inputs)).get
              exact Fin.ext hval
    _ = x :=
      List.idxOf_get (List.idxOf_lt_length_of_mem hmem)
    _ = inputs i := by
      dsimp [x, pref]
      simp [input_prefix, List.getLast_eq_getElem]

/-- The number of distinct queries never exceeds the call count. -/
private theorem fresh_query_count_le {q : Nat}
    (inputs : Fin q → X) :
    fresh_query_count inputs ≤ q := by
  calc
    fresh_query_count inputs ≤ (List.ofFn inputs).length := by
      simpa [fresh_query_count, first_occurrences] using
        (List.dedup_sublist
          (List.ofFn inputs).reverse).length_le
    _ = q := List.length_ofFn

/-- Include a shorter rank space as the initial segment of a longer one. -/
private def fin_prefix_embedding {r q : Nat}
    (h : r ≤ q) : Fin r ↪ Fin q where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 h⟩
  inj' i j hij := by
    apply Fin.ext
    exact congrArg (fun k : Fin q => k.val) hij

/-- Restrict a tape to its first `r` fresh ranks. -/
private def tape_prefix {r q : Nat}
    (h : r ≤ q) (tape : Fin q → H) : Fin r → H :=
  fun i => tape (fin_prefix_embedding h i)

/-- Restrict an injective fresh-query schedule to its first `r` entries. -/
private def prefix_query_embedding {r q : Nat}
    (xs : Fin q ↪ X) (h : r ≤ q) : Fin r ↪ X :=
  (fin_prefix_embedding h).trans xs

/-- Prefixing a real tape is the real tape on the prefixed schedule. -/
private theorem ordered_pair_real_fresh_tape_prefix {r q : Nat}
    (P : ordered_pair_partition X H) (xs : Fin q ↪ X)
    (h : r ≤ q) :
    Dist.fTransform (tape_prefix (H := H) h)
        (ordered_pair_real_fresh_tape P xs).val =
      (ordered_pair_real_fresh_tape P
        (prefix_query_embedding xs h)).val := by
  unfold ordered_pair_real_fresh_tape tape_prefix
    prefix_query_embedding
  rw [Dist.fTransform_comp]
  rfl

/-- The real fresh-tape law depends only on its length, not on the names of
the injective queried blocks. -/
private theorem ordered_pair_real_fresh_tape_schedule_independent
    {m : Nat} (P : ordered_pair_partition X H)
    (xs zs : Fin m ↪ X) :
    (ordered_pair_real_fresh_tape P xs).val =
      (ordered_pair_real_fresh_tape P zs).val := by
  rw [ordered_pair_real_fresh_tape_eq_uniform_matching,
    ordered_pair_real_fresh_tape_eq_uniform_matching]
  unfold ordered_pair_uniform_endpoint_embedding
  rfl

/-- Expand a distinct-query tape back to every absolute query position. -/
private def expand_fresh_outputs {q : Nat}
    (inputs : Fin q → X)
    (fresh : Fin (fresh_query_count inputs) → H) : Fin q → H :=
  fun i =>
    fresh
      ⟨(fresh_rank_at inputs i).1,
        fresh_rank_at_lt_count inputs i⟩

/-- Fixed-schedule outputs of the literal fresh-rank cache. -/
private def fresh_rank_fixed_outputs {q : Nat}
    (inputs : Fin q → X) (tape : Fin q → H) : Fin q → H :=
  fun i => tape (fresh_rank_at inputs i)

/-- Cache evaluation factors through the prefix containing exactly the
distinct-query ranks. -/
private theorem fresh_rank_fixed_outputs_eq_expand {q : Nat}
    (inputs : Fin q → X) (tape : Fin q → H) :
    fresh_rank_fixed_outputs inputs tape =
      expand_fresh_outputs inputs
        (tape_prefix (fresh_query_count_le inputs) tape) := by
  funext i
  rfl

/-- Evaluating any total function on a repeated query vector factors through
the first-occurrence embedding and the same deterministic expansion. -/
private theorem function_eval_eq_expand_fresh {q : Nat}
    (inputs : Fin q → X) (f : X → H) :
    (fun i => f (inputs i)) =
      expand_fresh_outputs inputs
        (fun j => f (fresh_input_embedding inputs j)) := by
  funext i
  unfold expand_fresh_outputs
  change
    f (inputs i) =
      f (fresh_input_embedding inputs
        ⟨(fresh_rank_at inputs i).1,
          fresh_rank_at_lt_count inputs i⟩)
  rw [fresh_input_embedding_fresh_rank_at]

/-- On every possibly repeated fixed schedule, the public real output law is
the output law of the honest fresh-rank tape representative. -/
private theorem ordered_pair_real_output_law_eq_fresh_rank_tape
    {q : Nat} (P : ordered_pair_partition X H)
    (xs : Fin q ↪ X) (inputs : Fin q → X) :
    Dist.fTransform
        (fun π : Equiv.Perm H =>
          fun i => ordered_pair_function P π (inputs i))
        (Dist.uniform (Equiv.Perm H)) =
      Dist.fTransform (fresh_rank_fixed_outputs inputs)
        (ordered_pair_real_fresh_tape P xs).val := by
  have hcache :
      fresh_rank_fixed_outputs (H := H) inputs =
        (expand_fresh_outputs (H := H) inputs) ∘
          tape_prefix (H := H) (fresh_query_count_le inputs) := by
    funext tape
    exact fresh_rank_fixed_outputs_eq_expand inputs tape
  rw [hcache, ← Dist.fTransform_comp,
    ordered_pair_real_fresh_tape_prefix]
  rw [ordered_pair_real_fresh_tape_schedule_independent P
    (prefix_query_embedding xs (fresh_query_count_le inputs))
    (fresh_input_embedding inputs)]
  unfold ordered_pair_real_fresh_tape
  rw [Dist.fTransform_comp]
  congr 1
  funext π
  exact function_eval_eq_expand_fresh inputs
    (ordered_pair_function P π)

/-- On every possibly repeated fixed schedule, the public ideal output law is
the output law of a uniform fresh-rank tape. -/
private theorem ordered_pair_ideal_output_law_eq_fresh_rank_tape
    {q : Nat} (inputs : Fin q → X) :
    Dist.fTransform
        (fun f : X → H => fun i => f (inputs i))
        (Dist.uniform (X → H)) =
      Dist.fTransform (fresh_rank_fixed_outputs inputs)
        (ordered_pair_ideal_fresh_tape (H := H) q).val := by
  have hcache :
      fresh_rank_fixed_outputs (H := H) inputs =
        (expand_fresh_outputs (H := H) inputs) ∘
          tape_prefix (H := H) (fresh_query_count_le inputs) := by
    funext tape
    exact fresh_rank_fixed_outputs_eq_expand inputs tape
  have hprefix :
      Dist.fTransform
          (tape_prefix (H := H)
            (fresh_query_count_le inputs))
          (ordered_pair_ideal_fresh_tape (H := H) q).val =
        Dist.uniform
          (Fin (fresh_query_count inputs) → H) := by
    change
      Dist.fTransform
          (fun tape : Fin q → H =>
            fun i =>
              tape
                (fin_prefix_embedding
                  (fresh_query_count_le inputs) i))
          (Dist.uniform (Fin q → H)) =
        _
    exact
      uniformFunction_eval_uniform
        (fin_prefix_embedding (fresh_query_count_le inputs))
        (fin_prefix_embedding
          (fresh_query_count_le inputs)).injective
  calc
    Dist.fTransform
          (fun f : X → H => fun i => f (inputs i))
          (Dist.uniform (X → H)) =
        Dist.fTransform (expand_fresh_outputs inputs)
          (Dist.fTransform
            (fun f : X → H =>
              fun j => f (fresh_input_embedding inputs j))
            (Dist.uniform (X → H))) := by
      rw [Dist.fTransform_comp]
      congr 1
      funext f
      exact function_eval_eq_expand_fresh inputs f
    _ = Dist.fTransform (expand_fresh_outputs inputs)
          (Dist.uniform
            (Fin (fresh_query_count inputs) → H)) := by
      rw [uniformFunction_eval_uniform
        (fresh_input_embedding inputs)
        (fresh_input_embedding inputs).injective]
    _ = Dist.fTransform (fresh_rank_fixed_outputs inputs)
          (ordered_pair_ideal_fresh_tape (H := H) q).val := by
      rw [hcache, ← Dist.fTransform_comp, hprefix]

/-- Literal fresh-rank cache induced by an output tape. -/
private def fresh_rank_tape_dds
    (q : Nat) (tape : Fin q → H) : PFunDDS.DDS X H :=
  ⟨(fun l : List X =>
      (⟨l ≠ [] ∧ l.length ≤ q,
        fun h => tape (fresh_rank_index l h)⟩ : Part H)),
    ⟨by
      intro h
      exact h.1 rfl,
    by
      intro l₁ l₂ hprefix hne hdom
      exact ⟨hne, Nat.le_trans hprefix.length_le hdom.2⟩⟩⟩

/-- The fresh-rank cache is total through its advertised call budget. -/
private theorem fresh_rank_tape_dds_k_step_total (q : Nat) :
    PFunPDS.RV.KStepTotal
      (fresh_rank_tape_dds (X := X) (H := H) q) q := by
  intro tape l hne hlen
  have hdom :
      l ∈ PFunDDS.dom
        (fresh_rank_tape_dds (X := X) (H := H) q tape) :=
    ⟨hne, hlen⟩
  exact
    ⟨PFunDDS.output
        (fresh_rank_tape_dds (X := X) (H := H) q tape) l hdom,
      (Part.some_get hdom).symm⟩

/-- On a fixed input vector, the CR18 system event for the lazy cache is
exactly equality with the deterministic fresh-rank expansion. -/
private theorem transcript_system_event_fresh_rank_tape_iff
    {q : Nat} (tape : Fin q → H)
    (inputs : Fin q → X) (outputs : Fin q → H) :
    PFunPDE.transcriptSystemEvent
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H)
        (vectorOfFunction inputs) (vectorOfFunction outputs)
        (fresh_rank_tape_dds (X := X) (H := H) q tape) ↔
      fresh_rank_fixed_outputs inputs tape = outputs := by
  constructor
  · intro h
    funext i
    have hi := h i.1 i.2
    have hi' :
        (fresh_rank_tape_dds (X := X) (H := H) q tape).1
            (input_prefix inputs i) =
          Part.some (outputs i) := by
      simpa [PFunPDS.funView, Dist.RV.eval, vectorOfFunction,
        input_prefix] using hi
    have hdom :
        ((fresh_rank_tape_dds (X := X) (H := H) q tape).1
          (input_prefix inputs i)).Dom :=
      ⟨input_prefix_ne_nil inputs i,
        input_prefix_length_le inputs i⟩
    rw [← Part.some_get hdom] at hi'
    have hval := Part.some_inj.mp hi'
    change tape (fresh_rank_at inputs i) = outputs i at hval
    exact hval
  · intro h i hi
    have hout := congrFun h ⟨i, hi⟩
    have heval :
        (fresh_rank_tape_dds (X := X) (H := H) q tape).1
            (input_prefix inputs ⟨i, hi⟩) =
          Part.some (outputs ⟨i, hi⟩) := by
      have hdom :
          ((fresh_rank_tape_dds (X := X) (H := H) q tape).1
            (input_prefix inputs ⟨i, hi⟩)).Dom :=
        ⟨input_prefix_ne_nil inputs ⟨i, hi⟩,
          input_prefix_length_le inputs ⟨i, hi⟩⟩
      rw [← Part.some_get hdom]
      congr 1
    simpa [PFunPDS.funView, Dist.RV.eval, vectorOfFunction,
      input_prefix] using heval

/-- Sample a tape and expose its literal fresh-rank cached system. -/
private noncomputable def fresh_rank_tape_prob {q : Nat}
    (D : Dist.ProbDist (Fin q → H)) : PFunPDS.Prob X H :=
  Dist.PMF D (fresh_rank_tape_dds (X := X) (H := H) q)

/-- The CR18 system rectangle of a sampled fresh-rank cache is exactly the
fixed-schedule output mass of its tape.  This is the factor-level interface
used to prove both honest marginals. -/
private theorem fresh_rank_tape_system_factor_eq_output_law
    {q : Nat} (D : Dist.ProbDist (Fin q → H))
    (xv : List.Vector X q) (yv : List.Vector H q) :
    PFunPDE.transcriptSystemFactor
        (fresh_rank_tape_prob (X := X) D)
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv =
      Dist.fTransform
        (fresh_rank_fixed_outputs (functionOfVector xv))
        D.val (functionOfVector yv) := by
  rw [← vectorOfFunction_functionOfVector xv,
    ← vectorOfFunction_functionOfVector yv]
  unfold PFunPDE.transcriptSystemFactor
    fresh_rank_tape_prob Dist.PMF
  rw [Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro tape
  simpa only [functionOfVector_vectorOfFunction] using
    transcript_system_event_fresh_rank_tape_iff
      tape (functionOfVector xv) (functionOfVector yv)

/-- The real public system rectangle is the output-vector law of one uniform
permutation summed across the displayed blocks. -/
private theorem ordered_pair_real_system_factor_eq_output_law
    {q : Nat} (P : ordered_pair_partition X H)
    (xv : List.Vector X q) (yv : List.Vector H q) :
    PFunPDE.transcriptSystemFactor (ordered_pair_real P)
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv =
      Dist.fTransform
        (fun π : Equiv.Perm H =>
          fun i => ordered_pair_function P π (functionOfVector xv i))
        (Dist.uniform (Equiv.Perm H))
        (functionOfVector yv) := by
  unfold PFunPDE.transcriptSystemFactor ordered_pair_real
    PFunPDS.Prob.functionEvaluator Dist.PMF
  rw [Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro π
  change
    PFunPDE.transcriptSystemEvent
        (functionEvaluatorRV (ordered_pair_function P)) xv yv π ↔ _
  rw [transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor
  · intro h
    funext i
    simpa [functionOfVector] using h i
  · intro h i
    simpa [functionOfVector] using congr_fun h i

/-- The ideal public system rectangle is uniform-function evaluation on the
same fixed input vector. -/
private theorem ordered_pair_ideal_system_factor_eq_output_law
    {q : Nat} (xv : List.Vector X q) (yv : List.Vector H q) :
    PFunPDE.transcriptSystemFactor
        (ordered_pair_ideal (X := X) (H := H))
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv =
      Dist.fTransform
        (fun f : X → H => fun i => f (functionOfVector xv i))
        (Dist.uniform (X → H)) (functionOfVector yv) := by
  unfold PFunPDE.transcriptSystemFactor ordered_pair_ideal
    PFunPDS.Prob.urf Dist.PMF
  rw [Dist.mass_fTransform, Dist.fTransform_apply_eq_mass]
  apply Dist.mass_congr
  intro f
  change
    PFunPDE.transcriptSystemEvent
        (functionEvaluatorRV (fun f : X → H => f)) xv yv f ↔ _
  rw [transcriptSystemEvent_functionEvaluatorRV_iff]
  constructor
  · intro h
    funext i
    simpa [functionOfVector] using h i
  · intro h i
    simpa [functionOfVector] using congr_fun h i

/-- Real marginal theorem at CR18 rectangle level: the public oracle and the
fresh-rank representative are the same bounded random system law. -/
private theorem ordered_pair_real_system_factor_eq_fresh_rank_tape
    {q : Nat} (P : ordered_pair_partition X H)
    (xs : Fin q ↪ X)
    (xv : List.Vector X q) (yv : List.Vector H q) :
    PFunPDE.transcriptSystemFactor (ordered_pair_real P)
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv =
      PFunPDE.transcriptSystemFactor
        (fresh_rank_tape_prob
          (X := X) (ordered_pair_real_fresh_tape P xs))
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv := by
  rw [ordered_pair_real_system_factor_eq_output_law,
    fresh_rank_tape_system_factor_eq_output_law,
    ordered_pair_real_output_law_eq_fresh_rank_tape]

/-- Ideal marginal theorem at CR18 rectangle level. -/
private theorem ordered_pair_ideal_system_factor_eq_fresh_rank_tape
    {q : Nat} (xv : List.Vector X q) (yv : List.Vector H q) :
    PFunPDE.transcriptSystemFactor
        (ordered_pair_ideal (X := X) (H := H))
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv =
      PFunPDE.transcriptSystemFactor
        (fresh_rank_tape_prob
          (X := X) (ordered_pair_ideal_fresh_tape (H := H) q))
        ((fun s : PFunDDS.DDS X H => s) :
          PFunPDS.RV (PFunDDS.DDS X H) X H) xv yv := by
  rw [ordered_pair_ideal_system_factor_eq_output_law,
    fresh_rank_tape_system_factor_eq_output_law,
    ordered_pair_ideal_output_law_eq_fresh_rank_tape]

/-- Real marginal theorem against every deterministic adaptive environment. -/
private theorem ordered_pair_real_transcript_eq_fresh_rank_tape
    {q : Nat} (P : ordered_pair_partition X H)
    (xs : Fin q ↪ X) (E : PFunDDS.DDE X H) :
    PFunPDS.Prob.deterministicTranscriptDist
        (q := q) (ordered_pair_real P) E =
      PFunPDS.Prob.deterministicTranscriptDist
        (q := q)
        (fresh_rank_tape_prob
          (X := X) (ordered_pair_real_fresh_tape P xs)) E :=
  deterministic_transcript_dist_eq_of_system_factor_eq
    (ordered_pair_real P)
    (fresh_rank_tape_prob
      (X := X) (ordered_pair_real_fresh_tape P xs))
    (ordered_pair_real_system_factor_eq_fresh_rank_tape P xs) E

/-- Ideal marginal theorem against every deterministic adaptive environment. -/
private theorem ordered_pair_ideal_transcript_eq_fresh_rank_tape
    {q : Nat} (E : PFunDDS.DDE X H) :
    PFunPDS.Prob.deterministicTranscriptDist
        (q := q) (ordered_pair_ideal (X := X) (H := H)) E =
      PFunPDS.Prob.deterministicTranscriptDist
        (q := q)
        (fresh_rank_tape_prob
          (X := X) (ordered_pair_ideal_fresh_tape (H := H) q)) E :=
  deterministic_transcript_dist_eq_of_system_factor_eq
    (ordered_pair_ideal (X := X) (H := H))
    (fresh_rank_tape_prob
      (X := X) (ordered_pair_ideal_fresh_tape (H := H) q))
    (fun xv yv =>
      ordered_pair_ideal_system_factor_eq_fresh_rank_tape xv yv) E

/-- Deterministically replay a fresh-rank tape against a total deterministic
environment. -/
private noncomputable def fresh_rank_tape_replay {q : Nat}
    (E : PFunPDE.QQueryEnvironment X H q) (tape : Fin q → H) :
    PFunPDE.TranscriptPrefix X H q :=
  Classical.choose
    (PFunPDE.transcriptJointEvent_exists_of_total
      (fresh_rank_tape_dds (X := X) (H := H) q)
      (fun _ : PUnit.{1} => E.1)
      (fresh_rank_tape_dds_k_step_total (X := X) (H := H) q)
      (fun _ ys hlen => E.2 ys hlen)
      (tape, PUnit.unit.{1}))

/-- The replayed prefix is the unique joint transcript generated by this
tape and environment. -/
private theorem fresh_rank_tape_replay_spec {q : Nat}
    (E : PFunPDE.QQueryEnvironment X H q) (tape : Fin q → H) :
    PFunPDE.transcriptJointEvent
      (fresh_rank_tape_dds (X := X) (H := H) q)
      (fun _ : PUnit.{1} => E.1)
      (fresh_rank_tape_replay E tape)
      (tape, PUnit.unit.{1}) :=
  Classical.choose_spec
    (PFunPDE.transcriptJointEvent_exists_of_total
      (fresh_rank_tape_dds (X := X) (H := H) q)
      (fun _ : PUnit.{1} => E.1)
      (fresh_rank_tape_dds_k_step_total (X := X) (H := H) q)
      (fun _ ys hlen => E.2 ys hlen)
      (tape, PUnit.unit.{1}))

/-- The transcript law of a sampled fresh-rank representative is the
pushforward of its tape law through deterministic replay. -/
private theorem deterministic_transcript_dist_fresh_rank_tape_prob
    {q : Nat} (D : Dist.ProbDist (Fin q → H))
    (E : PFunPDE.QQueryEnvironment X H q) :
    PFunPDS.Prob.deterministicTranscriptDist
        (q := q) (fresh_rank_tape_prob (X := X) D) E.1 =
      Dist.fTransform (fresh_rank_tape_replay E) D.val := by
  ext t
  rw [Dist.fTransform_apply_eq_mass]
  unfold PFunPDS.Prob.deterministicTranscriptDist
  rw [PFunPDE.deterministicTranscriptLawDist_apply]
  unfold fresh_rank_tape_prob
  rw [PFunPDE.deterministicTranscriptLaw_pmf]
  rw [PFunPDE.transcriptLaw_apply,
    PFunPDE.transcriptDist_eq_mass_jointEvent]
  rw [Dist.prodProbDist_val, Dist.mass_prod_unitProbDist_right]
  congr 1
  apply Dist.mass_congr
  intro tape
  constructor
  · intro ht
    exact
      (PFunPDE.transcriptJointEvent_unique
        (fresh_rank_tape_dds (X := X) (H := H) q)
        (fun _ : PUnit.{1} => E.1)
        t (fresh_rank_tape_replay E tape)
        (tape, PUnit.unit.{1})
        ht (fresh_rank_tape_replay_spec E tape)).symm
  · intro ht
    subst t
    exact fresh_rank_tape_replay_spec E tape

end FreshRankRepresentative

/-!
### Honest maximal coupling and the adaptive reduction

The two fresh-tape laws are now coupled maximally.  Their proved lazy
marginals let the same deterministic replay map handle every adaptive
environment.  Conversely, the fixed environment that queries the displayed
injective schedule reads the entire tape, so the coupling upper bound is
exact.
-/

section AdaptiveCoupling

/-- A maximal coupling of the honest real and ideal ordered-pair tapes. -/
noncomputable def ordered_pair_maximal_tape_coupling {q : Nat}
    (P : ordered_pair_partition X H) (xs : Fin q ↪ X) :
    DistCoupling
      (ordered_pair_real_fresh_tape P xs).val
      (ordered_pair_ideal_fresh_tape (H := H) q).val :=
  Classical.choose
    (RandomSystems.optimal_coupling_exists
      (ordered_pair_real_fresh_tape P xs).val
      (ordered_pair_ideal_fresh_tape (H := H) q).val
      (by
        rw [(ordered_pair_real_fresh_tape P xs).property,
          (ordered_pair_ideal_fresh_tape (H := H) q).property]))

/-- First marginal of the honest tape coupling. -/
theorem ordered_pair_maximal_tape_coupling_fst {q : Nat}
    (P : ordered_pair_partition X H) (xs : Fin q ↪ X) :
    Dist.fTransform Prod.fst
        (ordered_pair_maximal_tape_coupling P xs).joint =
      (ordered_pair_real_fresh_tape P xs).val :=
  (ordered_pair_maximal_tape_coupling P xs).marginal_fst

/-- Second marginal of the honest tape coupling. -/
theorem ordered_pair_maximal_tape_coupling_snd {q : Nat}
    (P : ordered_pair_partition X H) (xs : Fin q ↪ X) :
    Dist.fTransform Prod.snd
        (ordered_pair_maximal_tape_coupling P xs).joint =
      (ordered_pair_ideal_fresh_tape (H := H) q).val :=
  (ordered_pair_maximal_tape_coupling P xs).marginal_snd

/-- The coupling disagreement is exactly the tape statistical distance. -/
theorem ordered_pair_maximal_tape_coupling_disagreement {q : Nat}
    (P : ordered_pair_partition X H) (xs : Fin q ↪ X) :
    (ordered_pair_maximal_tape_coupling P xs).prDisagree =
      RandomSystems.statDist
        (ordered_pair_real_fresh_tape P xs).val
        (ordered_pair_ideal_fresh_tape (H := H) q).val :=
  (Classical.choose_spec
    (RandomSystems.optimal_coupling_exists
      (ordered_pair_real_fresh_tape P xs).val
      (ordered_pair_ideal_fresh_tape (H := H) q).val
      (by
        rw [(ordered_pair_real_fresh_tape P xs).property,
          (ordered_pair_ideal_fresh_tape (H := H) q).property]))).symm

/-- For every deterministic adaptive environment, transcript distance is at
most the actual disagreement probability of the honest maximal coupling. -/
theorem ordered_pair_deterministic_transcript_distance_le_coupling
    {q : Nat} (P : ordered_pair_partition X H)
    (xs : Fin q ↪ X) (E : PFunPDE.QQueryEnvironment X H q) :
    RandomSystems.statDist
        (PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (ordered_pair_real P) E.1)
        (PFunPDS.Prob.deterministicTranscriptDist
          (q := q) (ordered_pair_ideal (X := X) (H := H)) E.1) ≤
      (ordered_pair_maximal_tape_coupling P xs).prDisagree := by
  rw [ordered_pair_real_transcript_eq_fresh_rank_tape P xs E.1,
    ordered_pair_ideal_transcript_eq_fresh_rank_tape E.1,
    deterministic_transcript_dist_fresh_rank_tape_prob,
    deterministic_transcript_dist_fresh_rank_tape_prob]
  exact
    (RandomSystems.statDist_fTransform_le
      (ordered_pair_real_fresh_tape P xs).val
      (ordered_pair_ideal_fresh_tape (H := H) q).val
      (fresh_rank_tape_replay E)).trans
      (RandomSystems.coupling_bound
        (ordered_pair_maximal_tape_coupling P xs))

/-- Paper Theorem 30.  For any available injective schedule of length `q`,
the maximum adaptive advantage is exactly the statistical distance between
the two honest fresh-tape laws. -/
theorem ordered_pair_advantage_eq_fresh_tape_distance
    (P : ordered_pair_partition X H) (q : Nat)
    (xs : Fin q ↪ X) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (ordered_pair_real P)
        (ordered_pair_ideal (X := X) (H := H)) =
      (RandomSystems.statDist
        (ordered_pair_real_fresh_tape P xs).val
        (ordered_pair_ideal_fresh_tape (H := H) q).val : ℝ) := by
  apply le_antisymm
  swap
  · let E : PFunPDE.QQueryEnvironment X H q :=
      ⟨fixedQueryDDE (Y := H) xs,
        fun ys hys =>
          fixedQueryEnvironment_KQueryTotal
            (Y := H) xs PUnit.unit.{1} ys hys⟩
    have h :=
      PFunPDS.Prob.deterministicTranscriptDist_statDist_le_adaptiveTranscriptAdvantage
        (q := q) (ordered_pair_real P)
        (ordered_pair_ideal (X := X) (H := H)) E
    have hreal :
        PFunPDS.Prob.deterministicTranscriptDist
            (q := q) (ordered_pair_real P) E.1 =
          fixedInputLiftDist xs
            (ordered_pair_real_fresh_tape P xs).val := by
      exact
        PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
          ⟨Dist.uniform (Equiv.Perm H),
            Dist.uniform_isProbDist⟩
          (ordered_pair_function P) xs
    have hideal :
        PFunPDS.Prob.deterministicTranscriptDist
            (q := q)
            (ordered_pair_ideal (X := X) (H := H)) E.1 =
          fixedInputLiftDist xs
            (ordered_pair_ideal_fresh_tape (H := H) q).val := by
      change
        PFunPDS.Prob.fixedQueryTranscriptDist
            (ordered_pair_ideal (X := X) (H := H)) xs =
          fixedInputLiftDist xs (Dist.uniform (Fin q → H))
      unfold ordered_pair_ideal
      rw [PFunPDS.Prob.fixedQueryTranscriptDist_urf,
        PFunPDS.uniformP_val,
        uniformFunction_eval_uniform xs xs.injective]
    rw [hreal, hideal] at h
    simpa only [fixedInputLiftDist,
      RandomSystems.statDist_fTransform_injective
        _ _ _ (fixedInputTranscriptPrefix_injective xs)] using h
  · apply PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise
      (ordered_pair_real P)
      (ordered_pair_ideal (X := X) (H := H))
      (RandomSystems.statDist
        (ordered_pair_real_fresh_tape P xs).val
        (ordered_pair_ideal_fresh_tape (H := H) q).val)
    intro E
    rw [← ordered_pair_maximal_tape_coupling_disagreement P xs]
    exact
      ordered_pair_deterministic_transcript_distance_le_coupling
        P xs E

end AdaptiveCoupling

/-!
### Exact ordered-matching tape law

Only after the honest tape marginal is established do we count its fibers.
The count below is a secondary exact certificate; it will not occur in the
closed numerical headline theorem.
-/

section ExactTapeLaw

/-- Paper Definition 29.  Number of ordered endpoint embeddings whose two
values in every block sum to the prescribed output. -/
def ordered_matching_compatible_count {m : Nat}
    (y : Fin m → H) : Nat :=
  ((Finset.univ : Finset (Fin (m * 2) ↪ H)).filter
    (fun a => ordered_pair_endpoint_sums a = y)).card

/-- Exact point mass of the canonical uniform ordered-matching tape. -/
theorem ordered_pair_real_fresh_tape_apply {m : Nat}
    (P : ordered_pair_partition X H) (xs : Fin m ↪ X)
    (y : Fin m → H) :
    (ordered_pair_real_fresh_tape P xs).val y =
      (ordered_matching_compatible_count y : NNReal) /
        ((Fintype.card H).descFactorial (m * 2) : NNReal) := by
  rw [ordered_pair_real_fresh_tape_eq_uniform_matching]
  letI : Nonempty (Fin (m * 2) ↪ H) :=
    ⟨ordered_pair_endpoint_inputs P xs⟩
  unfold ordered_pair_uniform_endpoint_embedding
  rw [Dist.fTransform_uniform_apply]
  rw [Fintype.card_embedding_eq, Fintype.card_fin]
  rfl

/-- Exact point mass of the ideal fresh tape. -/
theorem ordered_pair_ideal_fresh_tape_apply
    (m : Nat) (y : Fin m → H) :
    (ordered_pair_ideal_fresh_tape (H := H) m).val y =
      1 / ((Fintype.card H ^ m : Nat) : NNReal) := by
  change Dist.uniform (Fin m → H) y = _
  rw [Dist.uniform_apply, Fintype.card_fun, Fintype.card_fin]

/-- The ordered-matching fibers partition the full endpoint-embedding
space. -/
theorem ordered_matching_compatible_count_sum (m : Nat) :
    ∑ y : Fin m → H, ordered_matching_compatible_count y =
      (Fintype.card H).descFactorial (m * 2) := by
  unfold ordered_matching_compatible_count
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin (m * 2) ↪ H)))
      (t := (Finset.univ : Finset (Fin m → H)))
      (f := ordered_pair_endpoint_sums)
      (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin] using hpartition.symm

/-- Paper Theorem 30 on the unsaturated range: exact finite
compatible-count characterization of the maximum adaptive advantage. -/
theorem ordered_pair_advantage_eq_count_distance_of_le_card
    (P : ordered_pair_partition X H) (q : Nat)
    (hq : q ≤ Fintype.card X) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (ordered_pair_real P)
        (ordered_pair_ideal (X := X) (H := H)) =
      (1 / 2 : ℝ) *
        ∑ y : Fin q → H,
          |(((ordered_matching_compatible_count y : NNReal) /
              ((Fintype.card H).descFactorial (q * 2) : NNReal) :
              NNReal) : ℝ) -
            ((1 / ((Fintype.card H ^ q : Nat) : NNReal) :
              NNReal) : ℝ)| := by
  obtain ⟨xs⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin q) (β := X) (by simpa using hq)
  rw [ordered_pair_advantage_eq_fresh_tape_distance P q xs]
  change
    (RandomSystems.statDist
      (ordered_pair_real_fresh_tape P xs).val
      (ordered_pair_ideal_fresh_tape (H := H) q).val : ℝ) = _
  rw [coe_statDist_eq_half_sum_abs
    (ordered_pair_real_fresh_tape P xs)
    (ordered_pair_ideal_fresh_tape (H := H) q)]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [ordered_pair_real_fresh_tape_apply P xs y,
    ordered_pair_ideal_fresh_tape_apply q y]

end ExactTapeLaw

/-!
### The one-query algebraic obstruction

At one fresh query the endpoint injection is simply a uniform ordered pair
of distinct group elements.  Counting the forbidden diagonal gives the
square/doubling-root formula directly; no higher-query matching machinery is
used in this audit.
-/

section OneQueryObstruction

private abbrev ordered_distinct_pair (H : Type*) :=
  Sigma fun a : H => {b : H // b ≠ a}

private def ordered_distinct_pair_output
    (p : ordered_distinct_pair H) : H :=
  p.1 + p.2.1

/-- Paper Proposition 31.  Number of solutions of `a + a = y`. -/
def ordered_pair_double_root_count (y : H) : Nat :=
  ((Finset.univ : Finset H).filter (fun a => a + a = y)).card

private theorem ordered_distinct_pair_card :
    Fintype.card (ordered_distinct_pair H) =
      Fintype.card H * (Fintype.card H - 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype_compl
    (p := fun b : H => b = _)]
  simp

/-- For a prescribed sum `y`, exactly the doubling roots are excluded from
the choice of the first endpoint. -/
private theorem ordered_distinct_pair_output_fiber_card (y : H) :
    ((Finset.univ : Finset (ordered_distinct_pair H)).filter
      (fun p => ordered_distinct_pair_output p = y)).card =
      Fintype.card H - ordered_pair_double_root_count y := by
  have hcard :
      ((Finset.univ : Finset H).filter
        (fun a => a + a ≠ y)).card =
        Fintype.card H - ordered_pair_double_root_count y := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl]
    rw [Fintype.card_subtype]
    rfl
  rw [← hcard]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro haa
    apply p.2.2
    have hout := (Finset.mem_filter.mp hp).2
    apply add_left_cancel (a := p.1)
    calc
      p.1 + p.2.1 = y := hout
      _ = p.1 + p.1 := haa.symm
  · intro p hp q hq hpq
    rcases p with ⟨a, b⟩
    rcases q with ⟨a', b'⟩
    dsimp at hpq
    subst a'
    congr 1
    apply Subtype.ext
    have hpout := (Finset.mem_filter.mp hp).2
    have hqout := (Finset.mem_filter.mp hq).2
    apply add_left_cancel (a := a)
    calc
      a + b.1 = y := hpout
      _ = a + b'.1 := hqout.symm
  · intro a ha
    have hane : a + a ≠ y := (Finset.mem_filter.mp ha).2
    have hba : -a + y ≠ a := by
      intro h
      apply hane
      calc
        a + a = a + (-a + y) := by rw [h]
        _ = y := by simp [add_assoc]
    refine ⟨⟨a, ⟨-a + y, hba⟩⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        by simp [ordered_distinct_pair_output, add_assoc]⟩

/-- A length-two embedding is the same object as an ordered pair of distinct
elements. -/
private def fin_two_embedding_equiv_ordered_distinct_pair :
    (Fin 2 ↪ H) ≃ ordered_distinct_pair H where
  toFun a :=
    ⟨a 0, ⟨a 1,
      fun h => Fin.zero_ne_one (a.injective h.symm)⟩⟩
  invFun p :=
    { toFun := ![p.1, p.2.1]
      inj' := by
        intro i j h
        fin_cases i <;> fin_cases j
        · rfl
        · exact (p.2.2 h.symm).elim
        · exact (p.2.2 h).elim
        · rfl }
  left_inv a := by
    apply Function.Embedding.ext
    intro i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b⟩
    rfl

/-- Specializing the compatible matching count to one block gives the
doubling-root obstruction. -/
private theorem ordered_matching_compatible_count_one (y : H) :
    ordered_matching_compatible_count
        (fun _ : Fin 1 => y) =
      Fintype.card H - ordered_pair_double_root_count y := by
  rw [← ordered_distinct_pair_output_fiber_card y]
  unfold ordered_matching_compatible_count
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact
    Fintype.card_congr
      ((fin_two_embedding_equiv_ordered_distinct_pair
        (H := H)).subtypeEquiv (fun a => by
          constructor
          · intro h
            have h0 := congrFun h 0
            simpa [ordered_pair_endpoint_sums,
              ordered_distinct_pair_output] using h0
          · intro h
            funext i
            fin_cases i
            simpa [ordered_pair_endpoint_sums,
              ordered_distinct_pair_output] using h))

/-- Paper Proposition 31, first formula: exact real one-query point mass. -/
theorem ordered_pair_one_query_law
    (P : ordered_pair_partition X H) (xs : Fin 1 ↪ X)
    (y : H) :
    (ordered_pair_real_fresh_tape P xs).val
        (fun _ : Fin 1 => y) =
      ((Fintype.card H - ordered_pair_double_root_count y : Nat) :
          NNReal) /
        ((Fintype.card H * (Fintype.card H - 1) : Nat) :
          NNReal) := by
  rw [ordered_pair_real_fresh_tape_apply,
    ordered_matching_compatible_count_one]
  simp [Nat.descFactorial, Nat.mul_comm]

/-- A partition supplies a canonical one-point fresh schedule. -/
private def ordered_pair_one_query_embedding
    (P : ordered_pair_partition X H) : Fin 1 ↪ X where
  toFun _ := P.symm 0 |>.1
  inj' _ _ _ := Subsingleton.elim _ _

/-- An ordered-pair partition over a group forces at least two output
elements. -/
private theorem ordered_pair_partition_nontrivial
    (P : ordered_pair_partition X H) : Nontrivial H := by
  let x : X := (P.symm 0).1
  refine
    ⟨(show X × Fin 2 ≃ H from P) (x, 0),
      (show X × Fin 2 ≃ H from P) (x, 1), ?_⟩
  intro h
  have hp : (x, (0 : Fin 2)) = (x, (1 : Fin 2)) :=
    P.injective h
  exact Fin.zero_ne_one (congrArg Prod.snd hp)

private theorem ordered_pair_double_root_count_le (y : H) :
    ordered_pair_double_root_count y ≤ Fintype.card H :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Paper Proposition 31, exact one-query algebraic obstruction. -/
theorem ordered_pair_one_query_advantage
    (P : ordered_pair_partition X H) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 1) (ordered_pair_real P)
        (ordered_pair_ideal (X := X) (H := H)) =
      (1 / (2 * (Fintype.card H : ℝ) *
        ((Fintype.card H : ℝ) - 1))) *
        ∑ y : H,
          |(ordered_pair_double_root_count y : ℝ) - 1| := by
  letI : Nontrivial H := ordered_pair_partition_nontrivial P
  let xs : Fin 1 ↪ X := ordered_pair_one_query_embedding P
  rw [ordered_pair_advantage_eq_fresh_tape_distance P 1 xs]
  rw [coe_statDist_eq_half_sum_abs
    (ordered_pair_real_fresh_tape P xs)
    (ordered_pair_ideal_fresh_tape (H := H) 1)]
  change
    (1 / 2 : ℝ) *
        ∑ z : Fin 1 → H,
          |((ordered_pair_real_fresh_tape P xs).val z : ℝ) -
            ((ordered_pair_ideal_fresh_tape (H := H) 1).val z : ℝ)| =
      _
  have hsum :
      (∑ z : Fin 1 → H,
          |((ordered_pair_real_fresh_tape P xs).val z : ℝ) -
            ((ordered_pair_ideal_fresh_tape (H := H) 1).val z : ℝ)|) =
        ∑ y : H,
          |((ordered_pair_real_fresh_tape P xs).val
                (fun _ => y) : ℝ) -
            ((ordered_pair_ideal_fresh_tape (H := H) 1).val
                (fun _ => y) : ℝ)| := by
    let e : H ≃ (Fin 1 → H) :=
      (Equiv.funUnique (Fin 1) H).symm
    exact
      (e.sum_comp
        (fun z =>
          |((ordered_pair_real_fresh_tape P xs).val z : ℝ) -
            ((ordered_pair_ideal_fresh_tape (H := H) 1).val z : ℝ)|)).symm
  rw [hsum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [ordered_pair_one_query_law P xs y,
    ordered_pair_ideal_fresh_tape_apply 1 (fun _ => y)]
  simp only [Nat.pow_one]
  push_cast
  have hNnat : 0 < Fintype.card H := Fintype.card_pos
  have hN : (Fintype.card H : ℝ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < Fintype.card H := by
    exact_mod_cast hNnat
  have hNm1 : ((Fintype.card H : ℝ) - 1) ≠ 0 := by
    have hlt : (1 : ℝ) < Fintype.card H := by
      exact_mod_cast
        (Fintype.one_lt_card_iff_nontrivial.mpr
          (inferInstance : Nontrivial H))
    exact sub_ne_zero.mpr (ne_of_gt hlt)
  have hNm1pos : (0 : ℝ) < (Fintype.card H : ℝ) - 1 := by
    exact sub_pos.mpr (by
      exact_mod_cast
        (Fintype.one_lt_card_iff_nontrivial.mpr
          (inferInstance : Nontrivial H)))
  have hrle :
      ordered_pair_double_root_count y ≤ Fintype.card H :=
    ordered_pair_double_root_count_le y
  rw [NNReal.coe_sub (by exact_mod_cast hrle)]
  rw [NNReal.coe_sub (by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNnat.ne'))]
  push_cast
  have hinside :
      ((Fintype.card H : ℝ) -
          ordered_pair_double_root_count y) /
            ((Fintype.card H : ℝ) *
              ((Fintype.card H : ℝ) - 1)) -
          1 / (Fintype.card H : ℝ) =
        (1 - (ordered_pair_double_root_count y : ℝ)) /
          ((Fintype.card H : ℝ) *
            ((Fintype.card H : ℝ) - 1)) := by
    field_simp [hN, hNm1]
    ring
  rw [hinside, abs_div, abs_sub_comm (1 : ℝ),
    abs_of_pos (mul_pos hNpos hNm1pos)]
  field_simp [hN, hNm1]

end OneQueryObstruction

section AbelianOneQuery

variable {A : Type*} [Fintype A] [AddCommGroup A]

private def ordered_pair_double_hom : A →+ A where
  toFun a := a + a
  map_zero' := by simp
  map_add' _ _ := by abel

private def ordered_pair_double_image : Finset A :=
  (Finset.univ : Finset A).image (fun a => a + a)

/-- Cardinality of the two-torsion subgroup, written as the zero fiber of
the doubling map. -/
def ordered_pair_two_torsion_count : Nat :=
  ordered_pair_double_root_count (0 : A)

private theorem zero_mem_ordered_pair_double_range :
    (0 : A) ∈ Set.range (ordered_pair_double_hom (A := A)) :=
  ⟨0, by simp [ordered_pair_double_hom]⟩

private theorem ordered_pair_double_root_count_eq_two_torsion_of_mem
    {y : A} (hy : y ∈ ordered_pair_double_image (A := A)) :
    ordered_pair_double_root_count y =
      ordered_pair_two_torsion_count (A := A) := by
  have hyrange :
      y ∈ Set.range (ordered_pair_double_hom (A := A)) := by
    rw [ordered_pair_double_image, Finset.mem_image] at hy
    obtain ⟨a, _, rfl⟩ := hy
    exact ⟨a, rfl⟩
  simpa [ordered_pair_double_root_count,
    ordered_pair_two_torsion_count,
    ordered_pair_double_hom] using
    (AddMonoidHom.card_fiber_eq_of_mem_range
      (ordered_pair_double_hom (A := A)) hyrange
      (zero_mem_ordered_pair_double_range (A := A)))

private theorem ordered_pair_double_root_count_eq_zero_of_not_mem
    {y : A} (hy : y ∉ ordered_pair_double_image (A := A)) :
    ordered_pair_double_root_count y = 0 := by
  unfold ordered_pair_double_root_count
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  apply hy
  obtain ⟨a, ha⟩ := hne
  rw [ordered_pair_double_image, Finset.mem_image]
  exact
    ⟨a, Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

/-- Every point in the doubling image has exactly the two-torsion
cardinality many preimages, and every point outside it has none. -/
theorem ordered_pair_double_root_count_abelian (y : A) :
    ordered_pair_double_root_count y =
      if y ∈ ordered_pair_double_image (A := A) then
        ordered_pair_two_torsion_count (A := A)
      else 0 := by
  by_cases hy : y ∈ ordered_pair_double_image (A := A)
  · rw [if_pos hy,
      ordered_pair_double_root_count_eq_two_torsion_of_mem hy]
  · rw [if_neg hy,
      ordered_pair_double_root_count_eq_zero_of_not_mem hy]

private theorem ordered_pair_double_image_card_mul_two_torsion :
    (ordered_pair_double_image (A := A)).card *
        ordered_pair_two_torsion_count (A := A) =
      Fintype.card A := by
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A))
      (t := ordered_pair_double_image (A := A))
      (f := fun a : A => a + a)
      (fun a _ => by simp [ordered_pair_double_image])
  rw [Finset.card_univ] at hpartition
  rw [hpartition]
  calc
    (ordered_pair_double_image (A := A)).card *
          ordered_pair_two_torsion_count (A := A) =
        ∑ _y ∈ ordered_pair_double_image (A := A),
          ordered_pair_two_torsion_count (A := A) := by simp
    _ = ∑ y ∈ ordered_pair_double_image (A := A),
        ((Finset.univ : Finset A).filter
          (fun a => a + a = y)).card := by
      apply Finset.sum_congr rfl
      intro y hy
      exact
        (ordered_pair_double_root_count_eq_two_torsion_of_mem
          hy).symm

private theorem ordered_pair_two_torsion_count_pos :
    0 < ordered_pair_two_torsion_count (A := A) := by
  unfold ordered_pair_two_torsion_count
    ordered_pair_double_root_count
  exact Finset.card_pos.mpr
    ⟨0, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simp⟩⟩

private theorem ordered_pair_sum_abs_double_root_sub_one :
    ∑ y : A, |(ordered_pair_double_root_count y : ℝ) - 1| =
      2 * ((ordered_pair_double_image (A := A)).card : ℝ) *
        ((ordered_pair_two_torsion_count (A := A) : ℝ) - 1) := by
  let f : A → ℝ :=
    fun y => |(ordered_pair_double_root_count y : ℝ) - 1|
  have ht_one :
      (1 : ℝ) ≤ ordered_pair_two_torsion_count (A := A) := by
    exact_mod_cast ordered_pair_two_torsion_count_pos (A := A)
  have hinside :
      ∑ y ∈ ordered_pair_double_image (A := A), f y =
        ((ordered_pair_double_image (A := A)).card : ℝ) *
          ((ordered_pair_two_torsion_count (A := A) : ℝ) - 1) := by
    calc
      ∑ y ∈ ordered_pair_double_image (A := A), f y =
          ∑ _y ∈ ordered_pair_double_image (A := A),
            |(ordered_pair_two_torsion_count (A := A) : ℝ) -
              1| := by
        apply Finset.sum_congr rfl
        intro y hy
        simp only [f]
        rw [ordered_pair_double_root_count_eq_two_torsion_of_mem
          hy]
      _ = ((ordered_pair_double_image (A := A)).card : ℝ) *
            ((ordered_pair_two_torsion_count (A := A) : ℝ) -
              1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht_one)]
        simp
        ring
  have houtside :
      ∑ y ∈ (ordered_pair_double_image (A := A))ᶜ, f y =
        ((ordered_pair_double_image (A := A))ᶜ.card : ℝ) := by
    calc
      ∑ y ∈ (ordered_pair_double_image (A := A))ᶜ, f y =
          ∑ _y ∈ (ordered_pair_double_image (A := A))ᶜ,
            (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hynot :
            y ∉ ordered_pair_double_image (A := A) := by
          simpa using hy
        simp [f,
          ordered_pair_double_root_count_eq_zero_of_not_mem hynot]
      _ = ((ordered_pair_double_image (A := A))ᶜ.card : ℝ) := by
        simp
  have hsplit :
      ∑ y : A, f y =
        ∑ y ∈ ordered_pair_double_image (A := A), f y +
          ∑ y ∈ (ordered_pair_double_image (A := A))ᶜ, f y := by
    have hs :=
      Finset.sum_sdiff
        (s₁ := ordered_pair_double_image (A := A))
        (s₂ := (Finset.univ : Finset A))
        (f := f)
        (Finset.subset_univ _)
    rw [← Finset.compl_eq_univ_sdiff] at hs
    linarith
  change (∑ y : A, f y) = _
  rw [hsplit, hinside, houtside, Finset.card_compl]
  have hIle :
      (ordered_pair_double_image (A := A)).card ≤
        Fintype.card A := by
    simpa using
      Finset.card_le_card
        (Finset.subset_univ
          (ordered_pair_double_image (A := A)))
  rw [Nat.cast_sub hIle]
  have hcard :
      ((ordered_pair_double_image (A := A)).card : ℝ) *
          (ordered_pair_two_torsion_count (A := A) : ℝ) =
        Fintype.card A := by
    exact_mod_cast
      ordered_pair_double_image_card_mul_two_torsion (A := A)
  linarith

/-- Paper Proposition 31, abelian specialization. -/
theorem ordered_pair_abelian_one_query_advantage
    (P : ordered_pair_partition X A) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := 1) (ordered_pair_real P)
        (ordered_pair_ideal (X := X) (H := A)) =
      ((ordered_pair_two_torsion_count (A := A) : ℝ) - 1) /
        ((ordered_pair_two_torsion_count (A := A) : ℝ) *
          ((Fintype.card A : ℝ) - 1)) := by
  letI : Nontrivial A := ordered_pair_partition_nontrivial P
  rw [ordered_pair_one_query_advantage P,
    ordered_pair_sum_abs_double_root_sub_one]
  have hN : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hNm1 : ((Fintype.card A : ℝ) - 1) ≠ 0 := by
    have hlt : (1 : ℝ) < Fintype.card A := by
      exact_mod_cast
        (Fintype.one_lt_card_iff_nontrivial.mpr
          (inferInstance : Nontrivial A))
    exact sub_ne_zero.mpr (ne_of_gt hlt)
  have ht :
      (ordered_pair_two_torsion_count (A := A) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ordered_pair_two_torsion_count_pos (A := A)).ne'
  have hcard :
      ((ordered_pair_double_image (A := A)).card : ℝ) *
          (ordered_pair_two_torsion_count (A := A) : ℝ) =
        Fintype.card A := by
    exact_mod_cast
      ordered_pair_double_image_card_mul_two_torsion (A := A)
  field_simp [hN, hNm1, ht]
  nlinarith

end AbelianOneQuery

end OrderedPairPartition


end RandomSystems.SoP
