/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.Symmetric.SpongeBDPV

/-!
# BDPV Lemma 4 — the conditional structure of a run

`SpongeBDPV` has the two probabilistic halves of Lemma 4 (`freshCapacity` is a
uniform draw from `C \ (R ∪ O)`; the resulting per-step distance) and the
coin-locality of a run.  What a lazy-sampling hybrid additionally needs is the
*structure* of the conditioning: after fixing an interaction, which seed
coordinates remain free.

Three facts carry that, and they are proved here.

* **Locality in the oracle.**  A run reads the random oracle only at the cells
  its own paths name (`run_congr_oracle`).  This is the oracle twin of
  `run_congr_coins`; it is harder only because the set of cells read is itself
  produced by the run, so the induction has to be over the *resulting* graph's
  paths, which grow monotonically (`paths_subset_answer`).
* **The paths are a tree with distinct words** (`WordsNodup`), which is what
  makes each rooted answer consume a *fresh* oracle cell once `unpad` is
  injective.  The invariant needs a companion (`PathInv`) recording that every
  non-empty path is a parent path extended by one block through an edge that
  the graph has already fixed — without it, "the new word is new" has nothing
  to induct on.
* **The consumed cells** (`consumedCells`) and the fact that a fresh rooted
  query consumes a cell outside them.
-/

noncomputable section

namespace RandomSystemsCC.Symmetric.SpongeBDPV

universe u

variable {A C M : Type u}

section Structure

variable [DecidableEq A] [DecidableEq C] [AddCommGroup A]
variable (root : Node A C) (capacities : List C) (unpad : List A → Option M)
variable {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
variable (coinC : Node A C → Equiv.Perm C)

/-! ## Paths only grow -/

omit [AddCommGroup A] in
/-- The outgoing edge of a graph extended at a *fresh* query, read at that
query: the new edge is the one `find?` meets first. -/
theorem outgoing_cons_self (graph : Graph A C) (s t : Node A C) :
    (⟨(s, t) :: graph.edges, graph.paths⟩ : Graph A C).outgoing s = some t := by
  simp [Graph.outgoing]

omit [AddCommGroup A] in
/-- Extending the edge list at a fresh query leaves every other query's
outgoing edge alone. -/
theorem outgoing_cons_of_ne (graph : Graph A C) (s t s' : Node A C)
    (hne : s' ≠ s) (paths' : List (Node A C × List A)) :
    (⟨(s, t) :: graph.edges, paths'⟩ : Graph A C).outgoing s'
      = graph.outgoing s' := by
  simp [Graph.outgoing, List.find?_cons_of_neg, Ne.symm hne]

/-- `answer` only ever prepends to `paths`. -/
theorem paths_subset_answer (graph : Graph A C) (s : Node A C) :
    graph.paths ⊆
      (answer root capacities unpad oracle coinA coinC graph s).2.paths := by
  intro entry hentry
  unfold answer
  cases hout : graph.outgoing s with
  | some t => simpa [hout] using hentry
  | none =>
      cases hpath : graph.pathAt s with
      | none => exact hentry
      | some e =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none => exact hentry
          | some fresh => exact List.mem_cons_of_mem _ hentry

/-- A run's paths only grow as queries are appended. -/
theorem paths_subset_run_concat (us : List (Node A C)) (u : Node A C) :
    (run root capacities unpad oracle coinA coinC us).paths ⊆
      (run root capacities unpad oracle coinA coinC (us ++ [u])).paths := by
  rw [run_concat]
  exact paths_subset_answer root capacities unpad oracle coinA coinC _ u

/-! ## The cells of the random oracle a graph has consumed -/

/-- The oracle cell a path word names, when it names one: strip the trailing
zero blocks, unpad, and read the block index. -/
def cellOf (unpad : List A → Option M) (w : List A) : Option (M × ℕ) :=
  (unpad (stripZeros w).1).map fun m => (m, (stripZeros w).2)

/-- The oracle cells a graph's paths name. -/
def consumedCells (unpad : List A → Option M) (graph : Graph A C) :
    Set (M × ℕ) :=
  {cell | ∃ entry ∈ graph.paths, cellOf unpad entry.2 = some cell}

/-- Two oracle assignments **agree on a graph's consumed cells**. -/
def AgreeOn (unpad : List A → Option M) {outBlocks : ℕ}
    (oracle oracle' : M → Fin outBlocks → A) (graph : Graph A C) : Prop :=
  ∀ (m : M) (j : ℕ) (h : j < outBlocks), (m, j) ∈ consumedCells unpad graph →
    oracle m ⟨j, h⟩ = oracle' m ⟨j, h⟩

omit [DecidableEq C] in
theorem agreeOn_mono {oracle' : M → Fin outBlocks → A} {graph graph' : Graph A C}
    (hsub : graph.paths ⊆ graph'.paths)
    (h : AgreeOn unpad oracle oracle' graph') :
    AgreeOn unpad oracle oracle' graph := by
  rintro m j hj ⟨entry, hentry, hcell⟩
  exact h m j hj ⟨entry, hsub hentry, hcell⟩

/-! ## Locality in the oracle -/

/-- The path a rooted step creates is in the graph it produces. -/
theorem mem_paths_answer_rooted (graph : Graph A C) (s : Node A C)
    {entry : Node A C × List A} {fresh : C} (hout : graph.outgoing s = none)
    (hpath : graph.pathAt s = some entry)
    (hfresh : freshCapacity capacities (coinC s) graph = some fresh) :
    ∃ node : Node A C,
      (node, entry.2 ++ [s.1 - entry.1.1]) ∈
        (answer root capacities unpad oracle coinA coinC graph s).2.paths := by
  simp only [answer, hout, hpath, hfresh]
  exact ⟨_, List.mem_cons_self⟩

/-- `answer` reads the oracle only at the cell its own new path names — and
only when it actually creates that path. -/
theorem answer_congr_oracle {oracle' : M → Fin outBlocks → A}
    (graph : Graph A C) (s : Node A C)
    (hag : graph.outgoing s = none →
      ∀ (entry : Node A C × List A), graph.pathAt s = some entry →
      ∀ fresh : C, freshCapacity capacities (coinC s) graph = some fresh →
      ∀ (m : M) (h : (stripZeros (entry.2 ++ [s.1 - entry.1.1])).2 < outBlocks),
        unpad (stripZeros (entry.2 ++ [s.1 - entry.1.1])).1 = some m →
          oracle m ⟨_, h⟩ = oracle' m ⟨_, h⟩) :
    answer root capacities unpad oracle coinA coinC graph s
      = answer root capacities unpad oracle' coinA coinC graph s := by
  unfold answer
  cases hout : graph.outgoing s with
  | some t => rfl
  | none =>
      cases hpath : graph.pathAt s with
      | none => rfl
      | some entry =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none => rfl
          | some fresh =>
              cases hunp : unpad (stripZeros (entry.2 ++ [s.1 - entry.1.1])).1 with
              | none => simp only [hunp]
              | some message =>
                  by_cases hb : (stripZeros (entry.2 ++ [s.1 - entry.1.1])).2
                      < outBlocks
                  · simp only [hunp, dif_pos hb,
                      hag hout entry hpath fresh hfresh message hb hunp]
                  · simp only [hunp, dif_neg hb]

/-- **A run reads the oracle only at the cells its own paths name.**  The
induction is over the *resulting* graph's paths, which is what makes it go
through: those grow monotonically (`paths_subset_run_concat`), and the one new
cell a step can read is named by the path that step creates. -/
theorem run_congr_oracle {oracle' : M → Fin outBlocks → A} :
    ∀ us : List (Node A C),
      AgreeOn unpad oracle oracle'
          (run root capacities unpad oracle coinA coinC us) →
        run root capacities unpad oracle coinA coinC us
          = run root capacities unpad oracle' coinA coinC us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton us u ih =>
      intro hag
      have hsub := paths_subset_run_concat root capacities unpad oracle coinA
        coinC us u
      have hrun := ih (agreeOn_mono unpad oracle hsub hag)
      rw [run_concat, run_concat, ← hrun]
      refine congrArg Prod.snd (answer_congr_oracle root capacities unpad oracle
        coinA coinC _ u fun hout entry hentry fresh hfresh m hb hunp => ?_)
      obtain ⟨node, hnode⟩ := mem_paths_answer_rooted root capacities unpad
        oracle coinA coinC _ u hout hentry hfresh
      refine hag m _ hb ⟨(node, entry.2 ++ [u.1 - entry.1.1]), ?_, ?_⟩
      · rw [run_concat]
        exact hnode
      · rw [cellOf, hunp]
        rfl

/-! ## `stripZeros` is injective

A path word is recovered from its stripped form and the number of zero blocks
removed, so distinct paths name distinct `(message, index)` cells once `unpad`
is injective. -/

omit [DecidableEq C] in
theorem stripZeros_reconstruct (p : List A) :
    p = (stripZeros p).1 ++ List.replicate (stripZeros p).2 0 := by
  have hzero : ∀ x ∈ List.takeWhile (fun a : A => decide (a = 0)) p.reverse,
      x = (0 : A) := by
    intro x hx
    have hd := List.mem_takeWhile_imp (p := fun a : A => decide (a = 0)) hx
    simpa using hd
  have hrep : List.takeWhile (fun a : A => decide (a = 0)) p.reverse
      = List.replicate
          (List.takeWhile (fun a : A => decide (a = 0)) p.reverse).length 0 :=
    List.eq_replicate_iff.mpr ⟨rfl, hzero⟩
  calc p = (List.takeWhile (fun a : A => decide (a = 0)) p.reverse
            ++ List.dropWhile (fun a : A => decide (a = 0)) p.reverse).reverse := by
        rw [List.takeWhile_append_dropWhile, List.reverse_reverse]
    _ = (List.dropWhile (fun a : A => decide (a = 0)) p.reverse).reverse
          ++ (List.takeWhile (fun a : A => decide (a = 0)) p.reverse).reverse := by
        rw [List.reverse_append]
    _ = (stripZeros p).1 ++ List.replicate (stripZeros p).2 0 := by
        simp only [stripZeros]
        exact congrArg _ (by conv_lhs => rw [hrep, List.reverse_replicate])

omit [DecidableEq C] in
theorem stripZeros_injective : Function.Injective (stripZeros (A := A)) := by
  intro p p' h
  rw [stripZeros_reconstruct p, stripZeros_reconstruct p', h]

/-! ## The path tree

Two invariants, maintained together.  `WordsNodup` is the one the freshness of
oracle cells rests on; `PathInv` is what it is proved by induction *from* —
without a record of how a non-empty path was built, "the new word is new" has
nothing to contradict. -/

/-- The words of a graph's paths are pairwise distinct. -/
def WordsNodup (graph : Graph A C) : Prop :=
  (graph.paths.map Prod.snd).Nodup

/-- Every non-empty path is a parent path extended by one block, through an
edge the graph has already fixed. -/
def PathInv (graph : Graph A C) : Prop :=
  ∀ entry ∈ graph.paths, entry.2 = [] ∨
    ∃ parent ∈ graph.paths, ∃ b : A,
      entry.2 = parent.2 ++ [b] ∧
      graph.outgoing (parent.1.1 + b, parent.1.2) = some entry.1

omit [DecidableEq A] [DecidableEq C] [AddCommGroup A] in
theorem init_wordsNodup : WordsNodup (Graph.init (A := A) (C := C) root) := by
  simp [WordsNodup, Graph.init]

theorem init_pathInv : PathInv (Graph.init (A := A) (C := C) root) := by
  intro entry hentry
  left
  have : entry = (root, ([] : List A)) := by simpa [Graph.init] using hentry
  rw [this]

omit [DecidableEq A] [AddCommGroup A] in
/-- The entry `pathAt` finds is a path of the graph carrying `s`'s capacity. -/
theorem pathAt_spec {graph : Graph A C} {s : Node A C}
    {entry : Node A C × List A} (hpath : graph.pathAt s = some entry) :
    entry ∈ graph.paths ∧ entry.1.2 = s.2 :=
  ⟨List.mem_of_find?_eq_some hpath, by simpa using List.find?_some hpath⟩

/-- **The word a rooted step creates is new.**  If it were already a path, that
path's own parent would have to be the entry `pathAt` just found — by
`WordsNodup` — and the edge `PathInv` records for it would be an outgoing edge
at the very query we assumed fresh. -/
theorem word_new_notMem {graph : Graph A C} {s : Node A C}
    {entry : Node A C × List A} (hnodup : WordsNodup graph)
    (hinv : PathInv graph) (hout : graph.outgoing s = none)
    (hpath : graph.pathAt s = some entry) :
    entry.2 ++ [s.1 - entry.1.1] ∉ graph.paths.map Prod.snd := by
  obtain ⟨hmem, hcap⟩ := pathAt_spec hpath
  intro hcontra
  obtain ⟨e, he, hew⟩ := List.mem_map.mp hcontra
  rcases hinv e he with hnil | ⟨parent, hparent, b', hword, hedge⟩
  · rw [hnil] at hew
    simp at hew
  · have hsplit : entry.2 = parent.2 ∧ s.1 - entry.1.1 = b' := by
      have hpair := hew.symm.trans hword
      exact ⟨(List.append_inj' hpair rfl).1,
        List.cons.inj ((List.append_inj' hpair rfl).2) |>.1⟩
    have hentryparent : entry = parent :=
      List.inj_on_of_nodup_map hnodup hmem hparent hsplit.1
    rw [← hentryparent, ← hsplit.2, add_sub_cancel, hcap] at hedge
    exact absurd (hedge.symm.trans hout) (by simp)

/-- A fresh rooted step consumes an oracle cell the graph has not consumed —
the point at which `unpad`'s injectivity enters, and the reason the answer's
bitrate part is a *fresh* uniform value. -/
theorem cellOf_new_notMem_consumed
    (hunpadInj : ∀ (w w' : List A) (m : M),
      unpad w = some m → unpad w' = some m → w = w')
    {graph : Graph A C} {s : Node A C} {entry : Node A C × List A}
    (hnodup : WordsNodup graph) (hinv : PathInv graph)
    (hout : graph.outgoing s = none) (hpath : graph.pathAt s = some entry)
    {cell : M × ℕ}
    (hcell : cellOf unpad (entry.2 ++ [s.1 - entry.1.1]) = some cell) :
    cell ∉ consumedCells unpad graph := by
  rintro ⟨e, he, hecell⟩
  rw [cellOf, Option.map_eq_some_iff] at hcell hecell
  obtain ⟨m, hm, hmc⟩ := hcell
  obtain ⟨m', hm', hmc'⟩ := hecell
  obtain ⟨hmm, hsnd⟩ := Prod.mk.inj (hmc'.trans hmc.symm)
  subst hmm
  have hfst : (stripZeros e.2).1
      = (stripZeros (entry.2 ++ [s.1 - entry.1.1])).1 :=
    hunpadInj _ _ _ hm' hm
  have hword : e.2 = entry.2 ++ [s.1 - entry.1.1] := by
    refine stripZeros_injective ?_
    rw [Prod.ext_iff]
    exact ⟨hfst, hsnd⟩
  exact word_new_notMem hnodup hinv hout hpath
    (List.mem_map.mpr ⟨e, he, hword⟩)

/-! ### The invariants are maintained -/

/-- `PathInv` survives adding an edge at a query that had none: the edges it
records are all at queries that already had one. -/
theorem pathInv_cons_edge {graph : Graph A C} {s node : Node A C}
    (hout : graph.outgoing s = none) (hinv : PathInv graph)
    (paths' : List (Node A C × List A))
    (hpaths : ∀ entry ∈ paths', entry ∈ graph.paths ∨
      (∃ parent ∈ paths', ∃ b : A, entry.2 = parent.2 ++ [b] ∧
        (⟨(s, node) :: graph.edges, paths'⟩ : Graph A C).outgoing
          (parent.1.1 + b, parent.1.2) = some entry.1))
    (hsub : graph.paths ⊆ paths') :
    PathInv (⟨(s, node) :: graph.edges, paths'⟩ : Graph A C) := by
  intro entry hentry
  rcases hpaths entry hentry with hold | hnew
  · rcases hinv entry hold with hnil | ⟨parent, hparent, b, hword, hedge⟩
    · exact Or.inl hnil
    · refine Or.inr ⟨parent, hsub hparent, b, hword, ?_⟩
      rw [outgoing_cons_of_ne graph s node _ ?_ paths']
      · exact hedge
      · intro hcontra
        rw [hcontra, hout] at hedge
        exact absurd hedge (by simp)
  · exact Or.inr hnew

/-- One answer preserves the two path invariants. -/
theorem answer_invariants (graph : Graph A C) (s : Node A C)
    (hnodup : WordsNodup graph) (hinv : PathInv graph) :
    WordsNodup (answer root capacities unpad oracle coinA coinC graph s).2 ∧
      PathInv (answer root capacities unpad oracle coinA coinC graph s).2 := by
  unfold answer
  cases hout : graph.outgoing s with
  | some t => exact ⟨hnodup, hinv⟩
  | none =>
      cases hpath : graph.pathAt s with
      | none =>
          refine ⟨hnodup, pathInv_cons_edge hout hinv graph.paths
            (fun entry h => Or.inl h) (fun _ h => h)⟩
      | some entry =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none =>
              refine ⟨hnodup, pathInv_cons_edge hout hinv graph.paths
                (fun entry h => Or.inl h) (fun _ h => h)⟩
          | some fresh =>
              obtain ⟨hmem, hcap⟩ := pathAt_spec hpath
              set node : Node A C := ((match unpad
                    (stripZeros (entry.2 ++ [s.1 - entry.1.1])).1 with
                  | some message =>
                      if below : (stripZeros (entry.2 ++ [s.1 - entry.1.1])).2
                          < outBlocks then
                        oracle message
                          ⟨(stripZeros (entry.2 ++ [s.1 - entry.1.1])).2, below⟩
                      else coinA s
                  | none => coinA s), fresh) with hnode
              have hquery : (entry.1.1 + (s.1 - entry.1.1), entry.1.2) = s := by
                refine Prod.ext ?_ hcap
                show entry.1.1 + (s.1 - entry.1.1) = s.1
                abel
              refine ⟨List.nodup_cons.mpr
                  ⟨word_new_notMem hnodup hinv hout hpath, hnodup⟩,
                pathInv_cons_edge hout hinv
                  ((node, entry.2 ++ [s.1 - entry.1.1]) :: graph.paths) ?_
                  (fun _ h => List.mem_cons_of_mem _ h)⟩
              intro e he
              rcases List.mem_cons.mp he with rfl | hold
              · refine Or.inr ⟨entry, List.mem_cons_of_mem _ hmem,
                  s.1 - entry.1.1, rfl, ?_⟩
                rw [hquery]
                exact outgoing_cons_self graph s node
              · exact Or.inl hold

/-- Both path invariants hold at every point of a run. -/
theorem run_invariants (us : List (Node A C)) :
    WordsNodup (run root capacities unpad oracle coinA coinC us) ∧
      PathInv (run root capacities unpad oracle coinA coinC us) := by
  induction us using List.reverseRecOn with
  | nil => exact ⟨init_wordsNodup root, init_pathInv root⟩
  | append_singleton us u ih =>
      rw [run_concat]
      exact answer_invariants root capacities unpad oracle coinA coinC _ u
        ih.1 ih.2

/-! ## The graph is a function of the interaction

Conditioning a seed on the answers it gave pins the graph.  That is what lets a
lazy-sampling invariant carry *one* graph rather than a seed-indexed family:
below saturation the branch `answer` takes is read off the graph and the query
alone, and each branch's new graph is a function of the graph, the query, and
the answer. -/

/-- One step: below saturation, the graph a query produces is determined by the
answer it produces. -/
theorem answer_snd_determined {o o' : M → Fin outBlocks → A}
    {cA cA' : Node A C → A} {cC cC' : Node A C → Equiv.Perm C}
    (graph : Graph A C) (s : Node A C)
    (h1 : (freshCapacity capacities (cC s) graph).isSome)
    (h2 : (freshCapacity capacities (cC' s) graph).isSome)
    (heq : (answer root capacities unpad o cA cC graph s).1
      = (answer root capacities unpad o' cA' cC' graph s).1) :
    (answer root capacities unpad o cA cC graph s).2
      = (answer root capacities unpad o' cA' cC' graph s).2 := by
  obtain ⟨fresh₁, hf1⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨fresh₂, hf2⟩ := Option.isSome_iff_exists.mp h2
  cases hout : graph.outgoing s with
  | some t => simp only [answer, hout]
  | none =>
      cases hpath : graph.pathAt s with
      | none =>
          simp only [answer, hout, hpath] at heq ⊢
          rw [heq]
      | some entry =>
          simp only [answer, hout, hpath, hf1, hf2] at heq ⊢
          rw [heq]

/-- **The graph is a function of the interaction.**  Two seeds that answer the
same query list the same way, and never saturate, reach the same graph. -/
theorem run_determined {o o' : M → Fin outBlocks → A}
    {cA cA' : Node A C → A} {cC cC' : Node A C → Equiv.Perm C} :
    ∀ us : List (Node A C),
      (∀ (vs : List (Node A C)) (u : Node A C), vs ++ [u] <+: us →
        (freshCapacity capacities (cC u)
          (run root capacities unpad o cA cC vs)).isSome ∧
        (freshCapacity capacities (cC' u)
          (run root capacities unpad o' cA' cC' vs)).isSome ∧
        ans root capacities unpad o cA cC vs u
          = ans root capacities unpad o' cA' cC' vs u) →
      run root capacities unpad o cA cC us
        = run root capacities unpad o' cA' cC' us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton us u ih =>
      intro hstep
      have hprev : run root capacities unpad o cA cC us
          = run root capacities unpad o' cA' cC' us :=
        ih fun vs w hpre => hstep vs w (hpre.trans (List.prefix_append us [u]))
      obtain ⟨hs1, hs2, hans⟩ := hstep us u List.prefix_rfl
      unfold ans at hans
      rw [← hprev] at hans
      rw [run_concat, run_concat, ← hprev]
      refine answer_snd_determined root capacities unpad _ u hs1 ?_ hans
      rwa [hprev]

end Structure

/-! ## Two free coordinates of a conditioned uniform law are jointly uniform

The generic counting step behind the ideal side of Lemma 4.  A conditioning
that survives re-pointing *two* coordinates leaves them jointly uniform: the
re-pointing is a bijection between fibres, so all `|R| · |S|` fibres are
equinumerous and each carries `1/(|R|·|S|)` of the conditioned mass.

Both of the sponge's uses are instances — `(coinA x, coinC x)` on a query the
interaction has not touched, and `(oracle cell, coinC x)` at a cell no earlier
path consumed.  Only the update operation differs, so it is abstracted. -/

section Fibres

open RandomSystems (Dist)

variable {Ω R S : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

omit [DecidableEq Ω] [Nonempty Ω] [Fintype R] [Fintype S] in
open Classical in
/-- All `(r, s)`-fibres of a conditioning that survives re-pointing are
equinumerous. -/
theorem card_filter_pair_eq (E : Ω → Prop) (r : Ω → R) (s : Ω → S)
    (upd : Ω → R → S → Ω) (hr : ∀ ω a b, r (upd ω a b) = a)
    (hs : ∀ ω a b, s (upd ω a b) = b) (hself : ∀ ω, upd ω (r ω) (s ω) = ω)
    (hidem : ∀ ω a b a' b', upd (upd ω a b) a' b' = upd ω a' b')
    (hE : ∀ ω a b, E ω → E (upd ω a b)) (a a' : R) (b b' : S) :
    (Finset.univ.filter fun ω => E ω ∧ r ω = a ∧ s ω = b).card
      = (Finset.univ.filter fun ω => E ω ∧ r ω = a' ∧ s ω = b').card := by
  classical
  refine Finset.card_bij' (fun ω _ => upd ω a' b') (fun ω _ => upd ω a b)
    ?_ ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_univ _, hE ω a' b' hω.2.1, hr ω a' b', hs ω a' b'⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_univ _, hE ω a b hω.2.1, hr ω a b, hs ω a b⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω
    show upd (upd ω a' b') a b = ω
    rw [hidem, ← hω.2.2.1, ← hω.2.2.2, hself]
  · intro ω hω
    rw [Finset.mem_filter] at hω
    show upd (upd ω a b) a' b' = ω
    rw [hidem, ← hω.2.2.1, ← hω.2.2.2, hself]

omit [DecidableEq Ω] in
open Classical in
/-- **Two free coordinates are jointly uniform.**  Each `(r, s)`-fibre of a
re-pointable conditioning carries exactly `1/(|R|·|S|)` of its mass. -/
theorem mass_pair_eq_div (E : Ω → Prop) (r : Ω → R) (s : Ω → S)
    (upd : Ω → R → S → Ω) (hr : ∀ ω a b, r (upd ω a b) = a)
    (hs : ∀ ω a b, s (upd ω a b) = b) (hself : ∀ ω, upd ω (r ω) (s ω) = ω)
    (hidem : ∀ ω a b a' b', upd (upd ω a b) a' b' = upd ω a' b')
    (hE : ∀ ω a b, E ω → E (upd ω a b)) (a : R) (b : S) :
    (Dist.uniform Ω).mass (fun ω => E ω ∧ r ω = a ∧ s ω = b)
      = (Dist.uniform Ω).mass E
          / ((Fintype.card R : NNReal) * (Fintype.card S : NNReal)) := by
  classical
  haveI : Nonempty R := ⟨a⟩
  haveI : Nonempty S := ⟨b⟩
  rw [Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]
  -- the fibres partition the conditioned set, and all have the same size
  have hpart : (Finset.univ.filter E).card
      = ∑ _p ∈ (Finset.univ : Finset (R × S)),
          (Finset.univ.filter fun ω => E ω ∧ r ω = a ∧ s ω = b).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun ω => (r ω, s ω)) (t := (Finset.univ : Finset (R × S)))
      fun ω _ => Finset.mem_univ _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show ((Finset.univ.filter E).filter fun ω => (r ω, s ω) = p)
        = Finset.univ.filter fun ω => E ω ∧ r ω = p.1 ∧ s ω = p.2 from by
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun ω _ => ?_
      exact and_congr_right' ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
        fun h => Prod.ext h.1 h.2⟩]
    exact card_filter_pair_eq E r s upd hr hs hself hidem hE p.1 a p.2 b
  rw [hpart, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
  have hR : ((Fintype.card R : NNReal)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : ((Fintype.card S : NNReal)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  field_simp

end Fibres

end RandomSystemsCC.Symmetric.SpongeBDPV
