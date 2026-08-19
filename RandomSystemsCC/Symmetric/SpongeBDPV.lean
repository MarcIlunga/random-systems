/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedConstruct
import RandomSystems.SwitchingLemma
import RandomSystems.TranscriptHybrid

/-!
# BDPV's sponge simulator, Algorithm 2

Bertoni–Daemen–Peeters–Van Assche, *On the Indifferentiability of the Sponge
Construction*, EUROCRYPT 2008 — `papers/BDPV08_SpongeIndifferentiability.pdf`.
This file is Algorithm 2 (the random-transformation simulator) as a mathematical
object, together with the two invariants its proof rests on.

Read against the paper, not from memory: the earlier attempt in
`SpongeIndifferentiability.lean` was reconstructed and got the load-bearing rule
wrong, which is recorded there and in `STATUS.md` §11.36.

## The graph (§3.2)

Nodes are `A × C` — `A` the bitrate part, `C` the capacity part.  **Supernodes
are `C`**: a supernode edge `(s_c, t_c)` exists iff some node edge
`((s_a, s_c), (t_a, t_c))` does.  `R ⊆ C` is the *rooted* supernodes — the
initial capacity plus everything reachable from it — and a node is rooted iff its
capacity is.  `O ⊆ C` is the supernodes with an outgoing edge.

Rootedness living on capacities rather than on full states is the first thing the
reconstruction got wrong, so `R` and `O` are *derived* here (`Graph.R`,
`Graph.O`) rather than stored: they cannot drift out of step with the graph.

## The rule that carries the proof (Algorithm 2, line 11)

`t_c` is drawn **uniformly from `C \ (R ∪ O)`**, not uniformly from `C`.  So
BDPV do not tolerate capacity collisions and count them — they *prevent* them.
Two consequences, and they are the whole architecture:

* every newly rooted capacity is fresh, so the rooted supernodes form a **tree**
  and each node has at most one path (Lemma 1).  `answer_R_nodup` below is that
  invariant, and `freshCapacity_notMem` is the one-line fact it rests on;
* the simulator is therefore **exactly** sponge-consistent (Lemma 2) — there is
  no bad event and nothing to condition on.  What can fail instead is
  *saturation*, `R ∪ O = C`; since `R ∪ O` grows by at most one per query
  (`card_rootedOrOutgoing_answer_le`) it cannot occur before `2^c` queries, so it
  is a hypothesis `N < 2^c` rather than an event to bound.

Saturation is represented by `freshCapacity` returning `none`, which merges
Algorithm 2's two guards (`s` rooted *and* `R ∪ O ≠ C`) into the single match
below.

## The block is an `A`-part difference

Algorithm 2 line 4 says "find path to `s`, append `s_a`", which is shorthand:
Lemma 1's closing sentence — "since `A` is a group, each `r`-bit block of the
path is uniquely determined by the transitions on the `A`-part of the nodes" —
fixes the appended block as `s_a - v_a`, where `v` is the rooted node of `s`'s
supernode.  That is what `answer` computes.

## Scope

* Random *transformation* (Algorithm 2).  The permutation simulator (Algorithm 3)
  additionally requires `t` to have no incoming edge, and its `F⁻¹` interface
  draws `t_c` from `C \ R` among nodes with no outgoing edge so that an inverse
  query can never create a rooted node.  Not modelled here.
* The random oracle returns finitely many blocks (`Fin outBlocks → A`).  BDPV's
  `RO` returns an infinite string and `z_j` is its `j`-th block; any distinguisher
  of bounded cost reads boundedly many, and the truncation is the same device
  `RandomSystems.CR18.Vn` uses for its message alphabet.
-/

noncomputable section

namespace RandomSystemsCC.Symmetric.SpongeBDPV

universe u

variable {A C M : Type u}

/-- A node of the simulator graph: a bitrate part and a capacity part. -/
abbrev Node (A C : Type u) := A × C

/-- **The simulator's graph.**  `edges` are the query/answer pairs it has fixed;
`paths` are the rooted nodes together with the block word reaching each.

`R` and `O` are not fields: they are read off these two (`Graph.R`, `Graph.O`),
so the invariant "the rooted set is the set of capacities carrying a path" holds
by construction rather than by maintenance. -/
structure Graph (A C : Type u) where
  /-- Fixed query/answer pairs `(s, t)`, most recent first. -/
  edges : List (Node A C × Node A C)
  /-- Rooted nodes with their paths — at most one per supernode, by Lemma 1. -/
  paths : List (Node A C × List A)

namespace Graph

/-- The initial graph: no edges, and the initial node rooted by the empty path. -/
def init (root : Node A C) : Graph A C :=
  ⟨[], [(root, [])]⟩

/-- **`R`** — the rooted supernodes, i.e. the capacities carrying a path. -/
def R (graph : Graph A C) : List C :=
  graph.paths.map fun entry => entry.1.2

/-- **`O`** — the supernodes with an outgoing edge. -/
def O (graph : Graph A C) : List C :=
  graph.edges.map fun edge => edge.1.2

/-- The answer already fixed for `s`, if any (Algorithm 2 lines 2 and 18). -/
def outgoing [DecidableEq A] [DecidableEq C] (graph : Graph A C)
    (s : Node A C) : Option (Node A C) :=
  (graph.edges.find? fun edge => decide (edge.1 = s)).map Prod.snd

/-- The rooted node of `s`'s supernode, with its path — `s` is rooted exactly
when this is `some` (§3.2: a node is rooted iff its capacity is). -/
def pathAt [DecidableEq C] (graph : Graph A C) (s : Node A C) :
    Option (Node A C × List A) :=
  graph.paths.find? fun entry => decide (entry.1.2 = s.2)

end Graph

/-- Strip the trailing all-zero blocks: Algorithm 2 line 5's `p = p' 0^{r j}`,
returning `p'` and `j`.  `p'` does not end with a zero block. -/
def stripZeros [Zero A] [DecidableEq A] (p : List A) : List A × ℕ :=
  ((p.reverse.dropWhile fun a => decide (a = 0)).reverse,
    (p.reverse.takeWhile fun a => decide (a = 0)).length)

/-- **Algorithm 2 line 11.**  The first capacity in the coin permutation's order
that is neither rooted nor already carries an outgoing edge — uniform on
`C \ (R ∪ O)` when the permutation is uniform.

`none` *is* saturation (`R ∪ O = C`), which is why the caller needs no separate
guard: Algorithm 2's "`s` is rooted AND `R ∪ O ≠ C`" is exactly "`pathAt` and
`freshCapacity` are both `some`". -/
def freshCapacity [DecidableEq C] (capacities : List C) (sigma : Equiv.Perm C)
    (graph : Graph A C) : Option C :=
  (capacities.map sigma).find? fun c =>
    decide (c ∉ graph.R ∧ c ∉ graph.O)

/-- A fresh capacity is neither rooted nor outgoing.  One line, and it is what
Lemma 1 rests on. -/
theorem freshCapacity_notMem [DecidableEq C] (capacities : List C)
    (sigma : Equiv.Perm C) (graph : Graph A C) {c : C}
    (found : freshCapacity capacities sigma graph = some c) :
    c ∉ graph.R ∧ c ∉ graph.O := by
  have := List.find?_some found
  simpa using this

/-- **Algorithm 2**, one answer: the new node and the updated graph.

* an `s` that already has an outgoing edge is answered from the graph (lines 2,
  18) — table consistency;
* an `s` that is rooted, at a graph that is not saturated, gets its bitrate part
  from the random oracle when the path unpads and a fresh capacity from
  `C \ (R ∪ O)` (lines 3–12), and becomes a new rooted node;
* otherwise the answer is uniform over all nodes (line 14) and no path is
  created.

The two coin arguments are indexed by the query, which is the right granularity:
a query gets a fresh answer at most once, so per-query coins are per-answer
coins. -/
def answer [DecidableEq A] [DecidableEq C] [AddCommGroup A]
    (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
    (coinC : Node A C → Equiv.Perm C) (graph : Graph A C) (s : Node A C) :
    Node A C × Graph A C :=
  match graph.outgoing s with
  | some t => (t, graph)
  | none =>
      match graph.pathAt s, freshCapacity capacities (coinC s) graph with
      | some entry, some fresh =>
          let path := entry.2 ++ [s.1 - entry.1.1]
          let stripped := stripZeros path
          let bitrate :=
            match unpad stripped.1 with
            | some message =>
                if below : stripped.2 < outBlocks then
                  oracle message ⟨stripped.2, below⟩
                else coinA s
            | none => coinA s
          let node := (bitrate, fresh)
          (node, ⟨(s, node) :: graph.edges, (node, path) :: graph.paths⟩)
      | _, _ =>
          let node := (coinA s, coinC s root.2)
          (node, ⟨(s, node) :: graph.edges, graph.paths⟩)

section Invariants

variable [DecidableEq A] [DecidableEq C] [AddCommGroup A]
variable (root : Node A C) (capacities : List C) (unpad : List A → Option M)
variable {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
variable (coinC : Node A C → Equiv.Perm C)

omit [DecidableEq A] [DecidableEq C] [AddCommGroup A] in
/-- The initial graph has one rooted supernode. -/
theorem init_R_nodup : (Graph.init root).R.Nodup := by
  simp [Graph.init, Graph.R]

/-- **Lemma 1, the invariant.**  At most one path per supernode — equivalently,
at most one path per node, since a node determines its capacity.  This is exactly
what drawing `t_c` from `C \ (R ∪ O)` buys: the new rooted capacity is not
already rooted, so it cannot be a second path into an existing supernode. -/
theorem answer_R_nodup (graph : Graph A C) (s : Node A C)
    (nodup : graph.R.Nodup) :
    (answer root capacities unpad oracle coinA coinC graph s).2.R.Nodup := by
  unfold answer
  cases hout : graph.outgoing s with
  | some t => simpa [hout] using nodup
  | none =>
      cases hpath : graph.pathAt s with
      | none => simpa [hout, hpath] using nodup
      | some entry =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none => simpa [hout, hpath, hfresh] using nodup
          | some fresh =>
              simp only [Graph.R, List.map_cons, List.nodup_cons]
              exact ⟨(freshCapacity_notMem capacities (coinC s) graph hfresh).1,
                nodup⟩

/-- **The saturation count.**  `R ∪ O` grows by at most one per query, which is
what makes saturation impossible before `2^c` queries — BDPV's replacement for a
bad event.

The rooted branch adds `s.2` to `O` and `fresh` to `R`, but `s` is rooted there,
so `s.2` was already in `R ∪ O`: only `fresh` is new.  The uniform branch adds
`s.2` to `O` and nothing to `R`. -/
theorem card_rootedOrOutgoing_answer_le [Fintype C] (graph : Graph A C)
    (s : Node A C) :
    ((answer root capacities unpad oracle coinA coinC graph s).2.R ++
        (answer root capacities unpad oracle coinA coinC graph s).2.O).toFinset.card ≤
      (graph.R ++ graph.O).toFinset.card + 1 := by
  -- one new capacity at most, so it is enough to land inside `insert x (old)`
  have key : ∀ (newR newO : List C) (x : C),
      (∀ c ∈ newR ++ newO, c = x ∨ c ∈ graph.R ++ graph.O) →
      (newR ++ newO).toFinset.card ≤ (graph.R ++ graph.O).toFinset.card + 1 := by
    intro newR newO x hsub
    refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le x _)
    intro c hc
    rw [List.mem_toFinset] at hc
    rcases hsub c hc with rfl | hmem
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hmem)
  unfold answer
  cases hout : graph.outgoing s with
  | some t => simp
  | none =>
      cases hpath : graph.pathAt s with
      | none =>
          -- only `s.2` joins `O`
          refine key graph.R (s.2 :: graph.O) s.2 ?_
          intro c hc
          rcases List.mem_append.mp hc with hR | hO
          · exact Or.inr (List.mem_append_left _ hR)
          · rcases List.mem_cons.mp hO with rfl | hO'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_append_right _ hO')
      | some entry =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none =>
              refine key graph.R (s.2 :: graph.O) s.2 ?_
              intro c hc
              rcases List.mem_append.mp hc with hR | hO
              · exact Or.inr (List.mem_append_left _ hR)
              · rcases List.mem_cons.mp hO with rfl | hO'
                · exact Or.inl rfl
                · exact Or.inr (List.mem_append_right _ hO')
          | some fresh =>
              -- `s.2` is already rooted here, so only `fresh` is new
              have hentry : entry.1.2 = s.2 := by
                simpa using List.find?_some hpath
              have hmem : s.2 ∈ graph.R := by
                rw [← hentry]
                exact List.mem_map_of_mem (List.mem_of_find?_eq_some hpath)
              refine key (fresh :: graph.R) (s.2 :: graph.O) fresh ?_
              intro c hc
              rcases List.mem_append.mp hc with hR | hO
              · rcases List.mem_cons.mp hR with rfl | hR'
                · exact Or.inl rfl
                · exact Or.inr (List.mem_append_left _ hR')
              · rcases List.mem_cons.mp hO with rfl | hO'
                · exact Or.inr (List.mem_append_left _ hmem)
                · exact Or.inr (List.mem_append_right _ hO')

end Invariants

/-! ## Running the simulator over a history

`answer` folded over the adversary's permutation queries.  The graph is genuine
state: nothing here replays, because nothing has to — the converter that will
carry this uses the general `PFunConverter.ProtocolFn`, which is
`List U × List (Option Y) →. X ⊕ V` and therefore sees the whole transcript.
(`ofHistoryStep` discards completed rounds' answers, which is what forced the
quadratic replay recorded in `STATUS.md` §11.35.) -/

section Run

variable [DecidableEq A] [DecidableEq C] [AddCommGroup A]
variable (root : Node A C) (capacities : List C) (unpad : List A → Option M)
variable {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
variable (coinC : Node A C → Equiv.Perm C)

/-- The simulator's graph after answering the queries `us`, in order. -/
def run (us : List (Node A C)) : Graph A C :=
  us.foldl
    (fun graph u => (answer root capacities unpad oracle coinA coinC graph u).2)
    (Graph.init root)

/-- The simulator's answer to `u` after the history `us`. -/
def ans (us : List (Node A C)) (u : Node A C) : Node A C :=
  (answer root capacities unpad oracle coinA coinC (run root capacities unpad
    oracle coinA coinC us) u).1

@[simp]
theorem run_nil : run root capacities unpad oracle coinA coinC [] =
    Graph.init root := rfl

theorem run_concat (us : List (Node A C)) (u : Node A C) :
    run root capacities unpad oracle coinA coinC (us ++ [u]) =
      (answer root capacities unpad oracle coinA coinC
        (run root capacities unpad oracle coinA coinC us) u).2 := by
  simp [run, List.foldl_append]

/-- **Lemma 1**, lifted to a whole history: at most one path per supernode, at
every point of the run. -/
theorem run_R_nodup (us : List (Node A C)) :
    (run root capacities unpad oracle coinA coinC us).R.Nodup := by
  induction us using List.reverseRecOn with
  | nil => exact init_R_nodup root
  | append_singleton us u ih =>
      rw [run_concat]
      exact answer_R_nodup root capacities unpad oracle coinA coinC _ u ih

/-! ### Locality in the coins

`answer` reads `coinA` and `coinC` only at the query it is answering, so a run
depends on them only through the queries already made.  This is what makes the
coins at a *fresh* node free after conditioning on the interaction so far — the
step every lazy-sampling argument needs, and the reason the per-query coin
indexing of `answer` is the right granularity. -/

theorem answer_congr_coins (graph : Graph A C) (s : Node A C)
    {coinA' : Node A C → A} {coinC' : Node A C → Equiv.Perm C}
    (hA : coinA s = coinA' s) (hC : coinC s = coinC' s) :
    answer root capacities unpad oracle coinA coinC graph s
      = answer root capacities unpad oracle coinA' coinC' graph s := by
  unfold answer
  rw [hA, hC]

/-- **A run reads the coins only at its own queries.** -/
theorem run_congr_coins {coinA' : Node A C → A}
    {coinC' : Node A C → Equiv.Perm C} :
    ∀ us : List (Node A C), (∀ u ∈ us, coinA u = coinA' u) →
      (∀ u ∈ us, coinC u = coinC' u) →
      run root capacities unpad oracle coinA coinC us
        = run root capacities unpad oracle coinA' coinC' us := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; rfl
  | append_singleton us u ih =>
      intro hA hC
      rw [run_concat, run_concat,
        ih (fun w hw => hA w (List.mem_append_left _ hw))
          (fun w hw => hC w (List.mem_append_left _ hw)),
        answer_congr_coins root capacities unpad oracle coinA coinC _ u
          (hA u (List.mem_append_right _ List.mem_cons_self))
          (hC u (List.mem_append_right _ List.mem_cons_self))]

/-- The simulator's answer likewise reads the coins only at the queries made. -/
theorem ans_congr_coins {coinA' : Node A C → A}
    {coinC' : Node A C → Equiv.Perm C} (us : List (Node A C)) (u : Node A C)
    (hA : ∀ w ∈ u :: us, coinA w = coinA' w)
    (hC : ∀ w ∈ u :: us, coinC w = coinC' w) :
    ans root capacities unpad oracle coinA coinC us u
      = ans root capacities unpad oracle coinA' coinC' us u := by
  unfold ans
  rw [run_congr_coins root capacities unpad oracle coinA coinC us
      (fun w hw => hA w (List.mem_cons_of_mem _ hw))
      (fun w hw => hC w (List.mem_cons_of_mem _ hw)),
    answer_congr_coins root capacities unpad oracle coinA coinC _ u
      (hA u List.mem_cons_self) (hC u List.mem_cons_self)]

/-! ### Saturation cannot happen before `|C|` queries

BDPV's replacement for a bad event.  `R ∪ O` starts at one capacity and grows by
at most one per query, so a run of `N` queries has touched at most `N + 1`; while
that is below `|C|` some capacity is still free and `freshCapacity` finds it. -/

/-- `R ∪ O` after `N` queries has at most `N + 1` capacities. -/
theorem card_rootedOrOutgoing_run_le [Fintype C] (us : List (Node A C)) :
    ((run root capacities unpad oracle coinA coinC us).R ++
        (run root capacities unpad oracle coinA coinC us).O).toFinset.card ≤
      us.length + 1 := by
  induction us using List.reverseRecOn with
  | nil => simp [Graph.init, Graph.R, Graph.O]
  | append_singleton us u ih =>
      rw [run_concat, List.length_append, List.length_singleton]
      exact le_trans
        (card_rootedOrOutgoing_answer_le root capacities unpad oracle coinA coinC
          _ u)
        (by omega)

omit [DecidableEq A] [AddCommGroup A] in
/-- Below saturation some capacity is free. -/
theorem exists_notMem_of_card_lt [Fintype C] (graph : Graph A C)
    (below : (graph.R ++ graph.O).toFinset.card < Fintype.card C) :
    ∃ c : C, c ∉ graph.R ∧ c ∉ graph.O := by
  by_contra none
  push Not at none
  have cover : (Finset.univ : Finset C) ⊆ (graph.R ++ graph.O).toFinset := by
    intro c _
    rw [List.mem_toFinset, List.mem_append]
    by_cases hR : c ∈ graph.R
    · exact Or.inl hR
    · exact Or.inr (none c hR)
  exact absurd (Finset.card_le_card cover) (by simpa using below)

omit [DecidableEq A] [AddCommGroup A] in
/-- A free capacity is found, provided `capacities` enumerates `C`. -/
theorem freshCapacity_isSome (enumerates : ∀ c : C, c ∈ capacities)
    (sigma : Equiv.Perm C) (graph : Graph A C)
    (free : ∃ c : C, c ∉ graph.R ∧ c ∉ graph.O) :
    (freshCapacity capacities sigma graph).isSome := by
  obtain ⟨c, hR, hO⟩ := free
  rw [← Option.ne_none_iff_isSome]
  intro empty
  rw [freshCapacity, List.find?_eq_none] at empty
  refine absurd (empty c ?_) (by simpa using ⟨hR, hO⟩)
  refine List.mem_map.mpr ⟨sigma.symm c, enumerates _, ?_⟩
  simp

/-- **Saturation is unreachable below `|C|` queries** — BDPV's `N < 2^c`, and the
reason their proof has no bad event to bound. -/
theorem freshCapacity_run_isSome [Fintype C] (enumerates : ∀ c : C, c ∈ capacities)
    (sigma : Equiv.Perm C) (us : List (Node A C))
    (below : us.length + 1 < Fintype.card C) :
    (freshCapacity capacities sigma
      (run root capacities unpad oracle coinA coinC us)).isSome :=
  freshCapacity_isSome capacities enumerates sigma _
    (exists_notMem_of_card_lt _
      (lt_of_le_of_lt
        (card_rootedOrOutgoing_run_le root capacities unpad oracle coinA coinC us)
        below))

end Run

/-! ## Lemma 2 — sponge consistency, as an invariant

BDPV's Lemma 2 says the simulator's responses are sponge-consistent unless it is
saturated.  The content is an invariant of the graph: **every rooted node's
bitrate part is the oracle block its own path dictates.**  Algorithm 2 lines 6–7
establish it for each new path, and nothing ever revises a path, so it is
maintained rather than argued.

There is no conditioning and no bad event here — that is the whole point of the
`C \ (R ∪ O)` draw.  The `unpad [] = none` hypothesis is BDPV's own restriction
that the all-zero path is not a sponge input ("the all-zero path does not
correspond to a block that can be output by the sponge construction"; Definition 2
requires `|p| > 0` with last block `≠ 0^r`). -/

section Consistency

variable [DecidableEq A] [DecidableEq C] [AddCommGroup A]
variable (root : Node A C) (capacities : List C) (unpad : List A → Option M)
variable {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
variable (coinC : Node A C → Equiv.Perm C)

/-- **Sponge consistency.**  Every path in the graph carries the oracle block it
names: strip the path's trailing zero blocks, unpad what remains, and the node's
bitrate part is that message's block at the stripped index. -/
def Graph.Consistent (unpad : List A → Option M)
    (oracle : M → Fin outBlocks → A) (graph : Graph A C) : Prop :=
  ∀ entry ∈ graph.paths, ∀ message : M,
    unpad (stripZeros entry.2).1 = some message →
      ∀ below : (stripZeros entry.2).2 < outBlocks,
        entry.1.1 = oracle message ⟨(stripZeros entry.2).2, below⟩

omit [DecidableEq C] in
/-- The initial graph is consistent: its only path is empty, and the empty word
is not a padded sponge input. -/
theorem init_consistent (rootPath : unpad [] = none) :
    (Graph.init root).Consistent unpad oracle := by
  intro entry member message unpadded _
  rw [Graph.init] at member
  have : entry = (root, ([] : List A)) := by
    simpa using member
  subst this
  rw [show stripZeros ([] : List A) = ([], 0) from rfl] at unpadded
  simp [rootPath] at unpadded

/-- **Lemma 2's step.**  One answer preserves consistency.  The rooted branch is
the only one that adds a path, and it takes the new node's bitrate part from the
oracle exactly when the path unpads and the index is in range — the two cases
where the invariant says anything. -/
theorem answer_consistent (graph : Graph A C)
    (s : Node A C) (consistent : graph.Consistent unpad oracle) :
    (answer root capacities unpad oracle coinA coinC graph s).2.Consistent
      unpad oracle := by
  unfold answer
  cases hout : graph.outgoing s with
  | some t => simpa [hout] using consistent
  | none =>
      cases hpath : graph.pathAt s with
      | none => simpa [hout, hpath] using consistent
      | some entry =>
          cases hfresh : freshCapacity capacities (coinC s) graph with
          | none => simpa [hout, hpath, hfresh] using consistent
          | some fresh =>
              intro newEntry member message unpadded below
              rcases List.mem_cons.mp member with rfl | older
              · -- the new path: its bitrate part is the oracle block by construction
                simp only [unpadded, dif_pos below]
              · exact consistent newEntry older message unpadded below

/-- **Lemma 2.**  Sponge consistency holds at every point of a run. -/
theorem run_consistent (rootPath : unpad [] = none) (us : List (Node A C)) :
    (run root capacities unpad oracle coinA coinC us).Consistent unpad oracle := by
  induction us using List.reverseRecOn with
  | nil => exact init_consistent root unpad oracle rootPath
  | append_singleton us u ih =>
      rw [run_concat]
      exact answer_consistent root capacities unpad oracle coinA coinC _ u ih

end Consistency

/-! ## Lemma 2's payoff — one step of the sponge chain

The invariant above is about paths in the graph; what the proof consumes is that
*walking the sponge chain through the simulator extends the path by the absorbed
block*, so the chain's final node carries the padded message's own path and
therefore, by consistency, the oracle's block.

This is where `A` being a group is used, and where Lemma 1 is used: the appended
block comes out as `(s.1 + b) - s.1 = b` only because `pathAt` finds *the* entry
for `s`'s supernode, and there is only one because `R` is `Nodup`. -/

section Chain

variable [DecidableEq A] [DecidableEq C] [AddCommGroup A]
variable (root : Node A C) (capacities : List C) (unpad : List A → Option M)
variable {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
variable (coinC : Node A C → Equiv.Perm C)

/-- `find?` on a predicate with a unique witness present in the list. -/
private theorem find?_eq_some_of_unique {α : Type u} (p : α → Bool) (l : List α)
    (a : α) (mem : a ∈ l) (holds : p a = true)
    (unique : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => exact absurd mem List.not_mem_nil
  | cons head tail ih =>
      by_cases hhead : p head = true
      · have hEq : head = a := unique head List.mem_cons_self hhead
        subst hEq
        simp [hhead]
      · rcases List.mem_cons.mp mem with rfl | tailMem
        · exact absurd holds hhead
        · rw [List.find?_cons_of_neg hhead]
          exact ih tailMem fun b bMem => unique b (List.mem_cons_of_mem _ bMem)

omit [DecidableEq A] [AddCommGroup A] in
/-- **Lemma 1, in the form the chain consumes**: a supernode carrying a path
carries exactly one, so `pathAt` returns it. -/
theorem pathAt_eq_of_mem (graph : Graph A C) (nodup : graph.R.Nodup)
    {entry : Node A C × List A} (member : entry ∈ graph.paths) {s : Node A C}
    (same : entry.1.2 = s.2) :
    graph.pathAt s = some entry := by
  refine find?_eq_some_of_unique _ _ _ member (by simpa using same) ?_
  intro other otherMember holds
  exact List.inj_on_of_nodup_map nodup otherMember member
    ((by simpa using holds : other.1.2 = s.2).trans same.symm)

/-- **One chain step.**  Absorbing `b` at a rooted node `s` with path `w` and
querying the simulator produces a node rooted by `w ++ [b]`.

The two freshness hypotheses are exactly Algorithm 2's guards: the query must not
already carry an outgoing edge (or the graph answers from the table and no path is
created), and the graph must not be saturated. -/
theorem answer_rooted_step (graph : Graph A C) (nodup : graph.R.Nodup)
    (s : Node A C) (w : List A) (member : (s, w) ∈ graph.paths) (b : A)
    (freshQuery : graph.outgoing (s.1 + b, s.2) = none)
    (unsaturated :
      (freshCapacity capacities (coinC (s.1 + b, s.2)) graph).isSome) :
    ((answer root capacities unpad oracle coinA coinC graph
          (s.1 + b, s.2)).1, w ++ [b]) ∈
      (answer root capacities unpad oracle coinA coinC graph
        (s.1 + b, s.2)).2.paths := by
  obtain ⟨fresh, hfresh⟩ := Option.isSome_iff_exists.mp unsaturated
  have hpath : graph.pathAt (s.1 + b, s.2) = some (s, w) :=
    pathAt_eq_of_mem graph nodup member rfl
  unfold answer
  rw [freshQuery]
  simp only [hpath, hfresh]
  -- the appended block is `(s.1 + b) - s.1 = b`, which is Lemma 1's group step
  rw [show (s.1 + b) - s.1 = b from add_sub_cancel_left s.1 b]
  exact List.mem_cons_self

/-- **Lemma 2 at a chain step.**  The node the chain reaches has the bitrate part
the random oracle dictates for its own path.  Consistency and the rooted step,
composed; no conditioning, no bad event. -/
theorem answer_bitrate_eq_oracle (graph : Graph A C) (nodup : graph.R.Nodup)
    (consistent : graph.Consistent unpad oracle) (s : Node A C) (w : List A)
    (member : (s, w) ∈ graph.paths) (b : A)
    (freshQuery : graph.outgoing (s.1 + b, s.2) = none)
    (unsaturated :
      (freshCapacity capacities (coinC (s.1 + b, s.2)) graph).isSome)
    (message : M) (unpadded : unpad (stripZeros (w ++ [b])).1 = some message)
    (below : (stripZeros (w ++ [b])).2 < outBlocks) :
    (answer root capacities unpad oracle coinA coinC graph (s.1 + b, s.2)).1.1 =
      oracle message ⟨(stripZeros (w ++ [b])).2, below⟩ :=
  answer_consistent root capacities unpad oracle coinA coinC graph _ consistent
    _
    (answer_rooted_step root capacities unpad oracle coinA coinC graph nodup s w
      member b freshQuery unsaturated)
    message unpadded below

/-! ### The whole walk — Lemma 3's content

Lemma 3 says a distinguisher can replace its honest-interface queries by
permutation queries at no greater cost, because the sponge is public: it walks the
chain itself.  The mathematical content is that the walk *works* — that absorbing
the blocks of a padded message one at a time drives the graph along a single path
and ends on the node the random oracle names.  That is `walk_rooted` and
`walk_bitrate_eq_oracle` below; the reduction on distinguishers is then a
converter/DPI step with no further content.

`WalkFresh` collects Algorithm 2's two guards at every step of the walk, which is
the honest way to carry them: they are conditions on the *intermediate* graphs, so
they cannot be stated up front. -/

/-- Walk the chain: absorb each block into the current node's bitrate part and
query the simulator. -/
def walk (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
    (coinC : Node A C → Equiv.Perm C) (graph : Graph A C) (s : Node A C) :
    List A → Node A C × Graph A C
  | [] => (s, graph)
  | b :: bs =>
      let step := answer root capacities unpad oracle coinA coinC graph
        (s.1 + b, s.2)
      walk root capacities unpad oracle coinA coinC step.2 step.1 bs

/-- Algorithm 2's guards, at every step of a walk: the query is not already
answered, and the graph is not saturated. -/
def WalkFresh (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    {outBlocks : ℕ} (oracle : M → Fin outBlocks → A) (coinA : Node A C → A)
    (coinC : Node A C → Equiv.Perm C) (graph : Graph A C) (s : Node A C) :
    List A → Prop
  | [] => True
  | b :: bs =>
      graph.outgoing (s.1 + b, s.2) = none ∧
        (freshCapacity capacities (coinC (s.1 + b, s.2)) graph).isSome ∧
        WalkFresh root capacities unpad oracle coinA coinC
          (answer root capacities unpad oracle coinA coinC graph
            (s.1 + b, s.2)).2
          (answer root capacities unpad oracle coinA coinC graph
            (s.1 + b, s.2)).1 bs

/-- **The walk stays on one path.**  Absorbing `bs` from a node rooted by `w`
ends on a node rooted by `w ++ bs`.  Each step is `answer_rooted_step`, and Lemma
1 is re-established at each step so the next one can use it. -/
theorem walk_rooted :
    ∀ (bs : List A) (graph : Graph A C) (s : Node A C) (w : List A),
      (s, w) ∈ graph.paths → graph.R.Nodup →
      WalkFresh root capacities unpad oracle coinA coinC graph s bs →
      ((walk root capacities unpad oracle coinA coinC graph s bs).1, w ++ bs) ∈
        (walk root capacities unpad oracle coinA coinC graph s bs).2.paths := by
  intro bs
  induction bs with
  | nil => intro graph s w member _ _; simpa using member
  | cons b bs ih =>
      intro graph s w member nodup fresh
      obtain ⟨freshQuery, unsaturated, rest⟩ := fresh
      have stepMember := answer_rooted_step root capacities unpad oracle coinA
        coinC graph nodup s w member b freshQuery unsaturated
      have stepNodup := answer_R_nodup root capacities unpad oracle coinA coinC
        graph (s.1 + b, s.2) nodup
      have := ih _ _ (w ++ [b]) stepMember stepNodup rest
      simpa [walk, List.append_assoc] using this

/-- Consistency survives a walk — unconditionally, since `answer` preserves it
in every branch. -/
theorem walk_consistent :
    ∀ (bs : List A) (graph : Graph A C) (s : Node A C),
      graph.Consistent unpad oracle →
      (walk root capacities unpad oracle coinA coinC graph s bs).2.Consistent
        unpad oracle := by
  intro bs
  induction bs with
  | nil => intro graph s consistent; exact consistent
  | cons b bs ih =>
      intro graph s consistent
      exact ih _ _
        (answer_consistent root capacities unpad oracle coinA coinC graph
          (s.1 + b, s.2) consistent)

/-- **Lemma 3 with Lemma 2.**  The walk's final node has the bitrate part the
random oracle dictates for the word it absorbed — so a distinguisher walking the
chain itself reads exactly the honest interface's answer, which is what lets the
honest port be dropped. -/
theorem walk_bitrate_eq_oracle (bs : List A)
    (graph : Graph A C) (s : Node A C) (w : List A)
    (member : (s, w) ∈ graph.paths) (nodup : graph.R.Nodup)
    (consistent : graph.Consistent unpad oracle)
    (fresh : WalkFresh root capacities unpad oracle coinA coinC graph s bs)
    (message : M) (unpadded : unpad (stripZeros (w ++ bs)).1 = some message)
    (below : (stripZeros (w ++ bs)).2 < outBlocks) :
    (walk root capacities unpad oracle coinA coinC graph s bs).1.1 =
      oracle message ⟨(stripZeros (w ++ bs)).2, below⟩ :=
  walk_consistent root capacities unpad oracle coinA coinC bs graph s consistent
    _
    (walk_rooted root capacities unpad oracle coinA coinC bs graph s w member
      nodup fresh)
    message unpadded below

end Chain

/-! ## Lemma 4's arithmetic

BDPV's bound and the elementary inequality that turns the exact product into the
headline `N(N+1)/2^{c+1}`.  The paper reaches it through `1 - x ≈ e^{-x}` (eq. 4);
the honest version is the union bound `1 - ∏(1 - aᵢ) ≤ ∑ aᵢ`, which is exact
rather than approximate and needs only `0 ≤ aᵢ ≤ 1`. -/

section Bound

/-- **BDPV's `f_T(N)`** (Lemma 4): the variational distance between `N` uniform
capacity draws and `N` draws without replacement from a set of size `q`. -/
noncomputable def fT (q N : ℕ) : ℝ :=
  1 - ∏ i ∈ Finset.range N, (1 - ((i : ℝ) + 1) / q)

/-- **BDPV eq. (4)**, exactly rather than approximately:
`f_T(N) ≤ N(N+1)/(2q)`. -/
theorem fT_le (q N : ℕ) (below : N ≤ q) :
    fT q N ≤ (N : ℝ) * ((N : ℝ) + 1) / (2 * q) := by
  have hgauss : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [Nat.le_zero.mp below]
    simp [fT]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbound : fT q N ≤ ∑ i ∈ Finset.range N, ((i : ℝ) + 1) / q := by
    unfold fT
    have := RandomSystems.CR18.Counting.one_sub_sum_le_prod_one_sub
      (Finset.range N) (fun i => ((i : ℝ) + 1) / q)
      (fun i _ => by positivity)
      (fun i hi => by
        rw [div_le_one hqpos]
        have hle : (i : ℝ) + 1 ≤ N := by
          have := Finset.mem_range.mp hi
          exact_mod_cast Nat.succ_le_of_lt this
        exact hle.trans (by exact_mod_cast below))
    linarith
  refine hbound.trans (le_of_eq ?_)
  rw [← Finset.sum_div, hgauss]
  field_simp

end Bound

/-! ## `P[RO]` as a system

Algorithm 2 over a uniform seed, on the flat one-port carrier Lemma 3 reduces to.
The real side of Lemma 4 is `RandomSystems.CR18.𝖱 (Node A C)`, the uniform
transformation, which the development already has. -/

section System

open RandomSystems (Dist)
open RandomSystems.CR18

/-- The simulator's seed: the random oracle and the two coin functions. -/
abbrev Seed (A C M : Type u) (outBlocks : ℕ) :=
  (M → Fin outBlocks → A) × (Node A C → A) × (Node A C → Equiv.Perm C)

/-- **`P[RO]`** — Algorithm 2 as a probabilistic system: the last-query evaluator
of `ans` over a uniform seed.  Its answers are uniform in the bitrate part and,
on rooted queries, drawn without replacement in the capacity — which is the entire
content of Lemma 4's distance. -/
noncomputable def idealSystem [Fintype A] [DecidableEq A] [AddCommGroup A]
    [Fintype C] [DecidableEq C] [Fintype M] [DecidableEq M]
    (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    (outBlocks : ℕ) : PFunPDS (Node A C) (Node A C) :=
  Dist.fTransform
    (fun seed : Seed A C M outBlocks =>
      PFunDDS.historyEvaluator fun history nonempty =>
        ans root capacities unpad seed.1 seed.2.1 seed.2.2 history.dropLast
          (history.getLast nonempty))
    (Dist.uniform (Seed A C M outBlocks))

theorem idealSystem_isProbDist [Fintype A] [DecidableEq A] [AddCommGroup A]
    [Fintype C] [DecidableEq C] [Fintype M] [DecidableEq M]
    (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    (outBlocks : ℕ) :
    (idealSystem root capacities unpad outBlocks).isProbDist :=
  Dist.fTransform_isProbDist _ Dist.uniform_isProbDist

/-! ### Both sides as lazily sampled systems

`RandomSystems.TranscriptHybrid` bounds `Δ(⌈N⌉ ·, ⌈N⌉ ·)` for two systems
presented as a seed law plus a deterministic answer function of the earlier
queries and the current one — the successor calculus of the thesis's
`S↑x↓y` collapses there to *shift the answer function* and *condition the
seed*.  Both sides of Lemma 4 are already in that shape on the nose: `ans`
takes the earlier queries as an argument, and a uniform random transformation
is the degenerate case that ignores them. -/

/-- **`P[RO]` is a lazily sampled system**: `ans` is a deterministic function
of the seed, the earlier queries, and the current one. -/
theorem idealSystem_eq_seededLaw [Fintype A] [DecidableEq A] [AddCommGroup A]
    [Fintype C] [DecidableEq C] [Fintype M] [DecidableEq M]
    (root : Node A C) (capacities : List C) (unpad : List A → Option M)
    (outBlocks : ℕ) :
    idealSystem root capacities unpad outBlocks
      = seededLaw (fun seed : Seed A C M outBlocks =>
            ans root capacities unpad seed.1 seed.2.1 seed.2.2)
          (Dist.uniform (Seed A C M outBlocks)) := rfl

/-- **The uniform random transformation is a lazily sampled system** whose
answer ignores the history — the real side of Lemma 4. -/
theorem urf_eq_seededLaw [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype C] [DecidableEq C] [Nonempty C] :
    PFunPDS.URF (X := Node A C) (Y := Node A C)
      = seededLaw (fun f : Node A C → Node A C => fun _ u => f u)
          (Dist.uniform (Node A C → Node A C)) := rfl

end System

/-! ## The counting leaf — a birthday bound on the *capacity*

This is the number in Lemma 4, obtained without BDPV's optimality assertion.

Their proof computes the variational distance for the all-rooted strategy and
asserts it is the worst case ("To obtain the greatest possible variational
distance, the optimum strategy consists in creating `N` rooted nodes").  That
assertion is not innocuous: `R ∪ O` grows on *every* query, rooted or not, so a
strategy that spends queries enlarging `O` first meets a bigger forbidden set at
each later rooted query.  Whether that trades favourably against having fewer
rooted queries is exactly what would need proving.

We do not need it.  The forbidden set at step `i` has size `≤ i`
(`card_rootedOrOutgoing_run_le`, which holds for *every* query list and hence
every strategy), so the deviation is a collision between an answer's capacity and
one of at most `i` earlier capacities — and a union bound over query pairs gives
`(N choose 2)/|C|`, whence `N(N+1)/(2|C|)` via `fT_le`.  Same headline bound,
strategy-independent, no asserted step. -/

section Counting

open RandomSystems (Dist)
open RandomSystems.CR18

variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype C] [DecidableEq C] [Nonempty C]

/-- **Reading only the capacity of a uniform transformation is a uniform random
function into `C`.**  Every fibre of the projection has one preimage per choice of
bitrate parts, so the fibres are equinumerous and the pushforward stays uniform. -/
theorem fTransform_capacity_uniform :
    Dist.fTransform (fun f : Node A C → Node A C => fun x => (f x).2)
        (Dist.uniform (Node A C → Node A C)) =
      Dist.uniform (Node A C → C) := by
  classical
  refine Dist.fTransform_uniform_eq_uniform_of_card_fiber_mul _ fun g => ?_
  have hfibre :
      (Finset.univ.filter
          (fun f : Node A C → Node A C => (fun x => (f x).2) = g)).card =
        Fintype.card (Node A C → A) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun f => fun x => ((f : Node A C → Node A C) x).1
        invFun := fun h => ⟨fun x => (h x, g x), rfl⟩
        left_inv := ?_, right_inv := ?_ }
    · intro f
      refine Subtype.ext (funext fun x => ?_)
      have := congrFun f.2 x
      exact Prod.ext rfl this.symm
    · intro h
      rfl
  rw [hfibre, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_prod, mul_pow]

/-- **Two-point capacity collision.**  A uniform transformation's answers at two
distinct points agree in the capacity with probability exactly `1/|C|`. -/
theorem uniform_capacity_pair_eq_mass {a b : Node A C} (hab : a ≠ b) :
    (Dist.uniform (Node A C → Node A C)).mass (fun f => (f a).2 = (f b).2) =
      1 / (Fintype.card C : NNReal) := by
  classical
  have push := Dist.mass_fTransform
    (fun f : Node A C → Node A C => fun x => (f x).2)
    (Dist.uniform (Node A C → Node A C))
    (fun g : Node A C → C => g a = g b)
  rw [fTransform_capacity_uniform] at push
  exact push.symm.trans (uniform_function_pair_eq_mass_of_codomain hab)

/-! ### Algorithm 2 line 11 draws uniformly from `C \ (R ∪ O)`

The definition takes the *first* capacity in the coin permutation's order that
is free.  That it is uniform on the free set is the without-replacement half of
Lemma 4, and it is a symmetry argument rather than a count: transposing two
free capacities is a bijection of `Equiv.Perm C` that fixes the free/forbidden
split pointwise, so it moves the `find?` result from one free capacity to the
other while leaving every earlier (forbidden) entry forbidden. -/

/-- The free capacities: neither rooted nor already outgoing. -/
def freeSet (graph : Graph A C) : Finset C :=
  Finset.univ.filter fun c => c ∉ graph.R ∧ c ∉ graph.O

omit [Fintype A] [DecidableEq A] [Nonempty A] [Nonempty C] in
theorem mem_freeSet {graph : Graph A C} {c : C} :
    c ∈ freeSet graph ↔ c ∉ graph.R ∧ c ∉ graph.O := by
  simp [freeSet]

omit [Fintype A] [DecidableEq A] [Nonempty A] [Fintype C] [Nonempty C] in
/-- Transposing two free capacities commutes with the search, because it fixes
every forbidden capacity. -/
theorem freshCapacity_swap_mul (capacities : List C)
    (graph : Graph A C) {c c' : C} (hc : c ∉ graph.R ∧ c ∉ graph.O)
    (hc' : c' ∉ graph.R ∧ c' ∉ graph.O) (sigma : Equiv.Perm C) :
    freshCapacity capacities (Equiv.swap c c' * sigma) graph
      = (freshCapacity capacities sigma graph).map (Equiv.swap c c') := by
  classical
  have hfix : ∀ y : C, ((Equiv.swap c c' y ∉ graph.R ∧ Equiv.swap c c' y ∉ graph.O)
      ↔ (y ∉ graph.R ∧ y ∉ graph.O)) := by
    intro y
    by_cases hy : y = c
    · subst hy
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => hc, fun _ => hc'⟩
    by_cases hy' : y = c'
    · subst hy'
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => hc', fun _ => hc⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hy hy']
  unfold freshCapacity
  rw [show capacities.map (Equiv.swap c c' * sigma)
      = (capacities.map sigma).map (Equiv.swap c c') from by
      rw [List.map_map]; rfl,
    List.find?_map]
  refine congrArg (Option.map _) (congrArg
    (fun p => List.find? p (capacities.map sigma)) (funext fun y => ?_))
  show decide (Equiv.swap c c' y ∉ graph.R ∧ Equiv.swap c c' y ∉ graph.O)
    = decide (y ∉ graph.R ∧ y ∉ graph.O)
  exact decide_eq_decide.mpr (hfix y)

omit [Fintype A] [DecidableEq A] [Nonempty A] [Nonempty C] in
/-- The two free capacities are hit equally often — the transposition above is
a bijection of the coin space. -/
theorem mass_freshCapacity_eq (capacities : List C) (graph : Graph A C) {c c' : C}
    (hc : c ∈ freeSet graph) (hc' : c' ∈ freeSet graph) :
    (Dist.uniform (Equiv.Perm C)).mass
        (fun sigma => freshCapacity capacities sigma graph = some c)
      = (Dist.uniform (Equiv.Perm C)).mass
          (fun sigma => freshCapacity capacities sigma graph = some c') := by
  classical
  rw [Dist.uniform_mass_eq_card_filter, Dist.uniform_mass_eq_card_filter]
  congr 1
  refine congrArg (Nat.cast) (Finset.card_bij'
    (fun sigma _ => Equiv.swap c c' * sigma)
    (fun sigma _ => Equiv.swap c c' * sigma) ?_ ?_ ?_ ?_)
  · intro sigma hsigma
    rw [Finset.mem_filter] at hsigma ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [freshCapacity_swap_mul capacities graph (mem_freeSet.mp hc)
      (mem_freeSet.mp hc'), hsigma.2]
    simp
  · intro sigma hsigma
    rw [Finset.mem_filter] at hsigma ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [freshCapacity_swap_mul capacities graph (mem_freeSet.mp hc)
      (mem_freeSet.mp hc'), hsigma.2]
    simp
  · intro sigma _
    show Equiv.swap c c' * (Equiv.swap c c' * sigma) = sigma
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro sigma _
    show Equiv.swap c c' * (Equiv.swap c c' * sigma) = sigma
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

omit [Fintype A] [DecidableEq A] [Nonempty A] [Nonempty C] in
/-- **Algorithm 2 line 11 is a uniform draw from `C \ (R ∪ O)`.**  The
capacity the simulator answers with is uniform on the free set — the exact
statement Lemma 4's without-replacement side needs, and the reason BDPV have
no capacity-collision event to bound. -/
theorem fTransform_freshCapacity_apply (capacities : List C) (enumerates : ∀ c : C, c ∈ capacities)
    (graph : Graph A C) {c : C} (hc : c ∈ freeSet graph) :
    Dist.fTransform (fun sigma => freshCapacity capacities sigma graph)
        (Dist.uniform (Equiv.Perm C)) (some c)
      = 1 / ((freeSet graph).card : NNReal) := by
  classical
  set g := Dist.fTransform (fun sigma => freshCapacity capacities sigma graph)
    (Dist.uniform (Equiv.Perm C)) with hg
  have hfree : ∃ c : C, c ∉ graph.R ∧ c ∉ graph.O := ⟨c, mem_freeSet.mp hc⟩
  -- every answer is a free capacity
  have hsupp : g.support ⊆ (freeSet graph).image Option.some := by
    intro y hy
    obtain ⟨sigma, -, rfl⟩ := Dist.mem_support_fTransform _ _ hy
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp
      (freshCapacity_isSome capacities enumerates sigma graph hfree)
    exact Finset.mem_image.mpr ⟨c', mem_freeSet.mpr
      (freshCapacity_notMem capacities sigma graph hc'), hc'.symm⟩
  -- all free capacities carry the same mass
  have hconst : ∀ c' ∈ freeSet graph, g (some c') = g (some c) := by
    intro c' hc'
    rw [hg, Dist.fTransform_apply_eq_mass, Dist.fTransform_apply_eq_mass]
    exact mass_freshCapacity_eq capacities graph hc' hc
  have hw : g.weight = 1 := by
    rw [hg, Dist.weight_fTransform]
    exact Dist.uniform_isProbDist
  have hsum : ∑ y ∈ (freeSet graph).image Option.some, g y = 1 := by
    rw [← hw, Dist.weight, Finsupp.sum]
    exact (Finset.sum_subset hsupp
      fun y _ hy => Finsupp.notMem_support_iff.mp hy).symm
  rw [Finset.sum_image (fun _ _ _ _ h => Option.some.inj h),
    Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : ((freeSet graph).card : NNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hc)
  rw [eq_div_iff hcard, mul_comm]
  exact hsum

/-! ### The real side: a conditioned uniform transformation stays uniform at a
fresh point

The real side of Lemma 4 is `𝖱 (Node A C)`, conditioned on the answers already
given.  Any conditioning that survives re-pointing the function at `x` — in
particular a table of values at points other than `x` — leaves the value at `x`
uniform.  This is the exact-density hypothesis the step bound consumes on the
real side. -/

/-- **A fresh point of a conditioned uniform function is uniform.**  The
hypothesis `stable` says the conditioning does not constrain the value at `x`;
for a query table over points other than `x` it holds by `Function.update_noteq`. -/
theorem fTransform_eval_restrict_uniform_fun {D R : Type*} [Fintype D]
    [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    (E : (D → R) → Prop) (x : D)
    (stable : ∀ (f : D → R) (r : R), E f → E (Function.update f x r)) (z : R) :
    Dist.fTransform (fun f : D → R => f x)
        ((Dist.uniform (D → R)).restrict E) z
      = ((Dist.uniform (D → R)).restrict E).weight
          / (Fintype.card R : NNReal) := by
  classical
  set nu := (Dist.uniform (D → R)).restrict E with hnu
  set g := Dist.fTransform (fun f : D → R => f x) nu with hg
  -- all fibres carry the same mass, by re-pointing at `x`
  have hconst : ∀ z' : R, g z' = g z := by
    intro z'
    rw [hg, Dist.fTransform_apply_eq_mass, Dist.fTransform_apply_eq_mass, hnu,
      Dist.mass_restrict, Dist.mass_restrict, Dist.uniform_mass_eq_card_filter,
      Dist.uniform_mass_eq_card_filter]
    congr 1
    refine congrArg (Nat.cast) (Finset.card_bij'
      (fun f _ => Function.update f x z) (fun f _ => Function.update f x z')
      ?_ ?_ ?_ ?_)
    · intro f hf
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨Finset.mem_univ _,
        Function.update_self _ _ _, stable f z hf.2.2⟩
    · intro f hf
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨Finset.mem_univ _,
        Function.update_self _ _ _, stable f z' hf.2.2⟩
    · intro f hf
      rw [Finset.mem_filter] at hf
      show Function.update (Function.update f x z) x z' = f
      rw [Function.update_idem, ← hf.2.1, Function.update_eq_self]
    · intro f hf
      rw [Finset.mem_filter] at hf
      show Function.update (Function.update f x z') x z = f
      rw [Function.update_idem, ← hf.2.1, Function.update_eq_self]
  -- the fibres exhaust the weight
  have hsum : ∑ z' : R, g z' = nu.weight := by
    rw [← Dist.weight_fTransform (fun f : D → R => f x) nu, ← hg, Dist.weight,
      Finsupp.sum]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun z' _ hz' => Finsupp.notMem_support_iff.mp hz').symm
  rw [Finset.sum_congr rfl (fun z' _ => hconst z'), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : ((Fintype.card R : NNReal)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [eq_div_iff hcard, mul_comm]
  exact hsum

/-! ### The per-step distance

An answer uniform on `A × (C \ (R ∪ O))` against one uniform on `A × C`.  The
ideal side only has to be *dominated* by the uniform density on its support —
which is what an equinumerous-fibre argument delivers — and the sub-probability
weight gap `p − q` is carried, because a conditioned lazily sampled system is
a sub-distribution. -/

/-- **The step bound.**  A law supported on `Good` with density at most
`p / |Good|`, against `q` times the uniform law on the whole alphabet, is
`(|Zᶜ Good| / |Z|)·p + (p − q)` away.  This is the numerical content of
BDPV's Lemma 4 at one query, with `|Zᶜ Good| / |Z|` the forbidden fraction. -/
theorem delta_le_of_dominated_by_uniform_on {Z : Type*} [Fintype Z]
    [DecidableEq Z] (Good : Finset Z) (hGood : Good.Nonempty) (p q : NNReal)
    (mu nu : RandomSystems.Dist Z) (hsupp : ∀ z, z ∉ Good → mu z = 0)
    (hdom : ∀ z ∈ Good, ((mu z : ℝ)) ≤ (p : ℝ) / (Good.card : ℝ))
    (hnu : ∀ z, ((nu z : ℝ)) = (q : ℝ) / (Fintype.card Z : ℝ)) :
    ((δ mu nu : NNReal) : ℝ)
      ≤ (((Fintype.card Z - Good.card : ℕ) : ℝ) / (Fintype.card Z : ℝ)) * (p : ℝ)
          + (((p - q : NNReal) : ℝ)) := by
  classical
  have hGle : Good.card ≤ Fintype.card Z := Finset.card_le_univ Good
  have hn : (0 : ℝ) < (Fintype.card Z : ℝ) := by
    have : 0 < Fintype.card Z := lt_of_lt_of_le (Finset.card_pos.mpr hGood) hGle
    exact_mod_cast this
  have hgpos : (0 : ℝ) < (Good.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hGood
  -- the distance is a sum over `Good`
  have hsub : mu.support ⊆ Good := fun z hz =>
    by_contra fun hzg => (Finsupp.mem_support_iff.mp hz) (hsupp z hzg)
  rw [δ_eq_sum_of_support_subset nu hsub, NNReal.coe_sum]
  -- each summand is at most `p/|Good| − q/|Z|`, truncated
  have hterm : ∀ z ∈ Good, ((mu z - nu z : NNReal) : ℝ)
      ≤ max 0 ((p : ℝ) / (Good.card : ℝ) - (q : ℝ) / (Fintype.card Z : ℝ)) := by
    intro z hz
    rcases le_total (mu z) (nu z) with hle | hle
    · rw [tsub_eq_zero_of_le hle]
      simp
    · rw [NNReal.coe_sub hle, hnu z]
      refine le_max_of_le_right (sub_le_sub (hdom z hz) le_rfl)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- `|Good| · max(0, p/|Good| − q/|Z|) = max(0, p − q|Good|/|Z|)`
  have hP : (0 : ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hQ : (0 : ℝ) ≤ (q : ℝ) := q.coe_nonneg
  have hcast : (((Fintype.card Z - Good.card : ℕ) : ℝ))
      = (Fintype.card Z : ℝ) - (Good.card : ℝ) := Nat.cast_sub hGle
  have hgle : (Good.card : ℝ) ≤ (Fintype.card Z : ℝ) := by exact_mod_cast hGle
  have hng : (0 : ℝ) ≤ (Fintype.card Z : ℝ) - (Good.card : ℝ) := by linarith
  have hgne : ((Good.card : ℝ)) ≠ 0 := ne_of_gt hgpos
  have hnne : ((Fintype.card Z : ℝ)) ≠ 0 := ne_of_gt hn
  rw [hcast]
  rcases le_total (q : ℝ) (p : ℝ) with hpq | hpq
  · rw [show (((p - q : NNReal) : ℝ)) = (p : ℝ) - (q : ℝ) from
      NNReal.coe_sub (by exact_mod_cast hpq)]
    rcases le_total ((p : ℝ) / (Good.card : ℝ))
      ((q : ℝ) / (Fintype.card Z : ℝ)) with h | h
    · rw [max_eq_left (by linarith), mul_zero]
      have h1 : (0 : ℝ) ≤ ((Fintype.card Z : ℝ) - (Good.card : ℝ))
          / (Fintype.card Z : ℝ) * (p : ℝ) :=
        mul_nonneg (div_nonneg hng hn.le) hP
      linarith
    · rw [max_eq_right (by linarith), ← sub_nonneg]
      have hid : ((Fintype.card Z : ℝ) - (Good.card : ℝ)) / (Fintype.card Z : ℝ)
            * (p : ℝ) + ((p : ℝ) - (q : ℝ))
            - (Good.card : ℝ)
              * ((p : ℝ) / (Good.card : ℝ) - (q : ℝ) / (Fintype.card Z : ℝ))
          = ((Fintype.card Z : ℝ) - (Good.card : ℝ)) * ((p : ℝ) - (q : ℝ))
              / (Fintype.card Z : ℝ) := by
        field_simp
        ring
      rw [hid]
      exact div_nonneg (mul_nonneg hng (by linarith)) hn.le
  · rw [show (((p - q : NNReal) : ℝ)) = 0 from by
      rw [tsub_eq_zero_of_le (by exact_mod_cast hpq)]; rfl, add_zero]
    have hmax : max (0 : ℝ)
          ((p : ℝ) / (Good.card : ℝ) - (q : ℝ) / (Fintype.card Z : ℝ))
        ≤ max 0 ((p : ℝ) / (Good.card : ℝ) - (p : ℝ) / (Fintype.card Z : ℝ)) := by
      refine max_le_max le_rfl (sub_le_sub le_rfl ?_)
      gcongr
    refine le_trans (mul_le_mul_of_nonneg_left hmax (by positivity)) ?_
    have hge : (0 : ℝ) ≤ (p : ℝ) / (Good.card : ℝ) - (p : ℝ) / (Fintype.card Z : ℝ) := by
      have : (p : ℝ) / (Fintype.card Z : ℝ) ≤ (p : ℝ) / (Good.card : ℝ) := by
        gcongr
      linarith
    rw [max_eq_right hge]
    refine le_of_eq ?_
    field_simp

/-- **The projected birthday bound.**  Among `N` distinct query points, a uniform
transformation's answers collide in the capacity with probability at most
`(N choose 2)/|C|`.

This is the counting content of Lemma 4, and it is where the security parameter
becomes the *capacity* rather than the whole state. -/
theorem mass_capacityCollision_le (N : ℕ) (xs : Fin N → Node A C)
    (inj : Function.Injective xs) :
    (Dist.uniform (Node A C → Node A C)).mass
        (fun f => ∃ i j : Fin N, i ≠ j ∧ (f (xs i)).2 = (f (xs j)).2)
      ≤ pairCollisionUnionBound C N := by
  classical
  refine mass_le_pairCollisionUnionBound_of_cover C _ N
    (fun p f => (f (xs p.1)).2 = (f (xs p.2)).2) _ ?_ ?_
  · rintro f ⟨i, j, hij, heq⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨(i, j), by simp [queryPairSet, hlt], heq⟩
    · exact ⟨(j, i), by simp [queryPairSet, hgt], heq.symm⟩
  · intro p hp
    have hlt : p.1 < p.2 := by simpa [queryPairSet] using hp
    refine le_of_eq (uniform_capacity_pair_eq_mass (fun h => ?_))
    exact absurd (inj h) (ne_of_lt hlt)

end Counting

/-! ## What remains: the converter and the conditional equivalence

Stated here rather than proved, with the route for each, so the shape of the
remaining work is on the record.

### Lemma 3 — done, as far as it is mathematics

"Any sequence of queries `Q⁰` up to cost `2^c` can be converted to a sequence of
queries `Q¹` where `Q¹` gives at least the same amount of information to the
adversary and has no higher cost."  The sponge is public, so a distinguisher
answers its own `H` queries by walking the chain itself; the content is that the
walk *works*, and that is `walk_rooted` and `walk_bitrate_eq_oracle` above.

What is left is the reduction on distinguishers, which carries no further
mathematics: the distinguisher's own sponge simulation is a **converter**, and
dropping the honest port is monotonicity of the advantage under it — a
converter/DPI step (`RandomSystems.AbsorbDPI`, `TypedConstruct`'s action lemmas),
not a conditional equivalence.  It is also what makes
`SpongeIndifferentiability.lean`'s two-port `condEquiv` architecture unnecessary.
It cannot be written until the two-port resources exist on this file's side.

### Lemma 4 — arithmetic done, probabilistic half open, **and the paper asserts it**

Target: `Δ(𝖱 (Node A C), P[RO]) ≤ fT |C| N` at cost `N < |C|`, with `P[RO]` the
`idealSystem` above.  Two halves.

*Arithmetic — done.*  `fT` is BDPV's `f_T(N) = 1 - ∏(1 - i/2^c)`, and `fT_le`
gives the headline `N(N+1)/2^{c+1}`.  The paper reaches that through
`1 - x ≈ e^{-x}` (eq. 4); `fT_le` proves it outright from the union bound
`1 - ∏(1 - aᵢ) ≤ ∑ aᵢ` (`CR18.Counting.one_sub_sum_le_prod_one_sub`), so nothing here is
approximate.

*Probabilistic — open, and it is not a transcription job.*  The mechanism is
sampling with versus without replacement **on the capacity only**: `𝖱` answers
uniformly on `A × C`, while Algorithm 2's rooted branch draws `t_c` from
`C \ (R ∪ O)`, so `N` rooted answers realise `N` distinct capacities.
`urf_urp_switching` is this shape one level up — full injectivity on the whole
alphabet — whereas this is partial injectivity on a *projection*, so it needs its
own count.

**The gap in the source.**  BDPV's proof of Lemma 4 says "To obtain the greatest
possible variational distance, the optimum strategy consists in creating `N` rooted
nodes" and computes the distance for *that* strategy.  The optimality is asserted,
not proved — and it is asserted at exactly the point a formal proof cannot skip,
since the variational distance has to be bounded for **every** distinguisher, not
for a strategy claimed to be worst-case.  Proving Lemma 4 here therefore means
supplying an argument the paper does not give.  The natural one in this
development's idiom is a hybrid over the `N` queries with the per-step forbidden
set of size `≤ i`, which yields `∑ i/|C|` — the same bound `fT_le` already
delivers, and reachable without the optimality claim.

Note `N` is BDPV's *cost* — total `F` calls, direct or via the sponge (§3.5) — not
a query count.

### The converter

Algorithm 2 as a CR18 Definition 3.8 converter at the adversary interface, over
an ideal resource carrying the random oracle and the coins
`(coinA, coinC) : (A × C → A) × (A × C → Equiv.Perm C)`.

Build it on the general `PFunConverter.ProtocolFn`, which is
`List U × List (Option Y) →. X ⊕ V` — the whole transcript, so the graph persists
and nothing replays.  `IsDDC` then has to be discharged by hand (`AnswersInY`
plus a uniform round bound) rather than through `isDDC_ofStep`; the round bound is
`1` oracle query plus the coin draw, since `answer` consults the oracle at most
once.  Do **not** use `ofHistoryStep`: it drops completed rounds' answers, which
is what forced the quadratic replay recorded in `STATUS.md` §11.35. -/

end RandomSystemsCC.Symmetric.SpongeBDPV
