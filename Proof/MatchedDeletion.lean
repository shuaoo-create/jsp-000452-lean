import CopyEdgeBound
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Lattice.Nat

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Attainable sizes count unordered edges of actual matching subgraphs. -/
def matchingSizes (G : SimpleGraph X) : Set ℕ :=
  {k | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k}

/-- Natural-number matching potential for finite hosts. -/
noncomputable def matchingEdges (G : SimpleGraph X) : ℕ := sSup (matchingSizes G)

private theorem matchingSizes_bdd [Finite X] (G : SimpleGraph X) : BddAbove (matchingSizes G) := by
  refine ⟨G.edgeSet.ncard, ?_⟩
  rintro _ ⟨M, _, rfl⟩
  exact Set.ncard_le_ncard M.edgeSet_subset

theorem exists_maximum_matching [Finite X] (G : SimpleGraph X) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G := by
  have nonempty : (matchingSizes G).Nonempty := by
    let M : G.Subgraph := ⊥
    exact ⟨M.edgeSet.ncard, M, (fun _ hv => False.elim hv), rfl⟩
  exact Nat.sSup_mem nonempty (matchingSizes_bdd G)

theorem le_matchingEdges [Finite X] {G : SimpleGraph X} {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ matchingEdges G :=
  le_csSup (matchingSizes_bdd G) ⟨M, hM, rfl⟩

/-- After removing v, retain actual cross-surviving matched pairs only. In particular,
the mate of v is not incorrectly counted as an isolated matching vertex. -/
def restrictMatched {G : SimpleGraph X} (M : G.Subgraph) (v : X) :
    (G.induce {x | x ≠ v}).Subgraph where
  verts := {x | ∃ y : {z : X // z ≠ v}, M.Adj x.val y.val}
  Adj x y := M.Adj x.val y.val
  adj_sub := fun h => M.adj_sub h
  edge_vert := fun h => ⟨_, h⟩
  symm := ⟨fun _ _ h => h.symm⟩

theorem restrictMatched_isMatching {G : SimpleGraph X} {M : G.Subgraph}
    (hM : M.IsMatching) (v : X) : (restrictMatched M v).IsMatching := by
  rintro x ⟨y, h⟩
  exact ⟨y, h, fun z hz => Subtype.ext (hM.eq_of_adj_left hz h)⟩

private theorem edges_delete_degree [Finite X] (G : SimpleGraph X) (v : X) :
    (G.induce {x | x ≠ v}).edgeSet.ncard = G.edgeSet.ncard - Nat.card (G.neighborSet v) := by
  classical
  let := Fintype.ofFinite X
  have h := (G.card_edgeFinset_induce_compl_singleton v).trans (G.card_edgeFinset_deleteIncidenceSet v)
  have same : ({v}ᶜ : Set X) = {x | x ≠ v} := by ext x; simp
  rw [← same]
  simpa only [← SimpleGraph.card_edgeSet, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using h

theorem restrictMatched_edge_count [Finite X] {G : SimpleGraph X} (M : G.Subgraph) (v : X) :
    (restrictMatched M v).edgeSet.ncard = M.edgeSet.ncard - Nat.card (M.spanningCoe.neighborSet v) :=
  edges_delete_degree M.spanningCoe v

/-- The inclusion of the surviving vertices sends a matching back into the host
and leaves the restored vertex genuinely outside the lifted matching's vertex set. -/
theorem liftMatching_avoids [Finite X] (G : SimpleGraph X) (v : X)
    (M : (G.induce {x | x ≠ v}).Subgraph) (hM : M.IsMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧ M.edgeSet.ncard ≤ N.edgeSet.ncard ∧ v ∉ N.verts := by
  let e := SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}
  let N : G.Subgraph := M.map e.toHom
  have hn : N.IsMatching := hM.map e.toHom e.injective
  have contain : M.spanningCoe.IsContained N.spanningCoe := by
    refine ⟨{ toHom := { toFun := fun x => x.val, map_rel' := ?_ }, injective' := Subtype.val_injective }⟩
    intro x y he
    exact ⟨x, y, he, rfl, rfl⟩
  refine ⟨N, hn, edge_ncard_le_of_copy contain, ?_⟩
  rintro ⟨x, _, h⟩
  exact x.property h

theorem matchingEdges_delete_le [Finite X] (G : SimpleGraph X) (v : X) :
    matchingEdges (G.induce {x | x ≠ v}) ≤ matchingEdges G := by
  obtain ⟨M, hM, size⟩ := exists_maximum_matching (G.induce {x | x ≠ v})
  obtain ⟨N, hN, le, _⟩ := liftMatching_avoids G v M hM
  exact size ▸ le.trans (le_matchingEdges hN)

/-- Removing a vertex discards at most its unique matching edge. -/
theorem matchingEdges_le_delete_add_one [Finite X] (G : SimpleGraph X) (v : X) :
    matchingEdges G ≤ matchingEdges (G.induce {x | x ≠ v}) + 1 := by
  obtain ⟨M, hM, size⟩ := exists_maximum_matching G
  have one : Nat.card (M.spanningCoe.neighborSet v) ≤ 1 :=
    (Set.ncard_le_one (s := M.spanningCoe.neighborSet v)).mpr
      fun _ hx _ hy => hM.eq_of_adj_left hx hy
  have bound := le_matchingEdges (restrictMatched_isMatching hM v)
  rw [restrictMatched_edge_count] at bound
  omega

/-- A maximum matching avoiding v survives unchanged in edge cardinality. -/
theorem matchingEdges_delete_eq_of_avoiding [Finite X] (G : SimpleGraph X) (v : X)
    (avoid : ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧ v ∉ M.verts) :
    matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G := by
  obtain ⟨M, hM, size, miss⟩ := avoid
  have empty : IsEmpty (M.spanningCoe.neighborSet v) :=
    ⟨fun x => miss (M.edge_vert x.property)⟩
  have hz : Nat.card (M.spanningCoe.neighborSet v) = 0 := @Nat.card_of_isEmpty _ empty
  have bound := le_matchingEdges (restrictMatched_isMatching hM v)
  rw [restrictMatched_edge_count, hz, Nat.sub_zero, size] at bound
  exact le_antisymm (matchingEdges_delete_le G v) bound

/-- Equality is equivalent to the existence of a maximum matching that exposes v. -/
theorem matchingEdges_delete_eq_iff_avoiding [Finite X] (G : SimpleGraph X) (v : X) :
    matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G ↔
      ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧ v ∉ M.verts := by
  refine ⟨?_, matchingEdges_delete_eq_of_avoiding G v⟩
  intro same
  obtain ⟨M, hM, size⟩ := exists_maximum_matching (G.induce {x | x ≠ v})
  obtain ⟨N, hN, le, avoids⟩ := liftMatching_avoids G v M hM
  rw [size, same] at le
  exact ⟨N, hN, le_antisymm (le_matchingEdges hN) le, avoids⟩

#print axioms liftMatching_avoids
#print axioms matchingEdges_delete_eq_iff_avoiding
#print axioms matchingEdges
#print axioms exists_maximum_matching
#print axioms le_matchingEdges
#print axioms restrictMatched_isMatching
#print axioms restrictMatched_edge_count
#print axioms matchingEdges_delete_le
#print axioms matchingEdges_le_delete_add_one
#print axioms matchingEdges_delete_eq_of_avoiding
end JSP452Audit.StarHost
