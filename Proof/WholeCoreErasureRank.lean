import StrictSourceWholeListConstraints
import EraseClosedEdges
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private def matchingInColour {G : SimpleGraph X} (M : G.Subgraph) (A : SimpleGraph X) : A.Subgraph where
  verts := {x | ∃y,M.Adj x y ∧ A.Adj x y}
  Adj x y := M.Adj x y ∧ A.Adj x y
  adj_sub := fun h => h.2
  edge_vert := fun {x y} h => ⟨y,h⟩
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩

private theorem matchingInColour_matching {G : SimpleGraph X} (M : G.Subgraph)
    (hm : M.IsMatching) (A : SimpleGraph X) : (matchingInColour M A).IsMatching := by
  rintro v ⟨w,edge⟩
  refine ⟨w,edge,?_⟩
  intro u hu
  exact hm.eq_of_adj_left hu.1 edge.1

theorem rank_of_two_edge_colours (G A B : SimpleGraph X) (cover : G≤A⊔B) :
    matchingEdges G≤matchingEdges A+matchingEdges B := by
  obtain ⟨M,hm,max⟩ := exists_maximum_matching G
  let P := matchingInColour M A
  let Q := matchingInColour M B
  have pcap := le_matchingEdges (matchingInColour_matching M hm A)
  have qcap := le_matchingEdges (matchingInColour_matching M hm B)
  have sub : M.edgeSet⊆P.edgeSet∪Q.edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro edge
      have me : M.Adj x y := edge
      rcases (show A.Adj x y ∨ B.Adj x y from cover (M.adj_sub me)) with red|blue
      · exact Or.inl (show P.Adj x y from ⟨me,red⟩)
      · exact Or.inr (show Q.Adj x y from ⟨me,blue⟩)
  have bound := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le _ _)
  exact max ▸ bound.trans (Nat.add_le_add pcap qcap)

theorem rank_of_internal_edges (G : SimpleGraph X) (U : Set X) :
    matchingEdges (G \ eraseInternal G U)=matchingEdges (G.induce U) := by
  classical
  let B := G \ eraseInternal G U
  have characterize (x y:X) : B.Adj x y ↔ G.Adj x y ∧ x∈U ∧ y∈U := by
    change (G.Adj x y ∧ ¬(G.Adj x y ∧ ¬(x∈U ∧ y∈U))) ↔ _
    tauto
  have inside : B.induce U=G.induce U := by
    ext a b
    exact ⟨fun h => ((characterize _ _).mp h).1,fun h => (characterize _ _).mpr ⟨h,a.property,b.property⟩⟩
  have none : eraseInternal B U=⊥ := by
    ext a b
    exact ⟨fun h => h.2 ((characterize a b).mp h.1).2,False.elim⟩
  have split := erase_closed_matching_rank B U (fun a _ b hb edge => hb ((characterize a b).mp edge).2.2)
  simpa only [none,inside,matchingEdges_bot,Nat.zero_add] using split

/-- The same host type is retained. Exactly the internal edges of K.core
are erased; all root edges and every exterior edge stay in the graph. -/
theorem whole_core_erasure_exact_rank (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D) :
    matchingEdges (eraseInternal G K.core)=K.roots.ncard+matchingEdges (G.induce K.rest) := by
  let Z := eraseInternal G K.core
  obtain ⟨cover,apart,sep⟩ := core_rest_partition G K.barrier K.pieces
  let iso := regionSumIso Z K.rootsᶜ K.core K.rest cover apart (fun _ hx _ hy e => sep hx hy e.1)
  have ext : Z.induce K.rest=G.induce K.rest := by
    ext a b
    exact ⟨fun e => e.1,fun e => ⟨e,fun k => Set.disjoint_left.mp apart k.1 a.property⟩⟩
  have rank := (rank_eq_of_graph_iso iso).symm
  have empty : Z.induce K.core=⊥ := eraseInternal_induce_inside G K.core
  rw [matchingEdges_sumGraph,empty,ext,matchingEdges_bot,Nat.zero_add] at rank
  have upper := matching_rank_le_cut_add Z K.roots
  rw [rank] at upper
  have partition := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=K.roots.ncard+matchingEdges (G.induce K.core)+matchingEdges (G.induce K.rest) at partition
  have lower := rank_of_two_edge_colours G Z (G \ Z) (by
    intro a b edge
    by_cases h : Z.Adj a b
    · exact Or.inl h
    · exact Or.inr ⟨edge,h⟩)
  change matchingEdges G≤matchingEdges Z+matchingEdges (G \ eraseInternal G K.core) at lower
  rw [rank_of_internal_edges] at lower
  change matchingEdges Z=K.roots.ncard+matchingEdges (G.induce K.rest)
  exact Nat.le_antisymm upper (by omega)

#print axioms rank_of_two_edge_colours
#print axioms rank_of_internal_edges
#print axioms whole_core_erasure_exact_rank
end JSP452Audit.StarHost
