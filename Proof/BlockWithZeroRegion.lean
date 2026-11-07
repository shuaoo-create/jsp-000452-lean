import ManyMateBlocks
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Adding the genuine zero region to a single pointed block keeps the
independent-set bound of two. This holds even when the zero region is empty. -/
theorem block_with_zero_region_small (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w : X) (hw : w∉N.verts)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1) :
    NoIndependentTriple (H.induce (mateBlock H N w ∪ zeroMateRegion H N)) := by
  have independent : H.IsIndepSet N.vertsᶜ := by
    intro a ha b hb _ edge
    exact hb (missed_neighbors_subset H N hm max ha edge)
  apply noIndependentTriple_of_set_bound
  apply independent_set_in_separated_block_le_two H N.vertsᶜ _ w hw independent limit
  · apply Set.disjoint_left.mpr
    rintro x (hx|⟨y,xy,_⟩) hu
    · exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N w) hx hu
    · exact hu.1 (N.edge_vert xy)
  · rintro x (hx|⟨y,_,away,_⟩) u hu
    · exact mateBlock_separated H N hm max hw x hx u hu
    · exact away u hu.1

#print axioms block_with_zero_region_small
end JSP452Audit.StarHost
