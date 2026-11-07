import MixedAndUnitRealComplementTax
namespace JSP452Audit.StarHost
open SimpleGraph

def componentVertices {X:Type*} (G:SimpleGraph X) (T:Finset G.ConnectedComponent) : Set X :=
  {v|G.connectedComponentMk v∈T}

theorem component_vertices_closed {X:Type*} (G:SimpleGraph X) (T:Finset G.ConnectedComponent) :
    ∀v∈componentVertices G T,∀w,G.Adj v w → w∈componentVertices G T := by
  intro v hv w edge
  change G.connectedComponentMk w∈T
  rwa [←ConnectedComponent.sound edge.reachable]

theorem component_union_accounts {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent) :
    let U := componentVertices G T
    U.ncard=(∑c∈T,Nat.card c.supp) ∧ matchingEdges (G.induce U)=(∑c∈T,matchingEdges c.toSimpleGraph) ∧
    (G.induce U).edgeSet.ncard=∑c∈T,c.toSimpleGraph.edgeSet.ncard := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have empty : componentVertices G ∅=∅ := by ext v;exact Finset.notMem_empty (G.connectedComponentMk v) |> (fun h => iff_false_intro h)
    have bot : G.induce (componentVertices G ∅)=⊥ := by ext v;exact (Finset.notMem_empty _ v.property).elim
    simp [empty,bot,matchingEdges_bot]
  | @insert c T fresh ih =>
    let V := componentVertices G T
    let U := componentVertices G (insert c T)
    have cover : c.supp∪V=U := by ext x;exact Finset.mem_insert.symm
    have apart : Disjoint c.supp V := Set.disjoint_left.mpr fun _ hc hv =>
      fresh ((show G.connectedComponentMk _=c from hc) ▸ hv)
    have sep (x:X) (hx:x∈c.supp) (y:X) (hy:y∈V) : ¬G.Adj x y := fun edge =>
      Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
    let e := regionSumIso G U c.supp V cover apart sep
    have edges : (c.toSimpleGraph ⊕g G.induce V).edgeSet.ncard=(G.induce U).edgeSet.ncard :=
      Nat.card_congr e.mapEdgeSet
    rw [edge_ncard_sumGraph] at edges
    have verts := Set.ncard_union_eq apart
    rw [cover] at verts
    have rank := rank_split_regions G U c.supp V cover apart sep
    change matchingEdges (G.induce U)=matchingEdges c.toSimpleGraph+matchingEdges (G.induce V) at rank
    obtain ⟨ie,ir,ig⟩ := ih
    change V.ncard=_ at ie
    change matchingEdges (G.induce V)=_ at ir
    change (G.induce V).edgeSet.ncard=_ at ig
    rw [ir] at rank
    rw [ie] at verts
    rw [ig] at edges
    simp only [Finset.sum_insert fresh]
    exact ⟨verts,rank,edges.symm⟩

#print axioms component_vertices_closed
#print axioms component_union_accounts
end JSP452Audit.StarHost
