import WholeComponentSubsetSumMenu
open private JSP452Audit.StarHost.piece_sup_adj from WholeComponentPieces
namespace JSP452Audit.StarHost
open SimpleGraph

def labelledPart {X:Type*} (G:SimpleGraph X) (c:G.ConnectedComponent) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ x∈c.supp
  symm := ⟨fun _ _ h => ⟨h.1.symm,(c.mem_supp_congr_adj h.1).mp h.2⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

theorem component_edges_on_labels {I X:Type*} [Finite X] (G:SimpleGraph X)
    (e:I ↪ G.ConnectedComponent) (V:Finset I) :
    let U := componentVertices G (V.map e)
    V.sup (fun i => labelledPart G (e i))=G \ eraseInternal G U := by
  intro U
  ext x y
  rw [JSP452Audit.StarHost.piece_sup_adj]
  change (∃i∈V,G.Adj x y ∧ G.connectedComponentMk x=e i) ↔
    G.Adj x y ∧ ¬(G.Adj x y ∧ ¬(x∈U ∧ y∈U))
  constructor
  · rintro ⟨i,mem,edge,label⟩
    have vx : x∈U := Finset.mem_map.mpr ⟨i,mem,label.symm⟩
    have vy := component_vertices_closed G (V.map e) x vx y edge
    exact ⟨edge,fun h => h.2 ⟨vx,vy⟩⟩
  · intro pair
    have hx : x∈U := by by_contra no;exact pair.2 ⟨pair.1,fun h => no h.1⟩
    obtain ⟨i,mem,label⟩ := Finset.mem_map.mp hx
    exact ⟨i,mem,pair.1,label.symm⟩

theorem original_component_menu_accounts {I X:Type*} [Finite X] (G:SimpleGraph X)
    (e:I ↪ G.ConnectedComponent) (V:Finset I) :
    let H := V.sup (fun i => labelledPart G (e i))
    matchingEdges H=(∑i∈V,matchingEdges (e i).toSimpleGraph) ∧
    H.edgeSet.ncard=∑i∈V,(e i).toSimpleGraph.edgeSet.ncard := by
  intro H
  let U := componentVertices G (V.map e)
  have who : H=G \ eraseInternal G U := component_edges_on_labels G e V
  have sub : eraseInternal G U≤G := eraseInternal_le G U
  have cut : H.edgeSet.ncard+(eraseInternal G U).edgeSet.ncard=G.edgeSet.ncard := by
    rw [who,edgeSet_sdiff]
    exact Set.ncard_sdiff_add_ncard_of_subset (edgeSet_subset_edgeSet.mpr sub)
  have base := erase_internal_edge_count G U
  have eq : H.edgeSet.ncard=(G.induce U).edgeSet.ncard := by omega
  obtain ⟨_,rank,ed⟩ := component_union_accounts G (V.map e)
  change matchingEdges (G.induce U)=_ at rank
  change (G.induce U).edgeSet.ncard=_ at ed
  rw [Finset.sum_map] at rank ed
  exact ⟨by rw [who,rank_of_internal_edges,rank],eq.trans ed⟩

#print axioms component_edges_on_labels
#print axioms original_component_menu_accounts
end JSP452Audit.StarHost
