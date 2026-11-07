import TransportTheActualTenDegreeSupportAndItsPorts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X Y:Type u} [Finite X] [Finite Y] (G:SimpleGraph X) (H:SimpleGraph Y)

theorem incident_sum_with_whole_component (U:Set Y) :
    eraseInternal (G⊕g H) (sumLabels (Set.univ:Set X) U)ᶜ=G⊕g eraseInternal H Uᶜ := by
  ext x y
  rcases x with x|x <;> rcases y with y|y
  · change (G.Adj x y ∧ ¬(x∉(Set.univ:Set X) ∧ y∉Set.univ)) ↔ G.Adj x y
    simp
  · exact ⟨fun e => (not_adj_sum_inl_inr x y e.1).elim,fun e => (not_adj_sum_inl_inr x y e).elim⟩
  · exact ⟨fun e => (not_adj_sum_inl_inr y x e.1.symm).elim,fun e => (not_adj_sum_inl_inr y x e.symm).elim⟩
  · rfl

namespace TenPortSupport
variable {G H}
noncomputable def add_closed_component {Q:TenBlockPartition G} {R:TenBlockPartition H} {h:ℕ}
    (W:TenPortSupport H R h) (empty:Q.rest=∅) (near:Nat.card X=2*matchingEdges G+1)
    (large:11≤Nat.card X) (regular:G.edgeSet.ncard=5*Nat.card X) : TenPortSupport (G⊕g H) (Q.join R) (h+1) := by
  let U := sumLabels (Set.univ:Set X) W.support
  have count : U.ncard=Nat.card X+W.support.ncard := by
    change (sumLabels _ _).ncard=_
    rw [sum_labels_count,Set.ncard_univ]
  have all := induceUnivIso G
  have irank : matchingEdges ((G⊕g H).induce U)=matchingEdges G+matchingEdges (H.induce W.support) := by
    rw [show U=sumLabels Set.univ W.support from rfl,sum_labels_rank,rank_eq_of_graph_iso all]
  have edges : ((G⊕g H).induce U).edgeSet.ncard=G.edgeSet.ncard+(H.induce W.support).edgeSet.ncard := by
    have iso := inducedSumLabelsIso G H Set.univ W.support
    change ((G⊕g H).induce (sumLabels Set.univ W.support)).edgeSet.ncard=_
    have eq : ((G.induce Set.univ)⊕g (H.induce W.support)).edgeSet.ncard=((G⊕g H).induce U).edgeSet.ncard := Nat.card_congr iso.mapEdgeSet
    have eqAll : (G.induce Set.univ).edgeSet.ncard=G.edgeSet.ncard := Nat.card_congr all.mapEdgeSet
    rw [edge_ncard_sumGraph,eqAll] at eq;exact eq.symm
  have piece := incident_sum_with_whole_component G H W.support
  change eraseInternal (G⊕g H) Uᶜ=_ at piece
  have rank : matchingEdges (eraseInternal (G⊕g H) Uᶜ)=matchingEdges G+matchingEdges (eraseInternal H W.supportᶜ) := by rw [piece,matchingEdges_sumGraph]
  have cross : crossCount (G⊕g H) U Uᶜ=crossCount H W.support W.supportᶜ := by
    have a := incident_piece_edge_count (G⊕g H) U
    rw [piece,edge_ncard_sumGraph,edges] at a
    have b := incident_piece_edge_count H W.support
    omega
  have bot : G.induce Q.rest=⊥ := by
    ext x y
    have no (v:X) (mem:v∈Q.rest) : False := by rw [empty] at mem;exact mem
    exact (no x.val x.property).elim
  have split := Q.rank
  rw [bot,matchingEdges_bot,Nat.add_zero] at split
  have qrank : matchingEdges G=Q.roots.ncard+Q.capacity := split
  have joined : (Q.join R).roots.ncard+(Q.join R).capacity=
      Q.roots.ncard+Q.capacity+(R.roots.ncard+R.capacity) := by
    change (sumLabels Q.roots R.roots).ncard+matchingEdges ((G⊕g H).induce (sumLabels Q.core R.core))=_
    rw [sum_labels_count,sum_labels_rank]
    change _+_+(Q.capacity+R.capacity)=_;omega
  refine ⟨U,W.targetPorts,W.targetDefect,?_,?_,?_,?_,?_,?_,?_⟩
  · have := W.orderFloor;omega
  · rw [rank,joined,←qrank,←W.regionRank]
  · rw [rank,irank,W.portRank];omega
  · have := W.order;omega
  · have := W.edges;omega
  · rw [cross];exact W.ports
  · rw [cross];exact W.defect

#print axioms add_closed_component
end TenPortSupport
#print axioms incident_sum_with_whole_component
end JSP452Audit.StarHost
