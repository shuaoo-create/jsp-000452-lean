import ActualOuterEndpointsOfTheTenDegreeMatchingPorts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem induced_edges_on_disjoint_union {X:Type u} [Finite X] (G:SimpleGraph X) (A B:Set X) (dis:Disjoint A B) :
    (G.induce (A∪B)).edgeSet.ncard=(G.induce A).edgeSet.ncard+(G.induce B).edgeSet.ncard+crossCount G A B := by
  have eq := crossCount_self G (A∪B)
  rw [cut_cross_union_right G (A∪B) A B dis,crossCount_swap G (A∪B) A,crossCount_swap G (A∪B) B,
    cut_cross_union_right G A A B dis,cut_cross_union_right G B A B dis,crossCount_swap G B A,
    crossCount_self G A,crossCount_self G B] at eq
  omega

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)
def enlargedSupport := K.support∪K.exteriorTargetEnds
def remainder := K.enlargedSupportᶜ

theorem disjoint_ends : Disjoint K.support K.exteriorTargetEnds := Set.disjoint_left.mpr (fun _ h m => m.1 h)

theorem true_exterior_partition : K.exteriorTargetEnds∪K.remainder=K.supportᶜ := by
  ext x
  constructor
  · rintro (e|r);exact e.1;exact fun h => r (Or.inl h)
  · intro out;by_cases e:x∈K.exteriorTargetEnds
    · exact Or.inl e
    · exact Or.inr (fun h => h.elim out e)

theorem no_matching_crosses_enlarged_support (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (M:G.Subgraph) (hm:M.IsMatching) (attained:(exposedFull G M 10).ncard=K.score+2) :
    ∀x∈K.enlargedSupport,∀y∈K.remainder,¬M.Adj x y := by
  intro x inc y outside e
  have out : y∉K.support := fun h => outside (Or.inl h)
  rcases inc with w|port
  · rcases w with (s|t)|j
    · have zero := (K.matching_endpoint_saturation cap M hm attained).2.2.2.1
      exact no_edge_when_port_zero M.spanningCoe zero s out e
    · exact outside (Or.inr (show y∈K.exteriorTargetEnds from ⟨out,x,t,M.adj_sub e⟩))
    · obtain root|inside := regionCore_neighbor G K.roots K.pieces j (M.adj_sub e)
      · obtain ⟨v,_,rfl⟩ := root;exact out (Or.inl v.property)
      · exact out (Or.inr inside)
  · exact K.exterior_end_has_no_exterior_matching_edge cap M hm attained x port y out e

theorem enlarged_induced_matching_edges (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    (M.spanningCoe.induce K.enlargedSupport).edgeSet.ncard=matchingEdges K.incidentPiece := by
  let R := M.spanningCoe
  let E := K.exteriorTargetEnds
  have union := induced_edges_on_disjoint_union R K.support E K.disjoint_ends
  have noRight := K.exterior_end_has_no_exterior_matching_edge cap M hm attained
  have empty : R.induce E=⊥ := by ext a b;exact ⟨fun e => (noRight a.val a.property b.val b.property.1 e).elim,False.elim⟩
  have noCross := K.no_matching_crosses_enlarged_support cap M hm attained
  have zero : crossCount R K.support K.remainder=0 := crossCount_of_no_edges R _ _
    (fun x hx y hy => noCross x (Or.inl hx) y hy)
  have dis : Disjoint E K.remainder := disjoint_compl_right.mono_left Set.subset_union_right
  have part := cut_cross_union_right R K.support E K.remainder dis
  rw [K.true_exterior_partition,zero,Nat.add_zero] at part
  have piece := (K.global_optimum_inside_piece cap M hm attained).1
  have fee := incident_piece_edge_count R K.support
  change (eraseInternal R K.supportᶜ).edgeSet.ncard=_ at piece
  rw [←K.incident_piece_rank cap M hm attained] at piece
  rw [empty] at union
  simp only [SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero] at union
  change (R.induce (K.support∪E)).edgeSet.ncard=_;omega

theorem enlarged_and_remainder_rank (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (best:M.edgeSet.ncard=matchingEdges G) (attained:(exposedFull G M 10).ncard=K.score+2) :
    matchingEdges (G.induce K.enlargedSupport)=matchingEdges K.incidentPiece ∧
    (M.spanningCoe.induce K.remainder).edgeSet.ncard=matchingEdges (G.induce K.remainder) ∧
    matchingEdges G=matchingEdges K.incidentPiece+matchingEdges (G.induce K.remainder) := by
  let R := M.spanningCoe
  have none : crossCount R K.enlargedSupport K.remainder=0 := crossCount_of_no_edges R _ _
    (K.no_matching_crosses_enlarged_support cap M hm attained)
  have inside := K.enlarged_induced_matching_edges cap M hm attained
  have split := erase_internal_edge_count R K.remainder
  have inc := incident_piece_edge_count R K.enlargedSupport
  change (eraseInternal R K.remainder).edgeSet.ncard=(R.induce K.enlargedSupport).edgeSet.ncard+
    crossCount R K.enlargedSupport K.remainder at inc
  have bound := ranks_of_complementary_induced_sets G K.enlargedSupport
  change matchingEdges (G.induce K.enlargedSupport)+matchingEdges (G.induce K.remainder)≤matchingEdges G at bound
  have ib := edges_of_matching_inside_set M hm K.enlargedSupport
  have ob := edges_of_matching_inside_set M hm K.remainder
  change R.edgeSet.ncard=matchingEdges G at best
  change (R.induce K.enlargedSupport).edgeSet.ncard=_ at inside
  change (R.induce K.enlargedSupport).edgeSet.ncard≤_ at ib
  change (R.induce K.remainder).edgeSet.ncard≤_ at ob
  change matchingEdges (G.induce K.enlargedSupport)=matchingEdges K.incidentPiece ∧
    (R.induce K.remainder).edgeSet.ncard=matchingEdges (G.induce K.remainder) ∧
    matchingEdges G=matchingEdges K.incidentPiece+matchingEdges (G.induce K.remainder)
  omega
end TenOuterCut
#print axioms induced_edges_on_disjoint_union
#print axioms TenOuterCut.no_matching_crosses_enlarged_support
#print axioms TenOuterCut.enlarged_induced_matching_edges
#print axioms TenOuterCut.enlarged_and_remainder_rank
end JSP452Audit.StarHost
