import UpperAndLowerDeficiencyForTheSameSupport
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem maximum_matching_supported_inside {X:Type u} [Finite X] (G:SimpleGraph X) (A:Set X) :
    ∃M:G.Subgraph,M.IsMatching ∧ M.verts⊆A ∧ matchingEdges (G.induce A)≤M.edgeSet.ncard := by
  obtain ⟨L,matchL,best⟩ := exists_maximum_matching (G.induce A)
  let e := SimpleGraph.Embedding.induce (G:=G) A
  let M := L.map e.toHom
  have contains : L.spanningCoe.IsContained M.spanningCoe := by
    refine ⟨{toHom:={toFun:=fun x => x.val,map_rel':=?_},injective':=Subtype.val_injective}⟩
    intro x y adj;exact ⟨x,y,adj,rfl,rfl⟩
  refine ⟨M,matchL.map e.toHom e.injective,?_,best ▸ edge_ncard_le_of_copy contains⟩
  rintro _ ⟨x,_,rfl⟩
  exact x.property

theorem induced_subset_cut_bound {X:Type u} [Finite X] (G:SimpleGraph X) (A U:Set X) (inside:U⊆A) :
    matchingEdges (G.induce A)≤U.ncard+matchingEdges (G.induce (A\U)) := by
  let V : Set ↥A := {x | x.val∈U}
  let lift : V ≃ U := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,inside x.property⟩,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let iso : ((G.induce A).induce Vᶜ) ≃g G.induce (A\U) := {
    toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  have price := matching_rank_le_cut_add (G.induce A) V
  have vCard : V.ncard=U.ncard := Nat.card_congr lift
  rw [vCard,rank_eq_of_graph_iso iso] at price
  exact price

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem rank_upper_after_source_deletions (cap:∀x,Nat.card (G.neighborSet x)≤10) (I:Set X) (inside:I⊆K.S) :
    2*matchingEdges (G.induce (K.support\I))+K.score+2+K.rootDefect K.T+
      crossCount G K.T K.supportᶜ+2*I.ncard≤K.support.ncard := by
  obtain ⟨M,hm,stays,rank⟩ := maximum_matching_supported_inside G (K.support\I)
  have zero : crossCount M.spanningCoe K.T K.supportᶜ=0 := by
    apply crossCount_of_no_edges;intro x _ y out edge
    exact out (stays (M.edge_vert edge.symm)).1
  have fee := K.restricted_matching_deficit_bound cap M hm zero
  have missed := split_covered_and_uncovered K.support M.verts
  have covered : K.support∩M.verts=M.verts := Set.inter_eq_right.mpr (fun _ hit => (stays hit).1)
  rw [covered,matching_vertices_eq_twice_edges hm] at missed
  have sub : I⊆K.S\M.verts := fun x hx => ⟨inside hx,fun hit => (stays hit).2 hx⟩
  have count := Set.ncard_le_ncard sub
  omega

theorem exact_support_matching_rank (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    (M.spanningCoe.induce K.support).edgeSet.ncard=matchingEdges (G.induce K.support) ∧
    2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+crossCount G K.T K.supportᶜ=K.support.ncard ∧
    ∀I:Set X,I⊆K.S → matchingEdges (G.induce K.support)=I.ncard+matchingEdges (G.induce (K.support\I)) := by
  have inner := K.optimal_internal_deficit cap M hm attained
  have best := edges_of_matching_inside_set M hm K.support
  have upper := K.rank_upper_after_source_deletions cap ∅ (Set.empty_subset _)
  have emptyEq : K.support\(∅:Set X)=K.support := by ext x;simp
  have sameRank := congrArg (fun A:Set X => matchingEdges (G.induce A)) emptyEq
  change matchingEdges (G.induce (K.support\(∅:Set X)))=matchingEdges (G.induce K.support) at sameRank
  rw [sameRank] at upper
  simp only [Set.ncard_empty,Nat.mul_zero,Nat.add_zero] at upper
  change 2*(M.spanningCoe.induce K.support).edgeSet.ncard+K.score+2+K.rootDefect K.T+crossCount G K.T K.supportᶜ=K.support.ncard at inner
  refine ⟨by omega,by omega,?_⟩
  intro I sub
  have low := induced_subset_cut_bound G K.support I (fun x hx => Or.inl (Or.inl (sub hx)))
  have high := K.rank_upper_after_source_deletions cap I sub
  omega
end TenOuterCut
#print axioms maximum_matching_supported_inside
#print axioms induced_subset_cut_bound
#print axioms TenOuterCut.rank_upper_after_source_deletions
#print axioms TenOuterCut.exact_support_matching_rank
end JSP452Audit.StarHost
