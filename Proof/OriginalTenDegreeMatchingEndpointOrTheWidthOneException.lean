import UncoveredVerticesOnTheTenDegreeTargetRootSet
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_original_matching_endpoint (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0) :
    ∃(K:TenOuterCut F.G) (M:F.G.Subgraph),M.IsMatching ∧ M.edgeSet.ncard=matchingEdges F.G ∧
      (exposedFull F.G M 10).ncard=minimumExposure F.G 10 ∧ highestWidth F.n F.m F.r≤K.score ∧
      (((exposedFull F.G M 10).ncard=K.score+2 ∧ K.S⊆M.verts ∧
        crossCount M.spanningCoe K.S K.supportᶜ=0 ∧ crossCount (F.G \ M.spanningCoe) K.T K.supportᶜ=0) ∨
        (highestWidth F.n F.m F.r=1 ∧ K.score=1 ∧ minimumExposure F.G 10=4)) := by
  obtain ⟨K,wide,price⟩ := strict_ten_cut_when_no_odd_component F paid ten none
  obtain ⟨M,hm,maxM,opt⟩ := minimumExposure_attained F.G 10
  refine ⟨K,M,hm,maxM,opt,wide,?_⟩
  by_cases eq:minimumExposure F.G 10=K.score+2
  · have sat := K.matching_endpoint_saturation (fun x => ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten)
      M hm (opt.trans eq)
    exact Or.inl ⟨opt.trans eq,sat.1,sat.2.2.2.1,sat.2.2.2.2.1⟩
  · have hp := (strict_ten_inventory F paid ten).1
    have bound := (strict_ten_inventory F paid ten).2.2.2.2.2.2 none
    have pos := K.positive
    exact Or.inr ⟨by omega,by omega,by omega⟩

#print axioms strict_ten_original_matching_endpoint
end JSP452Audit.StarHost
