import OnePortPiecesHaveNearPerfectMatchings
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_two_ports_share_one_optimal_matching (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    ∃(K:NineOriginalCut F.G) (M:F.G.Subgraph),M.IsMatching ∧ M.edgeSet.ncard=matchingEdges F.G ∧
      (exposedFull F.G M 9).ncard=minimumExposure F.G 9 ∧
      (highestWidth F.n F.m F.r:ℤ)≤K.eta ∧ K.S.ncard=K.T.ncard+1 ∧
      (∀J:NineOriginalCut F.G,J.eta≤K.eta) ∧
      (∀J:NineOriginalCut F.G,J.eta=K.eta → J.S.ncard+J.T.ncard≤K.S.ncard+K.T.ncard) ∧
      ∃(e:Fin 2↪↥K.onePortBlocks) (port:∀i,K.Port (e i).val),
        let A := Set.range (fun i => (port i).root)
        A⊆K.S ∧ 1≤A.ncard ∧ A.ncard≤2 ∧
          (rootShortfall F.G A 9:ℤ)+2*((F.G.induce A).edgeSet.ncard:ℤ)+K.eta≤6 ∧
          ∀i,let U := K.labels (e i).val
            U.ncard=2*matchingEdges (F.G.induce U)+1 ∧ 5≤matchingEdges (F.G.induce U) ∧
            (M.spanningCoe.induce U).edgeSet.ncard=matchingEdges (F.G.induce U) := by
  obtain ⟨K,pay,gap,best,large,e,ports,sub,lo,hi,debt,_⟩ := strict_nine_has_two_actual_ports F paid nine
  obtain ⟨M,matchM,maximum,opt⟩ := minimumExposure_attained F.G 9
  obtain ⟨hp,_,_,few,_⟩ := strict_nine_original_peak F paid nine
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  refine ⟨K,M,matchM,maximum,opt,pay,gap,best,large,e,ports,sub,lo,hi,debt,?_⟩
  intro i
  obtain ⟨_,internal,order,size⟩ := K.one_port_actual_inner_matching cap few gap (by omega) M matchM opt
    (e i).val (e i).property
  exact ⟨order,size,internal⟩

#print axioms strict_nine_two_ports_share_one_optimal_matching
end JSP452Audit.StarHost
