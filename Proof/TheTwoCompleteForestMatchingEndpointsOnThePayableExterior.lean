import BothOriginalListsStillEscapeOnThePaidPhysicalExterior
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem whole_forest_endpoint_on_summand {A B:Type*} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    {s t r:ℕ} (hs:0<s) (n:Fin s→ℕ) (m:Fin t→ℕ) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r) (legal:r<t) :
    ForestMatchingEndpoint Y n (t-r-matchingEdges C) := by
  intro R incl
  have orig := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors incl (bot_le : (⊥:SimpleGraph B)≤C)
  rcases orig _ both with red|blue
  · left
    have eq : (fun i:Fin s => padDemand n (0+i.val))=n := by funext i;simp [padDemand,i.isLt]
    change (forest (fun i:Fin s => padDemand n (0+i.val))).IsContained _ at red
    rw [eq] at red
    exact copy_in_left_summand R _ (forest_has_neighbor n pn) red
  · right
    rw [comp,sdiff_bot] at blue
    have rank := forest_copy_matching _ (fun j:Fin (t-r) => padDemand m (r+j.val))
      (fun j => pad_positive m pm _ (by have := j.isLt;omega)) blue
    rw [Fintype.card_fin,matchingEdges_sumGraph] at rank
    omega

theorem strict_payable_exterior_endpoints (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let d := F.rank-matchingEdges F.G
    let p := F.t-r-P.capacity
    let q := F.s-r-P.capacity
    matchingEdges Y+d+1=F.s+p ∧ matchingEdges Y+d+1=F.t+q ∧
    ForestMatchingEndpoint Y F.n p ∧ ForestMatchingEndpoint Y F.m q ∧
    2*(d+∑i,(F.n i-1)/2)≤p ∧ 2*(d+∑j,(F.m j-1)/2)≤q := by
  intro Y r d p q
  obtain ⟨long,_,pos,rank,_,row⟩ := strict_payable_exterior_constraints F paid P
  change P.capacity+r+d+1≤min F.s F.t at long
  obtain ⟨ls,lt⟩ := le_min_iff.mp long
  change F.s+F.t-1-r=P.capacity+matchingEdges Y+d at rank
  have a : matchingEdges Y+d+1=F.s+p := by dsimp only [p];omega
  have b : matchingEdges Y+d+1=F.t+q := by dsimp only [q];omega
  have nend : ForestMatchingEndpoint Y F.n p := whole_forest_endpoint_on_summand _ _ F.hs F.n F.m F.pn F.pm row (by omega)
  have mend : ForestMatchingEndpoint Y F.m q := whole_forest_endpoint_on_summand _ _ F.ht F.m F.n F.pm F.pn
    (swap_positive_forcing_row _ _ _ row) (by omega)
  exact ⟨a,b,nend,mend,endpoint_forest_parity_cost Y F.n F.pn nend pos (by dsimp only [p];omega)
    (positive_endpoint_rank Y F.hs F.n F.pn nend) a,endpoint_forest_parity_cost Y F.m F.pm mend pos
    (by dsimp only [q];omega) (positive_endpoint_rank Y F.ht F.m F.pm mend) b⟩

#print axioms whole_forest_endpoint_on_summand
#print axioms strict_payable_exterior_endpoints
end JSP452Audit.StarHost
