import TheLargeSurvivingWidthPaysThreeBelowTheOriginalMaximumDegree
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem paid_fixed_exterior_cut (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (U:Set ↥P.exterior) (l:ℕ) (lp:0<l) (lz:l≤P.capacity) (small:U.ncard≤l)
    (legal:l≤F.r+P.cutRoots.ncard+U.ncard+1) :
    let C := F.G.induce P.paidCore
    let Y := (F.G.induce P.exterior).induce Uᶜ
    let r := F.r+P.cutRoots.ncard+U.ncard+l
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    let s := min F.s ((componentBudget C F.n).len+l)
    let t := min F.t ((componentBudget C F.m).len+l)
    0<rowCount s t r ∧ rowCount s t r<F.rank ∧ ForcingRow Y s t (padDemand n) (padDemand m) r ∧ rowEnergy n m r≤Y.edgeSet.ncard := by
  intro C Y r n m s t
  obtain ⟨long,_,_,_,_,start⟩ := strict_payable_exterior_constraints F paid P
  let W := componentBudget C F.n
  let V := componentBudget C F.m
  have w : W.loss≤P.capacity := component_budget_loss_le C F.n
  have v : V.loss≤P.capacity := component_budget_loss_le C F.m
  have next := fixed_core_list_row _ C F.n F.m F.hn F.hm F.pn F.pm start U l legal
  have lens : 0<rowCount s t r ∧ rowCount s t r<F.rank := by
    dsimp only [s,t,r,StrictFamily.rank,rowCount,RemovalBudget.len]
    change (componentBudget C F.n).loss≤P.capacity at w
    change (componentBudget C F.m).loss≤P.capacity at v
    omega
  have hs := F.hs
  have ht := F.ht
  exact ⟨lens.1,lens.2,next,paid (show 0<s by dsimp only [s];omega) (show 0<t by dsimp only [t];omega) n m
    (protected_demand_antitone F.n _ F.hn (W.entries_antitone _ F.hn) l)
    (protected_demand_antitone F.m _ F.hm (V.entries_antitone _ F.hm) l)
    (protected_demand_positive F.n _ F.pn (W.entries_positive _ F.pn) l)
    (protected_demand_positive F.m _ F.pm (V.entries_positive _ F.pm) l) Y r next lens.2⟩

#print axioms paid_fixed_exterior_cut
end JSP452Audit.StarHost
