import TheTwoCompleteForestMatchingEndpointsOnThePayableExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_payable_full_profile (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    (Y.edgeSet.ncard:ℤ)+(D:ℤ)*P.capacity+1≤(rowEnergy F.n F.m r:ℤ)+P.gamma h ∧
    (Y.edgeSet.ncard:ℤ)+1≤(rowEnergy F.n F.m (r+P.capacity):ℤ)+P.gamma h := by
  intro D h Y r
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have fee := P.true_exterior_fee cap h
  change (F.G.edgeSet.ncard:ℤ)+P.gamma h=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(P.cutRoots.ncard+P.capacity)+h at fee
  have prefixCost (a:ℕ) : (rowEnergy F.n F.m F.r:ℤ)≤(rowEnergy F.n F.m (F.r+a):ℤ)+(D:ℤ)*a+h := by
    exact_mod_cast prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r a F.live
  have strict : (F.G.edgeSet.ncard:ℤ)+1≤rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  have one := prefixCost P.cutRoots.ncard
  have both := prefixCost (P.cutRoots.ncard+P.capacity)
  change _≤(rowEnergy F.n F.m r:ℤ)+_+_ at one
  rw [←Nat.add_assoc] at both
  change _≤(rowEnergy F.n F.m (r+P.capacity):ℤ)+_+_ at both
  push_cast at both
  constructor <;> linarith only [fee,strict,one,both]

theorem payable_exterior_refuses_full_shift (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    ¬ForcingRow (F.G.induce P.exterior) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+P.cutRoots.ncard+P.capacity) := by
  intro row
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  let h := highestWidth F.n F.m F.r
  have weight := (P.exact_weight_and_root_cost E cap h).2.2.2.2.1
  change (P.shortfall:ℤ)+(F.G.induce P.cutRoots).edgeSet.ncard+h-P.weight≤0 at credit
  have progress : 0<P.capacity := by change 0<h at hp;omega
  have live := F.live
  have smaller : rowCount F.s F.t (F.r+P.cutRoots.ncard+P.capacity)<F.rank := by
    change _<rowCount F.s F.t F.r
    dsimp only [rowCount] at live ⊢;omega
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ row smaller
  have lose := (strict_payable_full_profile F paid P).2
  change _≤_+((P.shortfall:ℤ)+(F.G.induce P.cutRoots).edgeSet.ncard+h-P.weight) at lose
  omega

#print axioms strict_payable_full_profile
#print axioms payable_exterior_refuses_full_shift
end JSP452Audit.StarHost
