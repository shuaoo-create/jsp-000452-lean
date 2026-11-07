import OneRealPrefixPaysTheShiftForAllPairsFromGapSix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_gap_six_fixed_successor (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let l := P.paidCore.ncard/6
    let i := l-(r+1)
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    H+6≤D → 0<l ∧ l≤P.capacity ∧ 0<rowCount (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l)) (r+i+l) ∧
      rowCount (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l)) (r+i+l)<F.rank ∧
      ForcingRow X (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l)) (padDemand n) (padDemand m) (r+i+l) ∧ rowEnergy n m (r+i+l)≤X.edgeSet.ncard ∧
      (X.edgeSet.ncard:ℤ)+(D:ℤ)*P.capacity+1≤(rowEnergy F.n F.m (r+i):ℤ)+P.gamma (highestWidth F.n F.m F.r)+((D:ℤ)-H-2)*i := by
  intro D H r C Y l i X n m gap
  obtain ⟨order,_,_,fit,zpos,_,_⟩ := full_capacity_prefix_data F paid P E hp credit
  have caps := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 (highestWidth F.n F.m F.r)
  obtain ⟨_,_,mass,pack,_,_⟩ := caps
  have positiveWeight : 0<P.weight := by dsimp only [ScaledPortPlan.gamma] at credit;omega
  have some : 0<P.positives.ncard := by
    by_contra! zero
    have eq : P.positives.ncard=0 := by omega
    rw [eq] at mass;push_cast at mass;omega
  have packs : D*P.positives.ncard≤2*P.capacity := by exact_mod_cast pack
  have degree := (Nat.mul_le_mul_left D some).trans packs
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  have lp : 0<l := by dsimp only [l];omega
  have lz : l≤P.capacity := by dsimp only [l];omega
  have pref := (six_gap_original_platform_prefix F paid P E hp credit gap).2.2.2 i (Nat.sub_le _ _)
  obtain ⟨size,spent⟩ := pref
  change X.edgeSet.ncard+(H+2)*i≤Y.edgeSet.ncard at spent
  obtain ⟨long,_,_,_,_,start⟩ := strict_payable_exterior_constraints F paid P
  change P.capacity+r+_+1≤min F.s F.t at long
  have next := fixed_core_list_row Y C F.n F.m F.hn F.hm F.pn F.pm start (peakPrefix Y i) l
    (by rw [size];dsimp only [i];omega)
  rw [size] at next
  let W := componentBudget C F.n
  let V := componentBudget C F.m
  have w : W.loss≤P.capacity := component_budget_loss_le C F.n
  have v : V.loss≤P.capacity := component_budget_loss_le C F.m
  let len := rowCount (min F.s (W.len+l)) (min F.t (V.len+l)) (r+i+l)
  have lens : 0<len ∧ len<F.rank := by
    dsimp only [len,rowCount,RemovalBudget.len,StrictFamily.rank,r,i] at *
    omega
  have kn := protected_demand_antitone F.n _ F.hn (W.entries_antitone _ F.hn) l
  have vm := protected_demand_antitone F.m _ F.hm (V.entries_antitone _ F.hm) l
  have pn := protected_demand_positive F.n _ F.pn (W.entries_positive _ F.pn) l
  have pm := protected_demand_positive F.m _ F.pm (V.entries_positive _ F.pm) l
  have hs := F.hs
  have ht := F.ht
  have bill := paid (show 0<min F.s (W.len+l) by omega) (show 0<min F.t (V.len+l) by omega)
    n m kn vm pn pm X (r+i+l) next lens.2
  refine ⟨lp,lz,lens.1,lens.2,next,bill,?_⟩
  have fee := P.true_exterior_fee (minimal_rank_exact_source F paid).2.2.2.1 (highestWidth F.n F.m F.r)
  change (F.G.edgeSet.ncard:ℤ)+_=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(P.cutRoots.ncard+P.capacity)+_ at fee
  have price := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r (P.cutRoots.ncard+i) F.live
  rw [←Nat.add_assoc] at price
  have pr : (rowEnergy F.n F.m F.r:ℤ)≤(rowEnergy F.n F.m (r+i):ℤ)+(D:ℤ)*(P.cutRoots.ncard+i)+highestWidth F.n F.m F.r := by exact_mod_cast price
  have st : (F.G.edgeSet.ncard:ℤ)+1≤rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  have cut : (X.edgeSet.ncard:ℤ)+((H:ℤ)+2)*i≤Y.edgeSet.ncard := by exact_mod_cast spent
  linarith only [pr,st,cut,fee]

#print axioms strict_gap_six_fixed_successor
end JSP452Audit.StarHost
