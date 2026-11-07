import TheThirdGapOriginalPriceAndTheActualSingletonRegularException
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem true_third_gap_taxes (Z N c rho r x y:ℕ) (fit:5*N≤11*Z) (size:N=2*Z+c) (roots:c≤r+rho)
    (px:0<x) (py:0<y) :
    2*actualCoordinateLoss Z N r x y≤2*Z+(if x+y=4 then rho else 0) := by
  by_cases special:x+y=4
  · rw [if_pos special]
    unfold actualCoordinateLoss
    split_ifs with unit
    · omega
    · have a : x=2 := by omega
      have b : y=2 := by omega
      rw [a,b];dsimp only [pointCoordinateTax,coveredCoordinateTax]
      norm_num;omega
  · have bound := actual_tax_when_mixed Z N c r x y size fit px py
    rw [if_neg special] at bound ⊢;omega

theorem original_exterior_deficit_volume (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (D:ℕ) (exactDegree:D=diagonal F.n F.m (F.r+2)-1) (L:ℕ→ℕ)
    (bill:∀j<D-1,widthAt F.n F.m (F.r+P.cutRoots.ncard) (j+2)≤uniformEnvelope (F.G.induce P.exterior) (j+2)+L j) :
    let h := highestWidth F.n F.m F.r
    let Z := P.capacity
    let d := F.rank-matchingEdges F.G
    (D:ℤ)*Z+1≤(Z:ℤ)+d+(∑j∈Finset.range (D-1),L j:ℕ)+P.gamma h := by
  subst D
  let D := diagonal F.n F.m (F.r+2)-1
  intro h Z d
  let Y := F.G.induce P.exterior
  let r := F.r+P.cutRoots.ncard
  let obs := ∑j∈Finset.range (D-1),uniformEnvelope Y (j+2)
  let loss := ∑j∈Finset.range (D-1),L j
  let area := ∑j∈Finset.range D,widthAt F.n F.m r (j+1)
  have size := (strict_payable_exterior_constraints F paid P).2.2.2.1
  change rowCount F.s F.t r=Z+matchingEdges Y+d at size
  have volume := (envelope_reserve_account Y (D-1)).1
  change _+(matchingEdges Y+obs)=Y.edgeSet.ncard at volume
  have degree : 0<D := by have low : 11≤D := strict_source_degree_at_least_eleven F paid;omega
  have split := Finset.sum_range_succ' (fun j => widthAt F.n F.m r (j+1)) (D-1)
  rw [show D-1+1=D by omega] at split
  change area=(∑j∈Finset.range (D-1),widthAt F.n F.m r (j+2))+widthAt F.n F.m r 1 at split
  have first : widthAt F.n F.m r 1=rowCount F.s F.t r := first_layer_complete F.hs F.ht F.n F.m F.pn F.pm r
  rw [first] at split
  have sum := Finset.sum_le_sum (s:=Finset.range (D-1)) (fun j hj => bill j (Finset.mem_range.mp hj))
  rw [Finset.sum_add_distrib] at sum
  change (∑j∈Finset.range (D-1),widthAt F.n F.m r (j+2))≤obs+loss at sum
  have price := original_physical_truncated_profile F paid P 0
  simp only [add_zero,Nat.cast_zero,mul_zero] at price
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(area:ℤ)+P.gamma h at price
  change (D:ℤ)*Z+1≤(Z:ℤ)+d+loss+P.gamma h
  omega

#print axioms true_third_gap_taxes
#print axioms original_exterior_deficit_volume
end JSP452Audit.StarHost
