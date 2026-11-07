import OnlyFiveHeadGapsRemainForTheOfficialSizeRamseyEquation
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem truncated_shift_single_peak (F:StrictFamily.{u}) (k:ℕ) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    rowEnergy F.n F.m F.r≤(∑j∈Finset.range D,widthAt F.n F.m (F.r+k) (j+1))+D*k+h := by
  intro D h
  have top : diagonal F.n F.m (F.r+2)≤D+1 := by dsimp only [D];omega
  have last : widthAt F.n F.m F.r (D+1)≤h := by
    apply Finset.card_le_card
    intro j hj
    obtain ⟨time,high⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr;refine ⟨time,?_⟩
    have room := Finset.mem_range.mp time
    change D+1≤diagonal F.n F.m (F.r+j+2) at high
    exact le_antisymm (earlier_diagonal_dominates F.hs F.ht F.n F.m F.hn F.hm (show F.r≤F.r+j by omega)
      (by dsimp only [rowCount] at room;omega)) (top.trans high)
  have area := profile_area_after_any_shift F.hs F.ht F.n F.m F.hn F.hm (show F.r≤F.r from le_rfl) top
  rw [Finset.sum_range_succ] at area
  have pred (j:ℕ) (_:j∈Finset.range D) : widthAt F.n F.m F.r (j+1)≤widthAt F.n F.m (F.r+k) (j+1)+k := by
    rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm];omega
  have sub := Finset.sum_le_sum pred
  rw [Finset.sum_add_distrib] at sub
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sub
  omega

theorem original_physical_truncated_profile (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (i:ℕ) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    (Y.edgeSet.ncard:ℤ)+(D:ℤ)*P.capacity+1≤
      ((∑j∈Finset.range D,widthAt F.n F.m (r+i) (j+1):ℕ):ℤ)+P.gamma h+(D:ℤ)*i := by
  intro D h Y r
  let area := ∑j∈Finset.range D,widthAt F.n F.m (r+i) (j+1)
  have fee := P.true_exterior_fee (minimal_rank_exact_source F paid).2.2.2.1 h
  change (F.G.edgeSet.ncard:ℤ)+P.gamma h=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(P.cutRoots.ncard+P.capacity)+h at fee
  have upper := truncated_shift_single_peak F (P.cutRoots.ncard+i)
  rw [←Nat.add_assoc] at upper
  change rowEnergy F.n F.m F.r≤area+D*(P.cutRoots.ncard+i)+h at upper
  have pr : (rowEnergy F.n F.m F.r:ℤ)≤(area:ℤ)+(D:ℤ)*(P.cutRoots.ncard+i)+h := by exact_mod_cast upper
  have st : (F.G.edgeSet.ncard:ℤ)+1≤rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  change _≤(area:ℤ)+_+_
  linarith only [pr,st,fee]

#print axioms truncated_shift_single_peak
#print axioms original_physical_truncated_profile
end JSP452Audit.StarHost
