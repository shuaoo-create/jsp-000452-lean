import TwoStagePricesFromEachOriginalPart
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_costed_four_residual (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (S:Set F.X)
    (cap:∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤4)
    (cost:F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+5*S.ncard+widthAt F.n F.m F.r 6)
    (done:widthAt F.n F.m F.r 6≤S.ncard) :
    minimumExposure (F.G.induce Sᶜ) 4≤6 := by
  let k := S.ncard
  let L := widthAt F.n F.m F.r 6
  let Y := F.G.induce Sᶜ
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have h := (strict_six_only_one_original_component F paid six).1
  have positive : 0<L := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by
    have live := F.live;change L≤k at done
    change rowCount F.s F.t (F.r+k)<rowCount F.s F.t F.r
    dsimp [rowCount] at live ⊢;omega
  have row := row_delete_set F.G S (padDemand F.n) (padDemand F.m) (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) at row
  have floor := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) row smaller
  have earlier := (minimal_rank_exact_source F paid).2.1
  have loss := six_prefix_two_columns F.hs F.ht F.n F.m F.hn F.hm top k
  rw [h] at loss
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+5*k+L+1 at loss
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+5*k+L at cost
  have exactE : Y.edgeSet.ncard=rowEnergy F.n F.m (F.r+k) := by omega
  change minimumExposure Y 4≤6
  by_cases live:0<rowCount F.s F.t (F.r+k)
  · have dead : widthAt F.n F.m (F.r+k) 6=0 := by rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm];omega
    have head : diagonal F.n F.m (F.r+k+2)≤5 := by
      by_contra! large
      have pos := (width_positive_at_first_offset (j:=6) F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨live,large⟩
      omega
    have price := universal_selector_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 4 F.rank row live smaller paid cap head
    rw [exactE] at price
    let w := widthAt F.n F.m (F.r+k) 5
    have ub : w≤minimumExposure Y 4 := by
      by_cases pos:0<w
      · have lo := ((width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mp pos).2
        have eq : diagonal F.n F.m (F.r+k+2)=5 := by omega
        have lim := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) live row
          (by rw [eq];exact cap)
        rw [←width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm,eq] at lim
        exact lim.2
      · omega
    change (rowEnergy F.n F.m (F.r+k):ℤ)+max 0 (((4*(minimumExposure Y 4:ℤ)+1)/2-6)-(w:ℤ))≤(rowEnergy F.n F.m (F.r+k):ℤ) at price
    omega
  · have dead : rowCount F.s F.t (F.r+k)=0 := by omega
    have none : Y.edgeSet.ncard=0 := by rw [exactE];simp [rowEnergy,dead]
    have noEdges : Y.edgeSet=∅ := Set.not_nonempty_iff_eq_empty.mp (fun non => by have := (Set.ncard_pos Y.edgeSet.toFinite).mpr non;omega)
    have bot : Y=⊥ := SimpleGraph.edgeSet_eq_empty.mp noEdges
    obtain ⟨M,_,_,att⟩ := minimumExposure_attained Y 4
    have empty : exposedFull Y M 4=∅ := by
      apply Set.eq_empty_of_forall_notMem;intro x hx
      have full := hx.2
      change Nat.card (Y.neighborSet x)=4 at full
      rw [bot] at full;simp at full
    rw [empty,Set.ncard_empty] at att;omega

#print axioms strict_six_costed_four_residual
end JSP452Audit.StarHost
