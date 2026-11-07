import SharpSignedFiveExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem stage_exposure_zero_of_no_edges {X:Type*} [Finite X] (G:SimpleGraph X) (zero:G.edgeSet.ncard=0) :
    minimumExposure G 5=0 := by
  have empty : G.edgeSet=∅ := Set.not_nonempty_iff_eq_empty.mp (fun non => by have := (Set.ncard_pos G.edgeSet.toFinite).mpr non;omega)
  have bot : G=⊥ := SimpleGraph.edgeSet_eq_empty.mp empty
  subst G
  obtain ⟨M,_,_,att⟩ := minimumExposure_attained (⊥:SimpleGraph X) 5
  have no : exposedFull (⊥:SimpleGraph X) M 5=∅ := by
    ext x
    simp [exposedFull]
  rw [no,Set.ncard_empty] at att
  exact att.symm

theorem strict_single_six_stage_caps (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (I:Set F.X) (stage:CompleteDegreeStage F.G 6 I) :
    let k := I.ncard
    let L := widthAt F.n F.m F.r 6
    let Y := F.G.induce Iᶜ
    k≤L ∧ Y.edgeSet.ncard=rowEnergy F.n F.m (F.r+k) ∧
      5*minimumExposure Y 5≤2*(L-k)+12 := by
  intro k L Y
  have h := (strict_six_only_one_original_component F paid six).1
  obtain ⟨hk,excess,_,_⟩ := strict_six_complete_stage_shadow F paid six I stage
  rw [h] at hk excess
  change 1≤k at hk
  change Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+1 at excess
  have src := minimal_rank_exact_source F paid
  have cap (v:F.X) := (src.2.2.2.1 v).trans_eq six
  obtain ⟨_,cost,row⟩ := original_stage_width_and_cost F.G F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row
    (by decide : 0<6) cap I stage
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+6*k at cost
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) at row
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by
    have live := F.live;change rowCount F.s F.t (F.r+k)<rowCount F.s F.t F.r;dsimp [rowCount] at live ⊢;omega
  have base := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) row smaller
  have exactE : Y.edgeSet.ncard=rowEnergy F.n F.m (F.r+k) := by omega
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have loss := six_prefix_two_columns F.hs F.ht F.n F.m F.hn F.hm top k
  rw [h] at loss
  have original := src.2.1
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+5*k+L+1 at loss
  refine ⟨by omega,exactE,?_⟩
  by_cases live:0<rowCount F.s F.t (F.r+k)
  · have head : diagonal F.n F.m ((F.r+k)+2)≤6 := by
      by_contra! high
      have pos := (width_positive_at_first_offset (j:=7) F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨live,high⟩
      rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm,←top,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm,h] at pos
      omega
    have bound (v:↥(Iᶜ:Set F.X)) : Nat.card (Y.neighborSet v)≤5 := by
      have reduced := complete_stage_lowers_cap F.G 6 I cap stage v
      change Nat.card (Y.neighborSet v)<6 at reduced;omega
    have price := universal_selector_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 5 F.rank row live smaller paid bound head
    rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm,exactE] at price
    change (rowEnergy F.n F.m (F.r+k):ℤ)+max 0 (((5*(minimumExposure Y 5:ℤ)+1)/2-6)-((L-k:ℕ):ℤ))≤(rowEnergy F.n F.m (F.r+k):ℤ) at price
    omega
  · have dead : rowCount F.s F.t (F.r+k)=0 := by omega
    have zero : rowEnergy F.n F.m (F.r+k)=0 := by simp [rowEnergy,dead]
    rw [stage_exposure_zero_of_no_edges Y (exactE.trans zero)]
    omega

#print axioms stage_exposure_zero_of_no_edges
#print axioms strict_single_six_stage_caps
end JSP452Audit.StarHost
