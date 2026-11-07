import CarryThePhysicalPartitionToTheOriginalVertexLabels
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_common_low_defect_region (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) :
    let h := highestWidth F.n F.m F.r
    let d := F.rank-matchingEdges F.G
    (h=1 ∨ h=2) ∧ minimumExposure F.G 10=h+2 ∧ h+3≤d ∧
      (0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8) ∧
      ∃P:TenBlockPartition F.G,P.epsilon≤2 ∧ h+2+P.epsilon≤P.eta ∧ P.eta≤h+4 ∧ P.eta≤d+1 := by
  intro h d
  have shapes := strict_ten_exactly_two_remaining_sources F paid ten
  change (h=1 ∧ _ ∧ _) ∨ (h=2 ∧ _ ∧ _) at shapes
  have exposure := (minimal_strict_source_deficit F paid).2.1
  rw [ten] at exposure
  change minimumExposure F.G 10+1≤d at exposure
  have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  have redBlue := (ten_excess_width_forces_four_eight F paid ten (by change _<h;omega)).1
  refine ⟨by omega,by omega,by omega,redBlue,?_⟩
  rcases shapes with ⟨hh,none,rho⟩|⟨hh,single,rho⟩
  · obtain ⟨_,_,K,M,hm,best,one,opt,_,_,B,_⟩ := strict_ten_zero_odd_requires_score_one F paid ten none
    obtain ⟨P,_,_,_,eta,low,high⟩ := TenBlockPartition.from_outer_cut K B cap none M hm best (by omega) one
    exact ⟨P,by omega,by omega,by omega,by omega⟩
  · obtain ⟨J,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<(oddRegularComponents F.G 10).ncard by omega)
    let O := F.G.induce J.suppᶜ
    let C := J.toSimpleGraph
    obtain ⟨noOdd,_,_,near,_⟩ := strict_ten_unique_component_exact_scores F paid ten single J mem
    obtain ⟨K,M,B,one,hm,best,opt,_⟩ := strict_ten_unique_component_exterior_partition F paid ten single J mem
    have capO (x:↥(J.suppᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 := (induced_neighbor_count_le F.G _ x).trans (cap x.val)
    obtain ⟨P,_,_,_,eta,low,high⟩ := TenBlockPartition.from_outer_cut K B capO noOdd M hm best (by omega) one
    have reg (x:J.supp) : Nat.card (C.neighborSet x)=10 := (component_degree_eq F.G J x).trans (mem.2 x.val x.property)
    obtain ⟨Q,_,qGain,qLoss⟩ := TenBlockPartition.from_nearperfect_regular C reg near
    let joined := (Q.join P).transport (component_exterior_iso F.G J)
    have re : joined.epsilon=Q.epsilon+P.epsilon := rfl
    have rt : joined.eta=Q.eta+P.eta := rfl
    exact ⟨joined,by omega,by omega,by omega,by omega⟩

#print axioms strict_ten_common_low_defect_region
end JSP452Audit.StarHost
