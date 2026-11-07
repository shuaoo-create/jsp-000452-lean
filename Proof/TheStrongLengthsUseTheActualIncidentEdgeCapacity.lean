import AdjoinTheUniqueRegularComponentToTheIdenticalPortSupport
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_same_partition_and_port_support (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) :
    let h := highestWidth F.n F.m F.r
    let d := F.rank-matchingEdges F.G
    (h=1 ∨ h=2) ∧ minimumExposure F.G 10=h+2 ∧ h+3≤d ∧
      (0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8) ∧
      ∃P:TenBlockPartition F.G,∃W:TenPortSupport F.G P h,P.epsilon≤2 ∧ h+2+P.epsilon≤P.eta ∧ P.eta≤h+4 ∧ P.eta≤d+1 ∧
        matchingEdges (eraseInternal F.G W.supportᶜ)+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤P.outsideRank := by
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
    obtain ⟨P,W,_,_,_,low,defect,high⟩ := TenPortSupport.of_cut K B cap none M hm best (by omega) one
    have strong := ten_partition_strong_lengths F paid ten P low (by change h+2+P.epsilon≤P.eta;omega) (by change P.eta≤d+1;omega)
    rw [hh]
    exact ⟨P,W,by omega,by omega,by omega,by omega,W.regionRank.symm ▸ strong.1,strong.2⟩
  · obtain ⟨J,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<(oddRegularComponents F.G 10).ncard by omega)
    let O := F.G.induce J.suppᶜ
    let C := J.toSimpleGraph
    obtain ⟨noOdd,_,_,near,_⟩ := strict_ten_unique_component_exact_scores F paid ten single J mem
    obtain ⟨K,M,B,one,hm,best,opt,_⟩ := strict_ten_unique_component_exterior_partition F paid ten single J mem
    have capO (x:↥(J.suppᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 := (induced_neighbor_count_le F.G _ x).trans (cap x.val)
    obtain ⟨P,W,_,_,_,low,defect,high⟩ := TenPortSupport.of_cut K B capO noOdd M hm best (by omega) one
    have reg (x:J.supp) : Nat.card (C.neighborSet x)=10 := (component_degree_eq F.G J x).trans (mem.2 x.val x.property)
    obtain ⟨Q,empty,qGain,qLoss⟩ := TenBlockPartition.from_nearperfect_regular C reg near
    let joined := (Q.join P).transport (component_exterior_iso F.G J)
    have re : joined.epsilon=Q.epsilon+P.epsilon := rfl
    have rt : joined.eta=Q.eta+P.eta := rfl
    have book := odd_regular_order_edge_count C 5 mem.1 reg
    change Nat.card J.supp=2*(Nat.card J.supp/2)+1 ∧ C.edgeSet.ncard=2*5*(Nat.card J.supp/2)+5 at book
    have fee : C.edgeSet.ncard=5*Nat.card J.supp := by omega
    have large : 11≤Nat.card J.supp := by
      by_contra! tooSmall
      have bounded := twice_edges_le_simple_order C
      have owed := small_component_owes_ten _ _ (by omega : 0<Nat.card J.supp) (by omega) bounded
      omega
    let pair := W.add_closed_component empty near large fee
    let whole := pair.transport (component_exterior_iso F.G J)
    have strong := ten_partition_strong_lengths F paid ten joined (by omega) (by change h+2+joined.epsilon≤joined.eta;omega)
      (by change joined.eta≤d+1;omega)
    have anchor : matchingEdges (eraseInternal F.G whole.supportᶜ)=joined.roots.ncard+joined.capacity := whole.regionRank
    rw [hh]
    exact ⟨joined,whole,by omega,by omega,by omega,by omega,anchor.symm ▸ strong.1,strong.2⟩

#print axioms strict_ten_same_partition_and_port_support
end JSP452Audit.StarHost
