import AnUncoveredHalfCapacityMenuHasOneActuallyDominantWholeComponent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ScaledPortPlan.each_paid_capacity_has_source_order {A:Type u} [Finite A] {G:SimpleGraph A} {D k c:ℕ}
    {K:DegreeRegion G D} (P:ScaledPortPlan K k c) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (Q:(G.induce P.paidCore).ConnectedComponent) : (D+1)/2≤matchingEdges Q.toSimpleGraph := by
  let q := coreComponentEquiv G K.barrier P.positives Q
  let _ : Nonempty q.val.supp := q.val.nonempty_supp.to_subtype
  have reg := K.critical q.val
  have positive := positive_core_caps q.val.toSimpleGraph reg.2 D
    (fun x => (induced_neighbor_count_le (G.induce K.barrierᶜ) q.val.supp x).trans
      ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap x.val.val))) q.property.2
  have sz := factorCritical_order_rank q.val.toSimpleGraph reg.2 (Classical.arbitrary q.val.supp)
  have iso := rank_eq_of_graph_iso (coreComponentIso G K.barrier P.positives Q)
  change matchingEdges Q.toSimpleGraph=matchingEdges q.val.toSimpleGraph at iso
  omega

theorem gap_two_long_stage_has_a_dominant_real_core (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let u := peakCountAbove Y H
    let A := r+1+u
    let Z := P.capacity
    let N := P.paidCore.ncard
    let z := P.positives.ncard
    D=H+2 → 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 → N/3<A →
      (∃Q:(F.G.induce P.paidCore).ConnectedComponent,Z+A<2*matchingEdges Q.toSimpleGraph) ∧
      6*((D+1)/2)*(z-1)+z<Z ∧ 3*D*(z-1)<Z := by
  classical
  intro D H h r Y u A Z N z gap sharp long
  let C := F.G.induce P.paidCore
  let _ := Fintype.ofFinite C.ConnectedComponent
  let _ := Fintype.ofFinite ↥P.positives
  let weight (Q:C.ConnectedComponent) := matchingEdges Q.toSimpleGraph
  have total : (∑Q,weight Q)=Z := (core_component_menu_totals C).symm
  let cap := (minimal_rank_exact_source F paid).2.2.2.1
  have os := (P.exact_weight_and_root_cost E cap h).2.2.2.2.2
  change N=2*Z+z at os
  have fail := gap_two_whole_capacity_menu_fails F paid P E kl hp hρ gap sharp
  have half : (∑Q,weight Q)≤2*(r+u+1) := by rw [total];dsimp only [A] at long;omega
  obtain ⟨Q,heavy⟩ := a_failed_half_capacity_menu_has_a_dominant_piece weight (r+u) half fail
  rw [total] at heavy
  have core : Z+A<2*weight Q := by dsimp only [A];omega
  refine ⟨⟨Q,core⟩,?_⟩
  let T := Finset.univ.erase Q
  have count : Fintype.card C.ConnectedComponent=z := by
    rw [Fintype.card_congr (coreComponentEquiv F.G K.barrier P.positives),←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have num : T.card=z-1 := by simp [T,count]
  let rest := ∑j∈T,weight j
  have balance := Finset.sum_erase_add (s:=Finset.univ) weight (Finset.mem_univ Q)
  change rest+weight Q=∑j,weight j at balance
  rw [total] at balance
  have bound := Finset.sum_le_sum (s:=T) (fun j _ => P.each_paid_capacity_has_source_order cap j)
  change (∑_j∈T,(D+1)/2)≤rest at bound
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,num] at bound
  have mass : 6*((D+1)/2)*(z-1)+z<Z := by rw [Nat.mul_assoc,Nat.mul_comm ((D+1)/2) (z-1)];omega
  have even := Nat.mul_le_mul_right (z-1) (show 3*D≤6*((D+1)/2) by omega)
  exact ⟨mass,by omega⟩

#print axioms ScaledPortPlan.each_paid_capacity_has_source_order
#print axioms gap_two_long_stage_has_a_dominant_real_core
end JSP452Audit.StarHost