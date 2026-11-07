import TheTwoPricesOnTheWeightedSuccessorAreIncompatibleAtEveryRemainingDegree
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 700000 in
theorem no_original_strict_family (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) : False := by
  classical
  let D := diagonal F.n F.m (F.r+2)-1
  let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
  let h := highestWidth F.n F.m F.r
  have degree : 11≤D := strict_source_degree_at_least_eleven F paid
  have gap : D=H+1 := strict_original_head_gap_is_one F paid
  obtain ⟨K,k₀,c₀,P,kl,⟨E⟩,hp,hρ,sharp,odd,_⟩ := strict_original_credit_and_singleton F paid
  let Y := F.G.induce P.exterior
  let C := F.G.induce P.paidCore
  let r := F.r+P.cutRoots.ncard
  let G := P.gamma h
  let Z := P.capacity
  let N := P.paidCore.ncard
  let c := P.positives.ncard
  let ρ := P.excess
  let b := peakCountAbove Y H
  let T := peakPrefix Y b
  let Y' := Y.induce Tᶜ
  let L := widthAt F.n F.m r D
  let p := H/2
  change 4*G+((D:ℤ)+2)*ρ+((D:ℤ)-6)*h+2*P.beta≤0 at sharp
  have credit : 4*G+((D:ℤ)+2)*ρ+((D:ℤ)-6)*h≤0 := by linarith only [sharp,show (0:ℤ)≤P.beta by positivity]
  have eq := gap_two_linear_degree_credit D h ρ G degree hp hρ credit
  have cheap : G≤-3*(ρ:ℤ) := by omega
  have top := (only_gap_automatic_entry F paid P E kl hp cheap).2.2.1
  change (Z:ℤ)+b+1≤(L:ℤ)+G at top
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have capC (v:↥P.paidCore) : Nat.card (C.neighborSet v)≤D := (induced_neighbor_count_le F.G _ v).trans (cap v.val)
  have capY (v:↥P.exterior) : Nat.card (Y.neighborSet v)≤D := (induced_neighbor_count_le F.G _ v).trans (cap v.val)
  have data := P.exact_weight_and_root_cost E cap h
  have rank := data.2.2.2.1
  have os := data.2.2.2.2.2
  change (D:ℤ)*c≤2*Z at rank
  change N=2*Z+c at os
  have order : D*Nat.card ↥P.paidCore≤(2*D+2)*Z := by
    rw [Nat.card_coe_set_eq];change D*N≤_;rw [os,Nat.mul_add,Nat.add_mul]
    have small : D*c≤2*Z := by exact_mod_cast rank
    nlinarith only [small]
  obtain ⟨A,B,residual,weighted⟩ := weighted_actual_core_deletion C D Z degree capC order
  let C₁ := C.induce Aᶜ
  let C₂ := C₁.induce Bᶜ
  let k := A.ncard+B.ncard
  let X := C₂⊕g Y'
  let offset := r+(k+b)
  change 3*(D-1)*k+2*C₂.edgeSet.ncard≤3*(D-1)*Z at weighted
  have ksmall : k≤Z := by
    by_contra! larger
    have over := Nat.mul_lt_mul_of_pos_left larger (show 0<3*(D-1) by omega)
    omega
  obtain ⟨stage,sz⟩ := peak_history_complete_top_stage Y D (by omega) capY
  rw [show D-1=H by omega] at stage sz
  change CompleteDegreeStage Y D T at stage
  change T.ncard=b at sz
  have saved := JSP452Audit.StarHost.degree_on_independent_full_set Y T D stage.2.1 stage.1
  rw [sz] at saved
  change Y.edgeSet.ncard=Y'.edgeSet.ncard+D*b at saved
  have thin := (exact_peak_inventory_cut Y H).2
  have capX := sum_vertex_degree_cap C₂ Y' H (fun v => (residual v).trans (by omega)) thin
  have capX' (v) : Nat.card (X.neighborSet v)≤H := capX v
  have rowA := sum_after_both_deletions C Y A T _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) (strict_payable_exterior_constraints F paid P).2.2.2.2.1
  rw [sz] at rowA
  have row := delete_only_from_left_summand C₁ Y' B _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) rowA
  change ForcingRow X F.s F.t (padDemand F.n) (padDemand F.m) (r+A.ncard+b+B.ncard) at row
  rw [show r+A.ncard+b+B.ncard=offset by dsimp only [offset,k];omega] at row
  have shift := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm r (k+b) D
  change widthAt F.n F.m offset D=L-(k+b) at shift
  have positive : 0<widthAt F.n F.m offset D := by omega
  have bound : widthAt F.n F.m offset D≤rowCount F.s F.t offset := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have live := positive.trans_le bound
  have height := live_row_height_at_degree_cap X F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row live capX'
  have advance : F.r<offset := by
    have le : F.r≤offset := by dsimp only [offset,r];omega
    by_contra! no
    rw [show offset=F.r by omega] at height
    dsimp only [D] at gap degree;omega
  have less : rowCount F.s F.t offset<F.rank := by
    change _<rowCount F.s F.t F.r;dsimp only [rowCount] at live ⊢;omega
  let g := (X.edgeSet.ncard:ℤ)-rowEnergy F.n F.m offset
  let e := minimumExposure X H
  have see := (original_width_le_deletion F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X offset H row (by omega)).trans
    (deletionBudget_le_minimumExposure X H (by omega) capX')
  rw [←gap] at see
  change widthAt F.n F.m offset D≤e at see
  have sel := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X offset H F.rank (by omega) row live less paid capX' height
  change ((H:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g at sel
  have near := original_physical_truncated_profile F paid P (k+b)
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(∑j∈Finset.range D,widthAt F.n F.m offset (j+1):ℕ)+G+(D:ℤ)*(k+b:ℕ) at near
  have area := partial_profile_area_le F.hs F.ht F.n F.m F.hn F.hm offset D
  have part : ((∑j∈Finset.range D,widthAt F.n F.m offset (j+1):ℕ):ℤ)≤rowEnergy F.n F.m offset := by exact_mod_cast area
  have balance : (Y.edgeSet.ncard:ℤ)=Y'.edgeSet.ncard+(D:ℤ)*b := by exact_mod_cast saved
  have edges : (X.edgeSet.ncard:ℤ)=(C₂.edgeSet.ncard:ℤ)+Y'.edgeSet.ncard := by exact_mod_cast edge_ncard_sumGraph C₂ Y'
  have bill : g+(D:ℤ)*Z+1≤G+(D:ℤ)*k+C₂.edgeSet.ncard := by
    dsimp only [g];push_cast at near;push_cast at part;linarith only [near,part,balance,edges]
  exact gap_one_weighted_price_contradiction D H h ρ Z k b L e C₂.edgeSet.ncard p G g degree gap rfl hp hρ
    (fun parity => (odd parity).1) credit top (by omega) weighted bill sel

#print axioms no_original_strict_family
end JSP452Audit.StarHost