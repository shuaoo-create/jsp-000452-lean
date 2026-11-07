import EachActualUnitAxisIsPaidByItsOwnExteriorDeletionSet
open private JSP452Audit.StarHost.through_degree_split from InteriorHeightArea
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_all_axes_contradict_port_support (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G} (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (narrow:highestWidth F.n F.m F.r≤2) (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (axes:∀j,1≤j → j≤9 → ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) : False := by
  let U := W.support
  let O := F.G.induce Uᶜ
  let P := W.rank
  let L := widthAt F.n F.m F.r 10
  let h := highestWidth F.n F.m F.r
  have cap (v:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤10 := (induced_neighbor_count_le F.G Uᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq ten)
  obtain ⟨B,stage⟩ := complete_degree_stage_exists O 10
  have low := complete_stage_lowers_cap O 10 B cap stage
  obtain ⟨small,hist⟩ := complete_degree_cut_account 9 (O.induce Bᶜ) (fun x => by have := low x;omega)
  obtain ⟨S,last,history⟩ := extend_history_by_first_stage O 9 B stage cap small hist
  obtain ⟨I,inner⟩ := complete_degree_stage_exists (F.G.induce W.available) 10
  have upper := (ten_port_first_stage_exposure F paid ten W length I inner B stage).2.2.2
  change L+W.targetPorts≤P+B.ncard+(38+2*h+2*W.seedLoss)/7 at upper
  have each (i:ℕ) (mem:i∈Finset.range 9) : widthAt F.n F.m F.r (i+1)≤P+(S (i+1)).ncard :=
    ten_port_axis_uses_cut F W deep length (i+1) (by omega) (S (i+1))
      (history.1 _ (by omega) (by have := Finset.mem_range.mp mem;omega)) (axes _ (by omega) (by have := Finset.mem_range.mp mem;omega))
  have costs := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at costs
  have eO := history.2
  rw [Finset.sum_range_succ] at eO
  change O.edgeSet.ncard=(∑i∈Finset.range 9,(S (i+1)).ncard)+(S 10).ncard at eO
  change S 10=B at last
  rw [last] at eO
  have sum := JSP452Audit.StarHost.through_degree_split F.hs F.ht F.n F.m F.pn F.pm F.r 10 (by decide)
  rw [show 10=9+1 by rfl,Finset.sum_range_succ] at sum
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=10) (by omega) (by decide)
  rw [←sum] at area
  change rowEnergy F.n F.m F.r=(∑i∈Finset.range 9,widthAt F.n F.m F.r (i+1))+L+h at area
  have exactPrice := (minimal_rank_exact_source F paid).2.1
  have fee : W.piece.edgeSet.ncard=10*P+W.fee := (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.2.2.2.2.2.1
  have sep := erase_internal_edge_count F.G Uᶜ
  change F.G.edgeSet.ncard=W.piece.edgeSet.ncard+O.edgeSet.ncard at sep
  have original (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  have bound := ten_port_fee_covers_first_exposure W (strict_ten_inventory F paid ten).1 narrow original
  change h+(38+2*h+2*W.seedLoss)/7≤W.fee+W.targetPorts at bound
  clear * - upper costs eO area exactPrice fee sep bound
  omega

#print axioms ten_all_axes_contradict_port_support
end JSP452Audit.StarHost
