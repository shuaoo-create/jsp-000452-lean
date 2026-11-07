import FollowTheSameRegularExteriorIntoItsSecondCompleteStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem regular_block_inventory_and_next (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let d := F.rank-matchingEdges F.G
    let O := B.outside
    let P := B.P
    let i := P-(F.r+1)
    let U := peakPrefix O i
    P<2*d ∧ P<peakCountAbove O (H-1) ∧ U.ncard=i ∧ 0<rowCount F.s F.t (F.r+i+P) ∧
    rowCount F.s F.t (F.r+i+P)<F.rank ∧ ForcingRow (O.induce Uᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+i+P) ∧
      rowEnergy F.n F.m (F.r+i+P)≤(O.induce Uᶜ).edgeSet.ncard := by
  intro H d O P i U
  let N := Nat.card B.piece.supp
  let D := 2*p
  let W := widthAt F.n F.m F.r
  let env := uniformEnvelope O
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  change H+3=D at head
  obtain ⟨floor,order,rank,edge,split⟩ := B.original_geometry
  change N=2*P+1 at order
  change matchingEdges B.inside≤P at rank
  change F.G.edgeSet.ncard=O.edgeSet.ncard+D*P+p at edge
  have closed (x) (hx:x∈B.piece.supp) (y) (edge:F.G.Adj x y) : y∈B.piece.supp := (B.piece.mem_supp_congr_adj edge).mp hx
  have full (v) (hv:v∈B.piece.supp) := (B.full.2 v hv).trans degree.symm
  obtain ⟨all,top,mid,_⟩ := regular_third_gap_block_widths F paid p B degree head one
  have count (j:ℕ) (_:j∈Finset.range H) : W (j+2)≤env (j+2)+P := all _ (by omega)
  have low := Finset.sum_le_sum count
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at low
  have middle : W (H+2)≤env (H+2)+N/3 := by
    have eq : H+2=2*p-1 := by dsimp only [D] at head;omega
    rw [eq];by_cases live:0<W (2*p-1)
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<2*p-1) live
      exact (mid x y win).2.2
    · omega
  have last : W (H+3)≤env (H+3)+N/5 := by
    rw [head];by_cases live:0<W D
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D by dsimp only [D];omega) live
      have w : WinsHeight F.n F.m F.r D x y := win
      rcases (top x y w).2 with zero|⟨u,v,hu,hv,len,force⟩
      · change W D-N/5=0 at zero;omega
      · have priced := uniform_pair_le_envelope O x y u v D w.1 w.2.1 hu hv w.2.2.1 force
        change u+v-1=W D-N/5 at len
        change u+v-1≤env D at priced;omega
    · omega
  have remainder := (envelope_reserve_account O (H+2)).1
  change _+(matchingEdges O+∑j∈Finset.range (H+2),env (j+2))=O.edgeSet.ncard at remainder
  rw [Finset.sum_range_succ,Finset.sum_range_succ] at remainder
  have height : diagonal F.n F.m (F.r+2)=D+1 := by dsimp only [D];omega
  have energy := profile_area_after_any_shift F.hs F.ht F.n F.m F.hn F.hm (show F.r≤F.r from le_rfl) height.le
  rw [Finset.sum_range_succ] at energy
  have peak := width_at_peak F.hs F.ht F.n F.m F.hn F.hm F.r
  rw [height,one] at peak
  rw [peak,←head,Finset.sum_range_succ'] at energy
  have unit : widthAt F.n F.m F.r 1=F.rank := first_layer_complete F.hs F.ht F.n F.m F.pn F.pm F.r
  change rowEnergy F.n F.m F.r=(∑j∈Finset.range (H+2),W (j+2))+W 1+1 at energy
  rw [Finset.sum_range_succ,Finset.sum_range_succ] at energy
  change W 1=F.rank at unit
  have strict := F.strict
  have deficit := (minimal_rank_exact_source F paid).2.2.1
  have account : F.rank=matchingEdges O+matchingEdges B.inside+d := by change matchingEdges F.G=matchingEdges O+matchingEdges B.inside at split;dsimp only [d];omega
  have linear : D*P=H*P+3*P := by rw [←head,Nat.add_mul]
  change _+(matchingEdges O+((∑j∈Finset.range H,env (j+2))+env (H+2)+env (H+3)))=O.edgeSet.ncard at remainder
  change rowEnergy F.n F.m F.r=((∑j∈Finset.range H,W (j+2))+W (H+2)+W (H+3))+W 1+1 at energy
  have first : P<2*d := by omega
  obtain ⟨qa,qb,a,b,red,blue⟩ := strict_closed_union_endpoint_pair F paid B.piece.supp closed full
  have stage := exact_peak_inventory_cut O (H-1)
  have inv : P<peakCountAbove O (H-1) := by
    have hh : H-1+1=H := by dsimp only [D] at head;omega
    have posd : 0<d := by omega
    rcases le_total (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) with less|less
    · have yes : 0<originalThresholdCount F.m (H-1+1) := (original_threshold_prefix F.m F.hm _ ⟨0,F.ht⟩).1 (by rw [hh,show H=F.m ⟨0,F.ht⟩ from max_eq_right less])
      have found := endpoint_stage_inventory O F.ht F.m F.pm blue posd (by omega) b _ stage.2 yes
      rw [stage.1] at found;omega
    · have yes : 0<originalThresholdCount F.n (H-1+1) := (original_threshold_prefix F.n F.hn _ ⟨0,F.hs⟩).1 (by rw [hh,show H=F.n ⟨0,F.hs⟩ from max_eq_left less])
      have found := endpoint_stage_inventory O F.hs F.n F.pn red posd (by omega) a _ stage.2 yes
      rw [stage.1] at found;omega
  have sz : U.ncard=i := (peak_prefix_size O i).trans (min_eq_left ((Nat.sub_le P (F.r+1)).trans (inv.le.trans (peak_inventory_spec O (H-1)).1)))
  have reg (x:B.piece.supp) := (component_degree_eq F.G B.piece x).trans (B.full.2 _ x.property)
  have holes := regular_exposure_order_rank B.inside (2*p) reg
  have both := minimumExposure_iso (component_exterior_iso F.G B.piece) (2*p)
  rw [minimumExposure_sumGraph] at both
  change minimumExposure B.inside (2*p)+minimumExposure O (2*p)=minimumExposure F.G (2*p) at both
  have exposed := (minimal_strict_source_deficit F paid).2.1
  rw [degree] at exposed
  change minimumExposure F.G (2*p)+1≤d at exposed
  change 2*matchingEdges B.inside+minimumExposure B.inside (2*p)=N at holes
  have lengths := (strict_closed_union_lengths F paid B.piece.supp closed full).1
  change matchingEdges B.inside+F.r+d+1≤min F.s F.t at lengths
  have pos : 0<rowCount F.s F.t (F.r+i+P) := by dsimp only [rowCount,i];omega
  have live := F.live
  have small : rowCount F.s F.t (F.r+i+P)<F.rank := by change _<rowCount F.s F.t F.r;change p≤P at floor;dsimp only [rowCount] at live ⊢;omega
  have next := regular_block_exterior_menu B _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm) (pad_positive F.n F.pn) (pad_positive F.m F.pm)
    F.row U (by rw [sz];change P≤F.r+i+1;dsimp only [i];omega)
  rw [sz] at next
  exact ⟨first,inv,sz,pos,small,next,paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ next small⟩

#print axioms regular_block_inventory_and_next
end JSP452Audit.StarHost
