import SelectorBoundsForBothPhysicalStagesIncludingAnExhaustedRow
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem sum_vertex_degree_cap {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B) (q:ℕ)
    (first:∀v,Nat.card (Y.neighborSet v)≤q) (second:∀v,Nat.card (C.neighborSet v)≤q) :
    ∀v,Nat.card ((Y⊕g C).neighborSet v)≤q := by
  rintro (v|v)
  · rw [Nat.card_coe_set_eq,neighborSet_sum_inl,Set.ncard_image_of_injective _ Sum.inl_injective];exact first v
  · rw [Nat.card_coe_set_eq,neighborSet_sum_inr,Set.ncard_image_of_injective _ Sum.inr_injective];exact second v

set_option maxHeartbeats 600000 in
theorem regular_block_first_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (p:ℕ) (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let C := B.inside
    let O := B.outside
    let b := peakCountAbove O (2*p-1)
    let S := peakPrefix O b
    ∃A:Set B.piece.supp,CompleteDegreeStage C (2*p) A ∧ A.ncard+1≤B.P ∧
      let J := O.induce Sᶜ⊕g C.induce Aᶜ
      let r := F.r+b+A.ncard
      ForcingRow J F.s F.t (padDemand F.n) (padDemand F.m) r ∧
      rowCount F.s F.t r<F.rank ∧ J.edgeSet.ncard≤rowEnergy F.n F.m r ∧
      (∀v,Nat.card (J.neighborSet v)≤2*p-1) ∧ minimumExposure (O.induce Sᶜ) (2*p-1)≤p ∧
      widthAt F.n F.m r (2*p)≤p-2 ∧ widthAt F.n F.m F.r (2*p)≤b+B.P+p-3 := by
  intro C O b S
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤2*p := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq degree
  have reg (v:B.piece.supp) : Nat.card (C.neighborSet v)=2*p := (component_degree_eq F.G B.piece v).trans (B.full.2 _ v.property)
  have ext (v:↥(B.piece.suppᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤2*p := (induced_neighbor_count_le F.G _ v).trans (cap v.val)
  obtain ⟨ord,cost⟩ := odd_regular_order_edge_count C p B.full.1 reg
  obtain ⟨A,stage,short⟩ := short_stage_odd_even_regular C p B.P (by omega) reg ord cost
  refine ⟨A,stage,short,?_⟩
  intro J r
  have active : 0<A.ncard := by
    obtain ⟨v,mem⟩ := B.piece.nonempty_supp
    let v' : B.piece.supp := ⟨v,mem⟩
    rcases stage.2.2 v' (reg v') with inside|⟨w,inside,_⟩
    · exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨v',inside⟩
    · exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨w,inside⟩
  obtain ⟨outstage,sz⟩ := peak_history_complete_top_stage O (2*p) (by omega) ext
  change S.ncard=b at sz
  have row := sum_after_both_deletions O C S A _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm) (pad_positive F.n F.pn)
    (pad_positive F.m F.pm) (B.original_row _ _ F.row)
  rw [sz] at row
  have inner := JSP452Audit.StarHost.degree_on_independent_full_set C A (2*p) stage.2.1 stage.1
  have outer := JSP452Audit.StarHost.degree_on_independent_full_set O S (2*p) outstage.2.1 outstage.1
  rw [sz] at outer
  have orig := B.original_geometry.2.2.2.1
  have total : F.G.edgeSet.ncard=J.edgeSet.ncard+(2*p)*(b+A.ncard) := by
    change F.G.edgeSet.ncard=O.edgeSet.ncard+(2*p)*B.P+p at orig
    change C.edgeSet.ncard=(2*p)*B.P+p at cost
    dsimp only [J];rw [edge_ncard_sumGraph,Nat.mul_add];omega
  have profile := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r (b+A.ncard) F.live
  rw [degree,one,←Nat.add_assoc] at profile
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m r+(2*p)*(b+A.ncard)+1 at profile
  have strict := F.strict
  have net : J.edgeSet.ncard≤rowEnergy F.n F.m r := by omega
  have small : rowCount F.s F.t r<F.rank := by
    have live := F.live;dsimp only [r,rowCount,StrictFamily.rank] at live ⊢;omega
  have bounds := sum_vertex_degree_cap (O.induce Sᶜ) (C.induce Aᶜ) (2*p-1)
    (fun v => by have := complete_stage_lowers_cap O (2*p) S ext outstage v;omega)
    (fun v => by have := complete_stage_lowers_cap C (2*p) A (fun v => (reg v).le) stage v;omega)
  have holes := odd_stage_zero_surplus J F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row small paid bounds many net
  have first : minimumExposure (O.induce Sᶜ) (2*p-1)≤p := by
    change minimumExposure (O.induce Sᶜ⊕g C.induce Aᶜ) (2*p-1)≤p at holes
    rw [minimumExposure_sumGraph] at holes;omega
  let w := widthAt F.n F.m r (2*p)
  have upper : w≤p-2 := by
    by_cases yes:0<w
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<2*p) yes
      have e : WinsHeight F.n F.m r (2*p) x y := win
      have xh := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 e.2.2.2.1
      have yh := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 e.2.2.2.2.1
      have ht := e.2.2.1
      have actual := typed_width_of_original_rectangle J F.n F.m F.hn F.hm e.2.2.2.1 e.2.2.2.2.1 row
      rw [←e.2.2.2.2.2] at actual
      have need := true_odd_cap_extra_width J (2*p-1) x y w (by omega) (by omega) (by omega) (by omega) bounds actual yes
      omega
    · omega
  have shift := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r (b+A.ncard) (2*p)
  rw [←Nat.add_assoc] at shift
  change w=widthAt F.n F.m F.r (2*p)-(b+A.ncard) at shift
  exact ⟨row,small,net,bounds,first,upper,by omega⟩

#print axioms sum_vertex_degree_cap
#print axioms regular_block_first_stage
end JSP452Audit.StarHost
