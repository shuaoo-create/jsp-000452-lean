import NineLeafHeadsForbidEveryMixedLowerWinnerAtDegreeTen
open private JSP452Audit.StarHost.through_degree_split from InteriorHeightArea
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_all_axes_contradict_regular_menu (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (axes:∀j,1≤j → j≤9 → ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) : False := by
  let U := A.K.support
  let O := F.G.induce Uᶜ
  let P := A.K.P
  let Q := matchingEdges (F.G.induce U)
  let L := widthAt F.n F.m F.r 10
  let h := highestWidth F.n F.m F.r
  have closed := A.K.support_closed
  have full (x) (hx:x∈U) := (A.K.support_full x hx).trans ten.symm
  have cap (v:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤10 := (induced_neighbor_count_le F.G Uᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq ten)
  obtain ⟨B,stage⟩ := complete_degree_stage_exists O 10
  have low := complete_stage_lowers_cap O 10 B cap stage
  obtain ⟨small,hist⟩ := complete_degree_cut_account 9 (O.induce Bᶜ) (fun x => by have := low x;omega)
  obtain ⟨S,last,history⟩ := extend_history_by_first_stage O 9 B stage cap small hist
  obtain ⟨I,inner,short⟩ := A.shortStage
  have upper := (ten_closed_stage_width F paid ten A.K I inner B stage).2
  change L≤I.ncard+B.ncard+(38+2*h)/7 at upper
  change I.ncard+A.saving≤P at short
  have each (i:ℕ) (mem:i∈Finset.range 9) : widthAt F.n F.m F.r (i+1)≤Q+(S (i+1)).ncard :=
    winning_axis_uses_cut_on_exterior F paid closed full (i+1) (by omega) (S (i+1))
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
  have edgeC := A.K.fee
  change (F.G.induce U).edgeSet.ncard=10*P+5*A.K.eps at edgeC
  have rank : Q≤P := A.K.fits
  have sep := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at sep
  have bound := A.stageCost
  change h+(38+2*h)/7≤5*A.K.eps+A.saving at bound
  clear * - upper short costs eO area exactPrice edgeC rank sep bound
  omega


theorem strict_ten_no_nine_leaf_with_regular_menu (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6) : (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) := by
  have no : ¬(0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9) := by
    intro heads
    have lengths := (ten_closed_endpoint_sizes F paid ten A.K).1
    have dpos := (minimal_strict_source_deficit F paid).2.2
    have axes (j:ℕ) (lo:1≤j) (hi:j≤9) : ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1) := by
      have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht lo hi
      have live : 0<widthAt F.n F.m F.r j := by omega
      obtain ⟨x,y,xp,yp,ht,rr,bb,wide⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm lo live
      have win : WinsHeight F.n F.m F.r j x y := ⟨xp,yp,ht,rr,bb,wide⟩
      refine ⟨x,y,win,?_⟩
      by_contra! neither
      exact ten_nine_leaf_forbids_mixed_columns F paid ten A cost heads j x y (by omega) hi (by omega) (by omega) win
    exact ten_all_axes_contradict_regular_menu F paid ten A axes
  constructor
  · intro i;by_contra! big
    have mem := (original_threshold_prefix F.n F.hn 9 i).mp big
    exact no (Or.inl (by omega))
  · intro j;by_contra! big
    have mem := (original_threshold_prefix F.m F.hm 9 j).mp big
    exact no (Or.inr (by omega))

#print axioms ten_all_axes_contradict_regular_menu
#print axioms strict_ten_no_nine_leaf_with_regular_menu
end JSP452Audit.StarHost
