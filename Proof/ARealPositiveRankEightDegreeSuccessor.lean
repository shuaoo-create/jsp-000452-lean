import TransferActualNinePortStageExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem shifted_head_below_spent_width {s t r k D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (live : k<rowCount s t r) (spent : widthAt n m r (D+1)≤k) :
    diagonal n m (r+k+2)≤D := by
  by_contra! high
  have hit : k∈offsetsAt n m r (D+1) := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,high⟩
  rw [offsetsAt_eq_range hs ht n m hn hm,Finset.mem_range] at hit
  omega

theorem strict_nine_first_stage_exposure (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    ∃I : Set F.X,let S := I∪H.upper
      R.tips⊆I ∧ I⊆R.chosen ∧ F.G.IsIndepSet I ∧ I.ncard≤R.totalCapacity ∧
      S.ncard<F.rank ∧ (F.G.induce S).edgeSet.ncard+R.portCount≤2 ∧
      ForcingRow (F.G.induce Sᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+S.ncard) ∧
      minimumExposure (R.erased.induce H.upperᶜ) 8≤minimumExposure (F.G.induce Sᶜ) 8 ∧
      6*(minimumExposure (F.G.induce Sᶜ) 8:ℤ)≤
        40+2*((highestWidth F.n F.m F.r:ℤ)+(F.G.induce S).edgeSet.ncard-1) := by
  classical
  let B := H.upper
  let h := highestWidth F.n F.m F.r
  let P := R.totalCapacity
  have cap (x : F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  obtain ⟨I,tips,ins,ind,_,dom⟩ := R.internal_stage_with_both_tips cap
  let S := I∪B
  have ic := R.independent_inside_both_boxes cap I ins ind
  change I.ncard≤P at ic
  have dis := (R.full_stage_off_boxes B H.first).symm.mono_left ins
  have size := Set.ncard_union_eq dis
  change S.ncard=I.ncard+B.ncard at size
  have distinct : (R.port 0).tip≠(R.port 1).tip := fun eq =>
    R.disjoint_boxes.ne_of_mem (R.port 0).tip_mem (R.port 1).tip_mem eq
  have two : ({(R.port 0).tip,(R.port 1).tip} : Set F.X).ncard=2 := by simp [distinct]
  have pair : ({(R.port 0).tip,(R.port 1).tip} : Set F.X)⊆I := by
    rintro x (zero|one)
    · exact tips ⟨0,zero.symm⟩
    · exact tips ⟨1,(Set.mem_singleton_iff.mp one).symm⟩
  have atLeast := Set.ncard_le_ncard pair
  rw [two] at atLeast
  have bs := (strict_nine_actual_stage_inventory F paid nine R H).1
  change B.ncard<portMenuGap R.capacity-(F.r+1) at bs
  have gap : portMenuGap R.capacity≤P := by
    change max (min _ _) (max _ _-min _ _)≤R.capacity 0+R.capacity 1;omega
  have ws := strict_nine_capacity_window F paid nine R
  have sl := ws.2.1 (lt_min_iff.mp long).1
  have tl := ws.2.2.2.1 (lt_min_iff.mp long).2
  change P+F.r+2*_≤F.s at sl
  change P+F.r+2*_≤F.t at tl
  have fit : S.ncard<F.rank := by change S.ncard<F.s+F.t-1-F.r;omega
  have account := R.first_stage_port_debt cap I B ins ind H.first
  change (F.G.induce S).edgeSet.ncard+R.portCount≤2 ∧
    F.G.edgeSet.ncard+(F.G.induce S).edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard at account
  have cap8 := R.original_cap_after_joining_first_stage cap I B tips dom H.first
  have row := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have hp : h≤2 := (strict_nine_original_peak F paid nine).2.1
  have top : widthAt F.n F.m F.r 10=h := by
    rw [show 10=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
  have bound := shifted_head_below_spent_width F.hs F.ht F.n F.m F.hn F.hm fit
    (show widthAt F.n F.m F.r (9+1)≤S.ncard by rw [top];omega)
  have live : 0<rowCount F.s F.t (F.r+S.ncard) := by dsimp [StrictFamily.rank,rowCount] at fit ⊢;omega
  have less : rowCount F.s F.t (F.r+S.ncard)<F.rank := by dsimp [StrictFamily.rank,rowCount] at fit ⊢;omega
  have fee := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (F.G.induce Sᶜ) (F.r+S.ncard)
    8 F.rank (by decide) row live less paid cap8 bound
  norm_num at fee
  have loss := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r S.ncard F.live
  rw [nine] at loss
  have strict := F.strict
  refine ⟨I,tips,ins,ind,ic,fit,account.1,row,R.actual_stage_exposure_transfer I B ins tips 8 (by decide),?_⟩
  change 6*(minimumExposure (F.G.induce Sᶜ) 8:ℤ)≤40+2*((highestWidth F.n F.m F.r:ℤ)+(F.G.induce S).edgeSet.ncard-1)
  omega

#print axioms shifted_head_below_spent_width
#print axioms strict_nine_first_stage_exposure
end JSP452Audit.StarHost
