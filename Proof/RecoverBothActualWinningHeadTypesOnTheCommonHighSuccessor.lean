import TheFullDegreeStageEndsBeforeTheQuarterAllowanceAndSuppliesTheHighCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 500000 in
theorem gap_two_high_fixed_selector (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let N := P.paidCore.ncard
    let Z := P.capacity
    let L := widthAt F.n F.m r D
    let b := peakCountAbove Y (H+1)
    let l := max (N/5) (R+b)
    let i := l-R
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    let g := (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)
    let e := minimumExposure X (H+1)
    let p := (H+1)/2
    D=H+2 → Z<L → 0≤g ∧ g+Z+2*l+R+b+1≤P.gamma h+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) ∧
      ((H:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g ∧
      ∀x y,WinsHeight F.n F.m r D x y → ∃w,ExactTypedWidth X x y w ∧ w≤e ∧
        L≤w+i+N/4 ∧ (4≤min x y → L≤w+i+l) ∧ (min x y=3 → H*w≤2*e) := by
  intro D H h C Y r R N Z L b l i X n m g e p gap high
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have hs := F.hs
  have ht := F.ht
  obtain ⟨ib,iu,lq,lp,cap,typed⟩ := gap_two_high_platform_supplies_both_stages F paid P E kl hp credit gap high
  change b ≤ i at ib
  change i≤peakCountAbove Y H at iu
  change l≤N/4 at lq
  have lo : N/5≤l := le_max_left _ _
  have highl : l≤N/3 := by omega
  obtain ⟨live,smaller,row,cost⟩ := gap_two_fixed_prefix_price F paid P E kl hp credit l gap lp lo highl
  change ForcingRow X _ _ (padDemand n) (padDemand m) (r+i+l) at row
  let s := min F.s ((componentBudget C F.n).len+l)
  let t := min F.t ((componentBudget C F.m).len+l)
  have sp : 0<s := by dsimp only [s];omega
  have tp : 0<t := by dsimp only [t];omega
  have hn := protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l
  have hm := protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l
  have pn := protected_demand_positive F.n _ F.pn ((componentBudget C F.n).entries_positive _ F.pn) l
  have pm := protected_demand_positive F.m _ F.pm ((componentBudget C F.m).entries_positive _ F.pm) l
  have bound (v) : Nat.card (X.neighborSet v)≤H+1 := (cap v).trans (by omega)
  have baseline := paid sp tp n m hn hm pn pm _ _ row smaller
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at baseline
  have gpos : 0≤g := by dsimp only [g];omega
  have lim := live_row_height_at_degree_cap X sp tp n m hn hm pn pm row live bound
  have price := smaller_row_exposure_budget sp tp n m hn hm pn pm X (r+i+l) (H+1) F.rank (by omega) row live smaller paid bound lim
  change (((H+1:ℕ):ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g at price
  simp only [Nat.cast_add,Nat.cast_one] at price
  have bill : g+Z+2*l+R+b+1≤P.gamma h+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) := by
    change ((X.edgeSet.ncard-rowEnergy n m (r+i+l):ℕ):ℤ)+Z+l+min i (peakCountAbove Y H)+min i b+1≤
      P.gamma h+2*((N/3:ℕ):ℤ)+2*((N/4-l:ℕ):ℤ)+2*i at cost
    have room : R≤l := by dsimp only [l];omega
    have sum : i+R=l := Nat.sub_add_cancel room
    dsimp only [g];omega
  refine ⟨gpos,bill,by linarith only [price],?_⟩
  intro x y win
  obtain ⟨mi,mx,_,_⟩ := typed x y win
  have fees := fixed_winner_typed_after_prefix X C F.n F.m F.hn F.hm l i lp win row
  obtain ⟨actual,_,pay⟩ := fees
  let w := originalThresholdCount n x+originalThresholdCount m y-1-(r+i+l)
  change ExactTypedWidth X x y w at actual
  rw [Nat.card_coe_set_eq] at pay
  change L≤w+i+l+fixedHeadLoss Z N l x+fixedHeadLoss Z N l y at pay
  have slots (v:ℕ) : (3≤v → fixedHeadLoss Z N l v≤N/4-l) ∧ (4≤v → fixedHeadLoss Z N l v=0) := by
    unfold fixedHeadLoss
    exact ⟨fun hv => by have h : N/(v+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide);omega,
      fun hv => by have h : N/(v+1)≤N/5 := Nat.div_le_div_left (by omega) (by decide);omega⟩
  obtain ⟨a,af⟩ := slots x
  obtain ⟨c,cf⟩ := slots y
  have ht := win.2.2.1
  have tax := typed_width_exposure_at_cap X (H+1) x y w (by omega) bound win.1 win.2.1 (by omega) actual
  refine ⟨w,actual,tax,by omega,fun both => by omega,?_⟩
  intro three
  rcases le_total x y with xy|yx
  · have xx : x=3 := by omega
    have yy : y=H := by omega
    rw [xx,yy] at actual
    exact true_three_head_exposure X H w (by omega) bound (exact_typed_width_swap X actual)
  · have yy : y=3 := by omega
    have xx : x=H := by omega
    rw [xx,yy] at actual
    exact true_three_head_exposure X H w (by omega) bound actual

#print axioms gap_two_high_fixed_selector
end JSP452Audit.StarHost