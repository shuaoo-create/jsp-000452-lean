import ChargeTheSameTwoStageDeletionToItsOwnSmallerFixedRow
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_full_stage_is_short (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let Y := F.G.induce P.exterior
    let R := F.r+P.cutRoots.ncard+1
    D=H+2 → R+peakCountAbove Y (H+1)<P.paidCore.ncard/4 := by
  intro D H Y R gap
  let N := P.paidCore.ncard
  let Z := P.capacity
  let b := peakCountAbove Y (H+1)
  let u := peakCountAbove Y H
  let i := N/4-R
  have Rpos : 0<R := by dsimp only [R];omega
  have big := (gap_two_initial_inventory F paid P E kl hp credit gap).1
  change R<Z at big
  obtain ⟨sz,_,_,ratio,_,_,_⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  change N=2*Z+P.positives.ncard at sz
  change 16*N≤35*Z at ratio
  have lp : 0<N/4 := by omega
  have run := (gap_two_fixed_prefix_price F paid P E kl hp credit (N/4) gap lp (by omega) (by omega)).2.2.2
  change (_:ℤ)+Z+(N/4:ℕ)+min i u+min i b+1≤P.gamma (highestWidth F.n F.m F.r)+2*((N/3:ℕ):ℤ)+2*((N/4-N/4:ℕ):ℤ)+2*i at run
  rw [Nat.sub_self] at run
  have ord : b≤u := peak_counts_antitone Y (by omega)
  by_contra! no
  change N/4≤R+b at no
  have short : i≤b := by dsimp only [i];omega
  rw [min_eq_left (short.trans ord),min_eq_left short] at run
  omega

theorem gap_two_high_platform_supplies_both_stages (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let R := F.r+P.cutRoots.ncard+1
    let N := P.paidCore.ncard
    let L := widthAt F.n F.m (F.r+P.cutRoots.ncard) D
    let b := peakCountAbove Y (H+1)
    let u := peakCountAbove Y H
    let l := max (N/5) (R+b)
    let i := l-R
    D=H+2 → P.capacity<L → b ≤ i ∧ i ≤ u ∧ l≤N/4 ∧ 0<l ∧
      (∀v,Nat.card ((Y.induce (peakPrefix Y i)ᶜ).neighborSet v)≤D-1) ∧
      ∀x y,WinsHeight F.n F.m (F.r+P.cutRoots.ncard) D x y →
        3≤min x y ∧ 4≤max x y ∧ ExactTypedWidth Y x y (L-N/(min x y+1)) ∧ L≤u+N/(min x y+1) := by
  intro D H C Y R N L b u l i gap high
  let r := F.r+P.cutRoots.ncard
  let Z := P.capacity
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have short := gap_two_full_stage_is_short F paid P E kl hp credit gap
  change R+b<N/4 at short
  have pos : 0<R := by dsimp only [R];omega
  have order : b≤u := peak_counts_antitone Y (by omega)
  have sizes := (full_capacity_prefix_data F paid P E hp (by omega)).2.2.2.1
  change 16*N≤35*Z at sizes
  have typed (x y:ℕ) (win:WinsHeight F.n F.m r D x y) :
      3≤min x y ∧ 4≤max x y ∧ ExactTypedWidth Y x y (L-N/(min x y+1)) ∧ L≤u+N/(min x y+1) := by
    have ht := win.2.2.1
    have mi := ((gap_two_top_typed F paid P E kl gap).2.2.1 x y win).1
    have six : 6≤max x y := by omega
    have price := monochrome_or_two_bounded_counts Y C F.n F.m F.hn F.hm (strict_payable_exterior_constraints F paid P).2.2.2.2.2 win
    rw [Nat.card_coe_set_eq] at price
    change ExactTypedWidth Y x y (L-N/(min x y+1)) ∨ L≤N/(x+1)+N/(y+1) at price
    have mark (h:ℕ) (h3:3≤h) : N/(h+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
    have far (h:ℕ) (h6:6≤h) : N/(h+1)≤N/7 := Nat.div_le_div_left (by omega) (by decide)
    have actual : ExactTypedWidth Y x y (L-N/(min x y+1)) := by
      rcases price with yes|dead
      · exact yes
      · have capX := mark x (by omega)
        have capY := mark y (by omega)
        change Z<L at high
        rcases le_total x y with xy|yx
        · have last := far y (by omega);omega
        · have last := far x (by omega);omega
    obtain ⟨card,small⟩ := exact_peak_inventory_cut Y H
    have inv := typed_inventory_on_actual_cut Y win.1 win.2.1 (by omega : x+y-1=(D-1)+1) (by omega)
      actual _ (fun v => (small v).trans_lt (by omega))
    rw [card] at inv
    change _≤u at inv
    exact ⟨mi,by omega,actual,by omega⟩
  obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) (by omega : 0<L)
  obtain ⟨mi,_,_,stock⟩ := typed x y w
  have worst : N/(min x y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  change Z<L at high
  have ib : b ≤ i := by dsimp only [i,l];omega
  have iu : i ≤ u := by dsimp only [i,l];omega
  have price := (peak_inventory_spec Y (H+1)).2.1
  have remain := (peak_fee_antitone Y ib).trans price
  refine ⟨ib,iu,by dsimp only [l];omega,by dsimp only [l];omega,fun v => ((chosenPeakStep Y (peakPrefix Y i)).cap v).trans (remain.trans (by omega)),typed⟩

#print axioms gap_two_full_stage_is_short
#print axioms gap_two_high_platform_supplies_both_stages
end JSP452Audit.StarHost