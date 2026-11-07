import TheUniqueRemainingOriginalGapHasItsFullAutomaticEntry
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem last_gap_winners_survive_monochromatically (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ))
    {x y:ℕ} (win:WinsHeight F.n F.m (F.r+P.cutRoots.ncard) (diagonal F.n F.m (F.r+2)-1) x y) :
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let N := P.paidCore.ncard
    let L := widthAt F.n F.m r (diagonal F.n F.m (F.r+2)-1)
    2≤min x y ∧ ExactTypedWidth Y x y (L-N/(min x y+1)) := by
  intro Y r N L
  let D := diagonal F.n F.m (F.r+2)-1
  let Z := P.capacity
  have gap := strict_original_head_gap_is_one F paid
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have mi := ((gap_one_top_typed F paid P E kl gap).2.2.1 x y win).1
  have hi := (only_gap_automatic_entry F paid P E kl hp credit).2.2.2
  change Z<L at hi
  have size := (full_capacity_prefix_data F paid P E hp (by omega)).2.2.2.1
  change 16*N≤35*Z at size
  have alive := monochrome_or_two_bounded_counts Y (F.G.induce P.paidCore) F.n F.m F.hn F.hm
    (strict_payable_exterior_constraints F paid P).2.2.2.2.2 win
  rw [Nat.card_coe_set_eq] at alive
  change ExactTypedWidth Y x y (L-N/(min x y+1)) ∨ L≤N/(x+1)+N/(y+1) at alive
  refine ⟨mi,?_⟩
  rcases alive with yes|dead
  · exact yes
  have ht := win.2.2.1
  change x+y-1=D at ht
  have bounds (a b:ℕ) (ord:a≤b) (sum:a+b-1=D) (two:2≤a) : N/(a+1)+N/(b+1)≤Z := by
    by_cases small:a=2
    · have large : N/(b+1)≤N/11 := Nat.div_le_div_left (by omega) (by decide)
      rw [small];omega
    · have first : N/(a+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
      have second : N/(b+1)≤N/7 := Nat.div_le_div_left (by omega) (by decide)
      omega
  rcases le_total x y with xy|yx
  · have := bounds x y xy ht (by omega);omega
  · have := bounds y x yx (by omega) (by omega);omega

theorem last_gap_smaller_row_and_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) (l:ℕ) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let N := P.paidCore.ncard
    let b := peakCountAbove Y H
    let i := l-R
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    let g := (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)
    let e := minimumExposure X H
    let p := H/2
    R+b≤l → N/6≤l → l≤N/3 →
      0≤g ∧ g+b+1≤P.gamma h+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ)+i ∧
      ((H:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g ∧
      (∀v,Nat.card (X.neighborSet v)≤H) ∧
      ∀x y,WinsHeight F.n F.m r D x y →
        let w := widthAt F.n F.m r D-N/(min x y+1)-i
        ExactTypedWidth X x y w ∧ w≤e ∧ (min x y=3 → (D-2)*w≤2*e) := by
  intro D H h C Y r R N b i X n m g e p cover lo hi
  have gap : D=H+1 := strict_original_head_gap_is_one F paid
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have rp : 0<R := by dsimp only [R];omega
  have lp : 0<l := by omega
  have ib : b ≤ i := by dsimp only [i];omega
  have stock := (only_gap_automatic_entry F paid P E kl hp credit).2.1
  change N/3-R<peakCountAbove Y (H-1) at stock
  have enough : i≤Nat.card ↥P.exterior := by
    exact (Nat.sub_le_sub_right hi R).trans (stock.le.trans (peak_inventory_spec Y (H-1)).1)
  have size := (peak_prefix_size Y i).trans (min_eq_left enough)
  have capX (v) : Nat.card (X.neighborSet v)≤H := ((chosenPeakStep Y (peakPrefix Y i)).cap v).trans ((peak_fee_antitone Y ib).trans (peak_inventory_spec Y H).2.1)
  obtain ⟨live,smaller,row,bill⟩ := gap_one_fixed_prefix_price F paid P E kl hp credit l gap lp lo hi
  change ForcingRow X _ _ (padDemand n) (padDemand m) (r+i+l) at row
  have hs := F.hs
  have ht := F.ht
  have sp : 0<min F.s ((componentBudget C F.n).len+l) := by omega
  have tp : 0<min F.t ((componentBudget C F.m).len+l) := by omega
  have hn := protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l
  have hm := protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l
  have pn := protected_demand_positive F.n _ F.pn ((componentBudget C F.n).entries_positive _ F.pn) l
  have pm := protected_demand_positive F.m _ F.pm ((componentBudget C F.m).entries_positive _ F.pm) l
  have baseline := paid sp tp n m hn hm pn pm _ _ row smaller
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at baseline
  have nonneg : 0≤g := by dsimp only [g];omega
  have lim := live_row_height_at_degree_cap X sp tp n m hn hm pn pm row live capX
  have sel := smaller_row_exposure_budget sp tp n m hn hm pn pm X (r+i+l) H F.rank (by omega) row live smaller paid capX lim
  change ((H:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g at sel
  change ((X.edgeSet.ncard-rowEnergy n m (r+i+l):ℕ):ℤ)+min i b+1≤P.gamma h+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ)+i at bill
  refine ⟨nonneg,by dsimp only [g];omega,sel,capX,?_⟩
  intro x y win w
  obtain ⟨mi,typed⟩ := last_gap_winners_survive_monochromatically F paid P E kl hp credit win
  have next := typed_width_after_deletion Y (peakPrefix Y i) win.1 win.2.1 typed
  rw [size] at next
  change ExactTypedWidth X x y w at next
  have ht := win.2.2.1
  refine ⟨next,typed_width_exposure_at_cap X H x y w (by omega) capX win.1 win.2.1 (by omega) next,?_⟩
  intro three
  have lifted (v) : Nat.card (X.neighborSet v)≤D-2+1 := (capX v).trans (by omega)
  change (D-2)*w≤2*minimumExposure X H
  rw [show H=D-2+1 by omega]
  rcases le_total x y with xy|yx
  · have xx : x=3 := by omega
    have yy : y=D-2 := by omega
    rw [xx,yy] at next
    exact true_three_head_exposure X (D-2) w (by omega) lifted (exact_typed_width_swap X next)
  · have yy : y=3 := by omega
    have xx : x=D-2 := by omega
    rw [xx,yy] at next
    exact true_three_head_exposure X (D-2) w (by omega) lifted next

#print axioms last_gap_winners_survive_monochromatically
#print axioms last_gap_smaller_row_and_exposure
end JSP452Audit.StarHost