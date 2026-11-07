import RetainEveryExtraEdgePaidByTheActualFourGapPrefix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_four_fixed_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let C := F.G.induce P.paidCore
    let N := P.paidCore.ncard
    let l := N/6
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    H+4≤D → 0<l → ∀i:ℕ,P.capacity+1≤widthAt n m (r+i+l) (D-2)+i+N/4 := by
  intro D H r C N l n m gap lp i
  have live := gap_four_last_three_nonpeak_cannot_be_low F paid P E hp credit gap
  change P.capacity<widthAt F.n F.m r (D-2) at live
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨a,b,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show 0<D-2 by omega) (show 0<widthAt F.n F.m r (D-2) by omega)
  have win : WinsHeight F.n F.m r (D-2) a b := w
  have ha : a≤H := ((original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
  have hb : b≤H := ((original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have smallA : N/(a+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have smallB : N/(b+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have keep : l+fixedHeadLoss P.capacity N l a+fixedHeadLoss P.capacity N l b≤N/4 := by
    have lo : l≤N/4 := Nat.div_le_div_left (by decide : 4≤6) (by decide)
    dsimp only [fixedHeadLoss]
    rcases (show 5≤a ∨ 5≤b by omega) with high|high
    · have safe : N/(a+1)≤l := Nat.div_le_div_left (by omega) (by decide)
      omega
    · have safe : N/(b+1)≤l := Nat.div_le_div_left (by omega) (by decide)
      omega
  have bill := fixed_lists_price_original_winner C F.n F.m F.hn F.hm l lp win
  rw [show Nat.card ↥P.paidCore=N from Nat.card_coe_set_eq _] at bill
  change widthAt F.n F.m r (D-2)≤widthAt n m (r+l) (D-2)+(l+fixedHeadLoss P.capacity N l a+fixedHeadLoss P.capacity N l b) at bill
  have kn := protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l
  have vm := protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l
  have hs := F.hs
  have ht' := F.ht
  rw [show r+i+l=r+l+i by omega,widthAt_shift (show 0<min F.s ((componentBudget C F.n).len+l) by omega)
    (show 0<min F.t ((componentBudget C F.m).len+l) by omega) n m kn vm (r+l) i (D-2)]
  omega

#print axioms gap_four_fixed_width
end JSP452Audit.StarHost
