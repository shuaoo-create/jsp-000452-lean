import AnEarlierLargerHeadPaysTheNearTopWidthOnTheActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem paid_near_top_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    {j x y:ℕ} (win:WinsHeight F.n F.m (F.r+P.cutRoots.ncard) (j+2) x y)
    (prior:(∃p,p<F.n ⟨0,F.hs⟩ ∧ diagonal F.n F.m (F.r+2)-1=p+(y-1)) ∨
      (∃q,q<F.m ⟨0,F.ht⟩ ∧ diagonal F.n F.m (F.r+2)-1=q+(x-1))) :
    let Y := F.G.induce P.exterior
    widthAt F.n F.m (F.r+P.cutRoots.ncard) (j+2)≤peakCountAbove Y j+P.paidCore.ncard/(min x y+1)+P.excess := by
  intro Y
  let D := diagonal F.n F.m (F.r+2)-1
  let r := F.r+P.cutRoots.ncard
  let C := F.G.induce P.paidCore
  have host := (minimal_rank_exact_source F paid).2.2.2.1
  have pos : 0<D := lt_of_lt_of_le (by decide : 0<11) (strict_source_degree_at_least_eleven F paid)
  have cap (v:↥P.paidCore) : Nat.card (C.neighborSet v)≤D := (induced_neighbor_count_le F.G _ v).trans (host v.val)
  have holes : minimumExposure C D≤P.excess := (P.true_internal_hole_budget host).trans
    (P.genuine_regular_injection.trans (P.includes_odd_regular_excess kl E))
  have row := (strict_payable_exterior_constraints F paid P).2.2.2.2.2
  have typed := near_top_two_sided_recovery Y C F.n F.m F.hs F.ht F.hn F.hm row win pos cap prior
  rw [Nat.card_coe_set_eq] at typed
  obtain ⟨sz,low⟩ := exact_peak_inventory_cut Y j
  have count := typed_inventory_on_actual_cut Y win.1 win.2.1 (by have := win.2.2.1;omega : x+y-1=(j+1)+1)
    (by omega) typed _ (fun v => Nat.lt_of_le_of_lt (low v) (by omega))
  rw [sz] at count
  change widthAt F.n F.m r (j+2)-P.paidCore.ncard/(min x y+1)-minimumExposure C D≤peakCountAbove Y j at count
  change widthAt F.n F.m r (j+2)≤_;omega

theorem third_gap_top_two_inventories (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let N := P.paidCore.ncard
    D=H+3 → (widthAt F.n F.m r D≤peakCountAbove Y (D-2)+N/5+P.excess) ∧
      ∀x y,WinsHeight F.n F.m r (D-1) x y → (min x y=3 →
        widthAt F.n F.m r (D-1)≤peakCountAbove Y (D-3)+N/4+P.excess) ∧ (3≤min x y) := by
  intro D H r Y N gap
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have upperLevel : D-2+2=D := by omega
  have lowerLevel : D-3+2=D-1 := by omega
  have dom := strict_double_head_gap_range F paid
  obtain ⟨_,sum,minHead,_⟩ := dom
  change D+2≤F.n ⟨0,F.hs⟩+F.m ⟨0,F.ht⟩ at sum
  change D-H+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) at minHead
  have ceilings (j x y:ℕ) (w:WinsHeight F.n F.m r j x y) : x≤H ∧ y≤H := by
    exact ⟨((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 w.2.2.2.1).trans (Nat.le_max_left _ _),
      ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 w.2.2.2.2.1).trans (Nat.le_max_right _ _)⟩
  constructor
  · by_cases active:0<widthAt F.n F.m r D
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) active
      have w : WinsHeight F.n F.m r D x y := win
      obtain ⟨a,b⟩ := ceilings D x y w
      have ht := w.2.2.1
      have xy : 5≤min x y+1 := by omega
      have prior : (∃p,p<F.n ⟨0,F.hs⟩ ∧ D=p+(y-1)) ∨ (∃q,q<F.m ⟨0,F.ht⟩ ∧ D=q+(x-1)) := by
        by_cases red:x<F.n ⟨0,F.hs⟩
        · exact Or.inl ⟨x,red,by omega⟩
        · exact Or.inr ⟨y,by omega,by omega⟩
      have seen := paid_near_top_inventory F paid P E kl (j:=D-2) (x:=x) (y:=y) (by rw [upperLevel];exact w) prior
      change widthAt F.n F.m r (D-2+2)≤peakCountAbove Y (D-2)+N/(min x y+1)+P.excess at seen
      rw [upperLevel] at seen
      have small : N/(min x y+1)≤N/5 := Nat.div_le_div_left xy (by decide)
      exact seen.trans (Nat.add_le_add_right (Nat.add_le_add_left small _) _)
    · omega
  · intro x y w
    obtain ⟨a,b⟩ := ceilings (D-1) x y w
    have ht := w.2.2.1
    refine ⟨?_,by omega⟩
    intro small
    have prior : (∃p,p<F.n ⟨0,F.hs⟩ ∧ D=p+(y-1)) ∨ (∃q,q<F.m ⟨0,F.ht⟩ ∧ D=q+(x-1)) := by
      by_cases red:x=3
      · exact Or.inl ⟨x+1,by omega,by omega⟩
      · exact Or.inr ⟨y+1,by omega,by omega⟩
    have seen := paid_near_top_inventory F paid P E kl (j:=D-3) (x:=x) (y:=y) (by rw [lowerLevel];exact w) prior
    change widthAt F.n F.m r (D-3+2)≤peakCountAbove Y (D-3)+N/(min x y+1)+P.excess at seen
    simpa only [small,lowerLevel] using seen

#print axioms paid_near_top_inventory
#print axioms third_gap_top_two_inventories
end JSP452Audit.StarHost
