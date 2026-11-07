import OneSurvivingMixedWinnerActuallyReplenishesTheFullGapOnePlatform
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem genuine_unit_width_uses_a_matching_and_the_actual_full_head {A:Type u} [Finite A] (X:SimpleGraph A)
    (x y j w:ℕ) (px:0<x) (py:0<y) (head:x=j+1 ∨ y=j+1) (cap:∀v,Nat.card (X.neighborSet v)≤j)
    (live:ExactTypedWidth X x y w) : w=0 := by
  rcases live with zero|⟨a,b,pa,pb,_,force⟩
  · exact zero
  · rcases head with red|blue
    · rcases force X le_rfl with copy|copy
      · have no := uniform_pack_below_degree X x (fun z => (cap z).trans_lt (by omega)) a copy;omega
      · rw [sdiff_self] at copy
        have no := uniform_pack_bot_cap y py b copy;omega
    · rcases force ⊥ bot_le with copy|copy
      · have no := uniform_pack_bot_cap x px a copy;omega
      · rw [sdiff_bot] at copy
        have no := uniform_pack_below_degree X y (fun z => (cap z).trans_lt (by omega)) b copy;omega

theorem original_unit_inventory_on_its_own_degree_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    {j x y:ℕ} (win:WinsHeight F.n F.m (F.r+P.cutRoots.ncard) (j+1) x y) (unit:x=1 ∨ y=1) :
    widthAt F.n F.m (F.r+P.cutRoots.ncard) (j+1)≤P.capacity+peakCountAbove (F.G.induce P.exterior) j := by
  let Y := F.G.induce P.exterior
  let W := widthAt F.n F.m (F.r+P.cutRoots.ncard) (j+1)
  let U := peakPrefix Y (peakCountAbove Y j)
  obtain ⟨sz,cap⟩ := exact_peak_inventory_cut Y j
  obtain ⟨typed,_,_⟩ := strict_exterior_typed_column_inventory F paid P win
  rw [actualCoordinateLoss,if_pos unit] at typed
  change ExactTypedWidth Y x y (W-P.capacity) at typed
  have cut := typed_width_after_deletion Y U win.1 win.2.1 typed
  change U.ncard=peakCountAbove Y j at sz;rw [sz] at cut
  have ht := win.2.2.1
  have no := genuine_unit_width_uses_a_matching_and_the_actual_full_head _ x y j _ win.1 win.2.1 (by omega) cap cut
  change W≤P.capacity+peakCountAbove Y j;omega

theorem original_full_history_pays_total_inventory {A:Type u} [Finite A] (Y:SimpleGraph A) (D:ℕ)
    (cap:∀v,Nat.card (Y.neighborSet v)≤D) :
    (∑j∈Finset.range D,peakCountAbove Y j)≤Y.edgeSet.ncard := by
  have spent := peak_prefix_layer_price Y D (Nat.card A) cap
  have all : (∑j∈Finset.range D,min (Nat.card A) (peakCountAbove Y j))=∑j∈Finset.range D,peakCountAbove Y j :=
    Finset.sum_congr rfl (fun j _ => min_eq_right (peak_inventory_spec Y j).1)
  rw [all] at spent;omega

#print axioms genuine_unit_width_uses_a_matching_and_the_actual_full_head
#print axioms original_unit_inventory_on_its_own_degree_stage
#print axioms original_full_history_pays_total_inventory
end JSP452Audit.StarHost