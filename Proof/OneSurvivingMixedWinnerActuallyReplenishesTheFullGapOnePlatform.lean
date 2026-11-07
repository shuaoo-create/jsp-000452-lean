import AddOneActualLowColumnRefundToTheLastGapMatchingDeficit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem original_head_endpoint_stock (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let d := F.rank-matchingEdges F.G
    let Y := F.G.induce P.exterior
    2*d≤peakCountAbove Y (H-1) := by
  intro H d Y
  have pos : 0<H := (F.pn ⟨0,F.hs⟩).trans (Nat.le_max_left _ _)
  have stages := strict_joint_peak_history_inventory F paid P
  have hh : H-1+1=H := by omega
  rcases le_total (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) with red|blue
  · have eq : H=F.m ⟨0,F.ht⟩ := max_eq_right red
    have yes : 0<originalThresholdCount F.m (H-1+1) := (original_threshold_prefix F.m F.hm _ ⟨0,F.ht⟩).1 (by rw [hh,eq])
    have r := stages.2.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    omega
  · have eq : H=F.n ⟨0,F.hs⟩ := max_eq_left blue
    have yes : 0<originalThresholdCount F.n (H-1+1) := (original_threshold_prefix F.n F.hn _ ⟨0,F.hs⟩).1 (by rw [hh,eq])
    have r := stages.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    omega


theorem every_original_head_height_has_a_large_unit_candidate (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (j:ℕ) (pos:0<j)
    (head:j≤max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)) :
    P.capacity+(F.rank-matchingEdges F.G)+1≤widthAt F.n F.m (F.r+P.cutRoots.ncard) j := by
  let r := F.r+P.cutRoots.ncard
  have lengths := (strict_payable_exterior_constraints F paid P).1
  change P.capacity+r+(F.rank-matchingEdges F.G)+1≤min F.s F.t at lengths
  rcases (show j≤F.n ⟨0,F.hs⟩ ∨ j≤F.m ⟨0,F.ht⟩ by omega) with red|blue
  · have high := (original_threshold_prefix F.n F.hn j ⟨0,F.hs⟩).1 red
    have one := original_threshold_one F.m F.pm
    have bill := actual_rectangle_le_column (r:=r) F.n F.m F.hn F.hm (by omega : j+1-1=j) high (show 0<originalThresholdCount F.m 1 by rw [one];exact F.ht)
    rw [one] at bill;change _≤widthAt F.n F.m r j;omega
  · have high := (original_threshold_prefix F.m F.hm j ⟨0,F.ht⟩).1 blue
    have one := original_threshold_one F.n F.pn
    have bill := actual_rectangle_le_column (r:=r) F.n F.m F.hn F.hm (by omega : 1+j-1=j) (show 0<originalThresholdCount F.n 1 by rw [one];exact F.hs) high
    rw [one] at bill;change _≤widthAt F.n F.m r j;omega

theorem gap_one_mixed_refund_stock (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let N := P.paidCore.ncard
    let Z := P.capacity
    let Y := F.G.induce P.exterior
    D=H+1 → N/3-R<peakCountAbove Y (H-1) ∧
      (∀j x y,j<D-2 → 2≤min x y → WinsHeight F.n F.m r (j+2) x y →
        ExactTypedWidth Y x y (widthAt F.n F.m r (j+2)-N/3) ∧ Z-R<peakCountAbove Y (H-1)) := by
  intro D H r R N Z Y gap
  let G := P.gamma (highestWidth F.n F.m F.r)
  let ρ := P.excess
  let d := F.rank-matchingEdges F.G
  let e := minimumExposure (F.G.induce P.paidCore) D
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  have initial := gap_one_deficit_with_one_actual_refund F paid P E kl hp (show G≤0 by dsimp only [G];omega) 0 0 gap (by omega) (Or.inl rfl)
  change 2*(Z:ℤ)+2*0+2≤2*d+2*((N/3:ℕ):ℤ)+2*e+ρ+2*G at initial
  have debt := (gap_one_top_typed F paid P E kl gap).1
  change e≤ρ at debt
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have facts := P.exact_weight_and_root_cost E cap (highestWidth F.n F.m F.r)
  have sz := facts.2.2.2.2.2
  change N=2*Z+P.positives.ncard at sz
  have room := facts.2.2.2.1
  change (D:ℤ)*P.positives.ncard≤2*Z at room
  have small := mul_le_mul_of_nonneg_right (show (11:ℤ)≤D by omega) (show (0:ℤ)≤P.positives.ncard by positivity)
  have roots := P.positive_count_with_original_roots E
  have root : P.positives.ncard+1≤R+ρ := by dsimp only [R,r,ρ];omega
  have stock := original_head_endpoint_stock F paid P
  change 2*d≤peakCountAbove Y (H-1) at stock
  change G≤-3*(ρ:ℤ) at credit
  have pos := (strict_payable_exterior_constraints F paid P).2.2.1
  change 0<d at pos
  refine ⟨by omega,?_⟩
  intro j x y valid mi win
  let W := widthAt F.n F.m r (j+2)
  have strong := every_original_head_height_has_a_large_unit_candidate F paid P (j+2) (by omega) (by omega)
  change Z+d+1≤W at strong
  have either := positive_monochrome_or_two_root_bounded_counts Y (F.G.induce P.paidCore) F.n F.m F.hn F.hm
    (strict_payable_exterior_constraints F paid P).2.2.2.2.2 win (show 0<W by omega)
  rw [Nat.card_coe_set_eq] at either
  change ExactTypedWidth Y x y (W-N/(min x y+1)) ∨ W+R≤N/(x+1)+N/(y+1) at either
  have slot (v:ℕ) (ok:2≤v) : N/(v+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide)
  have typed : ExactTypedWidth Y x y (W-N/3) := by
    rcases either with yes|dead
    · exact actual_typed_width_down _ yes (by have := slot (min x y) mi;omega)
    · have := slot x (by omega);have := slot y (by omega);omega
  refine ⟨typed,?_⟩
  have env : W-N/3≤uniformEnvelope Y (j+2) := by
    rcases typed with no|⟨a,b,pa,pb,len,force⟩
    · omega
    · exact len ▸ uniform_pair_le_envelope Y x y a b (j+2) win.1 win.2.1 pa pb win.2.2.1 force
  have bonus := gap_one_deficit_with_one_actual_refund F paid P E kl hp (show G≤0 by omega) j (Z-N/3) gap valid (Or.inr (by
    change 2*(W-uniformEnvelope Y (j+2))+2*(Z-N/3)≤2*Z+(if j=1 then ρ else 0);omega))
  change (2:ℤ)*Z+2*((Z-N/3:ℕ):ℤ)+2≤2*d+2*((N/3:ℕ):ℤ)+2*e+ρ+2*G at bonus
  omega

#print axioms original_head_endpoint_stock
#print axioms every_original_head_height_has_a_large_unit_candidate
#print axioms gap_one_mixed_refund_stock
end JSP452Audit.StarHost