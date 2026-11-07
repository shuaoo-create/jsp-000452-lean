import CostOfADeadNonunitPortRectangle
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_live_port_column {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)
    {s t r a b j : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (win : WinsHeight n m r j a b) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : R.starTax a<originalThresholdCount n a ∨ R.starTax b<originalThresholdCount m b) :
    widthAt n m r j≤uniformEnvelope R.erased j+R.totalCapacity := by
  obtain ⟨pa,pb,height,red,blue,width⟩ := win
  rcases live with ar|br
  · have real := R.active_port_rectangle n m hn hm ar blue row
    have fee := R.typed_width_envelope pa pb height real
    have tax := Nat.min_le_left R.totalCapacity (R.slotDamage a)
    change R.starTax a≤R.totalCapacity at tax
    omega
  · have real := R.active_port_rectangle m n hm hn br red (swap_positive_forcing_row _ _ _ row)
    have fee := R.typed_width_envelope pb pa (by omega : b+a-1=j) real
    have tax := Nat.min_le_left R.totalCapacity (R.slotDamage b)
    change R.starTax b≤R.totalCapacity at tax
    omega

theorem strict_nine_two_long_low_columns (F : StrictFamily.{u}) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (j : ℕ) (lo : 2≤j) :
    widthAt F.n F.m F.r j≤uniformEnvelope R.erased j+R.totalCapacity+(if j=3 then 1 else 0) := by
  by_cases live : 0<widthAt F.n F.m F.r j
  · obtain ⟨a,b,pa,pb,height,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by omega : 0<j) live
    have win : WinsHeight F.n F.m F.r j a b := ⟨pa,pb,height,red,blue,w⟩
    by_cases axes : a=1 ∨ b=1
    · have active : R.starTax a<originalThresholdCount F.n a ∨ R.starTax b<originalThresholdCount F.m b := by
        rcases axes with rfl|rfl
        · left;rw [original_threshold_one F.n F.pn]
          exact (Nat.min_le_left _ _).trans_lt (lt_min_iff.mp long).1
        · right;rw [original_threshold_one F.m F.pm]
          exact (Nat.min_le_left _ _).trans_lt (lt_min_iff.mp long).2
      have price := nine_live_port_column R F.n F.m F.hn F.hm win F.row active
      omega
    · exact nine_nonunit_port_column R F.n F.m F.hn F.hm (by omega) (by omega) win F.row
  · omega

theorem strict_nine_two_long_deficit (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (z : ℕ) (rn : ∀i,F.n i+z≤10) (bm : ∀j,F.m j+z≤10) :
    let d := F.rank-matchingEdges F.G
    let h := highestWidth F.n F.m F.r
    R.totalCapacity+9+R.portCount+envelopeReserve R.erased 8≤d+2*h+R.slotDamage z := by
  intro d h
  let P := R.totalCapacity
  let M := R.slotDamage z
  let tax (j : ℕ) := if j=9 then M+(h-1) else P+(if j=3 then 1 else 0)
  have near := (strict_nine_ninth_column_restoration F paid nine R z rn bm).1
  have prices (j) (lo : 2≤j) (_ : j≤9) : widthAt F.n F.m F.r j≤uniformEnvelope R.erased j+tax j := by
    by_cases last : j=9
    · subst j;simpa [tax,M,h,Nat.add_assoc] using near
    · have bound := strict_nine_two_long_low_columns F R long j lo
      simpa [tax,last,P,Nat.add_assoc] using bound
  have sum : (∑i∈Finset.range 8,tax (i+2))=7*P+1+M+(h-1) := by simp [Finset.sum_range_succ,tax];omega
  have price := strict_nine_port_column_account F paid nine R tax prices
  change 8*P+9+R.portCount+envelopeReserve R.erased 8≤d+h+(∑i∈Finset.range 8,tax (i+2)) at price
  rw [sum] at price
  change P+9+R.portCount+envelopeReserve R.erased 8≤d+2*h+M
  have hp : 1≤h := (strict_nine_original_peak F paid nine).1
  omega

#print axioms nine_live_port_column
#print axioms strict_nine_two_long_low_columns
#print axioms strict_nine_two_long_deficit
end JSP452Audit.StarHost
