import SurvivingOriginalRectangleOnNinePorts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_ninth_column_restoration (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (z : ℕ)
    (rn : ∀i,F.n i+z≤10) (bm : ∀j,F.m j+z≤10) :
    let L := widthAt F.n F.m F.r 9
    let h := highestWidth F.n F.m F.r
    L≤uniformEnvelope R.erased 9+R.slotDamage z+(h-1) ∧
    ∀T : Set F.X,(∀v : ↥(Tᶜ : Set F.X),Nat.card ((R.erased.induce Tᶜ).neighborSet v)≤8) →
      L-T.ncard≤R.slotDamage z+max (h-1) (minimumExposure (R.erased.induce Tᶜ) 8) := by
  intro L h
  by_cases live : 0<L
  · obtain ⟨a,b,pa,pb,height,red,blue,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<9) live
    change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at win
    have na := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).mpr red
    have mb := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).mpr blue
    have nlim := rn ⟨0,F.hs⟩
    have mlim := bm ⟨0,F.ht⟩
    have ta : R.starTax a≤R.slotDamage z := (Nat.min_le_right _ _).trans (R.port_slot_decreases (by omega))
    have tb : R.starTax b≤R.slotDamage z := (Nat.min_le_right _ _).trans (R.port_slot_decreases (by omega))
    have alive {x y M : ℕ} (px : 0<x) (py : 0<y) (eq : x+y-1=9) (price : M≤R.slotDamage z)
        (rest : ExactTypedWidth R.erased x y (L-M)) :
        L≤uniformEnvelope R.erased 9+R.slotDamage z+(h-1) ∧
        ∀T : Set F.X,(∀v : ↥(Tᶜ : Set F.X),Nat.card ((R.erased.induce Tᶜ).neighborSet v)≤8) →
          L-T.ncard≤R.slotDamage z+max (h-1) (minimumExposure (R.erased.induce Tᶜ) 8) := by
      have envelope := R.typed_width_envelope px py eq rest
      refine ⟨by omega,?_⟩
      intro T cap
      have reduced := typed_width_after_deletion R.erased T px py rest
      have exposure := typed_width_exposure_at_cap _ 8 x y _ (by decide) cap px py eq reduced
      omega
    by_cases moreA : R.starTax a<originalThresholdCount F.n a
    · apply alive pa pb height ta
      rw [win];exact R.active_port_rectangle F.n F.m F.hn F.hm moreA blue F.row
    by_cases moreB : R.starTax b<originalThresholdCount F.m b
    · apply alive pb pa (by omega : b+a-1=9) tb
      rw [win,Nat.add_comm (originalThresholdCount F.n a)]
      exact R.active_port_rectangle F.m F.n F.hm F.hn moreB red (swap_positive_forcing_row _ _ _ F.row)
    obtain ⟨hp,_,_,_,i,j,_,_,_,shape,_⟩ := strict_nine_original_peak F paid nine
    have peak : F.n i+F.m j=11 := by rcases shape with ⟨x,y⟩|⟨x,y⟩ <;> omega
    have ten : widthAt F.n F.m F.r 10=h := by
      rw [show 10=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
    change 1≤h at hp
    have weak : L≤R.slotDamage z+(h-1) := by
      by_cases bigger : a+1≤F.n i
      · have hit := (original_threshold_prefix F.n F.hn (a+1) i).mp bigger
        have bound := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm
          (show (a+1)+b-1=10 by omega) (Nat.zero_lt_of_lt hit) blue
        rw [ten] at bound;omega
      · have hit := (original_threshold_prefix F.m F.hm (b+1) j).mp (by omega)
        have bound := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm
          (show a+(b+1)-1=10 by omega) red (Nat.zero_lt_of_lt hit)
        rw [ten] at bound;omega
    exact ⟨by omega,fun T _ => by omega⟩
  · exact ⟨by omega,fun _ _ => by omega⟩

#print axioms strict_nine_ninth_column_restoration
end JSP452Audit.StarHost
