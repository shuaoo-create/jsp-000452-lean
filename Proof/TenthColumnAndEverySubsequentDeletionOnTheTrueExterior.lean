import KeepTheSurvivingAngularWidthsOnTheTrueExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_tenth_column_on_the_actual_exterior (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G} {w:ℕ} (R : TenPortSupport F.G K w) (z : ℕ)
    (rn : ∀i,F.n i+z≤11) (bm : ∀j,F.m j+z≤11) :
    let L := widthAt F.n F.m F.r 10
    let h := highestWidth F.n F.m F.r
    L≤uniformEnvelope R.outside 10+R.slotDamage z+(h-1) ∧
    ∀T : Set (↥(R.supportᶜ:Set F.X)),(∀v : ↥(Tᶜ : Set (↥(R.supportᶜ:Set F.X))),Nat.card ((R.outside.induce Tᶜ).neighborSet v)≤9) →
      L-T.ncard≤R.slotDamage z+max (h-1) (minimumExposure (R.outside.induce Tᶜ) 9) := by
  intro L h
  by_cases live : 0<L
  · obtain ⟨a,b,pa,pb,height,red,blue,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<10) live
    change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at win
    have na := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).mpr red
    have mb := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).mpr blue
    have nlim := rn ⟨0,F.hs⟩
    have mlim := bm ⟨0,F.ht⟩
    have ta : R.starTax a≤R.slotDamage z := (Nat.min_le_right _ _).trans (R.port_slot_decreases (by omega))
    have tb : R.starTax b≤R.slotDamage z := (Nat.min_le_right _ _).trans (R.port_slot_decreases (by omega))
    have alive {x y M : ℕ} (px : 0<x) (py : 0<y) (eq : x+y-1=10) (price : M≤R.slotDamage z)
        (rest : ExactTypedWidth R.outside x y (L-M)) :
        L≤uniformEnvelope R.outside 10+R.slotDamage z+(h-1) ∧
        ∀T : Set (↥(R.supportᶜ:Set F.X)),(∀v : ↥(Tᶜ : Set (↥(R.supportᶜ:Set F.X))),Nat.card ((R.outside.induce Tᶜ).neighborSet v)≤9) →
          L-T.ncard≤R.slotDamage z+max (h-1) (minimumExposure (R.outside.induce Tᶜ) 9) := by
      have envelope : L-M≤uniformEnvelope R.outside 10 := by
        rcases rest with zero|⟨u,v,hu,hv,sz,force⟩
        · omega
        · exact sz ▸ uniform_pair_le_envelope _ _ _ _ _ _ px py hu hv eq force
      refine ⟨by omega,?_⟩
      intro T cap
      have reduced := typed_width_after_deletion R.outside T px py rest
      have exposure := typed_width_exposure_at_cap _ 9 x y _ (by decide) cap px py eq reduced
      omega
    by_cases moreA : R.starTax a<originalThresholdCount F.n a
    · apply alive pa pb height ta
      rw [win];exact R.real_typed_rectangle F.n F.m F.hn F.hm pa pb moreA blue F.row
    by_cases moreB : R.starTax b<originalThresholdCount F.m b
    · apply alive pb pa (by omega : b+a-1=10) tb
      rw [win,Nat.add_comm (originalThresholdCount F.n a)]
      exact R.real_typed_rectangle F.m F.n F.hm F.hn pb pa moreB red (swap_positive_forcing_row _ _ _ F.row)
    have hp := (strict_ten_inventory F paid ten).1
    obtain ⟨i,j,_,_,_,_,shape,_⟩ := strict_ten_true_factor_peak F paid ten
    have peak : F.n i+F.m j=12 := by rcases shape with pair|pair|pair <;> omega
    have atTop : widthAt F.n F.m F.r 11=h := by
      rw [show 11=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
    change 1≤h at hp
    have weak : L≤R.slotDamage z+(h-1) := by
      by_cases bigger : a+1≤F.n i
      · have hit := (original_threshold_prefix F.n F.hn (a+1) i).mp bigger
        have bound := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm
          (show (a+1)+b-1=11 by omega) (Nat.zero_lt_of_lt hit) blue
        rw [atTop] at bound;omega
      · have hit := (original_threshold_prefix F.m F.hm (b+1) j).mp (by omega)
        have bound := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm
          (show a+(b+1)-1=11 by omega) red (Nat.zero_lt_of_lt hit)
        rw [atTop] at bound;omega
    exact ⟨by omega,fun T _ => by omega⟩
  · exact ⟨by omega,fun _ _ => by omega⟩

#print axioms ten_tenth_column_on_the_actual_exterior
end JSP452Audit.StarHost
