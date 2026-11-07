import SignedPriceOfTheTenthColumnAfterTheFirstStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem column_after_closed_set_deletion (F:StrictFamily.{u}) (K:TenRegularBudget F.G)
    (D j a b z:ℕ) (positive:0<D) (height:j=D+1) (win:WinsHeight F.n F.m F.r j a b)
    (za:z≤a) (zb:z≤b) (V:Set ↥(K.supportᶜ:Set F.X))
    (cap:∀v,Nat.card (((F.G.induce K.supportᶜ).induce Vᶜ).neighborSet v)≤D) :
    let L := widthAt F.n F.m F.r j
    (L≤chosenSlots F.G K.selected a+chosenSlots F.G K.selected b-1-F.r) ∨
    L-V.ncard≤chosenSlots F.G K.selected z+minimumExposure ((F.G.induce K.supportᶜ).induce Vᶜ) D := by
  intro L
  rcases actual_mono_width_or_two_small_counts F.G K.selected F.n F.m F.hn F.hm za zb win F.row with ⟨k,price,typed⟩|⟨small,small'⟩
  · right
    have kept := typed_width_after_deletion (F.G.induce K.supportᶜ) V win.1 win.2.1 typed
    have fee := typed_width_exposure_at_cap _ D a b (L-k-V.ncard) positive cap win.1 win.2.1 (win.2.2.1.trans height) kept
    omega
  · left
    have w := win.2.2.2.2.2
    change L=_ at w
    omega

theorem ten_ninth_column_on_second_cut (F:StrictFamily.{u}) (K:TenRegularBudget F.G)
    (redMax:∀i,F.n i≤8) (blueMax:∀j,F.m j≤8) (V:Set ↥(K.supportᶜ:Set F.X))
    (cap:∀v,Nat.card (((F.G.induce K.supportᶜ).induce Vᶜ).neighborSet v)≤8) :
    let L := widthAt F.n F.m F.r 9
    L≤K.P ∨ L-V.ncard≤chosenSlots F.G K.selected 2+minimumExposure ((F.G.induce K.supportᶜ).induce Vᶜ) 8 := by
  intro L
  by_cases live:0<L
  · obtain ⟨a,b,ap,bp,ht,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<9) live
    have ar := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
    have br := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
    have nr := redMax ⟨0,F.hs⟩
    have mr := blueMax ⟨0,F.ht⟩
    have ax : 2≤a := by omega
    have bx : 2≤b := by omega
    have bill := column_after_closed_set_deletion F K 8 9 a b 2 (by decide) rfl ⟨ap,bp,ht,red,blue,w⟩ ax bx V cap
    rcases bill with dead|actual
    · left
      change L≤chosenSlots F.G K.selected a+chosenSlots F.G K.selected b-1-F.r at dead
      have two := ten_regular_slot_volume K 2
      have five := ten_regular_slot_volume K 5
      have sm := K.small
      by_cases big:5≤a
      · have aa := chosen_slots_antitone F.G K.selected big
        have bb := chosen_slots_antitone F.G K.selected bx
        omega
      · have aa := chosen_slots_antitone F.G K.selected ax
        have bb := chosen_slots_antitone F.G K.selected (by omega : 5≤b)
        omega
    · exact Or.inr actual
  · left;omega

#print axioms column_after_closed_set_deletion
#print axioms ten_ninth_column_on_second_cut
end JSP452Audit.StarHost
