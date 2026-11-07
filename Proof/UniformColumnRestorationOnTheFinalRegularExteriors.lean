import BothFinalExposuresAreChargedToTheirOwnSurplus
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_two_missing_slot_counts (F:StrictFamily.{u}) (K:TenRegularBudget F.G) (a b:ℕ)
    (red:2≤a) (blue:2≤b) (high:8≤a+b) :
    chosenSlots F.G K.selected a+chosenSlots F.G K.selected b≤K.P+1 := by
  let M := chosenSlots F.G K.selected
  have two := ten_regular_slot_volume K 2
  have three := ten_regular_slot_volume K 3
  have five := ten_regular_slot_volume K 5
  change 3*M 2≤_ at two
  change 4*M 3≤_ at three
  change 6*M 5≤_ at five
  have sm := K.small
  have mono : Antitone M := chosen_slots_antitone F.G K.selected
  change M a+M b≤K.P+1
  by_cases ar:3≤a
  · by_cases bl:3≤b
    · have x := mono ar;have y := mono bl;omega
    · have x := mono (by omega : 5≤a);have y := mono blue;omega
  · have x := mono red;have y := mono (by omega : 5≤b);omega

theorem ten_regular_platform_on_its_graph (F:StrictFamily.{u}) (K:TenRegularBudget F.G)
    (j z w:ℕ) (high:7≤j) (nonunit:2≤z) (large:2*w≤j+2)
    (reds:∀i,F.n i+z≤j+1) (blues:∀i,F.m i+z≤j+1)
    (V:Set ↥(K.supportᶜ:Set F.X)) (cap:∀v,Nat.card (((F.G.induce K.supportᶜ).induce Vᶜ).neighborSet v)≤j-1) :
    let L := widthAt F.n F.m F.r j
    let M := chosenSlots F.G K.selected
    let rho := minimumExposure ((F.G.induce K.supportᶜ).induce Vᶜ) (j-1)
    (L≤K.P ∧ L≤M z+M w) ∨ L≤V.ncard+M z+rho := by
  intro L M rho
  by_cases live:0<L
  · obtain ⟨a,b,ap,bp,ht,red,blue,width⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by omega : 0<j) live
    have ar := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
    have br := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
    have nr := reds ⟨0,F.hs⟩
    have mr := blues ⟨0,F.ht⟩
    have az : z≤a := by omega
    have bz : z≤b := by omega
    have floor := ten_two_missing_slot_counts F K a b (by omega) (by omega) (by omega)
    change M a+M b≤K.P+1 at floor
    have mono : Antitone M := chosen_slots_antitone F.G K.selected
    rcases column_after_closed_set_deletion F K (j-1) j a b z (by omega) (by omega)
      ⟨ap,bp,ht,red,blue,width⟩ az bz V cap with dead|actual
    · change L≤M a+M b-1-F.r at dead
      left
      by_cases big:w≤a
      · have aa := mono big;have bb := mono bz;omega
      · have aa := mono az;have bb := mono (by omega : w≤b);omega
    · change L-V.ncard≤M z+rho at actual
      right;omega
  · left;omega

#print axioms ten_two_missing_slot_counts
#print axioms ten_regular_platform_on_its_graph
end JSP452Audit.StarHost
