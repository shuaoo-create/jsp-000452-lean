import BothExposureBoundsOnTheSamePortHistoryAtNineAndEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem column_after_port_exterior_deletion (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ} (W:TenPortSupport F.G K h)
    (D j a b z:ℕ) (positive:0<D) (height:j=D+1) (win:WinsHeight F.n F.m F.r j a b)
    (za:z≤a) (zb:z≤b) (V:Set ↥(W.supportᶜ:Set F.X))
    (cap:∀v,Nat.card ((W.outside.induce Vᶜ).neighborSet v)≤D) :
    let L := widthAt F.n F.m F.r j
    (L≤W.slotDamage a+W.slotDamage b-1-F.r) ∨
    L-V.ncard≤W.slotDamage z+minimumExposure (W.outside.induce Vᶜ) D := by
  intro L
  rcases W.retained_type_or_two_small_heads F.n F.m F.hn F.hm za zb win F.row with ⟨k,price,typed⟩|⟨small,small'⟩
  · right
    have kept := typed_width_after_deletion W.outside V win.1 win.2.1 typed
    have fee := typed_width_exposure_at_cap _ D a b (L-k-V.ncard) positive cap win.1 win.2.1 (win.2.2.1.trans height) kept
    omega
  · left
    have w := win.2.2.2.2.2
    change L=_ at w
    omega

theorem ten_ninth_column_on_second_port_cut (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ} (W:TenPortSupport F.G K h)
    (redMax:∀i,F.n i≤8) (blueMax:∀j,F.m j≤8) (V:Set ↥(W.supportᶜ:Set F.X))
    (cap:∀v,Nat.card ((W.outside.induce Vᶜ).neighborSet v)≤8) :
    let L := widthAt F.n F.m F.r 9
    L≤(W.half+4) ∨ L-V.ncard≤W.slotDamage 2+minimumExposure (W.outside.induce Vᶜ) 8 := by
  intro L
  by_cases live:0<L
  · obtain ⟨a,b,ap,bp,ht,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<9) live
    have ar := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
    have br := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
    have nr := redMax ⟨0,F.hs⟩
    have mr := blueMax ⟨0,F.ht⟩
    have ax : 2≤a := by omega
    have bx : 2≤b := by omega
    have bill := column_after_port_exterior_deletion F W 8 9 a b 2 (by decide) rfl ⟨ap,bp,ht,red,blue,w⟩ ax bx V cap
    rcases bill with dead|actual
    · left
      change L≤W.slotDamage a+W.slotDamage b-1-F.r at dead
      have book := W.orderFloor
      have total : W.support.ncard=2*W.half+W.parity := by
        dsimp only [TenPortSupport.half,TenPortSupport.parity];omega
      have eps : W.parity≤2 := by dsimp only [TenPortSupport.half,TenPortSupport.parity];omega
      have port := W.defect
      change W.targetDefect+W.portCount≤2 at port
      have two : 3*W.slotDamage 2≤2*W.half+W.parity+2*W.portCount := by dsimp only [TenPortSupport.slotDamage];omega
      have five : 6*W.slotDamage 5≤2*W.half+W.parity+5*W.portCount := by dsimp only [TenPortSupport.slotDamage];omega
      by_cases big:5≤a
      · have aa := W.port_slot_decreases big
        have bb := W.port_slot_decreases bx
        omega
      · have aa := W.port_slot_decreases ax
        have bb := W.port_slot_decreases (by omega : 5≤b)
        omega
    · exact Or.inr actual
  · left;omega

#print axioms column_after_port_exterior_deletion
#print axioms ten_ninth_column_on_second_port_cut
end JSP452Audit.StarHost
