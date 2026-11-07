import ExposureOnFixedFourDegreeExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_no_five_actual_fifth_column (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4)
    (T:Finset F.G.ConnectedComponent) (H:SixFiveFourHistory (F.G.induce (componentVertices F.G T)ᶜ)) :
    widthAt F.n F.m F.r 5≤max (2*chosenSlots F.G T 3) (H.fiveCut.ncard+6+chosenSlots F.G T 2) := by
  let U := componentVertices F.G T
  let C := F.G.induce U
  let O := F.G.induce Uᶜ
  let M := chosenSlots F.G T 2
  let N := chosenSlots F.G T 3
  let L := widthAt F.n F.m F.r 5
  let E := uniformEnvelope O 5
  change L≤max (2*N) (H.fiveCut.ncard+6+M)
  have ep := strict_no_five_fifth_envelope F paid six red blue U (component_vertices_closed F.G T) H
  change E≤H.fiveCut.ncard+6 at ep
  have nm : N≤M := by
    apply Finset.sum_le_sum;intro c _;change Nat.card c.supp/4≤Nat.card c.supp/3;omega
  by_cases live : 0<L
  · obtain ⟨x,y,rx,byh,ht,rf,bg,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<5) live
    have nx := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 rf
    have my := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 bg
    have ncap := red ⟨0,F.hs⟩
    have mcap := blue ⟨0,F.ht⟩
    obtain ⟨n4,m4,_,_⟩ := six_degree_head_count_guards F paid six
    have h := (strict_six_only_one_original_component F paid six).1
    rw [h] at n4 m4
    have cases : (x=2 ∧ y=4) ∨ (x=4 ∧ y=2) ∨ (x=3 ∧ y=3) := by omega
    rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have b := six_pair_tax_direction F.G T (k:=0) F.n F.m F.hn F.hm rx byh bg m4 F.row
      rw [←win] at b;change L≤E+M+0 at b;omega
    · have b := six_pair_tax_direction F.G T (k:=0) F.m F.n F.hm F.hn byh rx rf n4 (swap_positive_forcing_row F.G _ _ F.row)
      rw [Nat.add_comm (originalThresholdCount F.m 2),←win] at b;change L≤E+M+0 at b;omega
    · have row := closed_union_sum_row F.G U (component_vertices_closed F.G T) F.row
      by_cases a:N<originalThresholdCount F.n 3
      · have b := mono_red_rectangle O C F.n F.m F.hn F.hm rx byh (selected_component_pack F.G T 3 rx) a bg row
        rw [←win] at b;change L≤E+N at b;omega
      by_cases b:N<originalThresholdCount F.m 3
      · have z := mono_blue_rectangle O C F.n F.m F.hn F.hm rx byh rf (selected_component_pack F.G T 3 byh) b row
        rw [←win] at z;change L≤E+N at z;omega
      change L=originalThresholdCount F.n 3+originalThresholdCount F.m 3-1-F.r at win
      omega
  · omega

#print axioms strict_no_five_actual_fifth_column
end JSP452Audit.StarHost
