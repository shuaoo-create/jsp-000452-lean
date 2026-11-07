import SixDegreeFourAndFiveThresholds
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_pair_tax_direction {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    {s t r x y k:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (blue:0<originalThresholdCount m y) (lim:originalThresholdCount m y≤r+k+1)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤
      uniformEnvelope (G.induce (componentVertices G T)ᶜ) (x+y-1)+chosenSlots G T x+k := by
  let M := chosenSlots G T x
  by_cases live : M<originalThresholdCount n x
  · have outside := closed_union_sum_row G _ (component_vertices_closed G T) row
    have price := mono_red_rectangle _ _ n m hn hm rx byh (selected_component_pack G T x rx) live blue outside
    omega
  · change _≤uniformEnvelope _ _+M+k;omega

theorem strict_sixth_column_by_slots (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    let h := highestWidth F.n F.m F.r
    let M2 := chosenSlots F.G T 2
    let M3 := chosenSlots F.G T 3
    widthAt F.n F.m F.r 6≤uniformEnvelope O 6+max M2 (M3+(h-1)) ∧
      ((∀i,F.n i≤4) → (∀j,F.m j≤4) → widthAt F.n F.m F.r 6≤uniformEnvelope O 6+M3+(h-1)) := by
  intro O h M2 M3
  let E := uniformEnvelope O 6
  let L := widthAt F.n F.m F.r 6
  change L≤E+max M2 (M3+(h-1)) ∧ ((∀i,F.n i≤4) → (∀j,F.m j≤4) → L≤E+M3+(h-1))
  by_cases live : 0<L
  · obtain ⟨x,y,xp,yp,height,rx,byh,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (show 0<6 by decide) live
    have caps := strict_only_double_escape F paid
    have nhead := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 rx
    have mhead := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 byh
    have nx := caps.1 ⟨0,F.hs⟩
    have my := caps.2.1 ⟨0,F.ht⟩
    rw [six] at nx my
    obtain ⟨red4,blue4,red5,blue5⟩ := six_degree_head_count_guards F paid six
    change originalThresholdCount F.n 4≤F.r+h at red4
    change originalThresholdCount F.m 4≤F.r+h at blue4
    have positive : 1≤h := (strict_six_real_component_bounds F paid six).1
    have cases : (x=2 ∧ y=5) ∨ (x=5 ∧ y=2) ∨ (x=3 ∧ y=4) ∨ (x=4 ∧ y=3) := by omega
    rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have paid := six_pair_tax_direction F.G T (k:=0) F.n F.m F.hn F.hm (by decide : 0<2) (by decide : 0<5)
        byh (by omega) F.row
      rw [←win] at paid
      change L≤E+M2+0 at paid
      refine ⟨by omega,?_⟩
      intro _ low;have := low ⟨0,F.ht⟩;omega
    · have paid := six_pair_tax_direction F.G T (k:=0) F.m F.n F.hm F.hn (by decide : 0<2) (by decide : 0<5)
        rx (by omega) (swap_positive_forcing_row F.G _ _ F.row)
      rw [Nat.add_comm (originalThresholdCount F.m 2),←win] at paid
      change L≤E+M2+0 at paid
      refine ⟨by omega,?_⟩
      intro low _;have := low ⟨0,F.hs⟩;omega
    · have paid := six_pair_tax_direction F.G T (k:=h-1) F.n F.m F.hn F.hm (by decide : 0<3) (by decide : 0<4)
        byh (by omega) F.row
      rw [←win] at paid
      change L≤E+M3+(h-1) at paid
      exact ⟨by omega,fun _ _ => paid⟩
    · have paid := six_pair_tax_direction F.G T (k:=h-1) F.m F.n F.hm F.hn (by decide : 0<3) (by decide : 0<4)
        rx (by omega) (swap_positive_forcing_row F.G _ _ F.row)
      rw [Nat.add_comm (originalThresholdCount F.m 3),←win] at paid
      change L≤E+M3+(h-1) at paid
      exact ⟨by omega,fun _ _ => paid⟩
  · exact ⟨by omega,fun _ _ => by omega⟩

#print axioms six_pair_tax_direction
#print axioms strict_sixth_column_by_slots
end JSP452Audit.StarHost
