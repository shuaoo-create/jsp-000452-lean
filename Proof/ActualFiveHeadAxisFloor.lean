import CompleteDegreeColumnHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem lower_axis_at_five_head {s t r j:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (heads:0<originalThresholdCount n 5 ∨ 0<originalThresholdCount m 5)
    (hs:0<s) (ht:0<t) (lo:0<j) (hi:j≤5) :
    min s t-r≤widthAt n m r j := by
  rcases heads with red|blue
  · have high := (original_threshold_prefix n hn 5 ⟨0,hs⟩).2 red
    have present := (original_threshold_prefix n hn j ⟨0,hs⟩).mp (hi.trans high)
    have full := original_threshold_one m pm
    have price := actual_rectangle_le_column (r:=r) n m hn hm (a:=j) (b:=1) (h:=j) (by omega)
      (by omega : 0<originalThresholdCount n j) (by omega)
    omega
  · have high := (original_threshold_prefix m hm 5 ⟨0,ht⟩).2 blue
    have present := (original_threshold_prefix m hm j ⟨0,ht⟩).mp (hi.trans high)
    have full := original_threshold_one n pn
    have price := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=j) (h:=j) (by omega)
      (by omega) (by omega : 0<originalThresholdCount m j)
    omega

theorem pack_cap_for_larger_heads {X:Type*} (G:SimpleGraph X) {x y a:ℕ}
    (order:x≤y) (cap:UniformPackCap G x a) : UniformPackCap G y a := by
  intro k copy
  obtain ⟨f⟩ := copy
  let e := subforestCopy (fun _:Fin k => x) (fun _:Fin k => y) (Function.Embedding.refl _) (fun _ => order)
  exact cap k ⟨f.comp e⟩

theorem mixed_low_winner_improves_tax (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (heads:0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5)
    (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6) (card:T.card=1)
    (j x y:ℕ) (low:2≤j) (high:j≤5) (xr:2≤x) (yb:2≤y) (win:WinsHeight F.n F.m F.r j x y) :
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+chosenSlots F.G T 2 := by
  let U := componentVertices F.G T
  let P := matchingEdges (F.G.induce U)
  let d := F.rank-matchingEdges F.G
  let M := chosenSlots F.G T 2
  let L := widthAt F.n F.m F.r j
  have h := (strict_six_only_one_original_component F paid six).1
  have price := (strict_six_chosen_edge_price F paid six T actual).1 (by rw [card,h];decide)
  rw [card,h] at price
  change 5*P+3*1+1≤d+1+4*(P+(1-1)/2)+M at price
  have cap := (strict_chosen_slot_totals F paid six T actual).1
  change 3*M≤2*P+T.card at cap
  rw [card] at cap
  have closed := component_vertices_closed F.G T
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk v) hv).2 v rfl).trans six.symm
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+d+1≤min F.s F.t at lens
  have floor := lower_axis_at_five_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht (by omega : 0<j) high
  change min F.s F.t-F.r≤L at floor
  obtain ⟨xp,yp,height,red,blue,cost⟩ := win
  change L=originalThresholdCount F.n x+originalThresholdCount F.m y-1-F.r at cost
  have row := closed_union_sum_row F.G U closed F.row
  have large : M<originalThresholdCount F.n x ∨ M<originalThresholdCount F.m y := by omega
  rcases large with a|b
  · have bound := mono_red_rectangle _ _ F.n F.m F.hn F.hm xp yp
      (pack_cap_for_larger_heads _ xr (selected_component_pack F.G T 2 (by decide))) a blue row
    rwa [←cost,height] at bound
  · have bound := mono_blue_rectangle _ _ F.n F.m F.hn F.hm xp yp red
      (pack_cap_for_larger_heads _ yb (selected_component_pack F.G T 2 (by decide))) b row
    rwa [←cost,height] at bound

#print axioms lower_axis_at_five_head
#print axioms pack_cap_for_larger_heads
#print axioms mixed_low_winner_improves_tax
end JSP452Audit.StarHost
