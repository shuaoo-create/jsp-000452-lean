import ExplicitOneAndTwoEightMenuGaps
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def EightSelectionSize (j h:ℕ) : Prop := (j=1 ∧ h=1) ∨ (j=2 ∧ h≤4) ∨ (j=3 ∧ h=5)

theorem lower_axis_at_any_head {s t r j H:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (heads:0<originalThresholdCount n H ∨ 0<originalThresholdCount m H)
    (hs:0<s) (ht:0<t) (lo:0<j) (hi:j≤H) :
    min s t-r≤widthAt n m r j := by
  rcases heads with red|blue
  · have high := (original_threshold_prefix n hn H ⟨0,hs⟩).2 red
    have present := (original_threshold_prefix n hn j ⟨0,hs⟩).mp (hi.trans high)
    have full := original_threshold_one m pm
    have price := actual_rectangle_le_column (r:=r) n m hn hm (a:=j) (b:=1) (h:=j) (by omega)
      (by omega : 0<originalThresholdCount n j) (by omega)
    omega
  · have high := (original_threshold_prefix m hm H ⟨0,ht⟩).2 blue
    have present := (original_threshold_prefix m hm j ⟨0,ht⟩).mp (hi.trans high)
    have full := original_threshold_one n pn
    have price := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=j) (h:=j) (by omega)
      (by omega) (by omega : 0<originalThresholdCount m j)
    omega

theorem regular_half_order_slot_counts {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (T:Finset G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents G D) :
    let P := ∑c∈T,Nat.card c.supp/2
    3*chosenSlots G T 2≤2*P+T.card ∧ 2*chosenSlots G T 3≤P := by
  intro P
  have order (c) (hc:c∈T) : Nat.card c.supp=2*(Nat.card c.supp/2)+1 := by
    obtain ⟨k,eq⟩ := (actual c hc).1;omega
  have a := Finset.sum_le_sum (s:=T) (fun c hc => show 3*(Nat.card c.supp/3)≤2*(Nat.card c.supp/2)+1 by have := order c hc;omega)
  have b := Finset.sum_le_sum (s:=T) (fun c hc => show 2*(Nat.card c.supp/4)≤Nat.card c.supp/2 by omega)
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const] at a
  rw [←Finset.mul_sum] at b
  simp only [nsmul_eq_mul,Nat.cast_id,mul_one] at a
  exact ⟨a,b⟩

theorem eight_low_column_price_for_three (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (j:ℕ) (pos:0<j) :
    let P := ∑c∈T,Nat.card c.supp/2
    let e := (T.card-1)/2
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+(P+e) := by
  intro P e
  let U := componentVertices F.G T
  have close := component_vertices_closed F.G T
  have full (x) (hx:x∈U) := ((actual (F.G.connectedComponentMk x) hx).2 x rfl).trans eight.symm
  have len := (strict_closed_union_lengths F paid U close full).1
  obtain ⟨order,_,rank,_⟩ := regular_union_at_even_degree F.G 4 T actual
  change U.ncard=2*P+T.card at order
  change matchingEdges (F.G.induce U)≤P at rank
  apply closed_union_column_tax F.G U close F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm pos (by omega) _ (by omega) F.row
  change U.ncard≤2*(P+(T.card-1)/2)+2;omega

#print axioms lower_axis_at_any_head
#print axioms regular_half_order_slot_counts
#print axioms eight_low_column_price_for_three
end JSP452Audit.StarHost
