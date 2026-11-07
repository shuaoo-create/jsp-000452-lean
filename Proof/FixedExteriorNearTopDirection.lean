import ActualEvenRegularUnionStage
namespace JSP452Audit.StarHost
open SimpleGraph

theorem near_top_even_direction {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    {s t r D a b:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (evenA:Even a) (oddB:Odd b) (ha:0<a) (hb:0<b) (height:a+b-1=D)
    (red:0<originalThresholdCount n a) (blue:0<originalThresholdCount m b)
    (positiveWidth:0<widthAt n m r (D+1)) (peak:∃i j,n i+m j=D+2) (cap:∀x,Nat.card (G.neighborSet x)≤D)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    let O := G.induce (componentVertices G T)ᶜ
    let h := widthAt n m r (D+1)
    originalThresholdCount n a+originalThresholdCount m b-1-r≤
      uniformEnvelope O D+max (chosenSlots G T a) (chosenSlots G T b+(h-1)) := by
  intro O h
  by_cases bigger:0<originalThresholdCount n (a+1)
  · obtain ⟨x,ax⟩ := evenA
    obtain ⟨y,by'⟩ := oddB
    obtain ⟨R,sub,split⟩ := even_even_degree_split G x y (fun z => (cap z).trans_eq (by omega))
    have noR := uniform_pack_below_degree R (a+1) (fun v => (split v).1.trans_lt (by omega))
    have noB := uniform_pack_below_degree (G \ R) b (fun v => (split v).2.trans_lt (by omega))
    have bound := absent_rectangle_of_split G R sub n m hn hm bigger blue noR noB row
    have fee := six_pair_tax_direction G T (k:=0) n m hn hm ha hb blue (by omega) row
    rw [height] at fee;change _≤uniformEnvelope O D+chosenSlots G T a+0 at fee;omega
  · obtain ⟨i,j,sum⟩ := peak
    have stop : n i≤a := by
      by_contra! large;have le := (original_threshold_prefix n hn (a+1) i).mp large;omega
    have more := (original_threshold_prefix m hm (b+1) j).mp (show b+1≤m j by omega)
    have guard := actual_rectangle_le_column (r:=r) n m hn hm (a:=a) (b:=b+1) (h:=D+1)
      (by omega) red (by omega : 0<originalThresholdCount m (b+1))
    have hp : 0<h := positiveWidth
    change _≤h at guard
    have fee := six_pair_tax_direction G T (k:=h-1) m n hm hn hb ha red (by omega) (swap_positive_forcing_row G _ _ row)
    rw [Nat.add_comm (originalThresholdCount m b),Nat.add_comm b a,height] at fee
    change _≤uniformEnvelope O D+chosenSlots G T b+(h-1) at fee;omega

#print axioms near_top_even_direction
end JSP452Audit.StarHost
