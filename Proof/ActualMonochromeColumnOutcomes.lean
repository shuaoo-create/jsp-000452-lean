import SecondExposureOnTheSameEightExterior
namespace JSP452Audit.StarHost
open SimpleGraph

theorem actual_mono_width_or_two_small_counts {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    {s t r j a b z:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (za:z≤a) (zb:z≤b)
    (win:WinsHeight n m r j a b) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    let O := G.induce (componentVertices G T)ᶜ
    let L := widthAt n m r j
    (∃k:ℕ,k≤chosenSlots G T z ∧ ExactTypedWidth O a b (L-k)) ∨
      (originalThresholdCount n a≤chosenSlots G T a ∧ originalThresholdCount m b≤chosenSlots G T b) := by
  intro O L
  let U := componentVertices G T
  let Q := G.induce U
  have out := closed_union_sum_row G U (component_vertices_closed G T) row
  obtain ⟨ap,bp,_,red,blue,width⟩ := win
  by_cases big:chosenSlots G T a<originalThresholdCount n a
  · have keep := palette_retains_typed_rectangle O Q Q le_rfl n m hn hm ap bp
      (selected_component_pack G T a ap) (by rw [sdiff_self];exact uniform_pack_bot_cap b bp) big blue out
    refine Or.inl ⟨chosenSlots G T a,chosen_slots_antitone G T za,?_⟩
    simpa only [←width,Nat.sub_zero] using keep
  by_cases bigB:chosenSlots G T b<originalThresholdCount m b
  · have swap := swap_positive_forcing_row (O⊕g Q) _ _ out
    have keep := palette_retains_typed_rectangle O Q Q le_rfl m n hm hn bp ap
      (selected_component_pack G T b bp) (by rw [sdiff_self];exact uniform_pack_bot_cap a ap) bigB red swap
    rw [Nat.add_comm (originalThresholdCount m b),←width,Nat.sub_zero] at keep
    exact Or.inl ⟨chosenSlots G T b,chosen_slots_antitone G T zb,exact_typed_width_swap O keep⟩
  exact Or.inr ⟨Nat.le_of_not_gt big,Nat.le_of_not_gt bigB⟩

theorem near_top_dead_count_price {X:Type*} [Finite X] (G:SimpleGraph X) {s t r D a b:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (evenA:Even a) (oddB:Odd b)
    (height:a+b-1=D) (apos:0<a) (red:0<originalThresholdCount n a) (blue:0<originalThresholdCount m b)
    (peak:∃i j,n i+m j=D+2) (cap:∀x,Nat.card (G.neighborSet x)≤D) (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (M:ℕ) (rsmall:originalThresholdCount n a≤M) (bsmall:originalThresholdCount m b≤M) :
    originalThresholdCount n a+originalThresholdCount m b-1-r≤M+(widthAt n m r (D+1)-1) := by
  by_cases bigger:0<originalThresholdCount n (a+1)
  · obtain ⟨x,ax⟩ := evenA
    obtain ⟨y,by'⟩ := oddB
    obtain ⟨R,sub,split⟩ := even_even_degree_split G x y (fun v => (cap v).trans_eq (by omega))
    have noR := uniform_pack_below_degree R (a+1) (fun v => (split v).1.trans_lt (by omega))
    have noB := uniform_pack_below_degree (G \ R) b (fun v => (split v).2.trans_lt (by omega))
    have bound := absent_rectangle_of_split G R sub n m hn hm bigger blue noR noB row
    omega
  · obtain ⟨i,j,sum⟩ := peak
    have stop : n i≤a := by
      by_contra! large;have le := (original_threshold_prefix n hn (a+1) i).mp large;omega
    have more := (original_threshold_prefix m hm (b+1) j).mp (show b+1≤m j by omega)
    have fee := actual_rectangle_le_column (r:=r) n m hn hm (a:=a) (b:=b+1) (h:=D+1)
      (by omega) red (by omega : 0<originalThresholdCount m (b+1))
    omega

#print axioms actual_mono_width_or_two_small_counts
#print axioms near_top_dead_count_price
end JSP452Audit.StarHost
