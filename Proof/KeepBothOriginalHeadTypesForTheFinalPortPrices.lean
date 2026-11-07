import TheActualTenDegreePortSuccessorStopsAtDegreeEight
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)
theorem retained_type_or_two_small_heads {s t r j a b z:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (za:z≤a) (zb:z≤b) (win:WinsHeight n m r j a b) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    (∃k:ℕ,k≤W.slotDamage z ∧ ExactTypedWidth W.outside a b (widthAt n m r j-k)) ∨
      (originalThresholdCount n a≤W.slotDamage a ∧ originalThresholdCount m b≤W.slotDamage b) := by
  obtain ⟨ap,bp,_,red,blue,width⟩ := win
  by_cases x:W.starTax a<originalThresholdCount n a
  · have real := W.real_typed_rectangle n m hn hm ap bp x blue row
    rw [←width] at real
    exact Or.inl ⟨_,(Nat.min_le_right _ _).trans (W.port_slot_decreases za),real⟩
  by_cases y:W.starTax b<originalThresholdCount m b
  · have real := W.real_typed_rectangle m n hm hn bp ap y red (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m b),←width] at real
    exact Or.inl ⟨_,(Nat.min_le_right _ _).trans (W.port_slot_decreases zb),exact_typed_width_swap _ real⟩
  exact Or.inr ⟨(Nat.le_of_not_gt x).trans (Nat.min_le_right _ _),(Nat.le_of_not_gt y).trans (Nat.min_le_right _ _)⟩

#print axioms retained_type_or_two_small_heads
end JSP452Audit.StarHost.TenPortSupport
