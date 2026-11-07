import ChooseTheActualCoverForAColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The two opposite cover choices cannot both be expensive for a nonunit
winner. At height three both heads can equal two, allowing one extra unit. -/
theorem nine_nonunit_port_column {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)
    {s t r a b j : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (wa : 2≤a) (wb : 2≤b) (win : WinsHeight n m r j a b)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    widthAt n m r j≤uniformEnvelope R.erased j+R.totalCapacity+(if j=3 then 1 else 0) := by
  let P := R.totalCapacity
  let e := R.portCount
  let L := widthAt n m r j
  let X0 := uniformEnvelope R.erased j
  let A := originalThresholdCount n a
  let B := originalThresholdCount m b
  let extra := if j=3 then 1 else 0
  change L≤X0+P+extra
  obtain ⟨pa,pb,hgt,red,blue,width⟩ := win
  have enough : 10≤P := by
    have c0 := (R.inner 0).2;have c1 := (R.inner 1).2
    change 5≤R.capacity 0 at c0;change 5≤R.capacity 1 at c1
    change 10≤R.capacity 0+R.capacity 1;omega
  have count : e≤2 := by have := R.physical_tip_and_root_counts.2.2;change R.looseRoots.ncard+e≤2 at this;omega
  have slot := R.port_slot_sizes.1
  change 3*R.slotDamage 2≤2*P+4+e at slot
  have taxA : R.starTax a≤R.slotDamage 2 := (Nat.min_le_right _ _).trans (R.port_slot_decreases wa)
  have taxB : R.starTax b≤R.slotDamage 2 := (Nat.min_le_right _ _).trans (R.port_slot_decreases wb)
  by_contra! fail
  have abs := R.original_port_winner_alternatives n m hn hm ⟨pa,pb,hgt,red,blue,width⟩ row
  change (L≤X0+R.starTax a) ∨ (L≤X0+R.starTax b) ∨ (A≤R.starTax a ∧ B≤R.starTax b) at abs
  obtain ⟨da,db⟩ := (abs.resolve_left (by omega)).resolve_left (by omega)
  have feeA := R.cover_original_rectangle m n hm hn pb pa red (swap_positive_forcing_row _ _ _ row)
  have feeB := R.cover_original_rectangle n m hn hm pa pb blue row
  change L=A+B-1-r at width
  rw [show b+a-1=j by omega] at feeA
  rw [hgt] at feeB
  change B+A-1-r≤X0+max (e+A-1) (2*P+4-e-a*A) at feeA
  change A+B-1-r≤X0+max (e+B-1) (2*P+4-e-b*B) at feeB
  have coveredA : a*A+P+e+extra≤2*P+3 := by omega
  have coveredB : b*B+P+e+extra≤2*P+3 := by omega
  have twoA := Nat.mul_le_mul_right A wa
  have twoB := Nat.mul_le_mul_right B wb
  by_cases low : j=3
  · have one : extra=1 := if_pos low
    omega
  · have zero : extra=0 := if_neg low
    rcases (show 3≤a ∨ 3≤b by omega) with hi|hi
    · have bound := Nat.mul_le_mul_right A hi
      omega
    · have bound := Nat.mul_le_mul_right B hi
      omega

#print axioms nine_nonunit_port_column
end JSP452Audit.StarHost
