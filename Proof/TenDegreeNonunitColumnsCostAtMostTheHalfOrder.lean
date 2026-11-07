import TwoColourRestorationWhenBothTenDegreeHeadsDisappear
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The two opposite cover choices cannot both be expensive for a nonunit
winner. At height three both heads can equal two, allowing one extra unit. -/
theorem ten_nonunit_port_column {X : Type u} [Finite X] {G : SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (R : TenPortSupport G K q) (positive:1≤q)
    {s t r a b j : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (wa : 2≤a) (wb : 2≤b) (win : WinsHeight n m r j a b)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    widthAt n m r j≤uniformEnvelope (G \ R.piece) j+R.half := by
  let P := R.half
  let e := R.portCount
  let L := widthAt n m r j
  let X0 := uniformEnvelope (G \ R.piece) j
  let A := originalThresholdCount n a
  let B := originalThresholdCount m b
  change L≤X0+P
  obtain ⟨pa,pb,hgt,red,blue,width⟩ := win
  have sizes := R.size_and_fee positive
  have order : R.support.ncard=2*P+R.parity := sizes.2.2.2.1
  have eps := sizes.2.2.1
  have count : e≤2 := sizes.2.1
  have slot : R.slotDamage 2+1≤P := (R.port_slot_sizes positive).2.2.2
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
  change B+A-1-r≤X0+max (e+A-1) (R.support.ncard-a*A) at feeA
  change A+B-1-r≤X0+max (e+B-1) (R.support.ncard-b*B) at feeB
  have first := Nat.mul_le_mul_right A wa
  have second := Nat.mul_le_mul_right B wb
  omega

#print axioms ten_nonunit_port_column
end JSP452Audit.StarHost
