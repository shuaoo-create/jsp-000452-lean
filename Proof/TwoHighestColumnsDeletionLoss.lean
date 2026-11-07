import RealExteriorAfterErasingClosedPart
namespace JSP452Audit.StarHost

theorem six_prefix_two_columns {s t r:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (top:diagonal n m (r+2)=7) (k:ℕ) :
    rowEnergy n m r≤rowEnergy n m (r+k)+5*k+widthAt n m r 6+highestWidth n m r := by
  let p := min k (rowCount s t r)
  let A := offsetsAt n m r 6
  let B := offsetsAt n m r 7
  have each (i:ℕ) (hi:i∈Finset.range p) : diagonal n m (r+i+2)≤
      5+(if i∈A then 1 else 0)+(if i∈B then 1 else 0) := by
    have live := (Finset.mem_range.mp hi).trans_le (Nat.min_le_right k (rowCount s t r))
    have dom := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+i by omega)
      (show r+i<s+t-1 by dsimp [rowCount] at live;omega)
    have a : i∈A ↔ 6≤diagonal n m (r+i+2) := by simp [A,offsetsAt,live]
    have b : i∈B ↔ 7≤diagonal n m (r+i+2) := by simp [B,offsetsAt,live]
    simp only [a,b]
    split_ifs <;> omega
  have total := Finset.sum_le_sum each
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,Finset.sum_boole] at total
  have count (j:ℕ) : ((Finset.range p).filter fun i => i∈offsetsAt n m r j).card≤widthAt n m r j :=
    Finset.card_le_card (fun _ h => (Finset.mem_filter.mp h).2)
  have ac := count 6
  change ((Finset.range p).filter fun i => i∈A).card≤widthAt n m r 6 at ac
  have bc := count 7
  change ((Finset.range p).filter fun i => i∈B).card≤widthAt n m r 7 at bc
  rw [←top,width_at_actual_top hs ht n m hn hm] at bc
  have parts := rowEnergy_prefix_split n m r k
  change rowEnergy n m r=(∑i∈Finset.range p,diagonal n m (r+i+2))+_ at parts
  have lim : p≤k := Nat.min_le_left _ _
  omega

#print axioms six_prefix_two_columns
end JSP452Audit.StarHost
