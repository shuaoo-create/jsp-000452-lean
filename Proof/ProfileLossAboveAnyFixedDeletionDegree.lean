import TheZeroOddComponentSourceMustHaveScoreOne
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem prefix_price_through_all_higher_columns {s t r:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (a b k:ℕ) (top:diagonal n m (r+2)≤a+b) :
    rowEnergy n m r≤rowEnergy n m (r+k)+a*k+∑j∈Finset.range b,widthAt n m r (a+j+1) := by
  classical
  let p := min k (rowCount s t r)
  let fee (i j:ℕ) : ℕ := if i∈offsetsAt n m r (a+j+1) then 1 else 0
  have per (i:ℕ) (hi:i∈Finset.range p) : diagonal n m (r+i+2)≤a+∑j∈Finset.range b,fee i j := by
    let v := diagonal n m (r+i+2)
    have live := (Finset.mem_range.mp hi).trans_le (Nat.min_le_right k (rowCount s t r))
    have dom := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+i by omega)
      (show r+i<s+t-1 by dsimp [rowCount] at live;omega)
    change v≤diagonal n m (r+2) at dom
    have covered : (∑j∈Finset.range (v-a),fee i j)=v-a := by
      calc
        _ = ∑_j∈Finset.range (v-a),(1:ℕ) := by
          apply Finset.sum_congr rfl
          intro j mem
          have below := Finset.mem_range.mp mem
          have threshold : a+j+1≤diagonal n m (r+i+2) := by change _≤v;omega
          exact if_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,threshold⟩)
        _ = _ := by simp
    have bound := Finset.sum_le_sum_of_subset_of_nonneg (f:=fee i)
      (Finset.range_mono (by omega : v-a≤b)) (fun _ _ _ => Nat.zero_le _)
    change v≤_;omega
  have sum := Finset.sum_le_sum (s:=Finset.range p) per
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,Finset.sum_comm] at sum
  have col (j) : (∑i∈Finset.range p,fee i j)≤widthAt n m r (a+j+1) := by
    simp only [fee,Finset.sum_boole]
    exact Finset.card_le_card (fun i h => (Finset.mem_filter.mp h).2)
  have columns := Finset.sum_le_sum (s:=Finset.range b) (fun j _ => col j)
  have parts := rowEnergy_prefix_split n m r k
  change rowEnergy n m r=(∑i∈Finset.range p,diagonal n m (r+i+2))+_ at parts
  have scale := Nat.mul_le_mul_right a (show p≤k from Nat.min_le_left _ _)
  rw [Nat.mul_comm a k];omega

#print axioms prefix_price_through_all_higher_columns
end JSP452Audit.StarHost
