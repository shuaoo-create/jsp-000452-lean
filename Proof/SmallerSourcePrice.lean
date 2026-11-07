import SmallerRankBaseline
import PrefixColumnTax
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Use only the rows actually reaching D+1, even when the allowed cap D
lies above the original highest column. -/
theorem prefix_at_degree_cap {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (r k D : ℕ) (height : diagonal n m (r+2)≤D+1) :
    rowEnergy n m r ≤ rowEnergy n m (r+k) + D*k + widthAt n m r (D+1) := by
  let p := min k (rowCount s t r)
  let high := offsetsAt n m r (D+1)
  have each (i : ℕ) (hi : i∈Finset.range p) :
      diagonal n m (r+i+2) ≤ D+(if i∈high then 1 else 0) := by
    have live : i<rowCount s t r := (Finset.mem_range.mp hi).trans_le (Nat.min_le_right _ _)
    have dom := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+i by omega)
      (show r+i<s+t-1 by dsimp [rowCount] at live; omega)
    by_cases peak : D+1≤diagonal n m (r+i+2)
    · have mem : i∈high := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,peak⟩
      rw [if_pos mem]; omega
    · split <;> omega
  have total := Finset.sum_le_sum each
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_range,smul_eq_mul,
    Nat.cast_id] at total
  have count : ((Finset.range p).filter fun i => i∈high).card ≤ widthAt n m r (D+1) :=
    Finset.card_le_card (fun _ hi => (Finset.mem_filter.mp hi).2)
  have mul := Nat.mul_le_mul_right D (Nat.min_le_left k (rowCount s t r))
  have parts := rowEnergy_prefix_split n m r k
  change (∑ i∈Finset.range p,diagonal n m (r+i+2)) ≤ p*D+_ at total
  change rowEnergy n m r = (∑ i∈Finset.range p,diagonal n m (r+i+2)) + _ at parts
  change p*D≤k*D at mul
  rw [Nat.mul_comm D k]
  omega

/-- Turn a physical saving on one genuine successor into a price at the
original rank. The successor may be empty, so the terminal case is included. -/
theorem smaller_source_price {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X Z : Type u} [Finite X] [Finite Z] (G : SimpleGraph X) (Y : SimpleGraph Z)
    (r k D N : ℕ) (paid : AllSmallerPaid.{u} N) (live : 0<rowCount s t r)
    (upper : rowCount s t r≤N) (progress : 0<k) (height : diagonal n m (r+2)≤D+1)
    (row : ForcingRow Y s t (padDemand n) (padDemand m) (r+k)) (w : ℤ)
    (saving : (G.edgeSet.ncard:ℤ) = (Y.edgeSet.ncard:ℤ)+(D:ℤ)*k+w) :
    (rowEnergy n m r:ℤ)+w ≤ (G.edgeSet.ncard:ℤ)+(widthAt n m r (D+1):ℤ) := by
  have smaller : rowCount s t (r+k)<N := by dsimp [rowCount] at live upper ⊢; omega
  have base := paid hs ht n m hn hm pn pm Y (r+k) row smaller
  have tax := prefix_at_degree_cap hs ht n m hn hm r k D height
  have baseZ : (rowEnergy n m (r+k):ℤ)≤(Y.edgeSet.ncard:ℤ) := by exact_mod_cast base
  have taxZ : (rowEnergy n m r:ℤ)≤(rowEnergy n m (r+k):ℤ)+(D:ℤ)*k+(widthAt n m r (D+1):ℤ) :=
    by exact_mod_cast tax
  omega
#print axioms prefix_at_degree_cap
#print axioms smaller_source_price
end JSP452Audit.StarHost