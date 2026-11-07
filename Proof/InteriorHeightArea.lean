import StrictJointAreaDeficit
namespace JSP452Audit.StarHost

/-- Heights 2 through D inclusive. -/
def interiorArea {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r D : ℕ) : ℕ :=
  ∑q∈Finset.range (D-1),widthAt n m r (q+2)

private theorem through_degree_split {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ)
    (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (r D : ℕ) (pos : 0<D) :
    (∑q∈Finset.range D,widthAt n m r (q+1))=rowCount s t r+interiorArea n m r D := by
  cases D with
  | zero => omega
  | succ D =>
    rw [Finset.sum_range_succ']
    have first : widthAt n m r 1=rowCount s t r := first_layer_complete hs ht n m pn pm r
    simp only [Nat.zero_add,first,interiorArea,Nat.succ_sub_one,Nat.add_assoc,Nat.reduceAdd]
    omega

theorem original_area_by_height {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ)
    (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (top : diagonal n m (r+2)=D+1) (pos : 0<D) :
    rowEnergy n m r=rowCount s t r+interiorArea n m r D+highestWidth n m r := by
  have caps (z:ℕ) (hz:z<rowCount s t r) : diagonal n m (r+z+2)≤D+1 := by
    rw [←top];exact earlier_diagonal_dominates hs ht n m hn hm (by omega) (by dsimp [rowCount] at hz;omega)
  have sum := finite_layer_count (fun z => diagonal n m (r+z+2)) (rowCount s t r) (D+1) caps
  change rowEnergy n m r=∑q∈Finset.range (D+1),widthAt n m r (q+1) at sum
  rw [sum,Finset.sum_range_succ,through_degree_split hs ht n m pn pm r D pos,←top,width_at_actual_top hs ht n m hn hm]

theorem interior_area_lower {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ)
    (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (pos : 0<D) :
    rowCount s t r+interiorArea n m r D≤rowEnergy n m r := by
  classical
  have point (z:ℕ) : (∑q∈Finset.range D,if q+1≤diagonal n m (r+z+2) then 1 else 0)≤diagonal n m (r+z+2) := by
    rw [Finset.sum_boole]
    have sub : (Finset.range D).filter (fun q => q+1≤diagonal n m (r+z+2))⊆Finset.range (diagonal n m (r+z+2)) :=
      fun q h => Finset.mem_range.mpr (Finset.mem_filter.mp h).2
    simpa using Finset.card_le_card sub
  have total := Finset.sum_le_sum (s:=Finset.range (rowCount s t r)) (fun z _ => point z)
  rw [Finset.sum_comm] at total
  simp only [Finset.sum_boole] at total
  rw [←through_degree_split hs ht n m pn pm r D pos]
  exact total

#print axioms original_area_by_height
#print axioms interior_area_lower
end JSP452Audit.StarHost
