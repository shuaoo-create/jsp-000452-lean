import ErasedSuccessorLengths
namespace JSP452Audit.StarHost

/-- Fill the first t−1 columns with the red head, then take each original
red entry once in order. k counts skipped entries from zero. -/
def unitAxisValue {s : ℕ} (n : Fin s→ℕ) (t D k : ℕ) : ℕ :=
  if k<t-1 then D else padDemand n (k-(t-1))

theorem unit_axis_row_sum {s t r : ℕ} (n : Fin s→ℕ) (D : ℕ) (live : r<t) :
    (∑j∈Finset.range (rowCount s t r),unitAxisValue n t D (r+j))=
      (t-1-r)*D+∑i,n i := by
  let L := t-1-r
  have count : rowCount s t r=L+s := by dsimp [rowCount,L];omega
  rw [count,Finset.sum_range_add]
  have early : (∑j∈Finset.range L,unitAxisValue n t D (r+j))=L*D := by
    calc
      _ = ∑ _j∈Finset.range L,D := by
        apply Finset.sum_congr rfl;intro j hj
        have k := Finset.mem_range.mp hj
        simp only [unitAxisValue,if_pos (show r+j<t-1 by dsimp [L] at k;omega)]
      _ = _ := by simp
  rw [early];congr 1
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have small := Finset.mem_range.mp hj
  have past : ¬r+(L+j)<t-1 := by dsimp [L];omega
  have index : r+(L+j)-(t-1)=j := by dsimp [L];omega
  simp [unitAxisValue,past,index,padDemand,small]

/-- Every positive opposite list supports at least the unit-axis area. -/
theorem row_energy_at_least_unit_axis {s t r : ℕ} (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pm : ∀j,1≤m j) (live : r<t) (D : ℕ) (head : n ⟨0,hs⟩=D) :
    (t-1-r)*D+(∑i,n i)≤rowEnergy n m r := by
  rw [←unit_axis_row_sum n D live]
  apply Finset.sum_le_sum
  intro j hj
  have bound := Finset.mem_range.mp hj
  dsimp [rowCount] at bound
  let k := r+j
  change unitAxisValue n t D k≤diagonal n m (k+2)
  by_cases before : k<t-1
  · let b : Fin t := ⟨k,by omega⟩
    have hit := antiDiag_member n m ⟨0,hs⟩ b
    change n ⟨0,hs⟩+m b-1≤diagonal n m (0+k+2) at hit
    rw [head,Nat.zero_add] at hit
    have one := pm b
    simp only [unitAxisValue,if_pos before];omega
  · let a : Fin s := ⟨k-(t-1),by dsimp [k] at *;omega⟩
    let b : Fin t := ⟨t-1,by omega⟩
    have add : a.val+b.val=k := by dsimp [a,b];omega
    have hit := antiDiag_member n m a b
    rw [add] at hit
    have one := pm b
    simp only [unitAxisValue,if_neg before]
    have same : padDemand n (k-(t-1))=n a := dif_pos a.isLt
    rw [same];omega

#print axioms unit_axis_row_sum
#print axioms row_energy_at_least_unit_axis
end JSP452Audit.StarHost
