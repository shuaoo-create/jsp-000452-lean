import PrefixColumnTax

namespace JSP452Audit.StarHost

/-- p two-leaf stars followed by a one-leaf stars. -/
def binaryProfile (p a : ℕ) (i : Fin (p+a)) : ℕ := if i.val < p then 2 else 1

theorem binaryProfile_positive (p a : ℕ) (i : Fin (p+a)) : 1 ≤ binaryProfile p a i := by
  dsimp [binaryProfile]; split <;> decide

theorem binaryProfile_antitone (p a : ℕ) : Antitone (binaryProfile p a) := by
  intro i j ij
  change i.val ≤ j.val at ij
  dsimp [binaryProfile]; split_ifs <;> omega

private theorem rectangle_witness {u v k : ℕ} (pu : 0<u) (pv : 0<v) (live : k<u+v-1) :
    ∃ i j : ℕ, i<u ∧ j<v ∧ i+j=k := by
  exact ⟨min k (u-1),k-min k (u-1),by omega,by omega,by omega⟩

/-- Exact costs of the three consecutive blocks of live original
antidiagonals, with k starting at zero. -/
theorem binary_diagonal {p q : ℕ} (hp : 0<p) (hq : 0<q) (a b k : ℕ)
    (live : k < (p+a)+(q+b)-1) :
    diagonal (binaryProfile p a) (binaryProfile q b) (k+2) =
      if k < p+q-1 then 3 else if k < p+q-1+max a b then 2 else 1 := by
  let n := binaryProfile p a
  let m := binaryProfile q b
  obtain ⟨x,y,xy,attains⟩ := diagonal_attained n m (by omega) (by omega) k live
  have boundx := x.isLt
  have boundy := y.isLt
  have member (i j : ℕ) (hi : i<p+a) (hj : j<q+b) (ij : i+j=k) :
      (if i < p then 2 else 1) + (if j < q then 2 else 1) - 1 ≤ diagonal n m (k+2) := by
    have cost := antiDiag_member n m (⟨i,hi⟩ : Fin (p+a)) (⟨j,hj⟩ : Fin (q+b))
    rw [← ij]
    exact cost
  change diagonal n m (k+2) = _
  apply le_antisymm
  · rw [attains]
    dsimp only [n,m,binaryProfile]
    split_ifs <;> omega
  · split_ifs with first second
    · obtain ⟨i,j,hi,hj,ij⟩ := rectangle_witness hp hq first
      have witness := member i j (by omega) (by omega) ij
      simpa [hi,hj] using witness
    · by_cases tail : a ≤ b
      · obtain ⟨i,j,hi,hj,ij⟩ := rectangle_witness (k:=k) (u:=p) (v:=q+b) hp (by omega) (by omega)
        have witness := member i j (by omega) hj ij
        split_ifs at witness <;> omega
      · obtain ⟨i,j,hi,hj,ij⟩ := rectangle_witness (k:=k) (u:=p+a) (v:=q) (by omega) hq (by omega)
        have witness := member i j hi (by omega) ij
        split_ifs at witness <;> omega
    · rw [attains]
      have := binaryProfile_positive p a x
      have := binaryProfile_positive q b y
      change 1 ≤ binaryProfile p a x + binaryProfile q b y - 1
      omega

/-- Exact area after removing r initial columns, as long as r is still in
the three-cost block. Both unit tails and either zero tail are allowed. -/
theorem binary_row_energy {p q : ℕ} (hp : 0<p) (hq : 0<q) (a b r : ℕ) (live : r<p+q-1) :
    rowEnergy (binaryProfile p a) (binaryProfile q b) r =
      3*(p+q-1-r) + 2*max a b + min a b := by
  let three := p+q-1-r
  let two := max a b
  let one := min a b
  let cost (i : ℕ) := diagonal (binaryProfile p a) (binaryProfile q b) (r+i+2)
  have count : rowCount (p+a) (q+b) r = (three+two)+one := by
    dsimp [rowCount,three,two,one]; omega
  have first (i : ℕ) (hi : i ∈ Finset.range three) : cost i = 3 := by
    have h := Finset.mem_range.mp hi
    dsimp [three] at h
    dsimp [cost]
    rw [binary_diagonal hp hq _ _ _ (by omega),if_pos (by omega)]
  have second (i : ℕ) (hi : i ∈ Finset.range two) : cost (three+i) = 2 := by
    have h := Finset.mem_range.mp hi
    dsimp [two] at h
    dsimp [cost,three]
    rw [binary_diagonal hp hq _ _ _ (by omega),if_neg (by omega),if_pos (by omega)]
  have third (i : ℕ) (hi : i ∈ Finset.range one) : cost (three+two+i) = 1 := by
    have h := Finset.mem_range.mp hi
    dsimp [one] at h
    dsimp [cost,three,two]
    rw [binary_diagonal hp hq _ _ _ (by omega),if_neg (by omega),if_neg (by omega)]
  change (∑ i ∈ Finset.range (rowCount (p+a) (q+b) r), cost i) = 3*three+2*two+one
  rw [count,Finset.sum_range_add,Finset.sum_range_add,Finset.sum_const_nat first,
    Finset.sum_const_nat second,Finset.sum_const_nat third]
  simp [Nat.mul_comm]

/-- Original antidiagonal area at the root row. -/
theorem binary_original_area {p q : ℕ} (hp : 0<p) (hq : 0<q) (a b : ℕ) :
    (∑ k ∈ Finset.Icc 2 ((p+a)+(q+b)), diagonal (binaryProfile p a) (binaryProfile q b) k) =
      3*(p+q-1)+2*max a b+min a b := by
  rw [← rowEnergy_zero]
  simpa using binary_row_energy hp hq a b 0 (by omega)

#print axioms binary_diagonal
#print axioms binary_row_energy
#print axioms binary_original_area
end JSP452Audit.StarHost
