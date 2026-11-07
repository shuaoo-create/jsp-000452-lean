import RowEnergy
namespace JSP452Audit.StarHost
/-- Count the boxes in the same finite diagram by height. No monotonicity of
the column heights is needed for this identity. -/
theorem finite_layer_count (f : ℕ → ℕ) (N H : ℕ) (cap : ∀ k < N, f k ≤ H) :
    (∑ k ∈ Finset.range N, f k) =
      ∑ h ∈ Finset.range H, ((Finset.range N).filter (fun k => h+1 ≤ f k)).card := by
  classical
  have one (k : ℕ) (hk : k < N) : f k =
      ∑ h ∈ Finset.range H, (if h+1 ≤ f k then 1 else 0) := by
    rw [Finset.sum_boole]
    have eq : ((Finset.range H).filter (fun h => h+1 ≤ f k)) = Finset.range (f k) := by
      ext h
      simp only [Finset.mem_filter,Finset.mem_range]
      have := cap k hk
      omega
    rw [eq,Finset.card_range]
    simp
  calc
    _ = ∑ k ∈ Finset.range N, ∑ h ∈ Finset.range H, (if h+1 ≤ f k then 1 else 0) :=
      Finset.sum_congr rfl (fun k hk => one k (Finset.mem_range.mp hk))
    _ = _ := by rw [Finset.sum_comm]; simp [Finset.sum_boole]

/-- Height one counts every live original row, even when all the heads vary. -/
theorem first_layer_complete {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) (r : ℕ) :
    ((Finset.range (rowCount s t r)).filter (fun k => 1 ≤ diagonal n m (r+k+2))).card =
      rowCount s t r := by
  have eq : (Finset.range (rowCount s t r)).filter (fun k => 1 ≤ diagonal n m (r+k+2)) =
      Finset.range (rowCount s t r) := by
    apply Finset.filter_true_of_mem
    intro k hk
    have valid := Finset.mem_range.mp hk
    obtain ⟨i,j,_,att⟩ := diagonal_attained n m hs ht (r+k) (by dsimp [rowCount] at valid; omega)
    have hi := pn i
    have hj := pm j
    omega
  rw [eq,Finset.card_range]

#print axioms finite_layer_count
#print axioms first_layer_complete
end JSP452Audit.StarHost