import RowDelete

namespace JSP452Audit.StarHost

/-- Embed the finite demand functions of the frozen statement into the natural
    indexing used by row descent. Only input values enter any positive suffix. -/
def padDemand {s : ℕ} (n : Fin s → ℕ) (k : ℕ) : ℕ :=
  if h : k<s then n ⟨k,h⟩ else 0

theorem pad_antitone {s : ℕ} (n : Fin s → ℕ) (sorted : Antitone n) :
    Antitone (padDemand n) := by
  intro x y hxy
  by_cases hy : y<s
  · have hx : x<s := lt_of_le_of_lt hxy hy
    simp only [padDemand,dif_pos hx,dif_pos hy]
    exact sorted (show (⟨x,hx⟩ : Fin s) ≤ ⟨y,hy⟩ from hxy)
  · simp [padDemand,hy]

theorem pad_positive {s : ℕ} (n : Fin s → ℕ) (positive : ∀ i, 1 ≤ n i) :
    ∀ k, k<s → 0 < padDemand n k := by
  intro k hk
  rw [padDemand,dif_pos hk]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (positive ⟨k,hk⟩)

private theorem pad_origin {s : ℕ} (n : Fin s → ℕ) :
    (fun i : Fin s => padDemand n (0+i.val)) = n := by
  funext i
  simp [padDemand,i.isLt]

/-- The base-row formulation uses exactly the original finite graph targets. -/
theorem finite_targets_row_zero {X : Type*} (G : SimpleGraph X) {s t : ℕ}
    (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ) :
    ForcingRow G s t (padDemand n) (padDemand m) 0 ↔ Forces G (forest n) (forest m) := by
  rw [row_zero_iff G hs ht]
  unfold suffixStars
  rw [pad_origin, pad_origin]

#print axioms finite_targets_row_zero

end JSP452Audit.StarHost
