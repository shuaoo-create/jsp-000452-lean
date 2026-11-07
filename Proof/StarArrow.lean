import UpperPath
import HostAntidiagonal

namespace JSP452Audit.StarHost
variable {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)

/-- Every red-blue edge coloring of the explicitly constructed star host has
    a non-induced copy of the first forest in red or the second in blue. -/
theorem host_arrows (R : SimpleGraph (Vertices (hostCapacity n m))) :
    (forest n).IsContained R ∨ (forest m).IsContained (forest (hostCapacity n m) \ R) := by
  let L := hostCapacity n m
  let blue := forest L \ R
  let r (k : Fin (s+t-1)) := Nat.card (Colored L R k)
  let b (k : Fin (s+t-1)) := Nat.card (Colored L blue k)
  have step (i : Fin s) (j : Fin t) :
      n i ≤ r (UpperPath.hostIndex i j) ∨ m j ≤ b (UpperPath.hostIndex i j) :=
    current_color_choice n m R i j _ rfl
  rcases UpperPath.selectFin n m r b step with ⟨f,hf,h⟩ | ⟨f,hf,h⟩
  · exact Or.inl (contained_of_center_counts n L R ⟨f,hf.injective⟩ h)
  · exact Or.inr (contained_of_center_counts m L blue ⟨f,hf.injective⟩ h)

#print axioms host_arrows
end JSP452Audit.StarHost
