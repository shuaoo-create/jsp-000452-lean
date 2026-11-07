import BinaryFlexDef
namespace JSP452Audit.StarHost
open SimpleGraph
theorem binary_vertices (p a : ℕ) : Nat.card (Vertices (binaryProfile p a))=3*p+2*a := by
  unfold Vertices
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  rw [Finset.sum_fin_eq_sum_range,Finset.sum_range_add]
  apply congrArg₂ Nat.add
  · calc
      _ = ∑ _k∈Finset.range p, (3:ℕ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hi := Finset.mem_range.mp hk
        simp [binaryProfile,hi,show k<p+a by omega]
      _ = _ := by simp [Nat.mul_comm]
  · calc
      _ = ∑ _k∈Finset.range a, (2:ℕ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hi := Finset.mem_range.mp hk
        simp [binaryProfile,show p+k<p+a by omega]
      _ = _ := by simp [Nat.mul_comm]

theorem exact_split_forcing_floor {X : Type*} [Finite X] {s t : ℕ} (G : SimpleGraph X)
    (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (split : ExactRankSplit G) : s+t-1≤matchingEdges G := by
  by_contra! small
  let u := min (s-1) (matchingEdges G)
  obtain ⟨R,sub,red,blue⟩ := split u (Nat.min_le_right _ _)
  rcases force R sub with fr | fb
  · have h := forest_copy_matching R n pn fr
    rw [Fintype.card_fin] at h; dsimp [u] at red; omega
  · have h := forest_copy_matching (G \ R) m pm fb
    rw [Fintype.card_fin] at h; dsimp [u] at blue; omega
#print axioms binary_vertices
#print axioms exact_split_forcing_floor
end JSP452Audit.StarHost