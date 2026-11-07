import StarColor

namespace JSP452Audit.StarHost

variable {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)

abbrev diagonal (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin s × Fin t)).filter
    (fun p => (p.1.val + 1) + (p.2.val + 1) = k)).sup
      (fun p => n p.1 + m p.2 - 1)

/-- Consecutive host components represent the original one-based antidiagonals. -/
abbrev hostCapacity (u : Fin (s+t-1)) : ℕ := diagonal n m (u.val+2)

theorem antiDiag_member (i : Fin s) (j : Fin t) :
    n i + m j - 1 ≤ diagonal n m (i.val+j.val+2) := by
  unfold diagonal
  apply Finset.le_sup (b := (i,j)) (f := fun p : Fin s × Fin t => n p.1 + m p.2 - 1)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp; omega⟩

theorem host_ncard :
    (forest (hostCapacity n m)).edgeSet.ncard =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  rw [← Nat.card_coe_set_eq, edge_count]
  apply Finset.sum_bij (fun (a : Fin (s+t-1)) _ => a.val+2)
  · intro a _
    apply Finset.mem_Icc.mpr
    have ha := a.isLt
    omega
  · intro a _ b _ he
    apply Fin.ext
    omega
  · intro b hb
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hb
    exact ⟨⟨b-2,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
  · intro a _
    rfl

/-- Pigeonhole step for the actual subgraph coloring of the explicit host. -/
theorem current_color_choice (R : SimpleGraph (Vertices (hostCapacity n m)))
    (i : Fin s) (j : Fin t) (u : Fin (s+t-1)) (step : u.val = i.val+j.val) :
    n i ≤ Nat.card (Colored (hostCapacity n m) R u) ∨
    m j ≤ Nat.card (Colored (hostCapacity n m) (forest (hostCapacity n m) \ R) u) := by
  have part := colors_partition (hostCapacity n m) R u
  have cap : hostCapacity n m u ≥ n i + m j - 1 := by
    simpa only [hostCapacity,step] using antiDiag_member n m i j
  omega

#print axioms host_ncard
#print axioms current_color_choice
end JSP452Audit.StarHost
