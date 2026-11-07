import OriginalUpper

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The candidate set appearing under the pinned minimum. -/
abbrev HostCounts {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y) : Set ℕ :=
  {c | ∃ n : ℕ, ∃ F : SimpleGraph (Fin n), F.edgeSet.ncard = c ∧
    ∀ R : SimpleGraph (Fin n), R ≤ F → G.IsContained R ∨ H.IsContained (F \ R)}

/-- The numerical infimum is attained: we explicitly exhibit a forcing finite
    host, including when the star families are empty. -/
theorem star_host_counts_nonempty {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    (HostCounts (forest n) (forest m)).Nonempty := by
  classical
  let L := hostCapacity n m
  let e : Vertices L ≃ Fin (Fintype.card (Vertices L)) := Fintype.equivFin _
  let K := (forest L).comap e.symm
  refine ⟨K.edgeSet.ncard,_,K,rfl,?_⟩
  intro R _
  rcases host_arrows n m (R.comap e) with h | h
  · exact Or.inl (h.trans (Iso.comap e R).isContained)
  · have blue : forest L \ R.comap e = (K \ R).comap e := by
      ext x y
      change ((forest L).Adj x y ∧ ¬ R.Adj (e x) (e y)) ↔
        ((forest L).Adj (e.symm (e x)) (e.symm (e y)) ∧ ¬ R.Adj (e x) (e y))
      simp only [Equiv.symm_apply_apply]
    rw [blue] at h
    exact Or.inr (h.trans (Iso.comap e (K \ R)).isContained)

theorem star_min_attained {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    sizeRamsey (forest n) (forest m) ∈ HostCounts (forest n) (forest m) :=
  Nat.sInf_mem (star_host_counts_nonempty n m)

#print axioms star_min_attained
end JSP452Audit.StarHost
