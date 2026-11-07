import ExposureThreshold
import SetRestoreAvoid
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Each actual matching of a forcing host misses this many full-degree vertices.
The lists can be of unequal lengths, and need not be sorted. -/
theorem forced_full_exposure {X I J : Type*} [Finite X] [Fintype I] [Fintype J]
    (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (p q : ℕ) (bound : ∀ x, Nat.card (G.neighborSet x) ≤ p+q)
    (n : I → ℕ) (m : J → ℕ) (row : Forces G (forest n) (forest m))
    {u v : ℕ} (hu : 0<u) (hv : 0<v)
    (red : u ≤ (Finset.univ.filter (fun i => p+1 ≤ n i)).card)
    (blue : v ≤ (Finset.univ.filter (fun j => q+1 ≤ m j)).card) :
    u+v-1 ≤ (exposedFull G M (p+q)).ncard := by
  by_contra! small
  let W := exposedFull G M (p+q)
  obtain ⟨A,B,parts,_,smallA,smallB⟩ := split_control_budget W hu hv small
  obtain ⟨F,sub,cap⟩ := degree_split_off_exposed G M hM p q bound
  obtain ⟨C,incl,_,onRed,onBlue⟩ :=
    set_restore_large_counts G W A B parts.symm F sub (fun x => (cap x).1) (fun x => (cap x).2) n m
  rcases row C incl with fr | fb
  · exact (not_le_of_gt smallA) (red.trans (onRed fr))
  · exact (not_le_of_gt smallB) (blue.trans (onBlue fb))

/-- An attaining pair of original suffix heads controls the number of
uncovered vertices on the very same graph and original degree threshold. -/
theorem suffix_pair_exposure {X : Type*} [Finite X] (G : SimpleGraph X)
    (M : G.Subgraph) (hM : M.IsMatching) {s t r : ℕ}
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (bound : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1)
    (i : Fin s) (j : Fin t) (sum : i.val+j.val=r)
    (att : diagonal n m (r+2) = n i + m j - 1) :
    headWidth n i + headWidth m j - 1 ≤ (exposedFull G M (diagonal n m (r+2)-1)).ncard := by
  have hni : n i-1+1=n i := by have := pn i; omega
  have hmj : m j-1+1=m j := by have := pm j; omega
  have D : diagonal n m (r+2)-1 = (n i-1)+(m j-1) := by omega
  rw [D] at bound ⊢
  apply forced_full_exposure G M hM _ _ bound (originalTail n i) (originalTail m j)
    (forces_original_tails G n m row i j sum) (headWidth_pos n i) (headWidth_pos m j)
  · rw [hni]; exact le_rfl
  · rw [hmj]; exact le_rfl

#print axioms forced_full_exposure
#print axioms suffix_pair_exposure
end JSP452Audit.StarHost