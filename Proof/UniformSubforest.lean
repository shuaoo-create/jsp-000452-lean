import ForcingHost
import Mathlib.Data.Fin.Embedding

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Retain distinct original indices and truncate their leaf labels. The
coordinate zero remains the center in every retained component. -/
def subforestCopy {I J : Type*} (small : I → ℕ) (n : J → ℕ) (labels : I ↪ J)
    (fit : ∀ i, small i ≤ n (labels i)) : (forest small).Copy (forest n) := by
  let verts : Vertices small ↪ Vertices n := Function.Embedding.sigmaMap labels fun i =>
    Fin.castLEEmb (Nat.succ_le_succ (fit i))
  refine ⟨⟨verts,?_⟩,verts.injective⟩
  intro x y e
  rcases e with ⟨ne,h|h⟩
  · exact ⟨fun eq => ne (verts.injective eq), Or.inl ⟨congrArg labels h.1,h.2⟩⟩
  · exact ⟨fun eq => ne (verts.injective eq), Or.inr ⟨congrArg labels h.1,h.2⟩⟩

/-- Choose u actual distinct large components. This works even when u=0;
the threshold may be zero as well. -/
noncomputable def uniform_subforest_copy {I : Type*} [Fintype I] (n : I → ℕ) (a u : ℕ)
    (enough : u ≤ (Finset.univ.filter (fun i => a ≤ n i)).card) :
    (forest (fun _ : Fin u => a)).Copy (forest n) := by
  classical
  let S := Finset.univ.filter (fun i => a ≤ n i)
  let pick : Fin u ↪ S := (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using enough)).some
  let labels : Fin u ↪ I := pick.trans (Function.Embedding.subtype _)
  exact subforestCopy _ n labels (fun i => (Finset.mem_filter.mp (pick i).property).2)

/-- Project both outcomes of the same host coloring to true uniform forests
inside their respective original full targets. -/
theorem forces_uniform_subforests {X I J : Type*} [Fintype I] [Fintype J]
    (G : SimpleGraph X) (n : I → ℕ) (m : J → ℕ) (a b u v : ℕ)
    (red : u ≤ (Finset.univ.filter (fun i => a ≤ n i)).card)
    (blue : v ≤ (Finset.univ.filter (fun j => b ≤ m j)).card)
    (force : Forces G (forest n) (forest m)) :
    Forces G (forest (fun _ : Fin u => a)) (forest (fun _ : Fin v => b)) := by
  intro R incl
  rcases force R incl with r | bcopy
  · obtain ⟨f⟩ := r
    exact Or.inl ⟨f.comp (uniform_subforest_copy n a u red)⟩
  · obtain ⟨f⟩ := bcopy
    exact Or.inr ⟨f.comp (uniform_subforest_copy m b v blue)⟩

#print axioms subforestCopy
#print axioms uniform_subforest_copy
#print axioms forces_uniform_subforests
end JSP452Audit.StarHost
