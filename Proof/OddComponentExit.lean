import TutteJoin

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- In a residual odd component a matching either exposes an original vertex
or matches an original vertex across the cut, with genuine labels in both cases. -/
theorem odd_component_exit (G : SimpleGraph X) (S : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) (M : G.Subgraph) (hm : M.IsMatching)
    (odd : Odd c.supp.ncard) :
    ∃ x : ↥(Sᶜ : Set X), x ∈ c.supp ∧
      (x.val ∉ M.verts ∨ ∃ s ∈ S, M.Adj x.val s) := by
  by_contra none
  have used (x : ↥(Sᶜ : Set X)) (hx : x ∈ c.supp) : x.val ∈ M.verts := by
    by_contra miss
    exact none ⟨x,hx,Or.inl miss⟩
  have away (x : ↥(Sᶜ : Set X)) (hx : x ∈ c.supp) {y : X} (edge : M.Adj x.val y) : y ∉ S :=
    fun hy => none ⟨x,hx,Or.inr ⟨y,hy,edge⟩⟩
  let Q : Set X := Subtype.val '' c.supp
  have restricted : (M.induce Q).IsMatching := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨y,edge,uniq⟩ := hm (used x hx)
    let ys : ↥(Sᶜ : Set X) := ⟨y,away x hx edge⟩
    have same : ys ∈ c.supp := c.mem_supp_of_adj_mem_supp hx
      (show (G.induce Sᶜ).Adj x ys from M.adj_sub edge)
    refine ⟨y,⟨⟨x,hx,rfl⟩,⟨ys,same,rfl⟩,edge⟩,?_⟩
    intro u hu
    exact uniq u hu.2.2
  have labels : Q.ncard = c.supp.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have card := matching_vertices_eq_twice_edges restricted
  change Q.ncard = 2 * (M.induce Q).edgeSet.ncard at card
  rw [labels] at card
  obtain ⟨t,ht⟩ := odd
  omega

theorem odd_component_exit_labels (G : SimpleGraph X) (S : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) (M : G.Subgraph) (hm : M.IsMatching)
    (odd : Odd c.supp.ncard) :
    (∃ x ∈ (Subtype.val '' c.supp : Set X), x ∉ M.verts) ∨
      ∃ x ∈ (Subtype.val '' c.supp : Set X), ∃ s ∈ S, M.Adj x s := by
  obtain ⟨x,hx,miss | exit⟩ := odd_component_exit G S c M hm odd
  · exact Or.inl ⟨x.val,⟨x,hx,rfl⟩,miss⟩
  · exact Or.inr ⟨x.val,⟨x,hx,rfl⟩,exit⟩

#print axioms odd_component_exit
#print axioms odd_component_exit_labels
end JSP452Audit.StarHost
