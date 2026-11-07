import DegreeTwoSplit

open private JSP452Audit.StarHost.initialVertices JSP452Audit.StarHost.prefix_card
  JSP452Audit.StarHost.prefix_boundary_le_two from PathCycleSplit

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Every prescribed cardinality can be realized with at most two original
vertices on the inside boundary. -/
def HasThinCuts {X : Type*} (G : SimpleGraph X) : Prop :=
  ∀ k ≤ Nat.card X, ∃ U : Set X, U.ncard = k ∧ (insideCutBoundary G U).ncard ≤ 2

private theorem indexed_thin (n : ℕ) (G : SimpleGraph (Fin n)) (cyclic : G ≤ cycleGraph n) :
    HasThinCuts G := by
  intro k fit
  rw [Nat.card_fin] at fit
  exact ⟨JSP452Audit.StarHost.initialVertices n k,JSP452Audit.StarHost.prefix_card fit,
    JSP452Audit.StarHost.prefix_boundary_le_two G cyclic⟩

private theorem thin_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (thin : HasThinCuts G) :
    HasThinCuts H := by
  intro k fit
  obtain ⟨A,card,bound⟩ := thin k (fit.trans_eq (Nat.card_congr e.toEquiv).symm)
  have boundary : insideCutBoundary H (e '' A) = e '' insideCutBoundary G A := by
    ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,z,hz,h⟩
      refine ⟨x,⟨hx,e.symm z,fun mem => hz ⟨e.symm z,mem,e.apply_symm_apply z⟩,?_⟩,rfl⟩
      exact e.map_rel_iff.mp (by simpa using h)
    · rintro ⟨x,⟨hx,z,hz,h⟩,rfl⟩
      refine ⟨⟨x,hx,rfl⟩,e z,?_,e.map_rel_iff.mpr h⟩
      rintro ⟨w,hw,eq⟩
      exact hz (e.injective eq ▸ hw)
  refine ⟨e '' A,?_,?_⟩
  · rwa [Set.ncard_image_of_injective _ e.injective]
  · rwa [boundary,Set.ncard_image_of_injective _ e.injective]

private def joinCut {X Y : Type*} (A : Set X) (B : Set Y) : Set (X ⊕ Y) :=
  {z | Sum.elim (·∈A) (·∈B) z}

private theorem join_card {X Y : Type*} [Finite X] [Finite Y] (A : Set X) (B : Set Y) :
    (joinCut A B).ncard = A.ncard+B.ncard := by
  exact (Nat.card_congr (Equiv.subtypeSum (p := fun z => z∈joinCut A B))).trans Nat.card_sum

private theorem join_boundary {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)
    (A : Set X) (B : Set Y) : insideCutBoundary (G ⊕g H) (joinCut A B) =
      joinCut (insideCutBoundary G A) (insideCutBoundary H B) := by
  ext z
  cases z <;> simp [insideCutBoundary,joinCut,Sum.exists]

private theorem thin_sum {X Y : Type*} [Finite X] [Finite Y] (G : SimpleGraph X) (H : SimpleGraph Y)
    (left : HasThinCuts G) (right : HasThinCuts H) : HasThinCuts (G ⊕g H) := by
  intro k fit
  rw [Nat.card_sum] at fit
  by_cases contains : k ≤ Nat.card X
  · obtain ⟨A,card,bound⟩ := left k contains
    have none : insideCutBoundary H ∅ = ∅ := by ext; simp [insideCutBoundary]
    exact ⟨joinCut A ∅,by simp [join_card,card],by simpa [join_boundary,join_card,none] using bound⟩
  · obtain ⟨B,card,bound⟩ := right (k-Nat.card X) (by omega)
    have none : insideCutBoundary G Set.univ = ∅ := by ext; simp [insideCutBoundary]
    refine ⟨joinCut Set.univ B,?_,?_⟩
    · rw [join_card,Set.ncard_univ,card]; omega
    · simpa [join_boundary,join_card,none] using bound

private def componentLabels {X : Type*} (G : SimpleGraph X) (T : Finset G.ConnectedComponent) : Set X :=
  {v | G.connectedComponentMk v ∈ T}

/-- Whole components can be put on either side without adding any boundary
vertex. Only one genuine component is partially selected. -/
theorem thin_cuts_of_degree_le_two {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) : HasThinCuts G := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have parts (c : G.ConnectedComponent) : HasThinCuts c.toSimpleGraph := by
    rcases degree_two_component_classification G cap c with path | cycle
    · obtain ⟨e⟩ := path
      exact thin_iso e (indexed_thin _ _ pathGraph_le_cycleGraph)
    · obtain ⟨_,⟨e⟩⟩ := cycle
      exact thin_iso e (indexed_thin _ _ le_rfl)
  have unions (T : Finset G.ConnectedComponent) : HasThinCuts (G.induce (componentLabels G T)) := by
    induction T using Finset.induction_on with
    | empty =>
      let _ : IsEmpty (componentLabels G ∅) := ⟨fun x => Finset.notMem_empty _ x.property⟩
      intro k fit
      have zero := Nat.card_eq_zero.mpr (Or.inl (inferInstance : IsEmpty (componentLabels G ∅)))
      refine ⟨∅,by rw [Set.ncard_empty]; omega,?_⟩
      simp [insideCutBoundary]
    | @insert c T fresh ih =>
      have cover : c.supp ∪ componentLabels G T = componentLabels G (insert c T) := by
        ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (componentLabels G T) := Set.disjoint_left.mpr (by
        intro x hx ht; exact fresh ((show G.connectedComponentMk x = c from hx) ▸ ht))
      have sep : ∀ x∈c.supp, ∀ y∈componentLabels G T, ¬ G.Adj x y :=
        fun _ hx _ hy edge => Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
      exact thin_iso (regionSumIso G _ _ _ cover apart sep) (thin_sum _ _ (parts c) ih)
  have all : componentLabels G Finset.univ = Set.univ := by ext; simp [componentLabels]
  have result := unions Finset.univ
  rw [all] at result
  exact thin_iso (induceUnivIso G) result

/-- The internal red cut has one fewer vertex than the red forest. Therefore
the same coloring must contain the full blue forest inside the complementary
vertices together with at most two inside boundary points. -/
theorem forced_forest_order_of_thin_cuts {X I J : Type*} [Finite X] [Finite I] [Finite J]
    [Nonempty I] [Nonempty J] (G : SimpleGraph X) (thin : HasThinCuts G)
    (n : I → ℕ) (m : J → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (force : Forces G (forest n) (forest m)) :
    Nat.card (Vertices n) + Nat.card (Vertices m) ≤ Nat.card X+3 := by
  classical
  let a := center n (Classical.choice (inferInstance : Nonempty I))
  let b := center m (Classical.choice (inferInstance : Nonempty J))
  have positive : 0 < Nat.card (Vertices n) := @Nat.card_pos _ ⟨a⟩ _
  have redCopy : (forest n).IsContained G := by
    rcases force G le_rfl with h | bad
    · exact h
    · obtain ⟨f⟩ := bad
      obtain ⟨w,e⟩ := forest_has_neighbor m pm b
      have edge := f.toHom.map_adj e
      exact (edge.2 edge.1).elim
  obtain ⟨f⟩ := redCopy
  have enough := Nat.card_le_card_of_injective f f.injective
  obtain ⟨U,size,bound⟩ := thin (Nat.card (Vertices n)-1) (by omega)
  obtain ⟨sub,red,blue⟩ := internal_cut_supports G U (forest n) (forest m)
    (forest_has_neighbor n pn) (forest_has_neighbor m pm)
  have all := Set.ncard_add_ncard_compl U
  rcases force _ sub with r | b
  · have := red r; omega
  · have := blue b; omega

theorem forced_forest_order_le_edges_add_four {X I J : Type*} [Finite X] [Finite I] [Finite J]
    [Nonempty I] [Nonempty J] (G : SimpleGraph X) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2)
    (n : I → ℕ) (m : J → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (force : Forces G (forest n) (forest m)) (order : Nat.card X ≤ G.edgeSet.ncard+1) :
    Nat.card (Vertices n)+Nat.card (Vertices m) ≤ G.edgeSet.ncard+4 := by
  have := forced_forest_order_of_thin_cuts G (thin_cuts_of_degree_le_two G cap) n m pn pm force
  omega

#print axioms thin_cuts_of_degree_le_two
#print axioms forced_forest_order_of_thin_cuts
#print axioms forced_forest_order_le_edges_add_four
end JSP452Audit.StarHost
