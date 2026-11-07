import DeletionBudget

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Original vertices outside the roots and their whole open neighborhood. -/
def awayFromRoots (G : SimpleGraph X) (T : Set X) : Set X :=
  {x | x∉T ∧ ∀ r∈T, ¬G.Adj r x}

/-- If an induced full vertex has the same degree as the ambient upper bound,
the original labels of its surviving neighbors exhaust its actual neighborhood. -/
theorem all_neighbors_survive_of_induced_full [Finite X] (G : SimpleGraph X) (S : Set X)
    (x : S) (D : ℕ) (cap : Nat.card (G.neighborSet x.val) ≤ D)
    (full : Nat.card ((G.induce S).neighborSet x) = D) :
    ∀ y, G.Adj x.val y → y∈S := by
  have image : Subtype.val '' ((G.induce S).neighborSet x) = G.neighborSet x.val := by
    apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
    · rintro y ⟨z,neigh,rfl⟩; exact neigh
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective]
      exact cap.trans_eq full.symm
  intro y edge
  obtain ⟨z,_,rfl⟩ := image.symm ▸ (show y∈G.neighborSet x.val from edge)
  exact z.property

/-- Delete the roots and exposed full vertices that avoid every root. Every surviving
full-degree vertex has all original neighbors, including a surviving matched partner. -/
theorem root_cut_coverage [Finite X] (G : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (M : G.Subgraph) (hm : M.IsMatching)
    (T : Set X) :
    deletionBudget G D ≤ T.ncard + (exposedFull G M D ∩ awayFromRoots G T).ncard := by
  classical
  let A := exposedFull G M D ∩ awayFromRoots G T
  let U := T ∪ A
  let H := G.induce Uᶜ
  let N : H.Subgraph := {
    verts := {x | ∃ y : ↥Uᶜ, M.Adj x.val y.val}
    Adj := fun x y => M.Adj x.val y.val
    adj_sub := fun edge => M.adj_sub edge
    edge_vert := fun edge => ⟨_,edge⟩
    symm := ⟨fun _ _ edge => edge.symm⟩ }
  have matchN : N.IsMatching := by
    rintro x ⟨y,xy⟩
    exact ⟨y,xy,fun z xz => Subtype.ext (hm.eq_of_adj_left xz xy)⟩
  have bound (x : ↥Uᶜ) : Nat.card (H.neighborSet x) ≤ D :=
    (induced_neighbor_count_le G Uᶜ x).trans (cap x.val)
  have covers (x : ↥Uᶜ) (full : Nat.card (H.neighborSet x) = D) : x∈N.verts := by
    have survive := all_neighbors_survive_of_induced_full G Uᶜ x D (cap x.val) full
    have originallyFull : Nat.card (G.neighborSet x.val) = D :=
      (cap x.val).antisymm (full.ge.trans (induced_neighbor_count_le G Uᶜ x))
    have away : x.val∈awayFromRoots G T := ⟨fun h => x.property (Or.inl h),
      fun r hr rx => survive r rx.symm (Or.inl hr)⟩
    have matched : x.val∈M.verts := by
      by_contra miss
      exact x.property (Or.inr (show x.val∈A from ⟨⟨miss,originallyFull⟩,away⟩))
    obtain ⟨y,xy,_⟩ := hm matched
    exact ⟨⟨y,survive y (M.adj_sub xy)⟩,xy⟩
  have witness := admits_remainder_of_full_cover H D pos bound N matchN covers
  exact (deletionBudget_le_of_witness G D U witness).trans (Set.ncard_union_le T A)

#print axioms root_cut_coverage
end JSP452Audit.StarHost
