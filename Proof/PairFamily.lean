import Mathlib.Combinatorics.SimpleGraph.Matching

namespace JSP452Audit.Padded

variable {I V : Type*} (G : SimpleGraph V) (l r : I ↪ V)
  (edge : ∀ i, G.Adj (l i) (r i))

/-- Realizes a family of named edges. The endpoints have exactly the given support. -/
def pairFamily : G.Subgraph where
  verts := Set.range l ∪ Set.range r
  Adj x y := (∃ i, l i = x ∧ r i = y) ∨ (∃ i, r i = x ∧ l i = y)
  adj_sub := by
    rintro x y (⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩)
    · exact edge i
    · exact (edge i).symm
  edge_vert := by
    rintro x y (⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩)
    · exact Or.inl (Set.mem_range_self i)
    · exact Or.inr (Set.mem_range_self i)
  symm := ⟨by
    rintro x y (⟨i, hl, hr⟩ | ⟨i, hr, hl⟩)
    · exact Or.inr ⟨i, hr, hl⟩
    · exact Or.inl ⟨i, hl, hr⟩⟩

@[simp] theorem pairFamily_verts :
    (pairFamily G l r edge).verts = Set.range l ∪ Set.range r := rfl

theorem pairFamily_adj_iff {x y : V} :
    (pairFamily G l r edge).Adj x y ↔
      (∃ i, l i = x ∧ r i = y) ∨ (∃ i, r i = x ∧ l i = y) := Iff.rfl

/-- No finiteness, enumeration or decision procedure for the index type is required. -/
theorem pairFamily_isMatching (apart : Disjoint (Set.range l) (Set.range r)) :
    (pairFamily G l r edge).IsMatching := by
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · refine ⟨r i, Or.inl ⟨i, rfl, rfl⟩, ?_⟩
    rintro y (⟨j, h, hr⟩ | ⟨j, h, hl⟩)
    · exact hr.symm.trans (congrArg r (l.injective h))
    · exact (apart.ne_of_mem (Set.mem_range_self i) (Set.mem_range_self j) h.symm).elim
  · refine ⟨l i, Or.inr ⟨i, rfl, rfl⟩, ?_⟩
    rintro y (⟨j, h, hr⟩ | ⟨j, h, hl⟩)
    · exact (apart.ne_of_mem (Set.mem_range_self j) (Set.mem_range_self i) h).elim
    · exact hl.symm.trans (congrArg l (r.injective h))

theorem pairFamily_adj_left_right_iff (apart : Disjoint (Set.range l) (Set.range r))
    (i j : I) : (pairFamily G l r edge).Adj (l i) (r j) ↔ i = j := by
  constructor
  · intro h
    apply r.injective
    exact (pairFamily_isMatching G l r edge apart).eq_of_adj_left (Or.inl ⟨i, rfl, rfl⟩) h
  · rintro rfl
    exact Or.inl ⟨i, rfl, rfl⟩

/-- Vertex-set disjointness suffices for mathlib's support-based matching union. -/
theorem matching_sup_of_disjoint_verts {M N : G.Subgraph} (hM : M.IsMatching)
    (hN : N.IsMatching) (apart : Disjoint M.verts N.verts) : (M ⊔ N).IsMatching :=
  hM.sup hN (apart.mono M.support_subset_verts N.support_subset_verts)

#print axioms pairFamily
#print axioms pairFamily_verts
#print axioms pairFamily_adj_iff
#print axioms pairFamily_isMatching
#print axioms pairFamily_adj_left_right_iff
#print axioms matching_sup_of_disjoint_verts

end JSP452Audit.Padded
