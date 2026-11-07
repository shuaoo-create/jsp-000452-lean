import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A matching has at most one edge incident to a vertex satisfying a predicate
that holds for at most one vertex. The predicate may hold nowhere. -/
theorem matching_edges_with_endpoint_le_one {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (P : X → Prop) (hP : {a | P a}.ncard ≤ 1) :
    {e : Sym2 X | e ∈ N.edgeSet ∧ ∃ a, a ∈ e ∧ P a}.ncard ≤ 1 := by
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  rintro e ⟨he, a, ae, pa⟩ f ⟨hf, b, bf, pb⟩
  have same : a = b := (Set.ncard_le_one (Set.toFinite {a : X | P a})).mp hP a pa b pb
  subst b
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp ae
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp bf
  have sameMate := hm.eq_of_adj_left (Subgraph.mem_edgeSet.mp he) (Subgraph.mem_edgeSet.mp hf)
  rw [sameMate]

#print axioms matching_edges_with_endpoint_le_one
end JSP452Audit.StarHost
