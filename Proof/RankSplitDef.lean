import PathCycleMatching
import RegionSplitRank
namespace JSP452Audit.StarHost
open SimpleGraph
/-- Split a matching allowance between red and blue on the same graph, with
at most one extra unit in the total. -/
def CanSplitRank {X : Type*} [Finite X] (G : SimpleGraph X) : Prop :=
  ∀ u : ℕ, u≤matchingEdges G → ∃ R : SimpleGraph X, R≤G ∧ matchingEdges R≤u ∧
    matchingEdges (G \ R) ≤ matchingEdges G-u+1

/-- Matching monotonicity works for a copy, so extra induced edges do not
affect the validity of the bound. -/
theorem rank_le_of_copy {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    (f : G.Copy H) : matchingEdges G≤matchingEdges H := by
  obtain ⟨M,hm,max⟩ := exists_maximum_matching G
  have moved := hm.map f.toHom f.injective
  have limit := le_matchingEdges moved
  have support := matching_vertices_eq_twice_edges moved
  change (f.toHom '' M.verts).ncard = _ at support
  rw [Set.ncard_image_of_injective _ f.injective,matching_vertices_eq_twice_edges hm,max] at support
  omega
#print axioms rank_le_of_copy
end JSP452Audit.StarHost