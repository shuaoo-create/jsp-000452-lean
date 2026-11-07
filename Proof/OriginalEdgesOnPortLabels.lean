import ActualNineDoubleShortCaseExcluded
import WholeCoreErasureRank
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type u} [Finite X]

/-- Original edges with both labels in the given set, on the original vertex type. -/
abbrev portInside (G : SimpleGraph X) (U : Set X) := G \ eraseInternal G U

omit [Finite X] in
theorem portInside_adj (G : SimpleGraph X) (U : Set X) (x y : X) :
    (portInside G U).Adj x y ↔ G.Adj x y ∧ x∈U ∧ y∈U := by
  classical
  change (G.Adj x y ∧ ¬(G.Adj x y ∧ ¬(x∈U ∧ y∈U))) ↔ _
  tauto

/-- If every edge except those through v lies inside U, deleting v leaves
at most the induced matching rank on U. The original labels can include isolates. -/
theorem rank_paid_by_one_tip (G H : SimpleGraph X) (sub : H≤G) (U : Set X) (v : X)
    (cover : ∀ ⦃x y⦄, H.Adj x y → x≠v → y≠v → x∈U ∧ y∈U) :
    matchingEdges H ≤ matchingEdges (G.induce U)+1 := by
  classical
  let A := portInside G U
  have split := rank_of_two_edge_colours H A (H \ A) (by
    intro x y edge
    by_cases a : A.Adj x y
    · exact Or.inl a
    · exact Or.inr ⟨edge,a⟩)
  have one := matchingEdges_le_cover_card (H \ A) {v} (by
    intro x y edge
    by_cases hx : x=v
    · exact Or.inl hx
    · by_cases hy : y=v
      · exact Or.inr hy
      · exact (edge.2 ((portInside_adj G U x y).mpr ⟨sub edge.1,cover edge.1 hx hy⟩)).elim)
  rw [Set.ncard_singleton] at one
  have inside : matchingEdges A=matchingEdges (G.induce U) := rank_of_internal_edges G U
  omega

namespace NinePortRegion
variable {G : SimpleGraph X} (R : NinePortRegion G)
abbrev tipDeleted (i : Fin 2) := R.box i \ {(R.port i).tip}
noncomputable abbrev tipRank (i : Fin 2) := matchingEdges (G.induce (R.tipDeleted i))
def essential (i : Fin 2) : Prop := R.tipRank i<R.capacity i

theorem tip_rank_dichotomy (i : Fin 2) :
    (R.essential i ∧ R.tipRank i+1=R.capacity i) ∨
      (¬R.essential i ∧ R.tipRank i=R.capacity i) := by
  have upper := induced_rank_le_of_subset G (show R.tipDeleted i⊆R.box i from Set.sdiff_subset)
  have lower := rank_paid_by_one_tip G (portInside G (R.box i)) sdiff_le
    (R.tipDeleted i) (R.port i).tip (by
      intro x y edge hx hy
      obtain ⟨_,ins,ins'⟩ := (portInside_adj G (R.box i) x y).mp edge
      exact ⟨⟨ins,hx⟩,⟨ins',hy⟩⟩)
  change R.tipRank i≤R.capacity i at upper
  rw [rank_of_internal_edges] at lower
  change R.capacity i≤R.tipRank i+1 at lower
  dsimp only [essential]
  omega

/-- An E block reserves its entire vertex set. An L block leaves its tip
available to the exterior while still realizing its entire internal capacity. -/
noncomputable def reserved (i : Fin 2) : Set X := by
  classical
  exact if R.essential i then R.box i else R.tipDeleted i

theorem reserved_subset (i : Fin 2) : R.reserved i⊆R.box i := by
  classical
  unfold reserved;split
  · exact fun _ h => h
  · exact Set.sdiff_subset

theorem reserved_rank (i : Fin 2) : matchingEdges (G.induce (R.reserved i))=R.capacity i := by
  classical
  by_cases h : R.essential i
  · rw [reserved,if_pos h]
  · rw [reserved,if_neg h]
    exact ((R.tip_rank_dichotomy i).resolve_left (fun he => h he.1)).2

#print axioms tip_rank_dichotomy
#print axioms reserved_subset
#print axioms reserved_rank
end NinePortRegion
#print axioms portInside_adj
#print axioms rank_paid_by_one_tip
end JSP452Audit.StarHost
