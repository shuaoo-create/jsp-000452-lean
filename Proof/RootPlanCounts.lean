import BarrierExitCount
import ParityGap

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

variable {X : Type*} [Finite X]

/-- The original labels of the chosen holes in the components with no assigned root. -/
def freeHoleLabels (G : SimpleGraph X) (S : Set X)
    (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) : Set X :=
  (fun c => (pick c).val.val) '' (Set.range place)ᶜ

omit [Finite X] in
/-- A chosen vertex determines its entire connected component, even after
forgetting the residual and component subtype labels. -/
theorem picked_original_injective (G : SimpleGraph X) (S : Set X)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) :
    Function.Injective (fun c => (pick c).val.val) := by
  intro c d eq
  have same : (pick c).val = (pick d).val := Subtype.ext eq
  have left := (c.mem_supp_iff _).mp (pick c).property
  have right := (d.mem_supp_iff _).mp (pick d).property
  exact left.symm.trans ((congrArg (G.induce Sᶜ).connectedComponentMk same).trans right)

theorem freeHoleLabels_ncard (G : SimpleGraph X) (S : Set X)
    (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) (tight : IsTightBarrier G S)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp)) :
    (freeHoleLabels G S place pick).ncard = minUnmatched G := by
  let Y := G.induce Sᶜ
  have all : Y.oddComponents = Set.univ :=
    Set.eq_univ_of_forall fun c => (odd c : Odd (Nat.card c.supp))
  change Y.oddComponents.ncard = S.ncard + minUnmatched G at tight
  rw [all,Set.ncard_univ] at tight
  rw [freeHoleLabels,Set.ncard_image_of_injective _ (picked_original_injective G S pick),
    Set.ncard_compl,Set.ncard_range_of_injective place.injective]
  change Nat.card Y.ConnectedComponent - S.ncard = _
  omega

/-- A matching that leaves precisely the unassigned-component labels
uncovered attains the matching number of the original host. -/
theorem maximum_of_freeHoleLabels (G : SimpleGraph X) (S : Set X)
    (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) (tight : IsTightBarrier G S)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp))
    (N : G.Subgraph) (matching : N.IsMatching)
    (holes : N.vertsᶜ = freeHoleLabels G S place pick) : N.edgeSet.ncard = matchingEdges G := by
  have count := freeHoleLabels_ncard G S place pick tight odd
  have cover := Set.ncard_add_ncard_compl N.verts
  rw [matching_vertices_eq_twice_edges matching,holes,count] at cover
  have best := minUnmatched_add_twice_matching G
  omega

#print axioms freeHoleLabels_ncard
#print axioms maximum_of_freeHoleLabels
end JSP452Audit.StarHost
