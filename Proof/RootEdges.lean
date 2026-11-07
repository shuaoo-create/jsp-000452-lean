import PairFamily
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} (G : SimpleGraph X) (S : Set X)

/-- A selected vertex determines its connected component even after both
subtype labels have been forgotten. -/
theorem pick_label_injective (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) :
    Function.Injective (fun c => (pick c).val.val) := by
  intro c d same
  have eq : (pick c).val = (pick d).val := Subtype.ext same
  have left : (G.induce Sᶜ).connectedComponentMk (pick c).val = c := (pick c).property
  have right : (G.induce Sᶜ).connectedComponentMk (pick d).val = d := (pick d).property
  exact left.symm.trans ((congrArg _ eq).trans right)

variable (place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent)
  (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
  (link : ∀ a : S, G.Adj a.val (pick (place a)).val.val)

private def rootImage : ↥S ↪ X :=
  ⟨fun a => (pick (place a)).val.val,(pick_label_injective G S pick).comp place.injective⟩

/-- The actual graph pairs each root with its specified vertex in the assigned component. -/
def rootEdgeMatching : G.Subgraph :=
  Padded.pairFamily G (Function.Embedding.subtype (· ∈ S)) (rootImage G S place pick) link

theorem rootEdgeMatching_edge (a : S) :
    (rootEdgeMatching G S place pick link).Adj a.val (pick (place a)).val.val :=
  Or.inl ⟨a,rfl,rfl⟩

theorem rootEdgeMatching_isMatching : (rootEdgeMatching G S place pick link).IsMatching := by
  apply Padded.pairFamily_isMatching
  apply Set.disjoint_left.mpr
  rintro _ ⟨a,rfl⟩ ⟨b,e⟩
  have eq : (pick (place b)).val.val = a.val := e
  exact (pick (place b)).val.property (eq.symm ▸ a.property)

theorem rootEdgeMatching_verts (v : X) :
    v ∈ (rootEdgeMatching G S place pick link).verts ↔
      v ∈ S ∨ ∃ a : S, (pick (place a)).val.val = v := by
  change ((∃ a : S, a.val = v) ∨ _) ↔ _
  constructor
  · rintro (⟨a,rfl⟩ | h)
    · exact Or.inl a.property
    · exact Or.inr h
  · rintro (h|h)
    · exact Or.inl ⟨⟨v,h⟩,rfl⟩
    · exact Or.inr h

include link in
theorem exists_root_edges_matching :
    ∃ K : G.Subgraph, K.IsMatching ∧ ∀ v,
      v ∈ K.verts ↔ v ∈ S ∨ ∃ a : S, (pick (place a)).val.val = v :=
  ⟨rootEdgeMatching G S place pick link,rootEdgeMatching_isMatching G S place pick link,
    rootEdgeMatching_verts G S place pick link⟩

#print axioms pick_label_injective
#print axioms rootEdgeMatching_edge
#print axioms exists_root_edges_matching
end JSP452Audit.StarHost
