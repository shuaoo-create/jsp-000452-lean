import TheActualPortSupportForTheTenDegreePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def incidentImageIso {X Y:Type u} {G:SimpleGraph X} {H:SimpleGraph Y} (e:G≃g H) (U:Set X) :
    eraseInternal G Uᶜ ≃g eraseInternal H (e '' U)ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change (H.Adj (e a) (e b) ∧ ¬(e a∉e '' U ∧ e b∉e '' U)) ↔
      G.Adj a b ∧ ¬(a∉U ∧ b∉U)
    have mem (x:X) : e x∈e '' U ↔ x∈U := by
      constructor
      · rintro ⟨z,hz,eq⟩;exact e.injective eq ▸ hz
      · exact fun hx => ⟨x,hx,rfl⟩
    simp only [e.map_rel_iff,mem]

namespace TenPortSupport
variable {X Y:Type u} [Finite X] [Finite Y] {G:SimpleGraph X} {H:SimpleGraph Y} {R:TenBlockPartition G} {h:ℕ}
noncomputable def transport (W:TenPortSupport G R h) (e:G≃g H) : TenPortSupport H (R.transport e) h := by
  let U := e '' W.support
  have inner := inducedImageIso e W.support
  have outer := incidentImageIso e W.support
  have count : U.ncard=W.support.ncard := Set.ncard_image_of_injective W.support e.injective
  have edges : (H.induce U).edgeSet.ncard=(G.induce W.support).edgeSet.ncard := (Nat.card_congr inner.mapEdgeSet).symm
  have piece : (eraseInternal H Uᶜ).edgeSet.ncard=(eraseInternal G W.supportᶜ).edgeSet.ncard := (Nat.card_congr outer.mapEdgeSet).symm
  have boundary : crossCount H U Uᶜ=crossCount G W.support W.supportᶜ := by
    have src := incident_piece_edge_count G W.support
    have dst := incident_piece_edge_count H U
    omega
  have rank : matchingEdges (eraseInternal H Uᶜ)=matchingEdges (eraseInternal G W.supportᶜ) := (rank_eq_of_graph_iso outer).symm
  have irank : matchingEdges (H.induce U)=matchingEdges (G.induce W.support) := (rank_eq_of_graph_iso inner).symm
  refine ⟨U,W.targetPorts,W.targetDefect,count.symm ▸ W.orderFloor,?_,?_,?_,?_,?_,?_⟩
  · change matchingEdges (eraseInternal H Uᶜ)=(e '' R.roots).ncard+matchingEdges (H.induce (e '' R.core))
    rw [rank,Set.ncard_image_of_injective _ e.injective,←rank_eq_of_graph_iso (inducedImageIso e R.core)]
    exact W.regionRank
  · rw [rank,irank];exact W.portRank
  · rw [irank,count];exact W.order
  · rw [edges,count];exact W.edges
  · rw [boundary];exact W.ports
  · rw [boundary];exact W.defect

#print axioms transport
end TenPortSupport
#print axioms incidentImageIso
end JSP452Audit.StarHost
