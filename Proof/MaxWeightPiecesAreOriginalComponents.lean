import StrictSixFourExposureEntry
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_weight_piece_label {X:Type u} [Finite X] {G:SimpleGraph X} (K:DegreeRegion G 6)
    (w:↥K.positive) (weight:K.pieceWeight w=3) :
    let c := w.val
    let O := originalComponentOfCutPiece G K.barrier c
    O.supp=cutPieceSet G K.barrier c ∧ O∈oddRegularComponents G 6 := by
  intro c O
  let U := cutPieceSet G K.barrier c
  let iso : c.toSimpleGraph ≃g G.induce U := { toEquiv := cutPieceVertexEquiv G K.barrier c, map_rel_iff' := Iff.rfl }
  have full : ∀x∈U,Nat.card (G.neighborSet x)=6 := by
    rintro _ ⟨v,hv,rfl⟩
    exact K.full w.property.1 ⟨v,hv⟩
  have degree := degree_sum_full G U 6 full
  have boundary := JSP452Audit.StarHost.two_block_handshake G U
  have cards : Nat.card c.supp=U.ncard := Nat.card_congr iso.toEquiv
  have edges : c.toSimpleGraph.edgeSet.ncard=(G.induce U).edgeSet.ncard := Nat.card_congr iso.mapEdgeSet
  let z := matchingEdges c.toSimpleGraph
  have order : Nat.card c.supp=2*z+1 := factorCritical_order_rank c.toSimpleGraph (K.critical c).2 c.nonempty_supp.to_subtype.some
  change (c.toSimpleGraph.edgeSet.ncard:ℤ)-6*(z:ℤ)=3 at weight
  have eq : (G.induce U).edgeSet.ncard=6*z+3 := by omega
  have zero : crossCount G U Uᶜ=0 := by rw [degree] at boundary;omega
  have cut : crossCount G U K.barrier=0 := crossCount_of_no_edges G U K.barrier (fun _ hx _ hy =>
    no_edge_when_port_zero G zero hx (fun h => cut_piece_outside G K.barrier c h hy))
  have labels := no_port_piece_is_global G K.barrier c cut
  change O.supp=U at labels
  refine ⟨labels,?_,?_⟩
  · rw [labels]
    change Odd U.ncard
    exact cards ▸ (K.critical c).1
  · intro x hx
    exact full x (labels ▸ hx)

theorem full_weight_piece_count {X:Type u} [Finite X] {G:SimpleGraph X} (K:DegreeRegion G 6) :
    ({w:↥K.positive | K.pieceWeight w=3}:Set ↥K.positive).ncard≤(oddRegularComponents G 6).ncard := by
  let A := {w:↥K.positive | K.pieceWeight w=3}
  let J (w:↥A) : ↥(oddRegularComponents G 6) := ⟨_,(full_weight_piece_label K w.val w.property).2⟩
  have inj : Function.Injective J := by
    intro w z eq
    have same := congrArg (fun o:↥(oddRegularComponents G 6) => o.val.supp) eq
    change (originalComponentOfCutPiece G K.barrier w.val.val).supp=(originalComponentOfCutPiece G K.barrier z.val.val).supp at same
    rw [(full_weight_piece_label K w.val w.property).1,(full_weight_piece_label K z.val z.property).1] at same
    obtain ⟨v,hv⟩ := w.val.val.nonempty_supp
    have mem : v.val∈cutPieceSet G K.barrier z.val.val := same ▸ (show v.val∈cutPieceSet G K.barrier w.val.val from ⟨v,hv,rfl⟩)
    obtain ⟨a,ha,eqv⟩ := mem
    have eq' : a=v := Subtype.ext eqv
    subst a
    exact Subtype.ext (Subtype.ext ((show (G.induce K.barrierᶜ).connectedComponentMk v=w.val.val from hv).symm.trans ha))
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective J inj

#print axioms full_weight_piece_label
#print axioms full_weight_piece_count
end JSP452Audit.StarHost
