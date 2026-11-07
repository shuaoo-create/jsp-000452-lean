import FourPositivePiecesAtSeven
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem actual_positive_piece_boundary {X:Type u} [Finite X] {G:SimpleGraph X} {D:ℕ}
    (K:DegreeRegion G D) (c:↥K.positive) :
    let U := cutPieceSet G K.barrier c.val
    (crossCount G U Uᶜ:ℤ)+2*K.pieceWeight c=(D:ℤ) := by
  intro U
  let e : c.val.toSimpleGraph ≃g G.induce U := {
    toEquiv := cutPieceVertexEquiv G K.barrier c.val
    map_rel_iff' := Iff.rfl }
  have order := factorCritical_order_rank c.val.toSimpleGraph (K.critical c.val).2 c.val.nonempty_supp.to_subtype.some
  have size : U.ncard=2*K.pieceCapacity c+1 := (Nat.card_congr e.toEquiv).symm.trans order
  have full (x) (hx:x∈U) : Nat.card (G.neighborSet x)=D := by
    obtain ⟨v,hv,rfl⟩ := hx;exact K.full c.property.1 ⟨v,hv⟩
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U D full,size] at hand
  have edges : c.val.toSimpleGraph.edgeSet.ncard=(G.induce U).edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  have wt : K.pieceWeight c=(c.val.toSimpleGraph.edgeSet.ncard:ℤ)-(D:ℤ)*(K.pieceCapacity c:ℤ) := rfl
  rw [wt,edges]
  have signed : (D:ℤ)*(2*(K.pieceCapacity c:ℤ)+1)=2*((G.induce U).edgeSet.ncard:ℤ)+(crossCount G U Uᶜ:ℤ) := by exact_mod_cast hand
  rw [mul_add,mul_one,←mul_assoc,mul_comm (D:ℤ) 2,mul_assoc] at signed
  omega

theorem strict_seven_piece_has_one_or_three_ports (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (c:↥K.positive) :
    let U := cutPieceSet F.G K.barrier c.val
    (K.pieceWeight c=3 ∧ crossCount F.G U Uᶜ=1) ∨ (K.pieceWeight c=2 ∧ crossCount F.G U Uᶜ=3) := by
  intro U
  have bounds := (strict_seven_four_positive_pieces F paid seven K).2.2.2 c
  have eq := actual_positive_piece_boundary K c
  change (crossCount F.G U Uᶜ:ℤ)+2*K.pieceWeight c=7 at eq
  by_cases top:K.pieceWeight c=3 <;> omega

#print axioms actual_positive_piece_boundary
#print axioms strict_seven_piece_has_one_or_three_ports
end JSP452Audit.StarHost
