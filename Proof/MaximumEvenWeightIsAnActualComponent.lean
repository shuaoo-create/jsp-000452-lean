import PhysicalHalfCapSpareVertices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem even_full_weight_label {X:Type u} [Finite X] {G:SimpleGraph X} (p:ℕ) (K:DegreeRegion G (2*p))
    (w:↥K.positive) (weight:K.pieceWeight w=(p:ℤ)) :
    let c := w.val
    let O := originalComponentOfCutPiece G K.barrier c
    O.supp=cutPieceSet G K.barrier c ∧ O∈oddRegularComponents G (2*p) := by
  intro c O
  let U := cutPieceSet G K.barrier c
  have boundary := actual_positive_piece_boundary K w
  change (crossCount G U Uᶜ:ℤ)+2*K.pieceWeight w=((2*p:ℕ):ℤ) at boundary
  have zero : crossCount G U Uᶜ=0 := by omega
  have cut : crossCount G U K.barrier=0 := crossCount_of_no_edges G U K.barrier (fun _ hx _ hy =>
    no_edge_when_port_zero G zero hx (fun h => cut_piece_outside G K.barrier c h hy))
  have labels := no_port_piece_is_global G K.barrier c cut
  change O.supp=U at labels
  have eq : Nat.card c.supp=U.ncard := Nat.card_congr (cutPieceVertexEquiv G K.barrier c)
  refine ⟨labels,?_,?_⟩
  · rw [labels];change Odd U.ncard;exact eq ▸ (K.critical c).1
  · intro x hx;obtain ⟨v,hv,rfl⟩ := labels ▸ hx
    exact K.full w.property.1 ⟨v,hv⟩

theorem even_full_weight_count {X:Type u} [Finite X] {G:SimpleGraph X} (p:ℕ) (K:DegreeRegion G (2*p)) :
    ({w:↥K.positive | K.pieceWeight w=(p:ℤ)}:Set ↥K.positive).ncard≤(oddRegularComponents G (2*p)).ncard := by
  let A := {w:↥K.positive | K.pieceWeight w=(p:ℤ)}
  let J (w:↥A) : ↥(oddRegularComponents G (2*p)) := ⟨_,(even_full_weight_label p K w.val w.property).2⟩
  have inj : Function.Injective J := by
    intro w z eq
    have same := congrArg (fun o:↥(oddRegularComponents G (2*p)) => o.val.supp) eq
    change (originalComponentOfCutPiece G K.barrier w.val.val).supp=(originalComponentOfCutPiece G K.barrier z.val.val).supp at same
    rw [(even_full_weight_label p K w.val w.property).1,(even_full_weight_label p K z.val z.property).1] at same
    obtain ⟨v,hv⟩ := w.val.val.nonempty_supp
    have mem : v.val∈cutPieceSet G K.barrier z.val.val := same ▸ (show v.val∈cutPieceSet G K.barrier w.val.val from ⟨v,hv,rfl⟩)
    obtain ⟨a,ha,eqv⟩ := mem
    have eq' : a=v := Subtype.ext eqv
    subst a
    exact Subtype.ext (Subtype.ext ((show (G.induce K.barrierᶜ).connectedComponentMk v=w.val.val from hv).symm.trans ha))
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective J inj

#print axioms even_full_weight_label
#print axioms even_full_weight_count
end JSP452Audit.StarHost
