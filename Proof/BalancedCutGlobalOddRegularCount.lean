import PortlessCutPiecesAreOriginalComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def oddRegularComponents {X : Type u} [Finite X] (G : SimpleGraph X) (D : ℕ) : Set G.ConnectedComponent :=
  {C | Odd (Nat.card C.supp) ∧ ∀v∈C.supp,Nat.card (G.neighborSet v)=D}

theorem portless_global_count {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*p) (S T : Set X) :
    (noPortOddPieces G p S T).ncard≤(oddRegularComponents G (2*p)).ncard := by
  classical
  let A := S∪T
  let N := noPortOddPieces G p S T
  let Z := oddRegularComponents G (2*p)
  let index (c:↥N) : ↥Z :=
    ⟨originalComponentOfCutPiece G A c.val,no_port_piece_properties G p cap S T c.val c.property⟩
  have inj : Function.Injective index := by
    intro c e eq
    have same : originalComponentOfCutPiece G A c.val=originalComponentOfCutPiece G A e.val :=
      congrArg (fun z:↥Z => z.val) eq
    have eqc := no_port_piece_is_global G A c.val c.property.2
    have eqe := no_port_piece_is_global G A e.val e.property.2
    have regions : cutPieceSet G A c.val=cutPieceSet G A e.val := eqc.symm.trans ((congrArg ConnectedComponent.supp same).trans eqe)
    let v := c.val.nonempty_supp.choose
    have inc : v∈c.val.supp := c.val.nonempty_supp.choose_spec
    have mem : v.val∈cutPieceSet G A e.val := regions ▸ (show v.val∈cutPieceSet G A c.val from ⟨v,inc,rfl⟩)
    obtain ⟨w,ew,eqw⟩ := mem
    have equal : w=v := Subtype.ext eqw
    rw [equal] at ew
    apply Subtype.ext
    change (G.induce Aᶜ).connectedComponentMk v=c.val at inc
    change (G.induce Aᶜ).connectedComponentMk v=e.val at ew
    exact inc.symm.trans ew
  have size := Nat.card_le_card_of_injective index inj
  simpa only [Nat.card_coe_set_eq] using size

theorem balanced_cut_le_original_odd_regular {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*p) (S T : Set X) (apart : Disjoint S T) :
    originalFactorCut G p p S T≤((oddRegularComponents G (2*p)).ncard:ℤ) := by
  exact (equal_factor_cut_le_no_ports G p cap S T apart).trans (by exact_mod_cast portless_global_count G p cap S T)

theorem strict_six_original_odd_regular (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (six : diagonal F.n F.m (F.r+2)-1=6) :
    highestWidth F.n F.m F.r≤(oddRegularComponents F.G 6).ncard := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,S,T,apart,price⟩ := strict_six_balanced_factor_cut F paid six
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have sixCap (v:F.X) : Nat.card (F.G.neighborSet v)≤2*3 := (cap v).trans_eq six
  have bound := balanced_cut_le_original_odd_regular F.G 3 sixCap S T apart
  exact_mod_cast price.trans bound

#print axioms portless_global_count
#print axioms balanced_cut_le_original_odd_regular
#print axioms strict_six_original_odd_regular
end JSP452Audit.StarHost