import TheOriginalUniformCutAndItsTwoColourError
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def component_exterior_iso {X:Type u} (G:SimpleGraph X) (J:G.ConnectedComponent) :
    (J.toSimpleGraph⊕g G.induce J.suppᶜ) ≃g G :=
  (regionSumIso G Set.univ J.supp J.suppᶜ (Set.union_compl_self _) disjoint_compl_right
    (fun x hx y hy edge => hy ((J.mem_supp_congr_adj edge).mp hx))).trans (induceUnivIso G)

theorem no_odd_regular_after_unique_component {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (J:G.ConnectedComponent) (mem:J∈oddRegularComponents G D) (one:(oddRegularComponents G D).ncard=1) :
    (oddRegularComponents (G.induce J.suppᶜ) D).ncard=0 := by
  let O := G.induce J.suppᶜ
  have unique : ∀c∈oddRegularComponents G D,c=J := by
    obtain ⟨w,eq⟩ := Set.ncard_eq_one.mp one
    have j : J=w := Set.mem_singleton_iff.mp (eq ▸ mem)
    intro c hc;exact (Set.mem_singleton_iff.mp (eq ▸ hc)).trans j.symm
  have closed (x) (hx:x∈J.suppᶜ) (y) (edge:G.Adj x y) : y∈J.suppᶜ :=
    fun hy => hx ((J.mem_supp_congr_adj edge).mpr hy)
  by_contra! positive
  obtain ⟨C,m⟩ := (Set.ncard_pos (Set.toFinite _)).mp (Nat.pos_of_ne_zero positive)
  let Q := cutPieceSet G J.supp C
  let B := originalComponentOfCutPiece G J.supp C
  have cut : crossCount G Q J.supp=0 := crossCount_of_no_edges _ _ _
    (fun x hx y hy adj => cut_piece_outside G J.supp C hx ((J.mem_supp_congr_adj adj).mpr hy))
  have actual : B.supp=Q := no_port_piece_is_global G J.supp C cut
  have order : Nat.card C.supp=Q.ncard := Nat.card_congr (cutPieceVertexEquiv G J.supp C)
  have hit : B∈oddRegularComponents G D := by
    have same : Nat.card B.supp=Nat.card C.supp := by change B.supp.ncard=_;rw [actual,order]
    refine ⟨same.symm ▸ m.1,?_⟩
    intro x hx
    rw [actual] at hx
    obtain ⟨v,cv,rfl⟩ := hx
    exact (closed_set_degree_eq G J.suppᶜ closed v).symm.trans (m.2 v cv)
  have same := unique B hit
  have impossible : J.supp=Q := same ▸ actual
  obtain ⟨x,hx⟩ := J.nonempty_supp
  have qx : x∈Q := (congrArg (fun A:Set X => x∈A) impossible).mp hx
  exact cut_piece_outside G J.supp C qx hx

theorem regular_component_colour_and_exposure {X:Type u} [Finite X] (G:SimpleGraph X)
    (J:G.ConnectedComponent) (full:J∈oddRegularComponents G 10) (four:minimumExposure G 10=4) :
    let O := G.induce J.suppᶜ
    let C := J.toSimpleGraph
    minimumExposure C 10+minimumExposure O 10=4 ∧
    (minimumExposure C 10=1 ∨ minimumExposure C 10=3) ∧
    ∃R:SimpleGraph J.supp,R≤C ∧ uniformColourError C R 3 7≤1 := by
  classical
  intro O C
  have join := minimumExposure_iso (component_exterior_iso G J) 10
  rw [minimumExposure_sumGraph,four] at join
  change minimumExposure C 10+minimumExposure O 10=4 at join
  have reg (v:J.supp) : Nat.card (C.neighborSet v)=10 := (component_degree_eq G J v).trans (full.2 v.val v.property)
  have balance := regular_exposure_order_rank C 10 reg
  change 2*matchingEdges C+minimumExposure C 10=Nat.card J.supp at balance
  obtain ⟨k,odd⟩ := full.1
  have either : minimumExposure C 10=1 ∨ minimumExposure C 10=3 := by omega
  have tiny : (oddRegularComponents C 10).ncard≤1 := by
    have linked := J.connected_toSimpleGraph
    let _ : Subsingleton C.ConnectedComponent := by
      constructor;intro p q
      obtain ⟨x,hx⟩ := p.nonempty_supp
      obtain ⟨y,hy⟩ := q.nonempty_supp
      exact (show C.connectedComponentMk x=p from hx).symm.trans
        ((ConnectedComponent.sound (linked.preconnected x y)).trans (show C.connectedComponentMk y=q from hy))
    exact Set.ncard_le_one (s:=oddRegularComponents C 10) |>.mpr (fun x _ y _ => Subsingleton.elim x y)
  obtain ⟨R,S,T,sub,dis,eq⟩ := uniform_cut_colour_witness C 3 7 (fun x => (reg x).le)
  obtain ⟨e,m,ep,mid⟩ := three_prices_of_ten_cut C (fun x => (reg x).le) S T dis
  exact ⟨join,either,R,sub,by omega⟩

#print axioms component_exterior_iso
#print axioms no_odd_regular_after_unique_component
#print axioms regular_component_colour_and_exposure
end JSP452Audit.StarHost
