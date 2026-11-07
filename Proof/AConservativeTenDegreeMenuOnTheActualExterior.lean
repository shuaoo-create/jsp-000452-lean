import ActualTenToNineStageOnTheOriginalHost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem TenRegularBudget.minimum_order {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenRegularBudget G) : 5≤K.P := by
  have size : K.support.ncard=2*K.P+K.eps := K.order
  have some := K.positive
  have small := K.small
  obtain ⟨v,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<K.support.ncard by omega)
  let x : ↥K.support := ⟨v,mem⟩
  have deg := (closed_set_degree_eq G K.support K.support_closed x).trans (K.support_full v mem)
  classical
  let _ := Fintype.ofFinite ↥K.support
  have many := (G.induce K.support).degree_lt_card_verts x
  rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card] at many
  change Nat.card ((G.induce K.support).neighborSet x)<K.support.ncard at many
  omega

theorem actual_ten_conservative_baseline {I:Type*} [Fintype I] [DecidableEq I] 
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (K:TenRegularBudget F.G) (e:I↪F.G.ConnectedComponent) (sel:Finset.univ.map e=K.selected)
    (z:I→ℕ) (ranks:∀i,matchingEdges (e i).toSimpleGraph≤z i) (budget:(∑i,z i)=K.P)
    (V:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (menu:SplitCapacities z (F.r+V.ncard)) :
    let U := componentVertices F.G (Finset.univ.map e)
    let O := F.G.induce Uᶜ
    let P := K.P
    rowEnergy F.n F.m (F.r+V.ncard+P)≤(O.induce Vᶜ).edgeSet.ncard ∧
      F.G.edgeSet.ncard=O.edgeSet.ncard+10*P+5*K.eps := by
  classical
  intro U O P
  let A := Subtype.val '' V
  have size : A.ncard=V.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  let part := fun i => labelledPart F.G (e i)
  let C := Finset.univ.sup part
  let Y := (F.G \ C).induce Aᶜ
  have next := conservative_whole_menu_row F.G e A z _ _
    (pad_antitone F.n F.hn) (pad_antitone F.m F.hm) (pad_positive F.n F.pn) (pad_positive F.m F.pm)
    ranks (by rw [size];exact menu) F.row
  rw [budget] at next
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+A.ncard+P) at next
  rw [size] at next
  have pos := K.minimum_order
  have live := F.live
  have smaller : rowCount F.s F.t (F.r+V.ncard+P)<F.rank := by
    change rowCount F.s F.t (F.r+V.ncard+P)<rowCount F.s F.t F.r;dsimp [rowCount] at live ⊢;omega
  have baseline := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y _ next smaller
  have ids := component_edges_on_labels F.G e Finset.univ
  change C=F.G \ eraseInternal F.G U at ids
  have erased : F.G \ C=eraseInternal F.G U := by
    rw [ids];ext x y
    change (F.G.Adj x y ∧ ¬(F.G.Adj x y ∧ ¬(eraseInternal F.G U).Adj x y)) ↔ (eraseInternal F.G U).Adj x y
    have sub : (eraseInternal F.G U).Adj x y → F.G.Adj x y := fun edge => edge.1
    tauto
  have closed := component_vertices_closed F.G (Finset.univ.map e)
  have edgesY : Y.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard := by
    change ((F.G \ C).induce Aᶜ).edgeSet.ncard=_
    rw [erased];exact erased_closed_exterior_edges F.G U closed V
  have eqU : U=K.support := congrArg (componentVertices F.G) sel
  have edges := K.fee
  rw [←eqU] at edges
  change (F.G.induce U).edgeSet.ncard=10*P+5*K.eps at edges
  have sep := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at sep
  exact ⟨baseline.trans_eq edgesY,by omega⟩


#print axioms TenRegularBudget.minimum_order
#print axioms actual_ten_conservative_baseline
end JSP452Audit.StarHost
