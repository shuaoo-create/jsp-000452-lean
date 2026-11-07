import TwoConsecutiveExteriorStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem half_order_of_regular_component {X:Type*} [Finite X] (Q:SimpleGraph X) (p:ℕ)
    (v:X) (reg:Nat.card (Q.neighborSet v)=2*p) : p≤Nat.card X/2 := by
  classical
  let _ := Fintype.ofFinite X
  have deg := Q.degree_lt_card_verts v
  rw [←Nat.card_eq_fintype_card,←Q.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,reg] at deg
  omega

theorem actual_eight_conservative_baseline {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (V:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (menu:SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+V.ncard)) :
    let U := componentVertices F.G (Finset.univ.map e)
    let O := F.G.induce Uᶜ
    let P := ∑i,Nat.card (e i).supp/2
    rowEnergy F.n F.m (F.r+V.ncard+P)≤(O.induce Vᶜ).edgeSet.ncard ∧
      F.G.edgeSet.ncard=O.edgeSet.ncard+8*P+4*Fintype.card I := by
  classical
  intro U O P
  let A := Subtype.val '' V
  have size : A.ncard=V.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  let part := fun i => labelledPart F.G (e i)
  let C := Finset.univ.sup part
  let Y := (F.G \ C).induce Aᶜ
  have reg (i) (v:(e i).supp) := (component_degree_eq F.G (e i) v).trans ((actual i).2 v.val v.property)
  have ranks (i:I) : matchingEdges (e i).toSimpleGraph≤Nat.card (e i).supp/2 := by
    have rank := regular_exposure_order_rank (e i).toSimpleGraph 8 (reg i)
    change 2*matchingEdges (e i).toSimpleGraph+minimumExposure (e i).toSimpleGraph 8=Nat.card (e i).supp at rank
    omega
  have next := conservative_whole_menu_row F.G e A (fun i => Nat.card (e i).supp/2) _ _
    (pad_antitone F.n F.hn) (pad_antitone F.m F.hm) (pad_positive F.n F.pn) (pad_positive F.m F.pm)
    ranks (by rw [size];exact menu) F.row
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+A.ncard+P) at next
  rw [size] at next
  let i := Classical.choice (inferInstance : Nonempty I)
  let v := (e i).nonempty_supp.to_subtype.some
  have pos := half_order_of_regular_component (e i).toSimpleGraph 4 v (reg i v)
  change 4≤Nat.card (e i).supp/2 at pos
  have one : Nat.card (e i).supp/2≤P := Finset.single_le_sum (f:=fun j => Nat.card (e j).supp/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
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
  have elements (c) (hc:c∈Finset.univ.map e) : c∈oddRegularComponents F.G 8 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hc;exact actual j
  have edges := (regular_union_at_even_degree F.G 4 (Finset.univ.map e) elements).2.1
  rw [Finset.sum_map,Finset.card_map,Finset.card_univ] at edges
  change (F.G.induce U).edgeSet.ncard=8*P+4*Fintype.card I at edges
  have sep := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at sep
  exact ⟨baseline.trans_eq edgesY,by omega⟩

#print axioms half_order_of_regular_component
#print axioms actual_eight_conservative_baseline
end JSP452Audit.StarHost
