import TwoHighestColumnsDeletionLoss
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_menu_history_price {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (six:diagonal F.n F.m (F.r+2)-1=6)
    (e:I ↪ F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 6)
    (k:ℕ) (menu:SplitCapacities (fun i => matchingEdges (e i).toSimpleGraph) (F.r+k))
    (H:SixFiveFourHistory (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ)) (fit:k≤H.fourCut.ncard) :
    let P := ∑i,matchingEdges (e i).toSimpleGraph
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 6
    P+3*Fintype.card I+1+min k H.fiveCut.ncard+min k H.six.ncard≤k+L+h ∧
    3*Fintype.card I+1+min k H.fiveCut.ncard+min k H.six.ncard≤2*k+h := by
  intro P h L
  let U := componentVertices F.G (Finset.univ.map e)
  let O := F.G.induce Uᶜ
  let z := fun i => matchingEdges (e i).toSimpleGraph
  obtain ⟨V,num,prefixPrice⟩ := H.stage_prefix_price k fit
  let A := Subtype.val '' V
  have card : A.ncard=k := (Set.ncard_image_of_injective _ Subtype.val_injective).trans num
  let part := fun i => labelledPart F.G (e i)
  let C := Finset.univ.sup part
  let Y := (F.G \ C).induce Aᶜ
  have shifted := original_whole_menu_row F.G e A _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) (by rw [card];exact menu) F.row
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+A.ncard+P) at shifted
  rw [card] at shifted
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
  have sep := intact_components_plus_exterior F.G U closed
  have elems (c) (hc:c∈Finset.univ.map e) : c∈oddRegularComponents F.G 6 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hc;exact actual i
  have edgeC := (strict_six_chosen_component_columns F paid six (Finset.univ.map e) elems).2.1
  have rank := (component_union_accounts F.G (Finset.univ.map e)).2.1
  rw [Finset.sum_map] at rank
  change matchingEdges (F.G.induce U)=P at rank
  change (F.G.induce U).edgeSet.ncard=6*matchingEdges (F.G.induce U)+3*(Finset.univ.map e).card at edgeC
  rw [rank,Finset.card_map,Finset.card_univ] at edgeC
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at sep
  change O.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+4*k+min k H.fiveCut.ncard+min k H.six.ncard at prefixPrice
  have saved : F.G.edgeSet.ncard=Y.edgeSet.ncard+6*P+3*Fintype.card I+4*k+min k H.fiveCut.ncard+min k H.six.ncard := by omega
  let i := Classical.choice (inferInstance : Nonempty I)
  have one := (strict_six_true_component_capacity F paid six (e i) (actual i)).1
  have sum : matchingEdges (e i).toSimpleGraph≤P := Finset.single_le_sum (f:=z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have smaller : rowCount F.s F.t (F.r+k+P)<F.rank := by
    have live := F.live
    change rowCount F.s F.t (F.r+k+P)<rowCount F.s F.t F.r
    dsimp [rowCount] at live ⊢;omega
  have lower := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k+P) shifted smaller
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have price5 := six_prefix_two_columns F.hs F.ht F.n F.m F.hn F.hm top (k+P)
  have price6 := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r (k+P) 6 top.le
  rw [show 6+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price6
  rw [←Nat.add_assoc] at price5 price6
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+5*(k+P)+L+h at price5
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+6*(k+P)+h at price6
  have original := (minimal_rank_exact_source F paid).2.1
  clear * - lower saved price5 price6 original
  constructor <;> omega

#print axioms strict_six_menu_history_price
end JSP452Audit.StarHost
