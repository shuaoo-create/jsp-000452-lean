import ThePaidRowOnTheRealExteriorVertexSet
namespace JSP452Audit.StarHost.PricedTenMenu
open SimpleGraph
universe u
variable {F:StrictFamily.{u}} (A:PricedTenMenu F)

theorem physical_successor_row (V:Set ↥(A.K.supportᶜ:Set F.X)) (size:V.ncard=A.steps) :
    ForcingRow ((F.G.induce A.K.supportᶜ).induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+A.steps+A.K.P) := by
  classical
  let e : ↥A.K.selected ↪ F.G.ConnectedComponent := Function.Embedding.subtype _
  have sel : Finset.univ.map e=A.K.selected := by
    ext c
    constructor
    · intro m;obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp m;exact v.property
    · intro m;exact Finset.mem_map.mpr ⟨⟨c,m⟩,Finset.mem_univ _,rfl⟩
  let T := Subtype.val '' V
  have count : T.ncard=A.steps := (Set.ncard_image_of_injective _ Subtype.val_injective).trans size
  let C := Finset.univ.sup (fun i => labelledPart F.G (e i))
  have next := conservative_whole_menu_row F.G e T A.units _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) A.upper (by rw [count];exact A.step_menu) F.row
  change ForcingRow ((F.G \ C).induce Tᶜ) F.s F.t _ _ (F.r+T.ncard+∑i,A.units i) at next
  rw [count,A.total] at next
  have ids := component_edges_on_labels F.G e Finset.univ
  rw [sel] at ids
  change C=F.G \ eraseInternal F.G A.K.support at ids
  have erased : F.G \ C=eraseInternal F.G A.K.support := by
    rw [ids];ext x y
    change (F.G.Adj x y ∧ ¬(F.G.Adj x y ∧ ¬(eraseInternal F.G A.K.support).Adj x y)) ↔ (eraseInternal F.G A.K.support).Adj x y
    have sub : (eraseInternal F.G A.K.support).Adj x y → F.G.Adj x y := fun edge => edge.1
    tauto
  rw [erased] at next
  exact erased_closed_exterior_forcing_row F.G A.K.support A.K.support_closed V _ _
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) next

theorem penultimate_original_successor (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6)
    (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) (fits:A.steps≤H.lastCut.ncard) :
    let O := F.G.induce A.K.supportᶜ
    let r' := F.r+A.steps+A.K.P
    0<rowCount F.s F.t r' ∧ rowCount F.s F.t r'<F.rank ∧
    ∃V:Set ↥(A.K.supportᶜ:Set F.X),V.ncard=A.steps ∧
      ForcingRow (O.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) r' ∧
      rowEnergy F.n F.m r'≤(O.induce Vᶜ).edgeSet.ncard ∧
      F.G.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+8*A.steps+H.upper.ncard+H.midCut.ncard+10*A.K.P+5*A.K.eps ∧
      2*A.K.P+5*A.K.eps+1+H.upper.ncard+H.midCut.ncard≤
        widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r := by
  intro O r'
  have short := (A.physical_stage_prefix paid ten cost H).1
  obtain ⟨V,num,fee⟩ := H.exact_last_prefix A.steps short fits
  have ranks := (A.step_bounds paid ten cost).2.2
  have next := A.physical_successor_row V num
  change ForcingRow (O.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) r' at next
  have baseline := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (O.induce Vᶜ) r' next ranks.2
  have original := intact_components_plus_exterior F.G A.K.support A.K.support_closed
  change F.G.edgeSet.ncard=(F.G.induce A.K.support).edgeSet.ncard+O.edgeSet.ncard at original
  rw [A.K.fee] at original
  change O.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+8*A.steps+H.upper.ncard+H.midCut.ncard at fee
  have tax := ten_prefix_three_columns F.hs F.ht F.n F.m F.hn F.hm (r:=F.r) (by omega) (A.steps+A.K.P)
  rw [←Nat.add_assoc] at tax
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m r'+8*(A.steps+A.K.P)+
    widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r at tax
  have old := F.strict
  exact ⟨ranks.1,ranks.2,V,num,next,baseline,by omega,by omega⟩
#print axioms physical_successor_row
#print axioms penultimate_original_successor
end JSP452Audit.StarHost.PricedTenMenu
