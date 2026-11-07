import OriginalWidthSixCarriesTheChosenFourComponentMenu
namespace JSP452Audit.StarHost.PricedTenMenu
open SimpleGraph
universe u
variable {F:StrictFamily.{u}} (A:PricedTenMenu F)
theorem bounds_when_capacity_fits (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (volume:A.K.P≤2*(F.rank-matchingEdges F.G)) :
    A.steps≤2*(F.rank-matchingEdges F.G) ∧ A.steps<A.K.P ∧ 0<rowCount F.s F.t (F.r+A.steps+A.K.P) ∧
      rowCount F.s F.t (F.r+A.steps+A.K.P)<F.rank := by
  classical
  have each (i:↥A.K.selected) : A.units i≤2*(F.rank-matchingEdges F.G) :=
    (Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (A.total.symm ▸ volume)
  have sup := Finset.sup_le (s:=Finset.univ) (fun i (_:i∈Finset.univ) => each i)
  have all : Finset.univ.sup A.units≤A.K.P := Finset.sup_le (fun i _ =>
    (Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq A.total)
  have progress := A.K.minimum_order
  have pos := (ten_conservative_forest_endpoints F paid ten A.K).1
  have adj := A.K.exposed_in_original
  have bounds := (ten_closed_endpoint_sizes F paid ten A.K).1
  let d := F.rank-matchingEdges F.G
  let Q := matchingEdges (F.G.induce A.K.support)
  change Q+F.r+2*d≤min F.s F.t at bounds
  have s := bounds.trans (Nat.min_le_left _ _)
  have t := bounds.trans (Nat.min_le_right _ _)
  change A.K.slack+A.K.eps+1≤d-A.K.slack at pos
  have fit : Q≤A.K.P := A.K.fits
  have exactSlack : A.K.slack=A.K.P-Q := rfl
  have size : F.rank=F.s+F.t-1-F.r := rfl
  change Finset.univ.sup A.units≤2*d at sup
  change A.steps≤2*d ∧ A.steps<A.K.P ∧ 0<F.s+F.t-1-(F.r+A.steps+A.K.P) ∧ F.s+F.t-1-(F.r+A.steps+A.K.P)<F.rank
  dsimp only [steps];omega

theorem prefix_when_capacity_fits (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (volume:A.K.P≤2*(F.rank-matchingEdges F.G))
    (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    H.midCut.ncard<A.steps ∧
    ((0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8) → A.steps≤H.lastCut.ncard) := by
  classical
  have price := A.outlast F paid ten A.steps A.step_menu H.upper H.first H.middle H.second
  have count := nested_removed_card H.upper H.middle
  change H.midCut.ncard=H.upper.ncard+H.middle.ncard at count
  refine ⟨by omega,?_⟩
  intro heads
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card ((F.G.induce A.K.supportᶜ).neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have tail := (H.degree_caps cap).2.2
  have size := (ten_closed_endpoint_sizes F paid ten A.K).2 H.lastCut 8 (by decide) tail heads
  exact (A.bounds_when_capacity_fits paid ten volume).1.trans size


theorem real_penultimate_when_capacity_fits (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (volume:A.K.P≤2*(F.rank-matchingEdges F.G))
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
  have short := (A.prefix_when_capacity_fits paid ten volume H).1
  obtain ⟨V,num,fee⟩ := H.exact_last_prefix A.steps short fits
  have ranks := (A.bounds_when_capacity_fits paid ten volume).2.2
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

#print axioms bounds_when_capacity_fits
#print axioms prefix_when_capacity_fits
#print axioms real_penultimate_when_capacity_fits
end JSP452Audit.StarHost.PricedTenMenu
