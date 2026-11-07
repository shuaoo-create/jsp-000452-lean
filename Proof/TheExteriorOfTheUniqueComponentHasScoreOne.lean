import AWidthLargerThanTheOddComponentCountForcesFourAgainstEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_unique_component_exact_scores (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (one:(oddRegularComponents F.G 10).ncard=1)
    (J:F.G.ConnectedComponent) (mem:J∈oddRegularComponents F.G 10) :
    let O := F.G.induce J.suppᶜ
    let C := J.toSimpleGraph
    (oddRegularComponents O 10).ncard=0 ∧ minimumExposure C 10=1 ∧ minimumExposure O 10=3 ∧
      Nat.card J.supp=2*matchingEdges C+1 ∧
      ∃(K:TenOuterCut O) (R:SimpleGraph J.supp) (B:SimpleGraph ↥(J.suppᶜ:Set F.X)),
        K.score=1 ∧ R≤C ∧ B≤O ∧ uniformColourError C R 3 7=1 ∧ uniformColourError O B 3 7=1 := by
  intro O C
  have cases := strict_ten_exactly_two_remaining_sources F paid ten
  have two : highestWidth F.n F.m F.r=2 := by omega
  have four : minimumExposure F.G 10=4 := by omega
  have none : (oddRegularComponents O 10).ncard=0 := no_odd_regular_after_unique_component F.G 10 J mem one
  obtain ⟨sum,either,R,subR,low⟩ := regular_component_colour_and_exposure F.G J mem four
  change minimumExposure C 10+minimumExposure O 10=4 at sum
  change minimumExposure C 10=1 ∨ minimumExposure C 10=3 at either
  change uniformColourError C R 3 7≤1 at low
  have capO (x:↥(J.suppᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have reg (v:J.supp) : Nat.card (C.neighborSet v)=10 := (component_degree_eq F.G J v).trans (mem.2 v.val v.property)
  obtain ⟨B,S,T,subB,dis,score⟩ := uniform_cut_colour_witness O 3 7 capO
  obtain ⟨_,u,v,pos,live,wide,force⟩ := ten_excess_width_forces_four_eight F paid ten (by omega)
  have both := two_summands_force_error_two C O (fun x => (reg x).le) capO u v pos live (wide.trans two)
    (forces_of_iso (component_exterior_iso F.G J).symm force) R B subR subB
  obtain ⟨e,m,endpt,mid⟩ := three_prices_of_ten_cut O capO S T dis
  have value : originalFactorCut O 3 7 S T=1 := by omega
  have roots : S.ncard=T.ncard+1 := by omega
  let K : TenOuterCut O := ⟨S,T,dis,roots,1,by decide,by decide,value⟩
  have order := regular_exposure_order_rank C 10 reg
  change 2*matchingEdges C+minimumExposure C 10=Nat.card J.supp at order
  exact ⟨none,by omega,by omega,by omega,K,R,B,rfl,subR,subB,by omega,by omega⟩

theorem strict_ten_unique_component_exterior_partition (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (one:(oddRegularComponents F.G 10).ncard=1)
    (J:F.G.ConnectedComponent) (mem:J∈oddRegularComponents F.G 10) :
    let O := F.G.induce J.suppᶜ
    ∃(K:TenOuterCut O) (M:O.Subgraph) (B:K.InnerBarrier),K.score=1 ∧
      M.IsMatching ∧ M.edgeSet.ncard=matchingEdges O ∧ (exposedFull O M 10).ncard=3 ∧
      45≤K.support.ncard ∧ (O.induce K.support).edgeSet.ncard+1=5*K.support.ncard ∧
      matchingEdges O=B.actualRoots.ncard+matchingEdges (O.induce B.residual)+matchingEdges (O.induce K.remainder) ∧
      K.rootDefect B.residual≤2 ∧ ∀x∈B.residual,∀y∈K.remainder,¬O.Adj x y := by
  intro O
  obtain ⟨none,_,rho,_,K,_,_,score,_⟩ := strict_ten_unique_component_exact_scores F paid ten one J mem
  have cap (x:↥(J.suppᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  obtain ⟨M,hm,best,opt⟩ := minimumExposure_attained O 10
  change minimumExposure O 10=3 at rho
  have sat : (exposedFull O M 10).ncard=K.score+2 := by omega
  obtain ⟨B⟩ := K.inner_barrier_exists cap M hm sat
  have shape := K.orders_and_edges_by_score cap none
  have whole := (B.exact_region_matching_partition cap M hm best sat).2.1
  have defic := B.residual_original_defect cap none
  rcases shape with ⟨_,size,price⟩|⟨wrong,_⟩
  · exact ⟨K,M,B,score,hm,best,by omega,size,price,whole,defic.1.trans defic.2,B.physical_partition.2.2.2.2⟩
  · omega

#print axioms strict_ten_unique_component_exact_scores
#print axioms strict_ten_unique_component_exterior_partition
end JSP452Audit.StarHost
