import RegularTenDegreeSelectionsCannotFinishAtDegreeEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_central_peak_bounds_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (narrow:∀i,F.n i≤7) (short:∀j,F.m j≤7) :
    highestWidth F.n F.m F.r≤(oddRegularComponents F.G 10).ncard ∧
    ∃(i:Fin F.s) (j:Fin F.t) (u v:ℕ),F.n i=6 ∧ F.m j=6 ∧ i.val+j.val=F.r ∧
      0<u ∧ 0<v ∧ u+v-1=highestWidth F.n F.m F.r ∧
      Forces F.G (forest (fun _:Fin u => F.n i)) (forest (fun _:Fin v => F.m j)) := by
  have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  obtain ⟨i,j,u,v,idx,wide,shape,up,vp,force,_⟩ := strict_ten_true_factor_peak F paid ten
  have a := narrow i
  have b := short j
  have red : F.n i=6 := by omega
  have blue : F.m j=6 := by omega
  refine ⟨?_,i,j,u,v,red,blue,idx,up,vp,wide,force⟩
  rw [red,blue] at force
  obtain ⟨S,T,dis,bill⟩ := original_uniform_factor_cut F.G 6 6 u v (by decide) (by decide) up vp cap force
  have mid := balanced_cut_le_original_odd_regular F.G 5 cap S T dis
  change originalFactorCut F.G 5 5 S T≤((oddRegularComponents F.G 10).ncard:ℤ) at mid
  change (u+v-1:ℕ)≤originalFactorCut F.G 5 5 S T at bill
  omega

theorem strict_ten_zero_odd_cannot_have_closed_four (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0)
    (C:ClosedTenFour F.G) : False := by
  obtain ⟨K,eps,_,_⟩ := strict_ten_closed_four_has_priced_menu F paid ten none C
  have hp := (strict_ten_inventory F paid ten).1
  have small := (strict_ten_excess_width_cut F paid ten (by omega)).2.1
  obtain ⟨red,blue⟩ := strict_ten_priced_regular_heads_at_most_seven F paid ten K (Or.inr ⟨eps,Or.inl small⟩)
  have c := (ten_central_peak_bounds_width F paid ten red blue).1
  omega

theorem strict_ten_zero_odd_requires_score_one (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0) :
    highestWidth F.n F.m F.r=1 ∧ minimumExposure F.G 10=3 ∧ ∃(K:TenOuterCut F.G) (M:F.G.Subgraph),
      M.IsMatching ∧ M.edgeSet.ncard=matchingEdges F.G ∧ K.score=1 ∧ (exposedFull F.G M 10).ncard=3 ∧
      45≤K.support.ncard ∧ (F.G.induce K.support).edgeSet.ncard+1=5*K.support.ncard ∧
      ∃B:K.InnerBarrier,matchingEdges F.G=B.actualRoots.ncard+matchingEdges (F.G.induce B.residual)+
        matchingEdges (F.G.induce K.remainder) ∧ K.rootDefect B.residual≤2 ∧
        ∀x∈B.residual,∀y∈K.remainder,¬F.G.Adj x y := by
  rcases strict_ten_zero_odd_alternatives F paid ten none with closed|piece
  · exact (strict_ten_zero_odd_cannot_have_closed_four F paid ten none (Classical.choice closed)).elim
  · exact piece
#print axioms ten_central_peak_bounds_width
#print axioms strict_ten_zero_odd_cannot_have_closed_four
#print axioms strict_ten_zero_odd_requires_score_one
end JSP452Audit.StarHost
