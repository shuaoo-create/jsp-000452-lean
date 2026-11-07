import FourActualComponentsExcludeTheNineLeafHead
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_width_six_four_component_source (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (six:highestWidth F.n F.m F.r=6) :
    (oddRegularComponents F.G 10).ncard=6 ∧ minimumExposure F.G 10=6 ∧
    ∃A:PricedTenMenu F,A.K.eps=2 ∧ 21≤A.K.P ∧ 1≤A.K.slack ∧ A.steps+5≤A.K.P ∧
      (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) ∧ A.K.P≤2*(F.rank-matchingEdges F.G) := by
  have counts := strict_ten_remaining_width_counts F paid ten
  change (highestWidth F.n F.m F.r=1 ∧ _) ∨ (highestWidth F.n F.m F.r=2 ∧ _) ∨ _ at counts
  rcases counts with x|x|⟨_,count,rho⟩
  · omega
  · omega
  · obtain ⟨A,eps,size,slack,spare⟩ := ten_choose_four_regular_blocks F six (by omega)
    obtain ⟨red,blue⟩ := width_six_regular_lists_at_most_eight F paid ten A six eps
    exact ⟨count,rho,A,eps,size,slack,spare,red,blue,width_six_conservative_capacity F paid ten A six eps slack⟩
#print axioms strict_ten_width_six_four_component_source
end JSP452Audit.StarHost
