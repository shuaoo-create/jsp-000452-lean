import TenDegreeRegularMenusExcludeNineLeafHeads
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_regular_small_heads_fit_two_deficits (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6) :
    (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) ∧ A.K.P≤2*(F.rank-matchingEdges F.G) ∧
    (∀i,A.units i≤2*(F.rank-matchingEdges F.G)) := by
  obtain ⟨red,blue⟩ := strict_ten_no_nine_leaf_with_regular_menu F paid ten A cost
  have fee := ten_regular_exterior_slot_deficit F paid ten A.K 3 (fun i => by have := red i;omega) (fun j => by have := blue j;omega)
  have sizes := ten_regular_slot_volume A.K 3
  have bound : A.K.P≤2*(F.rank-matchingEdges F.G) := by omega
  refine ⟨red,blue,bound,fun i => ?_⟩
  exact (Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (A.total ▸ bound)

theorem priced_ten_even_imperfect_component (F:StrictFamily.{u}) (c:F.G.ConnectedComponent)
    (reg:∀x∈c.supp,Nat.card (F.G.neighborSet x)=10) (even:Even (Nat.card c.supp))
    (imp:2*matchingEdges c.toSimpleGraph<Nat.card c.supp) (height:highestWidth F.n F.m F.r≤4) :
    ∃A:PricedTenMenu F,A.K.selected={c} ∧ A.K.eps=2 := by
  classical
  obtain ⟨K,sel,half⟩ := TenRegularBudget.from_one_component c reg imp
  have card : K.selected.card=1 := by rw [sel];simp
  have total : (∑_i:↥K.selected,K.P)=K.P := by simp [card]
  have fit (i:↥K.selected) : matchingEdges i.val.toSimpleGraph≤K.P := by
    have same (x:F.G.ConnectedComponent) (m:x∈K.selected) : x=c := by rw [sel,Finset.mem_singleton] at m;exact m
    rw [same _ i.property,half];omega
  have support : K.support=c.supp := by rw [TenRegularBudget.support,sel];ext x;exact Finset.mem_singleton
  have size : K.support.ncard=2*K.P+K.eps := K.order
  rw [support] at size
  have natOrder : Nat.card c.supp=2*K.P+K.eps := size
  obtain ⟨j,eq⟩ := even
  have pos := K.positive
  have sm := K.small
  have eps : K.eps=2 := by omega
  obtain ⟨S,stage⟩ := complete_degree_stage_exists (F.G.induce K.support) 10
  have full (x:↥K.support) := (closed_set_degree_eq F.G K.support K.support_closed x).trans (K.support_full x.val x.property)
  have lim := full_independent_set_le_matching (F.G.induce K.support) 10 (by decide) (fun x => (full x).le) S stage.1 stage.2.1
  have rank : matchingEdges (F.G.induce K.support)≤K.P := K.fits
  exact ⟨⟨K,fun _ => K.P,fit,total,0,⟨S,stage,by omega⟩,by omega,by omega⟩,sel,eps⟩

theorem strict_ten_closed_four_has_priced_menu (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0) (C:ClosedTenFour F.G) :
    ∃A:PricedTenMenu F,A.K.eps=2 ∧ 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 ∧
    (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) ∧ A.K.P≤2*(F.rank-matchingEdges F.G) := by
  obtain ⟨c,_,reg,gap⟩ := C.actual_imperfect_component none
  have h : highestWidth F.n F.m F.r≤2 := by
    have hp := (strict_ten_inventory F paid ten).1
    exact (strict_ten_excess_width_cut F paid ten (by omega)).2.1
  have even : Even (Nat.card c.supp) := by rw [Nat.even_iff];omega
  obtain ⟨A,_,eps⟩ := priced_ten_even_imperfect_component F c reg even (by omega) (by omega)
  have numeric : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by omega
  obtain ⟨red,blue,volume,_⟩ := ten_regular_small_heads_fit_two_deficits F paid ten A numeric
  exact ⟨A,eps,numeric,red,blue,volume⟩

#print axioms ten_regular_small_heads_fit_two_deficits
#print axioms priced_ten_even_imperfect_component
#print axioms strict_ten_closed_four_has_priced_menu
end JSP452Audit.StarHost
