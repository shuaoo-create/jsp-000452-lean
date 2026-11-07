import AConservativeMenuMustOutlastTheFirstTwoStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure PricedTenMenu (F:StrictFamily.{u}) where
  K : TenRegularBudget F.G
  units : (i:↥K.selected) → ℕ
  upper : ∀i,matchingEdges i.val.toSimpleGraph≤units i
  total : (∑i,units i)=K.P
  saving : ℕ
  shortStage : ∃A:Set ↥K.support,CompleteDegreeStage (F.G.induce K.support) 10 A ∧ A.ncard+saving≤K.P
  heightCost : highestWidth F.n F.m F.r≤5*K.eps
  stageCost : highestWidth F.n F.m F.r+(38+2*highestWidth F.n F.m F.r)/7≤5*K.eps+saving

theorem priced_ten_single_component (F:StrictFamily.{u}) (c:F.G.ConnectedComponent)
    (reg:∀x∈c.supp,Nat.card (F.G.neighborSet x)=10) (imp:2*matchingEdges c.toSimpleGraph<Nat.card c.supp)
    (one:highestWidth F.n F.m F.r=1) :
    ∃A:PricedTenMenu F,A.K.selected={c} ∧ A.K.P=(Nat.card c.supp-1)/2 := by
  classical
  obtain ⟨K,selected,half⟩ := TenRegularBudget.from_one_component c reg imp
  have card : K.selected.card=1 := by rw [selected];simp
  have sum : (∑_i:↥K.selected,K.P)=K.P := by simp [card]
  have fit (i:↥K.selected) : matchingEdges i.val.toSimpleGraph≤K.P := by
    have atC (x:F.G.ConnectedComponent) (mem:x∈K.selected) : x=c := by rw [selected,Finset.mem_singleton] at mem;exact mem
    rw [atC _ i.property,half];omega
  have size := K.order
  have sup : K.support=c.supp := by rw [TenRegularBudget.support,selected];ext x;exact Finset.mem_singleton
  change K.support.ncard=_ at size
  rw [sup] at size
  have n : Nat.card c.supp=2*K.P+K.eps := size
  have pos := K.positive
  have small := K.small
  by_cases eps:K.eps=1
  · have odd : Odd (Nat.card c.supp) := ⟨K.P,by omega⟩
    have good (d) (mem:d∈K.selected) : d∈oddRegularComponents F.G 10 := by
      rw [selected,Finset.mem_singleton] at mem;subst d;exact ⟨odd,reg⟩
    obtain ⟨S,stage,b⟩ := short_stages_on_odd_regular_components F.G 5 (by decide) K.selected good
    have ss : (∑i∈K.selected,Nat.card i.supp/2)=Nat.card c.supp/2 := by rw [selected,Finset.sum_singleton]
    rw [ss,card] at b
    refine ⟨⟨K,fun _ => K.P,fit,sum,1,⟨S,stage,?_⟩,by omega,by omega⟩,selected,half⟩
    change S.ncard+1≤K.P
    omega
  · obtain ⟨S,stage⟩ := complete_degree_stage_exists (F.G.induce K.support) 10
    have full (x:↥K.support) := (closed_set_degree_eq F.G K.support K.support_closed x).trans (K.support_full x.val x.property)
    have lim := full_independent_set_le_matching (F.G.induce K.support) 10 (by decide) (fun x => (full x).le) S stage.1 stage.2.1
    have max : matchingEdges (F.G.induce K.support)≤K.P := K.fits
    exact ⟨⟨K,fun _ => K.P,fit,sum,0,⟨S,stage,by omega⟩,by omega,by omega⟩,selected,half⟩

theorem priced_ten_two_odd_components (F:StrictFamily.{u}) (T:Finset F.G.ConnectedComponent)
    (two:T.card=2) (actual:∀c∈T,c∈oddRegularComponents F.G 10) (small:highestWidth F.n F.m F.r≤5) :
    ∃A:PricedTenMenu F,A.K.selected=T ∧ A.K.eps=2 := by
  classical
  obtain ⟨K,sel,half,eps⟩ := TenRegularBudget.from_two_odd_components T two actual
  let z (i:↥K.selected) := Nat.card i.val.supp/2
  have total : (∑i,z i)=K.P := by
    have v := Finset.sum_coe_sort K.selected (fun c => Nat.card c.supp/2)
    change (∑i,z i)=(∑c∈K.selected,Nat.card c.supp/2) at v
    rw [v,sel,half]
  have rank (i:↥K.selected) : matchingEdges i.val.toSimpleGraph≤z i := by
    have room := matching_edges_fit_order i.val.toSimpleGraph
    change 2*matchingEdges i.val.toSimpleGraph≤Nat.card i.val.supp at room
    dsimp only [z];omega
  have good (c) (hc:c∈K.selected) := actual c (sel ▸ hc)
  obtain ⟨S,stage,bound⟩ := short_stages_on_odd_regular_components F.G 5 (by decide) K.selected good
  have card : K.selected.card=2 := sel ▸ two
  have s : (∑c∈K.selected,Nat.card c.supp/2)=K.P := by rw [sel,half]
  change S.ncard+K.selected.card≤_ at bound
  rw [s,card] at bound
  exact ⟨⟨K,z,rank,total,2,⟨S,stage,bound⟩,by omega,by omega⟩,sel,eps⟩

#print axioms priced_ten_single_component
#print axioms priced_ten_two_odd_components
end JSP452Audit.StarHost
