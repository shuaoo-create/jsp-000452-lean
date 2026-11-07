import AnActualNonperfectComponentOfTheClosedTenDegreeRegion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure TenRegularBudget {X:Type u} [Finite X] (G:SimpleGraph X) where
  selected : Finset G.ConnectedComponent
  full : ∀c∈selected,∀x∈c.supp,Nat.card (G.neighborSet x)=10
  P : ℕ
  eps : ℕ
  positive : 1≤eps
  small : eps≤2
  order : (componentVertices G selected).ncard=2*P+eps
  fits : matchingEdges (G.induce (componentVertices G selected))≤P

namespace TenRegularBudget
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenRegularBudget G)
def support := componentVertices G K.selected
noncomputable def slack := K.P-matchingEdges (G.induce K.support)
theorem support_closed : ∀x∈K.support,∀y,G.Adj x y → y∈K.support := component_vertices_closed G K.selected
theorem support_full : ∀x∈K.support,Nat.card (G.neighborSet x)=10 := fun x hx => K.full _ hx x rfl
theorem fee : (G.induce K.support).edgeSet.ncard=10*K.P+5*K.eps := by
  have hand := root_deletion_cost G K.support
  rw [degree_sum_full G K.support 10 K.support_full] at hand
  have zero : crossCount G K.support K.supportᶜ=0 := crossCount_of_no_edges _ _ _ (fun x h y o adj => o (K.support_closed x h y adj))
  have piece := incident_piece_edge_count G K.support
  have split := erase_internal_edge_count G K.supportᶜ
  have order : K.support.ncard=2*K.P+K.eps := K.order
  omega

theorem from_one_component (c:G.ConnectedComponent) (reg:∀x∈c.supp,Nat.card (G.neighborSet x)=10)
    (imperfect:2*matchingEdges c.toSimpleGraph<Nat.card c.supp) :
    ∃K:TenRegularBudget G,K.selected={c} ∧ K.P=(Nat.card c.supp-1)/2 := by
  classical
  let n := Nat.card c.supp
  let p := (n-1)/2
  let e := n-2*p
  have mem : componentVertices G {c}=c.supp := by
    ext x
    exact Finset.mem_singleton
  have size : c.supp.ncard=n := rfl
  change 2*matchingEdges c.toSimpleGraph<n at imperfect
  have fit : matchingEdges (G.induce (componentVertices G {c}))≤p := by
    have eq := congrArg (fun A:Set X => matchingEdges (G.induce A)) mem
    change matchingEdges (G.induce (componentVertices G {c}))=matchingEdges c.toSimpleGraph at eq
    dsimp only [p];omega
  refine ⟨⟨{c},fun i hi => (Finset.mem_singleton.mp hi : i=c) ▸ reg,p,e,?_,?_,?_,fit⟩,rfl,rfl⟩
  · dsimp only [e,p];omega
  · dsimp only [e,p];omega
  · rw [mem,size];dsimp only [e,p];omega

theorem from_two_odd_components (T:Finset G.ConnectedComponent) (two:T.card=2)
    (actual:∀c∈T,c∈oddRegularComponents G 10) :
    ∃K:TenRegularBudget G,K.selected=T ∧ K.P=∑c∈T,Nat.card c.supp/2 ∧ K.eps=2 := by
  obtain ⟨order,_,fit,_⟩ := regular_union_at_even_degree G 5 T actual
  refine ⟨⟨T,fun c hc => (actual c hc).2,_,2,by decide,by decide,?_,fit⟩,rfl,rfl,rfl⟩
  simpa only [two] using order

end TenRegularBudget
#print axioms TenRegularBudget.fee
#print axioms TenRegularBudget.from_one_component
#print axioms TenRegularBudget.from_two_odd_components
end JSP452Audit.StarHost
