import EighthColumnOnOneExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_union_at_even_degree {X:Type u} [Finite X] (G:SimpleGraph X) (p:ℕ)
    (T:Finset G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents G (2*p)) :
    let U := componentVertices G T
    let P := ∑c∈T,Nat.card c.supp/2
    U.ncard=2*P+T.card ∧ (G.induce U).edgeSet.ncard=(2*p)*P+p*T.card ∧
      matchingEdges (G.induce U)≤P ∧ T.card≤minimumExposure (G.induce U) (2*p) := by
  classical
  intro U P
  have acc (c) (hc:c∈T) := odd_regular_order_edge_count c.toSimpleGraph p (actual c hc).1
    (fun v => (component_degree_eq G c v).trans ((actual c hc).2 v.val v.property))
  have order := Finset.sum_congr (s₁:=T) rfl (fun c hc => (acc c hc).1)
  have edges := Finset.sum_congr (s₁:=T) rfl (fun c hc => (acc c hc).2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at order edges
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] at order edges
  obtain ⟨n,r,k⟩ := component_union_accounts G T
  change U.ncard=∑c∈T,Nat.card c.supp at n
  change (∑c∈T,Nat.card c.supp)=2*P+T.card at order
  rw [←n] at order
  change U.ncard=2*P+T.card at order
  have ed : (G.induce U).edgeSet.ncard=(2*p)*P+p*T.card := by rw [Nat.mul_comm p T.card];exact k.trans edges
  have rankBounds (c) (hc:c∈T) : matchingEdges c.toSimpleGraph≤Nat.card c.supp/2 := by
    have reg (v:c.supp) := (component_degree_eq G c v).trans ((actual c hc).2 v.val v.property)
    have val := regular_exposure_order_rank c.toSimpleGraph (2*p) reg
    change 2*matchingEdges c.toSimpleGraph+minimumExposure c.toSimpleGraph (2*p)=Nat.card c.supp at val
    omega
  have rank := Finset.sum_le_sum (s:=T) rankBounds
  rw [←r] at rank
  change matchingEdges (G.induce U)≤P at rank
  have closed := component_vertices_closed G T
  have full (v:U) : Nat.card ((G.induce U).neighborSet v)=2*p :=
    (closed_set_degree_eq G U closed v).trans ((actual (G.connectedComponentMk v.val) v.property).2 v.val rfl)
  have exposed := regular_exposure_order_rank (G.induce U) (2*p) full
  change 2*matchingEdges (G.induce U)+minimumExposure (G.induce U) (2*p)=U.ncard at exposed
  exact ⟨order,ed,rank,by omega⟩

theorem strict_eight_low_column_tax (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (few:T.card≤2) (j:ℕ) (pos:0<j) :
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+
      ∑c∈T,Nat.card c.supp/2 := by
  let U := componentVertices F.G T
  have closed := component_vertices_closed F.G T
  have full (x) (mem:x∈U) : Nat.card (F.G.neighborSet x)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk x) mem).2 x rfl).trans eight.symm
  have length := (strict_closed_union_lengths F paid U closed full).1
  obtain ⟨size,_,rank,_⟩ := regular_union_at_even_degree F.G 4 T actual
  apply closed_union_column_tax F.G U closed F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm pos rank _ _ F.row
  · change U.ncard=_ at size;omega
  · omega

#print axioms regular_union_at_even_degree
#print axioms strict_eight_low_column_tax
end JSP452Audit.StarHost
