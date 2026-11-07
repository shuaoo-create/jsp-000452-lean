import ChosenComponentsActualAccounts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_chosen_component_columns (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    let U := componentVertices F.G T
    let P := matchingEdges (F.G.induce U)
    U.ncard=2*P+T.card ∧ (F.G.induce U).edgeSet.ncard=6*P+3*T.card ∧
    ∀j:ℕ,0<j → widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce Uᶜ) j+(P+(T.card-1)/2) := by
  intro U P
  obtain ⟨order,rank,edges⟩ := component_union_accounts F.G T
  change P=∑c∈T,matchingEdges c.toSimpleGraph at rank
  have members := fun c (hc:c∈T) => strict_six_true_component_capacity F paid six c (actual c hc)
  have orderSum := Finset.sum_congr (s₁:=T) rfl (fun c hc => (members c hc).2.1)
  have edgeSum := Finset.sum_congr (s₁:=T) rfl (fun c hc => (members c hc).2.2.2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at orderSum edgeSum
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←rank] at orderSum edgeSum
  norm_cast at edgeSum
  have size : U.ncard=2*P+T.card := order.trans orderSum
  have cost : (F.G.induce U).edgeSet.ncard=6*P+3*T.card := by change (F.G.induce U).edgeSet.ncard=_ at edges;omega
  have closed := component_vertices_closed F.G T
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk v) hv).2 v rfl).trans six.symm
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t at lens
  refine ⟨size,cost,?_⟩
  intro j hj
  apply closed_union_column_tax F.G U closed F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm hj _ _ _ F.row
  · change P≤P+(T.card-1)/2;omega
  · omega
  · change P<min F.s F.t;omega

#print axioms strict_six_chosen_component_columns
end JSP452Audit.StarHost
