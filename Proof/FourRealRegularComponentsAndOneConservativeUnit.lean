import ThreeRemainingNumericalTenDegreeSources
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_choose_four_regular_blocks (F:StrictFamily.{u}) (six:highestWidth F.n F.m F.r=6)
    (many:4≤(oddRegularComponents F.G 10).ncard) :
    ∃A:PricedTenMenu F,A.K.eps=2 ∧ 21≤A.K.P ∧ 1≤A.K.slack ∧ A.steps+5≤A.K.P := by
  classical
  let Z := oddRegularComponents F.G 10
  have count : 4≤Z.toFinite.toFinset.card := by rw [←Set.ncard_coe_finset,Z.toFinite.coe_toFinset];exact many
  obtain ⟨T,sub,num⟩ := Finset.exists_subset_card_eq count
  have full (c) (mem:c∈T) : c∈oddRegularComponents F.G 10 := Z.toFinite.mem_toFinset.mp (sub mem)
  let p := ∑c∈T,Nat.card c.supp/2
  obtain ⟨n,_,fit,_⟩ := regular_union_at_even_degree F.G 5 T full
  change (componentVertices F.G T).ncard=2*p+T.card at n
  change matchingEdges (F.G.induce (componentVertices F.G T))≤p at fit
  have lower (c:F.G.ConnectedComponent) (mem:c∈T) : 5≤Nat.card c.supp/2 := by
    let x := c.nonempty_supp.to_subtype.some
    exact half_order_of_regular_component c.toSimpleGraph 5 x ((component_degree_eq F.G c x).trans ((full c mem).2 x.val x.property))
  have sum := Finset.sum_le_sum (s:=T) lower
  rw [Finset.sum_const,num,nsmul_eq_mul,Nat.cast_id] at sum
  change 4*5≤p at sum
  let K : TenRegularBudget F.G := ⟨T,fun c hc => (full c hc).2,p+1,2,by decide,by decide,by omega,by omega⟩
  have elem : T.Nonempty := Finset.card_pos.mp (by omega)
  let i0 : ↥K.selected := ⟨elem.choose,elem.choose_spec⟩
  let z (i:↥K.selected) := Nat.card i.val.supp/2+(if i=i0 then 1 else 0)
  have total : (∑i,z i)=K.P := by
    have primary := Finset.sum_coe_sort T (fun c => Nat.card c.supp/2)
    change (∑i:↥K.selected,Nat.card i.val.supp/2)=p at primary
    simp only [z,Finset.sum_add_distrib,primary]
    simp [K]
  have upper (i:↥K.selected) : matchingEdges i.val.toSimpleGraph≤z i := by
    have order := matching_edges_fit_order i.val.toSimpleGraph
    change 2*matchingEdges i.val.toSimpleGraph≤Nat.card i.val.supp at order
    dsimp only [z];omega
  obtain ⟨I,stage,len⟩ := short_stages_on_odd_regular_components F.G 5 (by decide) T full
  change I.ncard+T.card≤p at len
  have cost : highestWidth F.n F.m F.r+(38+2*highestWidth F.n F.m F.r)/7≤5*K.eps+5 := by rw [six];change 6+(38+2*6)/7≤5*2+5;decide
  let A : PricedTenMenu F := ⟨K,z,upper,total,5,⟨I,stage,by change I.ncard+5≤p+1;omega⟩,by rw [six];change 6≤5*2;decide,cost⟩
  have room := (A.spare_capacity_from_two (by change 2≤T.card;omega)).2
  refine ⟨A,rfl,?_,?_,room⟩
  · change 21≤p+1;omega
  · change 1≤p+1-matchingEdges (F.G.induce (componentVertices F.G T));omega

#print axioms ten_choose_four_regular_blocks
end JSP452Audit.StarHost
