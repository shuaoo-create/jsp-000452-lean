import PaymentOnTheActualDegreeSixExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_regular_component_rank_floor {X:Type u} [Finite X] (G:SimpleGraph X) (c:G.ConnectedComponent)
    (full:∀x∈c.supp,Nat.card (G.neighborSet x)=10) : 5≤matchingEdges c.toSimpleGraph := by
  let Q := c.toSimpleGraph
  have reg (v:c.supp) : Nat.card (Q.neighborSet v)=10 := (component_degree_eq G c v).trans (full v.val v.property)
  obtain ⟨M,hm,best⟩ := exists_maximum_matching Q
  by_cases all:M.verts=Set.univ
  · have size := matching_vertices_eq_twice_edges hm
    rw [all,Set.ncard_univ,best] at size
    have min := half_order_of_regular_component Q 5 c.nonempty_supp.to_subtype.some (reg _)
    change 5≤matchingEdges Q;omega
  · have missed : ∃x,x∉M.verts := by by_contra! hit;exact all (Set.eq_univ_of_forall hit)
    obtain ⟨x,out⟩ := missed
    have degree := missed_degree_le_twice_rank Q M hm best out
    rw [reg] at degree
    change 5≤matchingEdges Q;omega

theorem PricedTenMenu.spare_capacity_from_two {F:StrictFamily.{u}} (A:PricedTenMenu F)
    (two:2≤A.K.selected.card) : 10≤A.K.P ∧ A.steps+5≤A.K.P := by
  classical
  have floor (i:↥A.K.selected) : 5≤A.units i := (ten_regular_component_rank_floor F.G i.val
    (A.K.full i.val i.property)).trans (A.upper i)
  have mass := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥A.K.selected)) (fun i _ => floor i)
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id,A.total] at mass
  have point (i:↥A.K.selected) : A.units i≤A.K.P-5 := by
    have existsOther : ∃j:↥A.K.selected,j≠i := by
      by_contra! none
      have incl : (Finset.univ:Finset ↥A.K.selected)⊆{i} := fun j _ => Finset.mem_singleton.mpr (none j)
      have size := Finset.card_le_card incl
      rw [Finset.card_univ,Fintype.card_coe,Finset.card_singleton] at size;omega
    obtain ⟨j,ne⟩ := existsOther
    have sum := Finset.sum_le_sum_of_subset_of_nonneg (f:=A.units) (Finset.subset_univ ({i,j}:Finset ↥A.K.selected))
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair ne.symm,A.total] at sum
    have lower := floor j;omega
  have bound := Finset.sup_le (s:=Finset.univ) (fun i _ => point i)
  unfold PricedTenMenu.steps;omega

theorem strict_ten_one_imperfect_at_width_one_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (one:highestWidth F.n F.m F.r=1)
    (c:F.G.ConnectedComponent) (full:∀x∈c.supp,Nat.card (F.G.neighborSet x)=10)
    (imp:2*matchingEdges c.toSimpleGraph<Nat.card c.supp) : False := by
  obtain ⟨A,_,_⟩ := priced_ten_single_component F c full imp one
  exact strict_ten_regular_source_impossible F paid ten A (Or.inl one) (Or.inl (by omega))

theorem strict_ten_two_odd_components_at_small_width_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (h:highestWidth F.n F.m F.r≤5)
    (T:Finset F.G.ConnectedComponent) (two:T.card=2) (actual:∀c∈T,c∈oddRegularComponents F.G 10) : False := by
  obtain ⟨A,sel,eps⟩ := priced_ten_two_odd_components F T two actual h
  obtain ⟨min,spare⟩ := A.spare_capacity_from_two (by rw [sel,two])
  exact strict_ten_regular_source_impossible F paid ten A (Or.inr ⟨eps,Or.inr ⟨min,h⟩⟩) (Or.inr spare)

#print axioms ten_regular_component_rank_floor
#print axioms PricedTenMenu.spare_capacity_from_two
#print axioms strict_ten_one_imperfect_at_width_one_impossible
#print axioms strict_ten_two_odd_components_at_small_width_impossible
end JSP452Audit.StarHost
