import IndependentSupplyOffOneVertex
namespace JSP452Audit.StarHost
open SimpleGraph

theorem independent_union_of_components {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (T:Set G.ConnectedComponent) [Fintype T] :
    ∃I:Set X,(∀x∈I,G.connectedComponentMk x∈T) ∧ G.IsIndepSet I ∧
      (∑c:↥T,(Nat.card c.val.supp-1))≤D*I.ncard := by
  classical
  have take (c:↥T) : ∃J:Set c.val.supp,c.val.toSimpleGraph.IsIndepSet J ∧
      Nat.card c.val.supp-1≤D*J.ncard := by
    let a := c.val.nonempty_supp.to_subtype.some
    have localCap (v:c.val.supp) : Nat.card (c.val.toSimpleGraph.neighborSet v)≤D :=
      (component_degree_eq G c.val v).trans_le (cap v.val)
    obtain ⟨J,_,ind,room⟩ := independent_supply_proper_subset c.val.toSimpleGraph D
      c.val.connected_toSimpleGraph.preconnected localCap a ({a}:Set c.val.supp)ᶜ (by simp)
    have total := Set.ncard_add_ncard_compl ({a}:Set c.val.supp)
    rw [Set.ncard_singleton] at total
    exact ⟨J,ind,by omega⟩
  choose J ind room using take
  let part (c:↥T) := Subtype.val '' J c
  have label {c:↥T} {x:X} (mem:x∈part c) : G.connectedComponentMk x=c.val := by
    obtain ⟨v,_,rfl⟩ := mem;exact v.property
  have dis : Pairwise (Function.onFun Disjoint part) := by
    intro c e ne
    exact Set.disjoint_left.mpr fun _ hc he => ne (Subtype.ext ((label hc).symm.trans (label he)))
  have unionInd : G.IsIndepSet (⋃c:↥T,part c) := by
    intro x hx y hy ne edge
    obtain ⟨c,xc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e,ye⟩ := Set.mem_iUnion.mp hy
    have same : c=e := Subtype.ext ((label xc).symm.trans ((ConnectedComponent.sound edge.reachable).trans (label ye)))
    subst e
    obtain ⟨v,hv,rfl⟩ := xc
    obtain ⟨w,hw,rfl⟩ := ye
    exact ind c hv hw (fun eq => ne (congrArg Subtype.val eq)) edge
  refine ⟨⋃c:↥T,part c,?_,unionInd,?_⟩
  · intro x hx
    obtain ⟨c,mem⟩ := Set.mem_iUnion.mp hx
    rw [label mem]
    exact c.property
  · have tally (c:↥T) : (part c).ncard=(J c).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    rw [Set.ncard_iUnion_of_finite (fun c => Set.toFinite (part c)) dis,finsum_eq_sum_of_fintype,Finset.mul_sum]
    simp only [tally]
    exact Finset.sum_le_sum (s:=(Finset.univ:Finset ↥T)) (fun c _ => room c)

#print axioms independent_union_of_components
end JSP452Audit.StarHost
