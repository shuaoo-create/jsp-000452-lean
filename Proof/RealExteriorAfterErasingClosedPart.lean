import PhysicalSixFiveFourHistory
namespace JSP452Audit.StarHost
open SimpleGraph

theorem erased_closed_exterior_edges {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (V:Set ↥(Uᶜ:Set X)) :
    ((eraseInternal G U).induce (Subtype.val '' V)ᶜ).edgeSet.ncard=((G.induce Uᶜ).induce Vᶜ).edgeSet.ncard := by
  let S := (Subtype.val '' V)ᶜ
  let Y := (eraseInternal G U).induce S
  let T : Set S := {v|v.val∈Uᶜ}
  have inside {a b:↥S} (edge:Y.Adj a b) : a∈T := fun h => edge.2 ⟨h,closed _ h _ edge.1⟩
  have empty : eraseInternal Y T=⊥ := by
    ext a b
    exact ⟨fun e => (e.2 ⟨inside e.1,inside e.1.symm⟩).elim,False.elim⟩
  have price := erase_internal_edge_count Y T
  rw [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.zero_add] at price
  let send (x:↥(Vᶜ:Set ↥(Uᶜ:Set X))) : T :=
    ⟨⟨x.val.val,by rintro ⟨v,hv,eq⟩;exact x.property ((Subtype.ext eq : v=x.val) ▸ hv)⟩,x.val.property⟩
  let back (y:↥T) : ↥(Vᶜ:Set ↥(Uᶜ:Set X)) :=
    let v : ↥(Uᶜ:Set X) := ⟨y.val.val,y.property⟩
    ⟨v,fun h => y.val.property ⟨v,h,rfl⟩⟩
  let e : (G.induce Uᶜ).induce Vᶜ ≃g Y.induce T := {
    toEquiv := {toFun := send,invFun := back,left_inv := fun _ => rfl,right_inv := fun _ => rfl}
    map_rel_iff' := fun {v _} => ⟨fun adj => adj.1,fun adj => ⟨adj,fun h => v.val.property h.1⟩⟩ }
  exact price.trans (Nat.card_congr e.mapEdgeSet).symm

theorem intact_components_plus_exterior {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) :
    G.edgeSet.ncard=(G.induce U).edgeSet.ncard+(G.induce Uᶜ).edgeSet.ncard := by
  let e : (G.induce U⊕g G.induce Uᶜ) ≃g G :=
    (regionSumIso G Set.univ U Uᶜ (Set.union_compl_self _) disjoint_compl_right
      (fun x hx y hy edge => hy (closed x hx y edge))).trans (induceUnivIso G)
  have price : (G.induce U⊕g G.induce Uᶜ).edgeSet.ncard=G.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rwa [edge_ncard_sumGraph,eq_comm] at price

#print axioms erased_closed_exterior_edges
#print axioms intact_components_plus_exterior
end JSP452Audit.StarHost
