import CrossingEdgeBoundFromBipartiteMatchingDeletions
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem crossing_edges_le_cap_times_matching {X:Type u} [Finite X] (G:SimpleGraph X) (S:Set X) (D:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) : crossCount G S Sᶜ≤D*matchingEdges G := by
  classical
  let H : SimpleGraph X := {
    Adj := fun x y => G.Adj x y ∧ (x∈S ↔ y∉S)
    symm := ⟨fun _ _ e => ⟨e.1.symm,by have := e.2;tauto⟩⟩
    loopless := ⟨fun _ e => e.1.ne rfl⟩ }
  have sub : H≤G := fun _ _ e => e.1
  have c (x) : Nat.card (H.neighborSet x)≤D :=
    (Set.ncard_le_ncard (show H.neighborSet x⊆G.neighborSet x from fun _ e => sub e)).trans (cap x)
  have limit := bipartite_edges_le_cap_times_rank H S D c (fun _ _ e => e.2)
  have rank := rank_le_of_copy (SimpleGraph.Copy.ofLE H G sub)
  have count : crossCount H S Sᶜ=crossCount G S Sᶜ := by
    let iso : {p:↥S × ↥(Sᶜ:Set X) // H.Adj p.1.val p.2.val} ≃ {p:↥S × ↥(Sᶜ:Set X) // G.Adj p.1.val p.2.val} :=
      {toFun := fun e => ⟨e.val,e.property.1⟩,invFun := fun e => ⟨e.val,e.property,iff_of_true e.val.1.property e.val.2.property⟩,
       left_inv := fun _ => rfl,right_inv := fun _ => rfl}
    exact Nat.card_congr iso
  have left : H.induce S=⊥ := by
    ext x y;exact ⟨fun e => (e.2.mp x.property y.property).elim,False.elim⟩
  have right : H.induce Sᶜ=⊥ := by
    ext x y;exact ⟨fun e => (x.property (e.2.mpr y.property)).elim,False.elim⟩
  have whole := erase_internal_edge_count H Sᶜ
  have part := incident_piece_edge_count H S
  rw [left,edgeSet_bot,Set.ncard_empty,Nat.zero_add,count] at part
  rw [right,edgeSet_bot,Set.ncard_empty,Nat.add_zero,part] at whole
  rw [←whole];exact limit.trans (Nat.mul_le_mul_left D rank)

theorem charged_set_fits_matching {X:Type u} [Finite X] (G:SimpleGraph X) (S:Set X) (D:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (cheap:rootShortfall G S D+2*(G.induce S).edgeSet.ncard<D) : S.ncard≤matchingEdges G := by
  have fees := partition_handshake G S Sᶜ ∅ disjoint_compl_right (by simp) (by simp) (by simp)
  have nil : crossCount G S ∅=0 := crossCount_of_no_edges _ _ _ (by simp)
  rw [nil,Nat.add_zero] at fees
  have cost := degree_sum_le_cap G S D (fun x _ => cap x)
  change D*S.ncard-originalDegreeSum G S+2*(G.induce S).edgeSet.ncard<D at cheap
  have bound := crossing_edges_le_cap_times_matching G S D cap
  by_contra! deficit
  have larger := Nat.mul_le_mul_left D (show matchingEdges G+1≤S.ncard by omega)
  rw [Nat.mul_add,Nat.mul_one] at larger;omega

#print axioms crossing_edges_le_cap_times_matching
#print axioms charged_set_fits_matching
end JSP452Audit.StarHost
