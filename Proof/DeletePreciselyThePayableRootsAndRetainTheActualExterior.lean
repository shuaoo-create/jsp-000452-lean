import OnePayableOriginalRootPackageAtEveryRemainingDegree
namespace JSP452Audit.StarHost.ScaledPortPlan
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} (P:ScaledPortPlan K k c)
abbrev exterior : Set X := (P.cutRoots ∪ P.paidCore)ᶜ

theorem nested_actual_sets :
    P.cutRoots⊆K.roots ∧ P.paidCore⊆K.core ∧ K.rest⊆P.exterior := by
  have a : P.cutRoots⊆K.roots := by
    rintro x ⟨v,⟨Q,⟨w,_,rfl⟩,edge⟩,rfl⟩
    exact ⟨v,⟨w.val,w.property,edge⟩,rfl⟩
  have b : P.paidCore⊆K.core := by
    rintro x ⟨v,rfl,h⟩
    obtain ⟨w,_,eq⟩ := h.1
    exact ⟨v,rfl,eq ▸ w.property⟩
  refine ⟨a,b,?_⟩
  intro x hx mem
  exact hx (mem.imp (fun h => a h) (fun h => b h))

theorem physical_exterior_split :
    Nonempty ((G.induce P.paidCore ⊕g G.induce P.exterior) ≃g G.induce P.cutRootsᶜ) := by
  have sepA : Disjoint P.cutRoots P.paidCore := by
    apply Set.disjoint_left.mpr
    rintro x ⟨v,_,rfl⟩ ⟨w,eq,_⟩
    exact w.property (eq.symm ▸ v.property)
  have cover : P.paidCore ∪ P.exterior=P.cutRootsᶜ := by
    ext x;change (_ ∨ ¬(_ ∨ _)) ↔ ¬_
    have dis : x∈P.cutRoots → x∈P.paidCore → False := fun h₁ h₂ => Set.disjoint_left.mp sepA h₁ h₂
    tauto
  have apart : Disjoint P.paidCore P.exterior :=
    Set.disjoint_left.mpr (fun _ hx hy => hy (Or.inr hx))
  refine ⟨regionSumIso G _ _ _ cover apart ?_⟩
  intro x hx y hy e
  rcases regionCore_neighbor G K.barrier P.positives hx e with hr|hc
  · obtain ⟨v,⟨Q,hQ,edge⟩,rfl⟩ := hr
    exact hy (Or.inl ⟨v,⟨Q,hQ.1,edge⟩,rfl⟩)
  · exact hy (Or.inr hc)

theorem true_exterior_rank :
    matchingEdges G=P.cutRoots.ncard+P.capacity+matchingEdges (G.induce P.exterior) := by
  obtain ⟨e⟩ := P.physical_exterior_split
  have rank := tight_deletes_rank G K.barrier P.cutRoots K.tight (by rintro _ ⟨x,_,rfl⟩;exact x.property)
  rw [←rank_eq_of_graph_iso e,matchingEdges_sumGraph] at rank
  simpa only [Nat.add_assoc] using rank

theorem true_exterior_fee (cap:∀x,Nat.card (G.neighborSet x)≤D) (h:ℕ) :
    (G.edgeSet.ncard:ℤ)+P.gamma h=(G.induce P.exterior).edgeSet.ncard+(D:ℤ)*(P.cutRoots.ncard+P.capacity)+h := by
  obtain ⟨e⟩ := P.physical_exterior_split
  have split : (G.induce P.cutRootsᶜ).edgeSet.ncard=(G.induce P.paidCore).edgeSet.ncard+(G.induce P.exterior).edgeSet.ncard := by
    rw [←edge_ncard_sumGraph];exact (Nat.card_congr e.mapEdgeSet).symm
  have cut := root_deletion_cost_with_slack G P.cutRoots D (fun x _ => cap x)
  change G.edgeSet.ncard+P.shortfall+(G.induce P.cutRoots).edgeSet.ncard=(G.induce P.cutRootsᶜ).edgeSet.ncard+D*P.cutRoots.ncard at cut
  rw [split] at cut
  have cost := congrArg (fun n:ℕ => (n:ℤ)) cut
  push_cast at cost
  dsimp only [gamma,weight,edgeSurplus,capacity]
  linarith only [cost]

#print axioms nested_actual_sets
#print axioms physical_exterior_split
#print axioms true_exterior_rank
#print axioms true_exterior_fee
end JSP452Audit.StarHost.ScaledPortPlan
