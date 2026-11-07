import RegionSplitRank
import EraseRestoration
import BudgetCeiling

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Keep the original vertex labels and remove precisely edges with both endpoints in U. -/
def eraseInternal (H : SimpleGraph X) (U : Set X) : SimpleGraph X where
  Adj x y := H.Adj x y ∧ ¬ (x ∈ U ∧ y ∈ U)
  symm := ⟨fun _ _ h => ⟨h.1.symm,fun p => h.2 ⟨p.2,p.1⟩⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

@[simp] theorem eraseInternal_adj (H : SimpleGraph X) (U : Set X) (x y : X) :
    (eraseInternal H U).Adj x y ↔ H.Adj x y ∧ ¬(x ∈ U ∧ y ∈ U) := Iff.rfl

theorem eraseInternal_le (H : SimpleGraph X) (U : Set X) : eraseInternal H U ≤ H :=
  fun _ _ h => h.1

@[simp] theorem eraseInternal_induce_inside (H : SimpleGraph X) (U : Set X) :
    (eraseInternal H U).induce U = ⊥ := by
  ext x y
  exact ⟨fun h => h.2 ⟨x.property,y.property⟩,False.elim⟩

@[simp] theorem eraseInternal_induce_outside (H : SimpleGraph X) (U : Set X) :
    (eraseInternal H U).induce Uᶜ = H.induce Uᶜ := by
  ext x y
  exact ⟨fun h => h.1,fun h => ⟨h,fun inU => x.property inU.1⟩⟩

/-- The edge-count identity also holds when there are edges across U's boundary. -/
theorem erase_internal_edge_count [Finite X] (H : SimpleGraph X) (U : Set X) :
    H.edgeSet.ncard = (eraseInternal H U).edgeSet.ncard + (H.induce U).edgeSet.ncard := by
  let block := (⊤ : H.Subgraph).induce U
  have difference : H \ block.spanningCoe = eraseInternal H U := by
    ext x y
    change (H.Adj x y ∧ ¬(x ∈ U ∧ y ∈ U ∧ H.Adj x y)) ↔ _
    rw [eraseInternal_adj]
    tauto
  have blockCard : (H.induce U).edgeSet.ncard = block.edgeSet.ncard := by
    rw [H.induce_eq_coe_induce_top]
    change block.coe.edgeSet.ncard = block.edgeSet.ncard
    rw [← block.image_coe_edgeSet_coe,Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  rw [blockCard,← difference]
  exact (eraseMatching_edge_count block).symm

private theorem rank_across_closed_set [Finite X] (H : SimpleGraph X) (U : Set X)
    (sep : ∀ x ∈ U, ∀ y ∈ Uᶜ, ¬H.Adj x y) :
    matchingEdges H = matchingEdges (H.induce U) + matchingEdges (H.induce Uᶜ) := by
  have cut := rank_split_regions H Set.univ U Uᶜ (Set.union_compl_self U) disjoint_compl_right sep
  rwa [rank_eq_of_graph_iso (induceUnivIso H)] at cut

/-- When U is closed, its maximum matching contributes independently of its complement. -/
theorem erase_closed_matching_rank [Finite X] (H : SimpleGraph X) (U : Set X)
    (sep : ∀ x ∈ U, ∀ y ∈ Uᶜ, ¬H.Adj x y) :
    matchingEdges H = matchingEdges (eraseInternal H U) + matchingEdges (H.induce U) := by
  have before := rank_across_closed_set H U sep
  have after := rank_across_closed_set (eraseInternal H U) U
    (fun x hx y hy edge => sep x hx y hy edge.1)
  rw [eraseInternal_induce_inside,matchingEdges_bot,eraseInternal_induce_outside,Nat.zero_add] at after
  rw [before,after,Nat.add_comm]

#print axioms erase_internal_edge_count
#print axioms erase_closed_matching_rank
end JSP452Audit.StarHost
