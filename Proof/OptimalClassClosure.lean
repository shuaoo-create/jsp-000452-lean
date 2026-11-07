import GoodFullAllocation
import RootDeficitBounds
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
theorem optimal_subclass_closed_region (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (H T : Set (G.induce Sᶜ).ConnectedComponent) (inside : T⊆H)
    (att : T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+(H \ Set.range A.place).ncard) :
    {a : S | A.place a∈T}=rootNeighbors (rootIncidence G S) T ∧
      T \ Set.range A.place = H \ Set.range A.place := by
  have split := root_allocation_split G S A T
  have subRoot := root_preimage_subset_neighbors G S A T
  have subFree : T \ Set.range A.place ⊆ H \ Set.range A.place := fun _ h => ⟨inside h.1,h.2⟩
  have a := Set.ncard_le_ncard subRoot
  have b := Set.ncard_le_ncard subFree
  exact ⟨Set.eq_of_subset_of_ncard_le subRoot (by omega),Set.eq_of_subset_of_ncard_le subFree (by omega)⟩
#print axioms optimal_subclass_closed_region
end JSP452Audit.StarHost
