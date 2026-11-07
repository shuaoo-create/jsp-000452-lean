import FullComponentDeficiency
import HallRegions
namespace JSP452Audit.StarHost
open SimpleGraph

/-- At simultaneous primal and dual equality the root neighborhood is
saturated inside T and no full component outside T is left unassigned. -/
theorem attaining_neighborhood_saturated {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (D : ℕ) (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent)
    (all : T ⊆ {c | allFullComponent G S D c}) (opt : (freeFull G S D A).ncard = minimumExposure G D)
    (cert : T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+minimumExposure G D) :
    ({a : S | A.place a ∈ T} : Set S) = rootNeighbors (rootIncidence G S) T ∧
      T \ Set.range A.place = freeFull G S D A := by
  have part := root_allocation_split G S A T
  have sr := root_preimage_subset_neighbors G S A T
  have sf : T \ Set.range A.place ⊆ freeFull G S D A := fun _ h => ⟨h.2,all h.1⟩
  have r := Set.ncard_le_ncard sr
  have f := Set.ncard_le_ncard sf
  constructor
  · exact Set.eq_of_subset_of_ncard_le sr (by omega)
  · exact Set.eq_of_subset_of_ncard_le sf (by omega)

/-- The full-degree deficiency is realized by an actual isolated group of
residual components and its adjacent roots in the original graph. -/
theorem exists_full_region {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) :
    ∃ (S : Set X) (T : Set (G.induce Sᶜ).ConnectedComponent) (A : RootAllocation G S),
      IsTightBarrier G S ∧
      (∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp)) ∧
      T ⊆ {c | allFullComponent G S D c} ∧
      T.ncard = (rootNeighbors (rootIncidence G S) T).ncard + minimumExposure G D ∧
      ({a : S | A.place a∈T} : Set S)=rootNeighbors (rootIncidence G S) T ∧
      T \ Set.range A.place = freeFull G S D A ∧
      (∀ x ∈ regionCore G S T, Nat.card (G.neighborSet x)=D) ∧
      (∀ x∈regionCore G S T, ∀ y∈regionRest G S T, ¬ G.Adj x y) := by
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  obtain ⟨T,full,cert⟩ := (full_component_deficiency G S tight data D).2
  obtain ⟨A,opt⟩ := (allocation_exposure_exact G S tight data D).2
  obtain ⟨sr,sf⟩ := attaining_neighborhood_saturated G S D A T full opt cert
  exact ⟨S,T,A,tight,data,full,cert,sr,sf,fun _ inside => regionCore_full_degree G S T D full inside,
    fun _ hx _ hy => no_edge_core_rest G S T hx hy⟩
#print axioms attaining_neighborhood_saturated
#print axioms exists_full_region
end JSP452Audit.StarHost