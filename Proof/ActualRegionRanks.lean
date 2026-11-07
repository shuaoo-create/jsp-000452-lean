import SaturatedRegion
import RegionSplitRank
import TightDeletesRank
import CoreComponentSum
import CoreComplement
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
variable {X : Type*} [Finite X]

theorem core_order_matching (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (odd : ∀ c∈T, Odd (Nat.card c.supp)) :
    (regionCore G S T).ncard = 2*matchingEdges (G.induce (regionCore G S T))+T.ncard := by
  have defic := tight_deletes_deficit G S S tight Set.Subset.rfl
  change (G.induce Sᶜ).oddComponents.ncard = S.ncard+minUnmatched G at tight
  have emptyTight : minUnmatched (G.induce Sᶜ) = (G.induce Sᶜ).oddComponents.ncard := by omega
  obtain ⟨cover,dis,sep⟩ := core_complement_partition G S T
  have eq := unmatched_eq_odd_on_region G Sᶜ _ _ cover dis (fun _ hx _ hy => sep hx hy) emptyTight
  rw [odd_components_regionCore_of_all_odd G S T odd] at eq
  have ord := minUnmatched_add_twice_matching (G.induce (regionCore G S T))
  rw [Nat.card_coe_set_eq] at ord
  omega

theorem region_rank_partition (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    matchingEdges G = (regionRoots G S T).ncard + matchingEdges (G.induce (regionCore G S T)) +
      matchingEdges (G.induce (regionRest G S T)) := by
  have sub : regionRoots G S T ⊆ S := by rintro _ ⟨a,_,rfl⟩; exact a.property
  have eq := tight_deletes_rank G S _ tight sub
  obtain ⟨cover,dis,sep⟩ := core_rest_partition G S T
  have split := rank_split_regions G _ _ _ cover dis (fun _ hx _ hy => sep hx hy)
  omega

/-- The two rank identities are attained on the same original vertex partition,
with genuine full-degree vertices and no edge between the core and the rest. -/
theorem original_region_ranks (G : SimpleGraph X) (D : ℕ) :
    ∃ (S : Set X) (T : Set (G.induce Sᶜ).ConnectedComponent) (A : RootAllocation G S),
      let roots := regionRoots G S T; let core := regionCore G S T; let rest := regionRest G S T
      IsTightBarrier G S ∧
      (∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp)) ∧
      T ⊆ {c | allFullComponent G S D c} ∧
      ({a : S | A.place a ∈ T} : Set S) = rootNeighbors (rootIncidence G S) T ∧
      T.ncard = roots.ncard + minimumExposure G D ∧
      Disjoint roots core ∧ Disjoint roots rest ∧ Disjoint core rest ∧ roots ∪ core ∪ rest=Set.univ ∧
      (∀ x∈core, Nat.card (G.neighborSet x)=D) ∧ (∀ x∈core, ∀ y∈rest, ¬G.Adj x y) ∧
      core.ncard=2*matchingEdges (G.induce core) + roots.ncard + minimumExposure G D ∧
      matchingEdges G=roots.ncard+matchingEdges (G.induce core)+matchingEdges (G.induce rest) := by
  obtain ⟨S,T,A,tight,data,full,att,sat,_,deg,sep⟩ := exists_full_region G D
  have nroot : (regionRoots G S T).ncard = (rootNeighbors (rootIncidence G S) T).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have core := core_order_matching G S tight T (fun c _ => (data c).1)
  obtain ⟨ac,ab,cb,all⟩ := region_partition G S T
  exact ⟨S,T,A,tight,data,full,sat,by omega,ac,ab,cb,all,deg,sep,by omega,region_rank_partition G S tight T⟩
#print axioms core_order_matching
#print axioms region_rank_partition
#print axioms original_region_ranks
end JSP452Audit.StarHost