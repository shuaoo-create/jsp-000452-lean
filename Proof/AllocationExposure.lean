import ExtractAllocation
import FullHoleCount
import RealizeRootPlan
namespace JSP452Audit.StarHost
open SimpleGraph
theorem realize_allocation_count {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (A : RootAllocation G S) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard=matchingEdges G ∧
      (exposedFull G M D).ncard=(freeFull G S D A).ncard := by
  obtain ⟨pick,link,degrees⟩ := choose_allocation_holes G S A D
  obtain ⟨M,hm,max,holes⟩ := realize_root_plan G S tight (fun c => (data c).1) (fun c => (data c).2)
    A.place pick link
  exact ⟨M,hm,max,exposed_eq_freeFull G S D A pick M holes degrees⟩

/-- Exact exposure minimization on a fixed critical barrier. This is a min
over actual root assignments that are individually realizable as maximum matchings. -/
theorem allocation_exposure_exact {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) :
    (∀ A : RootAllocation G S, minimumExposure G D ≤ (freeFull G S D A).ncard) ∧
      ∃ A : RootAllocation G S, (freeFull G S D A).ncard=minimumExposure G D := by
  have lo (A : RootAllocation G S) : minimumExposure G D ≤ (freeFull G S D A).ncard := by
    obtain ⟨M,hm,max,paid⟩ := realize_allocation_count G S tight data D A
    exact (minimumExposure_le G D M hm max).trans_eq paid
  refine ⟨lo,?_⟩
  obtain ⟨M,hm,max,paid⟩ := minimumExposure_attained G D
  obtain ⟨e,exits⟩ := matched_exit_equiv G S tight M hm max (fun c => (data c).1)
  obtain ⟨A,le⟩ := extract_root_allocation G S M D e exits
  exact ⟨A,le_antisymm (le.trans_eq paid) (lo A)⟩

theorem exists_barrier_all_exposures {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ S : Set X, IsTightBarrier G S ∧
      (∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp)) ∧
      ∀ D, (∀ A : RootAllocation G S, minimumExposure G D ≤ (freeFull G S D A).ncard) ∧
        ∃ A : RootAllocation G S, (freeFull G S D A).ncard=minimumExposure G D := by
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  exact ⟨S,tight,data,allocation_exposure_exact G S tight data⟩
#print axioms realize_allocation_count
#print axioms allocation_exposure_exact
#print axioms exists_barrier_all_exposures
end JSP452Audit.StarHost