import OptimalNestedAssignment
import OddRegionPort
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def goodFullClass (G : SimpleGraph X) (S : Set X) (D : ℕ) :
    Set (G.induce Sᶜ).ConnectedComponent :=
  {c | allFullComponent G S D c ∧ internallyGood c.toSimpleGraph D}

theorem optimal_good_port_allocation (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) :
    ∃ (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent), T⊆goodFullClass G S D ∧
      (freeFull G S D A).ncard=minimumExposure G D ∧
      T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+((goodFullClass G S D) \ Set.range A.place).ncard ∧
      ∀ B : RootAllocation G S, ((goodFullClass G S D) \ Set.range A.place).ncard≤((goodFullClass G S D) \ Set.range B.place).ncard :=
    nested_optimal_root_assignment G S tight data D _ (fun _ h => h.1)

#print axioms optimal_good_port_allocation
end JSP452Audit.StarHost
