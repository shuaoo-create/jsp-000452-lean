import BadPortsSelected
import FreeBadPortIncidence
import OptimalClassClosure
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- A quantified family of different unassigned components and different
barrier roots. Each assigned pair uses an actual edge to an actual bad port. -/
structure BadPortPlan (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S) where
  chosen : Set ↥(badFree G S D A)
  root : ↥chosen ↪ ↥S
  edge : ∀ c, badPortIncidence G S D (root c) c.val.val
  enough : deletionBudget G D - ((goodFullClass G S D) \ Set.range A.place).ncard ≤ chosen.ncard

theorem exists_bad_port_plan (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (data : ∀c : (G.induce Sᶜ).ConnectedComponent,Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (A : RootAllocation G S)
    (opt : (freeFull G S D A).ncard=minimumExposure G D) : Nonempty (BadPortPlan G S D A) := by
  classical
  let B := badFree G S D A
  let good := goodFullClass G S D \ Set.range A.place
  let F := freeFull G S D A
  have sub : B⊆F := fun _ h => h.1
  have rest : F \ B = good := by
    ext c
    change ((_ ∧ _) ∧ ¬((_ ∧ _) ∧ ¬_)) ↔ ((_ ∧ _) ∧ _)
    by_cases g : internallyGood c.toSimpleGraph D <;> simp [g, and_comm]
  have eq := Set.ncard_sdiff_add_ncard_of_subset sub
  rw [rest] at eq
  have types : B.ncard+good.ncard=minimumExposure G D := by change F.ncard=_ at opt; omega
  obtain ⟨sel,f,inc,_,bound⟩ := bad_ports_selected G S tight data D pos cap A opt B sub
    (fun c a => badPortIncidence G S D a c.val)
    (fun c a h => badPortIncidence_rootIncidence G S D a c.val h)
    (fun c => every_free_bad_has_root G S D A c.val c.property)
  exact ⟨⟨sel,f,inc,bound good.ncard types⟩⟩

theorem exists_optimized_disjoint_ports (G : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) :
    ∃ (S : Set X) (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent),
      IsTightBarrier G S ∧ (∀c : (G.induce Sᶜ).ConnectedComponent,Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph) ∧ T⊆goodFullClass G S D ∧
      (freeFull G S D A).ncard=minimumExposure G D ∧
      T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+((goodFullClass G S D) \ Set.range A.place).ncard ∧
      Nonempty (BadPortPlan G S D A) := by
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  obtain ⟨A,T,sub,opt,att,_⟩ := optimal_good_port_allocation G S tight data D
  exact ⟨S,A,T,tight,data,sub,opt,att,exists_bad_port_plan G S tight data D pos cap A opt⟩
#print axioms exists_optimized_disjoint_ports
end JSP452Audit.StarHost
