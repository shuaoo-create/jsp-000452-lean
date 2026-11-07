import RootCutCounts
import RootCutCoverage
import TargetedRootHoles
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
def touchedFree (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (T : Set ↥S) : Set (G.induce Sᶜ).ConnectedComponent :=
  {c ∈ freeFull G S D A | ∃ a∈T, rootIncidence G S a c}

/-- The exact A.2 inequality for an actual allocation and an arbitrary
set of actual roots. It also holds before minimizing the allocation. -/
theorem actual_touched_free_bound (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (A : RootAllocation G S) (T : Set ↥S) :
    (touchedFree G S D A T).ncard + deletionBudget G D ≤ T.ncard + (freeFull G S D A).ncard := by
  obtain ⟨pick,M,hm,_,labelEq,injects,touches,_⟩ := realize_targeted_root_holes G S tight data D A T
  let W : Set X := Subtype.val '' T
  have size : W.ncard=T.ncard := Set.ncard_image_of_injective T Subtype.val_injective
  have cover := root_cut_coverage G D pos cap M hm W
  let label (c : (G.induce Sᶜ).ConnectedComponent) := (pick c).val.val
  have hit : ∀c∈touchedFree G S D A T,label c∉awayFromRoots G W := by
    intro c hc away
    obtain ⟨r,root,edge⟩ := touches c hc.1 hc.2
    exact away.2 r.val ⟨r,root,rfl⟩ edge
  have count := away_image_count (freeFull G S D A) (touchedFree G S D A T)
    (fun _ h => h.1) label injects (awayFromRoots G W) hit
  rw [size,labelEq] at cover
  change deletionBudget G D ≤ T.ncard + ((label '' freeFull G S D A) ∩ awayFromRoots G W).ncard at cover
  omega

theorem optimal_root_cut_slack (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (A : RootAllocation G S) (opt : (freeFull G S D A).ncard=minimumExposure G D) (T : Set ↥S) :
    (touchedFree G S D A T).ncard ≤ T.ncard+(minimumExposure G D-deletionBudget G D) := by
  have bound := actual_touched_free_bound G S tight data D pos cap A T
  rw [opt] at bound
  omega
#print axioms actual_touched_free_bound
#print axioms optimal_root_cut_slack
end JSP452Audit.StarHost
