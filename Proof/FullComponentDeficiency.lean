import TwoClassHall
import RootDeficitBounds
import LimitedExitAllocation
namespace JSP452Audit.StarHost
open SimpleGraph
/-- Hall deficiency on just the full components. The same original barrier
supplies both the optimal root assignment and an actual attaining subset. -/
theorem full_component_deficiency {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp)) (D : ℕ) :
    (∀ T : Set (G.induce Sᶜ).ConnectedComponent, T ⊆ {c | allFullComponent G S D c} →
      T.ncard ≤ (rootNeighbors (rootIncidence G S) T).ncard+minimumExposure G D) ∧
    ∃ T : Set (G.induce Sᶜ).ConnectedComponent, T ⊆ {c | allFullComponent G S D c} ∧
      T.ncard = (rootNeighbors (rootIncidence G S) T).ncard+minimumExposure G D := by
  classical
  let C := (G.induce Sᶜ).ConnectedComponent
  let L := rootIncidence G S
  let F : Set C := {c | allFullComponent G S D c}
  let d := Nat.card C - S.ncard
  let rho := minimumExposure G D
  obtain ⟨lower,A,att⟩ := allocation_exposure_exact G S tight data D
  have ub (T : Set C) (sub : T ⊆ F) : T.ncard ≤ (rootNeighbors L T).ncard+rho := by
    have h := root_deficit_bound_full G S D A T sub
    rwa [att] at h
  refine ⟨ub,?_⟩
  by_cases zero : rho=0
  · exact ⟨∅,Set.empty_subset _,by change (∅ : Set C).ncard = (rootNeighbors L ∅).ncard+rho; simp [zero,rootNeighbors_empty]⟩
  have free : freeFull G S D A ⊆ (Set.range A.place)ᶜ := fun _ h => h.1
  have dk : rho ≤ d := by
    have ct := Set.ncard_le_ncard free
    rw [Set.ncard_compl,Set.ncard_range_of_injective A.place.injective,att] at ct
    exact ct
  have size : Nat.card C = Nat.card ↥S + d := by
    have hh := Nat.card_le_card_of_injective A.place A.place.injective
    change Nat.card ↥S ≤ Nat.card C at hh
    change Nat.card C = Nat.card ↥S + (Nat.card C-Nat.card ↥S)
    omega
  by_contra noT
  have small (T : Set C) (inside : T ⊆ F) : T.ncard ≤ (rootNeighbors L T).ncard+(rho-1) := by
    have atMost := ub T inside
    have different : T.ncard ≠ (rootNeighbors L T).ncard+rho := fun eq => noT ⟨T,inside,eq⟩
    omega
  obtain ⟨e,real,limit⟩ := two_class_hall L F d (rho-1) (by omega) size
    (root_deficit_bound_all G S A) small
  obtain ⟨B,less⟩ := allocation_of_limited_exits G S D e real limit
  have h : rho ≤ (freeFull G S D B).ncard := lower B
  omega
#print axioms full_component_deficiency
end JSP452Audit.StarHost