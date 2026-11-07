import ClassDeficiency
import NestedAllocation
import NestedClassHall
import FullComponentDeficiency
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The same actual root assignment simultaneously minimizes free full
components and the free components of any specified subclass. -/
theorem nested_optimal_root_assignment (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (H : Set (G.induce Sᶜ).ConnectedComponent)
    (nested : H⊆{c | allFullComponent G S D c}) :
    ∃ (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent), T⊆H ∧
      (freeFull G S D A).ncard=minimumExposure G D ∧
      T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+(H \ Set.range A.place).ncard ∧
      ∀ (B : RootAllocation G S),(H \ Set.range A.place).ncard≤(H \ Set.range B.place).ncard := by
  classical
  let C := (G.induce Sᶜ).ConnectedComponent
  let F : Set C := {c | allFullComponent G S D c}
  let L := rootIncidence G S
  let ρ := minimumExposure G D
  let d := Nat.card C-S.ncard
  obtain ⟨h,limit,⟨T,sub,att⟩⟩ := class_deficiency_attained L H
  obtain ⟨lower,A0,opt⟩ := allocation_exposure_exact G S tight data D
  have allF (U : Set C) (hf : U⊆F) : U.ncard ≤ (rootNeighbors L U).ncard+ρ := by
    have bound := root_deficit_bound_full G S D A0 U hf
    rwa [opt] at bound
  have hr : h≤ρ := by have bound := allF T (sub.trans nested); omega
  have potential := (Set.ncard_le_ncard (show freeFull G S D A0 ⊆ (Set.range A0.place)ᶜ from fun _ hc => hc.1))
  rw [Set.ncard_compl,Set.ncard_range_of_injective A0.place.injective,opt] at potential
  have rd : ρ≤d := potential
  have cardinal := Nat.card_le_card_of_injective A0.place A0.place.injective
  have order : Nat.card C=Nat.card ↥S+d := by
    change Nat.card ↥S≤Nat.card C at cardinal
    change Nat.card C=Nat.card ↥S+(Nat.card C-Nat.card ↥S)
    omega
  obtain ⟨e,real,outer,inner⟩ := nested_class_hall L H F d ρ h nested hr rd order
    (root_deficit_bound_all G S A0) allF limit
  obtain ⟨A,full,less⟩ := allocation_of_nested_exits G S e real H F ρ h outer inner
  have split : F \ Set.range A.place = freeFull G S D A := by ext c; exact and_comm
  rw [split] at full
  have forced (B : RootAllocation G S) : h≤(H \ Set.range B.place).ncard := by
    have realB : ∀r,L r (B.place r) := B.link
    have cost := class_deficit_le_free L H B.place realB T sub
    omega
  have eq := le_antisymm less (forced A)
  exact ⟨A,T,sub,le_antisymm full (lower A),by rwa [eq],fun B => eq.symm ▸ forced B⟩
#print axioms nested_optimal_root_assignment
end JSP452Audit.StarHost
