import HallNeighborhoods

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Retain the assigned endpoints and the nonfull holes. In each touched free
full component pick an endpoint of an actual edge from the chosen root set. -/
theorem choose_targeted_root_holes (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (A : RootAllocation G S) (T : Set ↥S) :
    ∃ pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp,
      (∀ a : S, G.Adj a.val (pick (A.place a)).val.val) ∧
      (∀ c, c ∉ Set.range A.place →
        (Nat.card (G.neighborSet (pick c).val.val) = D ↔ allFullComponent G S D c)) ∧
      (∀ c ∈ freeFull G S D A, (∃ a ∈ T, rootIncidence G S a c) →
        ∃ a ∈ T, G.Adj a.val (pick c).val.val) := by
  classical
  obtain ⟨base, links, degrees⟩ := choose_allocation_holes G S A D
  have one (c : (G.induce Sᶜ).ConnectedComponent) :
      ∃ z : c.supp, (∀ a : S, A.place a = c → G.Adj a.val z.val.val) ∧
        (c ∉ Set.range A.place →
          (Nat.card (G.neighborSet z.val.val) = D ↔ allFullComponent G S D c)) ∧
        (c ∈ freeFull G S D A → (∃ a ∈ T, rootIncidence G S a c) →
          ∃ a ∈ T, G.Adj a.val z.val.val) := by
    by_cases hit : c ∈ freeFull G S D A ∧ ∃ a ∈ T, rootIncidence G S a c
    · obtain ⟨free, a, ha, z, edge⟩ := hit
      refine ⟨z, fun b eq => (free.1 ⟨b, eq⟩).elim, ?_, fun _ _ => ⟨a, ha, edge⟩⟩
      exact fun _ => ⟨fun _ => free.2, fun full => full z⟩
    · refine ⟨base c, ?_, degrees c, fun free touched => (hit ⟨free,touched⟩).elim⟩
      rintro a rfl
      exact links a
  choose pick hp using one
  exact ⟨pick, fun a => (hp (A.place a)).1 a rfl, fun c => (hp c).2.1, fun c => (hp c).2.2⟩

/-- A single maximum matching realizes all the targeted holes simultaneously.
Distinct residual components give distinct exposed original labels. -/
theorem realize_targeted_root_holes [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (A : RootAllocation G S) (T : Set ↥S) :
    ∃ (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) (M : G.Subgraph),
      M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      exposedFull G M D = (fun c => (pick c).val.val) '' freeFull G S D A ∧
      Function.Injective (fun c => (pick c).val.val) ∧
      (∀ c ∈ freeFull G S D A, (∃ a ∈ T, rootIncidence G S a c) →
        ∃ a ∈ T, G.Adj a.val (pick c).val.val) ∧
      (∀ a : S, G.Adj a.val (pick (A.place a)).val.val) ∧
      (∀ c, c ∉ Set.range A.place →
        (Nat.card (G.neighborSet (pick c).val.val) = D ↔ allFullComponent G S D c)) ∧
      M.vertsᶜ = freeHoleLabels G S A.place pick := by
  obtain ⟨pick, link, degree, touched⟩ := choose_targeted_root_holes G S D A T
  obtain ⟨M, hm, max, holes⟩ := realize_root_plan G S tight (fun c => (data c).1)
    (fun c => (data c).2) A.place pick link
  exact ⟨pick, M, hm, max, exposedFull_eq_label_image G S D A pick M holes degree,
    picked_original_injective G S pick, touched, link, degree, holes⟩

#print axioms choose_targeted_root_holes
#print axioms realize_targeted_root_holes

end JSP452Audit.StarHost
