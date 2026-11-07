import HallNeighborhoods

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} (G : SimpleGraph X) (S : Set X) {d : ℕ}
    (e : (G.induce Sᶜ).ConnectedComponent ≃ ↥S ⊕ Fin d)
    (real : ∀ c a, e c = .inl a → rootIncidence G S a c)

/-- Pull the real seats of one fixed allocation bijection back to components. -/
def rootAllocationOfSeats : RootAllocation G S where
  place := ⟨fun a => e.symm (.inl a),e.symm.injective.comp Sum.inl_injective⟩
  link a := real _ a (e.apply_symm_apply _)

private theorem dummy_of_unassigned (c : (G.induce Sᶜ).ConnectedComponent)
    (miss : c∉Set.range (rootAllocationOfSeats G S e real).place) : ∃ i : Fin d, e c = .inr i := by
  cases eq : e c with
  | inl a =>
    exact (miss ⟨a,e.injective ((e.apply_symm_apply _).trans eq.symm)⟩).elim
  | inr i => exact ⟨i,rfl⟩

/-- Each unassigned component of a restricted family gives a different allowed dummy seat. -/
theorem unassigned_class_bound (C : Set (G.induce Sᶜ).ConnectedComponent) (k : ℕ)
    (limit : ∀ c i, c∈C → e c=.inr i → i.val<k) :
    (C \ Set.range (rootAllocationOfSeats G S e real).place).ncard ≤ k := by
  let U := C \ Set.range (rootAllocationOfSeats G S e real).place
  have exits (s : U) := dummy_of_unassigned G S e real s.val s.property.2
  let send (s : U) : Fin k := ⟨(exits s).choose.val,
    limit s.val _ s.property.1 (exits s).choose_spec⟩
  have inj : Function.Injective send := by
    intro s t eq
    have same : (exits s).choose = (exits t).choose := Fin.ext (congrArg (fun i : Fin k => i.val) eq)
    exact Subtype.ext (e.injective (((exits s).choose_spec.trans (congrArg Sum.inr same)).trans
      (exits t).choose_spec.symm))
  simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_le_card_of_injective send inj

include real

/-- Both deficit bounds use the same placement, with the order H,F matching nested_class_hall. -/
theorem allocation_of_nested_exits (H F : Set (G.induce Sᶜ).ConnectedComponent) (k r : ℕ)
    (outer : ∀ c i, c∈F → e c=.inr i → i.val<k)
    (inner : ∀ c i, c∈H → e c=.inr i → i.val<r) :
    ∃ A : RootAllocation G S,
      (F \ Set.range A.place).ncard ≤ k ∧ (H \ Set.range A.place).ncard ≤ r :=
  ⟨rootAllocationOfSeats G S e real,unassigned_class_bound G S e real F k outer,
    unassigned_class_bound G S e real H r inner⟩

theorem allocation_of_saturated_inner (H F : Set (G.induce Sᶜ).ConnectedComponent) (k : ℕ)
    (outer : ∀ c i, c∈F → e c=.inr i → i.val<k)
    (inner : ∀ c i, c∈H → e c=.inr i → i.val<0) :
    ∃ A : RootAllocation G S, (F \ Set.range A.place).ncard ≤ k ∧ H ⊆ Set.range A.place := by
  refine ⟨rootAllocationOfSeats G S e real,unassigned_class_bound G S e real F k outer,?_⟩
  intro c hc
  by_contra miss
  obtain ⟨i,hi⟩ := dummy_of_unassigned G S e real c miss
  exact (Nat.not_lt_zero i.val) (inner c i hc hi)

#print axioms allocation_of_nested_exits
#print axioms allocation_of_saturated_inner
end JSP452Audit.StarHost
