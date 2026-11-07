import HallNeighborhoods

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Real exits assign different components to the roots. Every remaining
all-full component uses its own dummy label strictly below k. -/
theorem allocation_of_limited_exits {X : Type*} (G : SimpleGraph X) (S : Set X) (D : ℕ)
    {d k : ℕ} (e : (G.induce Sᶜ).ConnectedComponent ≃ ↥S ⊕ Fin d)
    (real : ∀ c a, e c = Sum.inl a → rootIncidence G S a c)
    (limit : ∀ c (i : Fin d), allFullComponent G S D c → e c = Sum.inr i → i.val < k) :
    ∃ A : RootAllocation G S, (freeFull G S D A).ncard ≤ k := by
  let place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent :=
    ⟨fun a => e.symm (Sum.inl a),e.symm.injective.comp Sum.inl_injective⟩
  let A : RootAllocation G S := {
    place := place
    link := fun a => real (place a) a (e.apply_symm_apply _) }
  have exit (c : freeFull G S D A) : ∃ i : Fin d, e c.val = .inr i := by
    cases eq : e c.val with
    | inl a =>
      have assigned : place a = c.val := e.injective ((e.apply_symm_apply _).trans eq.symm)
      exact (c.property.1 ⟨a,assigned⟩).elim
    | inr i => exact ⟨i,rfl⟩
  let send (c : freeFull G S D A) : Fin k :=
    ⟨(exit c).choose.val,limit c.val (exit c).choose c.property.2 (exit c).choose_spec⟩
  have inj : Function.Injective send := by
    intro c c' eq
    have indices : (exit c).choose = (exit c').choose := Fin.ext (congrArg (fun x : Fin k => x.val) eq)
    exact Subtype.ext (e.injective (((exit c).choose_spec.trans (congrArg Sum.inr indices)).trans
      (exit c').choose_spec.symm))
  refine ⟨A,?_⟩
  simpa only [Nat.card_coe_set_eq,Nat.card_fin] using Nat.card_le_card_of_injective send inj

#print axioms allocation_of_limited_exits
end JSP452Audit.StarHost
