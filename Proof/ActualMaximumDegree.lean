import RowEnergy
namespace JSP452Audit.StarHost
open SimpleGraph
/-- A finite graph either has zero degree everywhere, or has an actual
positive-degree vertex whose degree bounds every vertex in the graph. -/
theorem all_zero_or_real_peak {X : Type*} [Finite X] (G : SimpleGraph X) :
    (∀ v, Nat.card (G.neighborSet v)=0) ∨
    ∃ v, 0 < Nat.card (G.neighborSet v) ∧ ∀ w, Nat.card (G.neighborSet w) ≤ Nat.card (G.neighborSet v) := by
  classical
  by_cases nil : ∀ v, Nat.card (G.neighborSet v)=0
  · exact Or.inl nil
  · push Not at nil
    obtain ⟨x,hx⟩ := nil
    let _ := Fintype.ofFinite X
    obtain ⟨v,_,high⟩ := Finset.exists_max_image Finset.univ (fun w => Nat.card (G.neighborSet w))
      (show (Finset.univ : Finset X).Nonempty from ⟨x,Finset.mem_univ _⟩)
    have le := high x (Finset.mem_univ _)
    exact Or.inr ⟨v,by omega,fun w => high w (Finset.mem_univ _)⟩
#print axioms all_zero_or_real_peak
end JSP452Audit.StarHost