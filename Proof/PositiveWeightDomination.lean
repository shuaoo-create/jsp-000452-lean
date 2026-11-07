import ComponentSurplusSum
import PositiveSelection

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Discarding a subfamily whose members each have nonpositive signed
surplus can only increase the surplus of the retained induced core. -/
theorem core_surplus_le_of_discarded_nonpos {X : Type*} [Finite X] (G : SimpleGraph X)
    (S : Set X) (T P : Set (G.induce Sᶜ).ConnectedComponent) (D : ℕ) (sub : P ⊆ T)
    (discard : ∀ c ∈ T, c ∉ P → edgeSurplus ((G.induce Sᶜ).induce c.supp) D ≤ 0) :
    edgeSurplus (G.induce (regionCore G S T)) D ≤ edgeSurplus (G.induce (regionCore G S P)) D := by
  classical
  let _ := Fintype.ofFinite T
  let _ := Fintype.ofFinite P
  let t := T.toFinite.toFinset
  let p := P.toFinite.toFinset
  let w (c : (G.induce Sᶜ).ConnectedComponent) := edgeSurplus ((G.induce Sᶜ).induce c.supp) D
  have incl : p ⊆ t := fun _ hc => (Set.Finite.mem_toFinset _).mpr (sub ((Set.Finite.mem_toFinset _).mp hc))
  have nonpositive : (∑ c ∈ t \ p, w c) ≤ 0 := by
    apply Finset.sum_nonpos
    intro c hc
    obtain ⟨ct,cp⟩ := Finset.mem_sdiff.mp hc
    exact discard c ((Set.Finite.mem_toFinset _).mp ct) (fun mem => cp ((Set.Finite.mem_toFinset _).mpr mem))
  have total := Finset.sum_sdiff (f := w) incl
  rw [core_surplus_eq_sum G S T D,core_surplus_eq_sum G S P D]
  change (∑ c : T, w c.val) ≤ (∑ c : P, w c.val)
  rw [← Finset.sum_subtype t (fun c => Set.Finite.mem_toFinset _) w,
      ← Finset.sum_subtype p (fun c => Set.Finite.mem_toFinset _) w]
  omega

/-- Concrete positive filter written out as a set of actual residual components. -/
theorem positive_core_surplus_dominates {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (D : ℕ) :
    edgeSurplus (G.induce (regionCore G S T)) D ≤
      edgeSurplus (G.induce (regionCore G S {c | c ∈ T ∧ 0 < edgeSurplus ((G.induce Sᶜ).induce c.supp) D})) D := by
  apply core_surplus_le_of_discarded_nonpos G S T _ D (fun _ h => h.1)
  intro c inT discarded
  exact le_of_not_gt (fun pos => discarded ⟨inT,pos⟩)

/-- The positive-piece graph dominates the original selected graph in signed surplus. -/
theorem positivePieces_dominate {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (D : ℕ) :
    edgeSurplus (G.induce (regionCore G S T)) D ≤
      edgeSurplus (G.induce (regionCore G S (positivePieces G S T D))) D :=
  positive_core_surplus_dominates G S T D

#print axioms positivePieces_dominate

#print axioms positive_core_surplus_dominates

#print axioms core_surplus_le_of_discarded_nonpos
end JSP452Audit.StarHost
