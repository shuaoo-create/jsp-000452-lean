import UntouchedComponents
import ParityRestore

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Restoring one vertex that meets at most two old components loses at most
    one odd component. The only input is the neighbor geometry of this vertex. -/
theorem restore_two_components {X : Type*} [Finite X] (H : SimpleGraph X) (v : X)
    (two : {c | componentTouches H v c}.ncard ≤ 2) :
    (H.induce {x | x≠v}).oddComponents.ncard ≤ H.oddComponents.ncard + 1 := by
  classical
  let Y := H.induce {x | x≠v}
  let keep : Set Y.ConnectedComponent := {c | ¬componentTouches H v c ∧ Odd c.supp.ncard}
  let touch : Set Y.ConnectedComponent := {c | componentTouches H v c}
  have cov : Y.oddComponents ⊆ keep ∪ touch := by
    intro c odd
    by_cases meets : componentTouches H v c
    · exact Or.inr meets
    · exact Or.inl ⟨meets,odd⟩
  have bound := (Set.ncard_le_ncard cov).trans (Set.ncard_union_le keep touch)
  have safe : keep.ncard ≤ H.oddComponents.ncard := by
    rw [show keep.ncard = _ from untouched_odd_count H v]
    exact Set.ncard_le_ncard (fun _ mem => mem.2) (Set.toFinite _)
  apply restore_odd_loss H v
  change Y.oddComponents.ncard ≤ H.oddComponents.ncard+2
  change touch.ncard ≤ 2 at two
  omega

theorem restore_two_score {X : Type*} [Finite X] (H : SimpleGraph X) (v : X) (k : ℕ)
    (two : {c | componentTouches H v c}.ncard ≤ 2) :
    ((H.induce {x | x≠v}).oddComponents.ncard : ℤ) - (k+1 : ℕ) ≤
      (H.oddComponents.ncard : ℤ) - k := by
  have := restore_two_components H v two
  omega

#print axioms restore_two_components
#print axioms restore_two_score
end JSP452Audit.StarHost
