import RowArithmetic
import DropHitStar
import RestoreColor
import AvoidIsolated

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Restore all deleted edges in red. A red copy can lose one component and
    a blue target with no isolated vertex survives intact on the induced host. -/
theorem delete_red_star {X W : Type*} {l : ℕ} (G : SimpleGraph X) (v : X)
    (n : Fin (l+1) → ℕ) (hn : Antitone n) (H : SimpleGraph W)
    (pos : ∀ a, ∃ b, H.Adj a b) (forces : Forces G (forest n) H) :
    Forces (G.induce {x | x ≠ v}) (forest (fun i : Fin l => n i.succ)) H := by
  intro R hR
  let A := restoreIncidentRed G v R
  rcases forces A (restoreIncidentRed_le G v R) with red | blue
  · have survivor := dropHitStar A v n hn red
    rw [restoreIncidentRed_induce G v R hR] at survivor
    exact Or.inl survivor
  · have iso : ∀ x, ¬(G \ A).Adj v x := fun _ h => (restoreIncidentRed_blue_endpoints h).1 rfl
    have survivor := copy_avoids_isolated v pos iso blue
    rw [restoreIncidentRed_blue_induce G v R] at survivor
    exact Or.inr survivor

/-- The *entire* next legal suffix row is forced on the very same residual host. -/
theorem row_delete_one {X : Type*} {s t r : ℕ} (G : SimpleGraph X) (v : X)
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, i<s → 0 < n i) (pm : ∀ j, j<t → 0 < m j)
    (row : ForcingRow G s t n m r) :
    ForcingRow (G.induce {x | x ≠ v}) s t n m (r+1) := by
  apply rowStep_of_starDeletion G v n m row
  · intro i j l q _ hq forces
    let R (a : Fin (l+1)) := n (i+a.val)
    have sorted : Antitone R := fun a b h => hn (Nat.add_le_add_left h _)
    have pos (a : Fin q) : 1 ≤ m (j+a.val) := pm _ (by have := a.isLt; omega)
    have h := delete_red_star G v R sorted (suffixStars m j q) (forest_has_neighbor _ pos) forces
    change Forces _ (forest (fun a : Fin l => n (i+a.succ.val))) _ at h
    rw [suffix_tail_eq n i l] at h
    exact h
  · intro i j l q hl _ forces
    let B (a : Fin (q+1)) := m (j+a.val)
    have sorted : Antitone B := fun a b h => hm (Nat.add_le_add_left h _)
    have pos (a : Fin l) : 1 ≤ n (i+a.val) := pn _ (by have := a.isLt; omega)
    have h := delete_red_star G v B sorted (suffixStars n i l) (forest_has_neighbor _ pos) (forces_swap forces)
    change Forces _ (forest (fun a : Fin q => m (j+a.succ.val))) _ at h
    rw [suffix_tail_eq m j q] at h
    exact forces_swap h

#print axioms delete_red_star
#print axioms row_delete_one
end JSP452Audit.StarHost
