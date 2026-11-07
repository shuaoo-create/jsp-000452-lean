import BinarySplitBounds
import ReserveRowBudget
namespace JSP452Audit.StarHost
open SimpleGraph
/-- The three necessary lower bounds are simultaneous on one host. If it
misses the binary area, they all bind and there is exactly one missing edge. -/
theorem strict_binary_tight {X : Type*} [Finite X] (G : SimpleGraph X)
    (p q a b : ℕ) (hp : 0<p) (hq : 0<q)
    (force : Forces G (forest (binaryProfile p a)) (forest (binaryProfile q b)))
    (split : CanSplitRank G) (under : G.edgeSet.ncard<3*(p+q-1)+2*max a b+min a b) :
    G.edgeSet.ncard+1=3*(p+q-1)+2*max a b+min a b ∧ matchingEdges G = p+q-1+a+b-1 ∧
    deletionBudget G 1=p+q-1+max a b ∧ deletionBudget G 2=p+q-1 ∧ baseReserve G 2=0 := by
  let f := binaryProfile p a
  let g := binaryProfile q b
  have hs : 0<p+a := by omega
  have ht : 0<q+b := by omega
  have row := (finite_targets_row_zero G hs ht f g).mpr force
  have rank := rank_floor_of_splittable G hs ht f g (binaryProfile_positive p a) (binaryProfile_positive q b) force split
  have layers (j : ℕ) (pos : 0<j) := original_width_le_deletion hs ht f g (binaryProfile_antitone p a)
    (binaryProfile_antitone q b) (binaryProfile_positive p a) (binaryProfile_positive q b) G 0 j row pos
  obtain ⟨one,two⟩ := binary_widths hp hq a b
  have h1 := layers 1 (by decide)
  have h2 := layers 2 (by decide)
  change widthAt (binaryProfile p a) (binaryProfile q b) 0 2 ≤ deletionBudget G 1 at h1
  change widthAt (binaryProfile p a) (binaryProfile q b) 0 3 ≤ deletionBudget G 2 at h2
  rw [one] at h1; rw [two] at h2
  have total := base_reserve_account G 2
  simp [Finset.sum_range_succ] at total
  omega
#print axioms strict_binary_tight
end JSP452Audit.StarHost