import RowEnergy

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Every legal suffix pair in a forced row supplies both actual monochromatic
extreme colorings; taking one edge per star gives this matching floor. -/
theorem row_suffix_matching_floor {s t r : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    {X : Type*} [Finite X] (G : SimpleGraph X)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i j : ℕ) (hi : i < s) (hj : j < t) (sum : i+j = r) :
    max (s-i) (t-j) ≤ matchingEdges G := by
  have pair := row i j (s-i) (t-j) sum (by omega) (by omega) (by omega) (by omega)
  apply forcing_matching_floor (s := s-i) (t := t-j) (by omega) (by omega)
    (fun a => padDemand n (i+a.val)) (fun b => padDemand m (j+b.val)) _ _ G pair
  · intro a
    apply pad_positive n pn
    have := a.isLt
    omega
  · intro b
    apply pad_positive m pm
    have := b.isLt
    omega

/-- A strictly deficient actual row precedes the penultimate boundary in
both original lists, even for a host that is not chosen minimal. -/
theorem strict_row_range {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (r : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (strict : G.edgeSet.ncard < rowEnergy n m r) : r+2 ≤ s ∧ r+2 ≤ t := by
  have budget := row_energy_budget hs ht n m hn hm pn pm G r row
  have short : matchingEdges G < s+t-1-r := by change matchingEdges G < rowCount s t r; omega
  constructor
  · by_contra! bad
    let i := s-1
    let j := r-i
    have hi : i < s := by dsimp [i]; omega
    have hj : j < t := by dsimp [j,i]; omega
    have sum : i+j = r := by dsimp [j,i]; omega
    have blue := le_max_right (s-i) (t-j) |>.trans (row_suffix_matching_floor n m pn pm G row i j hi hj sum)
    dsimp [j,i] at blue
    omega
  · by_contra! bad
    let j := t-1
    let i := r-j
    have hi : i < s := by dsimp [i,j]; omega
    have hj : j < t := by dsimp [j]; omega
    have sum : i+j = r := by dsimp [i,j]; omega
    have red := le_max_left (s-i) (t-j) |>.trans (row_suffix_matching_floor n m pn pm G row i j hi hj sum)
    dsimp [i,j] at red
    omega

#print axioms row_suffix_matching_floor
#print axioms strict_row_range
end JSP452Audit.StarHost
