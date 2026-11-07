import EmbeddedHeadAxisUpper
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem core_edges_pay_matching_and_width (G : SimpleGraph X) {D : ℕ} (large : 2≤D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (K : DegreeRegion G D)
    (h : ℕ) (width : h≤minimumExposure G D) :
    D*matchingEdges (G.induce K.core)+h≤(G.induce K.core).edgeSet.ncard := by
  have identity := K.weight_identity cap
  have scale := Nat.mul_le_mul_right (minimumExposure G D) large
  have paid : (2:ℤ)*(minimumExposure G D:ℤ)≤(D:ℤ)*(minimumExposure G D:ℤ) := by exact_mod_cast scale
  have wz : (h:ℤ)≤minimumExposure G D := by exact_mod_cast width
  unfold edgeSurplus at identity
  have fee : (D:ℤ)*(matchingEdges (G.induce K.core):ℤ)+(h:ℤ)≤((G.induce K.core).edgeSet.ncard:ℤ) := by omega
  exact_mod_cast fee

/-- Price the original head-at-cap row by its actual shorter blue successor
and the edges erased inside this same ordinary region. -/
theorem head_at_cap_erasure_pays {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (G : SimpleGraph X)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1) (room : s+r+highestWidth n m r≤t)
    (large : 2≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (K : DegreeRegion G D)
    (width : highestWidth n m r≤minimumExposure G D)
    (tailLive : r<t-matchingEdges (G.induce K.core))
    (smaller : rowEnergy n (remainingDemand m (matchingEdges (G.induce K.core))) r+
      (G.induce K.core).edgeSet.ncard≤G.edgeSet.ncard) : rowEnergy n m r≤G.edgeSet.ncard := by
  let μ := matchingEdges (G.induce K.core)
  let h := highestWidth n m r
  have original := embedded_head_axis_upper hs ht n m hn hm pm head top room
  have next := row_energy_at_least_unit_axis hs n (remainingDemand m μ) (remainingDemand_positive m pm μ)
    tailLive D head
  have fee := core_edges_pay_matching_and_width G large cap K h width
  have split : t-1-r=(t-μ-1-r)+μ := by change r<t-μ at tailLive;omega
  change rowEnergy n m r≤(t-1-r)*D+(∑i,n i)+h at original
  rw [split,Nat.add_mul,Nat.mul_comm μ D] at original
  change D*μ+h≤(G.induce K.core).edgeSet.ncard at fee
  change rowEnergy n (remainingDemand m μ) r+(G.induce K.core).edgeSet.ncard≤G.edgeSet.ncard at smaller
  omega

theorem row_energy_colour_swap {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    rowEnergy n m r=rowEnergy m n r := by
  unfold rowEnergy
  rw [show rowCount s t r=rowCount t s r by simp [rowCount,Nat.add_comm s t]]
  apply Finset.sum_congr rfl
  intro j _;exact diagonal_swap n m _

theorem highest_width_colour_swap {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    highestWidth n m r=highestWidth m n r := by
  unfold highestWidth highestOffsets
  rw [show rowCount s t r=rowCount t s r by simp [rowCount,Nat.add_comm s t]]
  congr 1;apply Finset.filter_congr
  intro j _
  rw [diagonal_swap n m (r+j+2),diagonal_swap n m (r+2)]

#print axioms core_edges_pay_matching_and_width
#print axioms head_at_cap_erasure_pays
#print axioms row_energy_colour_swap
#print axioms highest_width_colour_swap
end JSP452Audit.StarHost
