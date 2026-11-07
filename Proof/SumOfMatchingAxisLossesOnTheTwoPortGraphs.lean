import ExtractActualAxisCopiesAfterEvenVertexDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable def axisAllowance {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r h : ℕ) : ℕ := by
  classical
  exact if 3≤h ∧ WinsHeight n m r h h 1 then 2*widthAt n m r h-R.jointPrice h else 0

theorem actual_axis_cost {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (space : t+2*(∑j,(m j-1)/2)≤R.totalCapacity) (h : ℕ) (pos : 0<h)
    (winner : WinsHeight n m r h h 1) :
    2*widthAt n m r h-R.jointPrice h≤originalThresholdCount n h := by
  let P := R.totalCapacity
  let Y := ∑j,(m j-1)/2
  let w := P+1-(t+Y)
  have fit : w≤P := by dsimp only [w];omega
  have mass := full_half_order_identity m pm
  change t+2*Y≤P at space
  have enough : P-w<∑j,(m j+1)/2 := by change (∑j,(m j+1)/2)=t+Y at mass;dsimp only [w];omega
  obtain ⟨exterior,retained⟩ := R.two_real_axis_inventories n m ht hn hm pn pm row w fit enough h pos
  have size := winner.2.2.2.2.2
  rw [original_threshold_one m pm] at size
  change 2*widthAt n m r h-(R.roots.ncard+2*P+uniformEnvelope (G.induce R.outside) h+uniformEnvelope R.retainedEdges h)≤_
  rw [size]
  apply matching_axis_double_loss _ t r R.roots.ncard P Y w 1 _ _ space ht rfl (by decide)
  intro _
  simpa only [Nat.add_sub_cancel] using And.intro exterior retained

theorem all_axis_allowances {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (space : t+2*(∑j,(m j-1)/2)≤R.totalCapacity) :
    (∑i∈Finset.range 8,R.axisAllowance n m r (i+2))≤2*∑i,(n i-1)/2 := by
  classical
  have each (i : ℕ) : R.axisAllowance n m r (i+3)≤originalThresholdCount n (i+3) := by
    unfold axisAllowance
    split
    · rename_i live
      exact R.actual_axis_cost n m ht hn hm pn pm row space _ (by omega) live.2
    · omega
  have sum := Finset.sum_le_sum (s:=Finset.range 7) (fun i _ => each i)
  have budget := large_threshold_sum n 7
  have zero : R.axisAllowance n m r 2=0 := by simp [axisAllowance]
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add,zero,Nat.add_zero]
  exact sum.trans budget

#print axioms actual_axis_cost
#print axioms all_axis_allowances
end NinePortRegion
end JSP452Audit.StarHost
