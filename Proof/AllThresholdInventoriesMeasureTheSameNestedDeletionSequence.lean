import OneNestedMaximumDegreeHistoryWithExactPriceAtEveryPrefix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)

theorem eventually_below_fee (j:ℕ) : ∃i,peakFee G i≤j :=
  ⟨Nat.card X,by rw [peak_fee_after_all G _ le_rfl];omega⟩
noncomputable def peakCountAbove (j:ℕ) : ℕ := Nat.find (eventually_below_fee G j)

theorem peak_inventory_spec (j:ℕ) :
    peakCountAbove G j≤Nat.card X ∧ peakFee G (peakCountAbove G j)≤j ∧
      ∀i,i<peakCountAbove G j ↔ j<peakFee G i := by
  have last := Nat.find_spec (eventually_below_fee G j)
  change peakFee G (peakCountAbove G j)≤j at last
  refine ⟨Nat.find_min' _ (by rw [peak_fee_after_all G _ le_rfl];omega),last,?_⟩
  intro i
  constructor
  · intro before
    exact Nat.lt_of_not_ge (Nat.find_min (eventually_below_fee G j) before)
  · intro costly
    by_contra! after
    have bound := (peak_fee_antitone G after).trans last
    omega

theorem peak_counts_antitone : Antitone (peakCountAbove G) := by
  intro a b less
  exact Nat.find_min' _ ((peak_inventory_spec G a).2.1.trans less)

theorem exact_peak_inventory_cut (j:ℕ) :
    let T := peakPrefix G (peakCountAbove G j)
    T.ncard=peakCountAbove G j ∧ ∀v:↥(Tᶜ:Set X),Nat.card ((G.induce Tᶜ).neighborSet v)≤j := by
  intro T
  have inv := peak_inventory_spec G j
  exact ⟨(peak_prefix_size G _).trans (min_eq_left inv.1),fun v => ((chosenPeakStep G T).cap v).trans inv.2.1⟩

theorem peak_prefix_layer_price (D i:ℕ) (cap:∀v,Nat.card (G.neighborSet v)≤D) :
    G.edgeSet.ncard=(G.induce (peakPrefix G i)ᶜ).edgeSet.ncard+
      ∑j∈Finset.range D,min i (peakCountAbove G j) := by
  have bound (k:ℕ) : peakFee G k≤D := by
    rcases (chosenPeakStep G (peakPrefix G k)).attained with zero|⟨v,att⟩
    · change (chosenPeakStep G _).fee≤D;omega
    · exact att.symm.trans_le ((induced_neighbor_count_le G _ v).trans (cap v.val))
  rw [peak_prefix_edge_account G i,finite_layer_count (peakFee G) i D (fun k _ => bound k)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have filt : ((Finset.range i).filter fun k => j+1≤peakFee G k)=Finset.range (min i (peakCountAbove G j)) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,lt_min_iff]
    have iff := (peak_inventory_spec G j).2.2 k
    omega
  rw [filt,Finset.card_range]

#print axioms peak_inventory_spec
#print axioms peak_counts_antitone
#print axioms exact_peak_inventory_cut
#print axioms peak_prefix_layer_price
end JSP452Audit.StarHost
