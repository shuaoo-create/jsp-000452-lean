import StrictNormalization
import StrictRowRange
import BlueExcessObstruction
namespace JSP452Audit.StarHost
open SimpleGraph

/-- A counterexample to the *original* equality would produce a strict
    normalized induced host with actual vertex labels and a full suffix row. -/
theorem normalized_source_of_failure {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (fail : sizeRamsey (forest n) (forest m) ≠ ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)) (U : Finset (Fin N)),
      let Y := G.induce {x | x∉U}; let r := U.card
      ForcingRow Y s t (padDemand n) (padDemand m) r ∧
      2≤rowCount s t r ∧ r+2≤s ∧ r+2≤t ∧ Y.edgeSet.ncard+1=rowEnergy n m r ∧
      matchingEdges Y < rowCount s t r ∧
      (∀ v, Nat.card (Y.neighborSet v) ≤ diagonal n m (r+2)-1) ∧
      (∃ v, Nat.card (Y.neighborSet v) = diagonal n m (r+2)-1) ∧
      ∀ (i : Fin s) (j : Fin t), i.val+j.val=r → diagonal n m (r+2)=n i+m j-1 →
        2≤n i ∧ 2≤m j := by
  obtain ⟨N,G,edge,forces⟩ := star_min_attained n m
  have bound := erdos561_upper n m
  have strict : G.edgeSet.ncard < rowEnergy n m 0 := by rw [edge,rowEnergy_zero]; omega
  obtain ⟨U,bad,children⟩ := maximal_strict_deletion n m G 0 strict
  let Y := G.induce {x | x∉U}
  have hY : ForcingRow Y s t (padDemand n) (padDemand m) U.card := by
    have h0 := (finite_targets_row_zero G hs ht n m).mpr forces
    simpa only [Nat.zero_add] using row_delete_finset G U _ _ (pad_antitone n hn) (pad_antitone m hm)
      (pad_positive n pn) (pad_positive m pm) h0
  simp only [Nat.zero_add] at bad children
  obtain ⟨rank,one,unpaid,allV,peak,heads⟩ := strict_local_normal hs ht n m hn hm pn pm Y U.card hY bad children
  obtain ⟨sr,tr⟩ := strict_row_range hs ht n m hn hm pn pm Y U.card hY bad
  exact ⟨N,G,U,hY,rank,sr,tr,one,unpaid,allV,peak,heads⟩

#print axioms normalized_source_of_failure
end JSP452Audit.StarHost
