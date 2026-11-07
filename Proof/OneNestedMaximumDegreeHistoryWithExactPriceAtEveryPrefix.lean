import ChooseARealMaximumDegreeVertexOfEachOriginalResidual
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)
noncomputable def chosenPeakStep (U:Set X) : PeakRemoval G U := Classical.choice (peak_removal_exists G U)
noncomputable def peakPrefix : ℕ→Set X
  | 0 => ∅
  | i+1 => (chosenPeakStep G (peakPrefix i)).removed
noncomputable abbrev peakFee (i:ℕ) := (chosenPeakStep G (peakPrefix G i)).fee

theorem peak_prefix_nested : Monotone (peakPrefix G) := by
  exact monotone_nat_of_le_succ (fun i => (chosenPeakStep G (peakPrefix G i)).extendsCut)

theorem peak_prefix_size (i:ℕ) : (peakPrefix G i).ncard=min i (Nat.card X) := by
  induction i with
  | zero => simp [peakPrefix]
  | succ i ih =>
    have step := (chosenPeakStep G (peakPrefix G i)).size
    change (peakPrefix G (i+1)).ncard=_ at step
    rw [ih] at step;omega

theorem peak_fee_antitone : Antitone (peakFee G) := by
  apply antitone_nat_of_succ_le
  intro i
  let U := peakPrefix G i
  let V := peakPrefix G (i+1)
  have sub : U⊆V := (chosenPeakStep G U).extendsCut
  rcases (chosenPeakStep G V).attained with zero|⟨v,real⟩
  · change (chosenPeakStep G V).fee≤_;omega
  · rw [show peakFee G (i+1)=Nat.card ((G.induce Vᶜ).neighborSet v) from real.symm]
    exact (nested_original_degree G U V sub v).trans ((chosenPeakStep G U).cap _)

theorem peak_fee_after_all (i:ℕ) (exhausted:Nat.card X ≤ i) : peakFee G i=0 := by
  let U := peakPrefix G i
  have size := peak_prefix_size G i
  have all : U=Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ U)
    rw [Set.ncard_univ];change _≤(peakPrefix G i).ncard;omega
  rcases (chosenPeakStep G U).attained with zero|⟨v,_⟩
  · exact zero
  · exact (v.property (all.ge (Set.mem_univ v.val))).elim

theorem peak_prefix_edge_account (i:ℕ) :
    G.edgeSet.ncard=(G.induce (peakPrefix G i)ᶜ).edgeSet.ncard+∑j∈Finset.range i,peakFee G j := by
  induction i with
  | zero =>
    rw [show (peakPrefix G 0)ᶜ=(Set.univ:Set X) from Set.compl_empty]
    simp only [Finset.range_zero,Finset.sum_empty,Nat.add_zero]
    exact (Nat.card_congr (induceUnivIso G).mapEdgeSet).symm
  | succ i ih =>
    have step := (chosenPeakStep G (peakPrefix G i)).edgeCount
    change (G.induce (peakPrefix G i)ᶜ).edgeSet.ncard=(G.induce (peakPrefix G (i+1))ᶜ).edgeSet.ncard+peakFee G i at step
    rw [Finset.sum_range_succ]
    omega

#print axioms peak_prefix_nested
#print axioms peak_prefix_size
#print axioms peak_fee_antitone
#print axioms peak_fee_after_all
#print axioms peak_prefix_edge_account
end JSP452Audit.StarHost
