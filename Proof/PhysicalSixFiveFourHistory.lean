import ActualNestedDeletionLabels
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

structure SixFiveFourHistory {X:Type*} [Finite X] (G:SimpleGraph X) where
  six : Set X
  stageSix : CompleteDegreeStage G 6 six
  five : Set ↥(sixᶜ:Set X)
  stageFive : CompleteDegreeStage (G.induce sixᶜ) 5 five
  four : Set ↥((nestedRemoved six five)ᶜ:Set X)
  stageFour : CompleteDegreeStage (G.induce (nestedRemoved six five)ᶜ) 4 four

theorem six_five_four_history_exists {X:Type*} [Finite X] (G:SimpleGraph X) :
    Nonempty (SixFiveFourHistory G) := by
  obtain ⟨S,six⟩ := complete_degree_stage_exists G 6
  obtain ⟨T,five⟩ := complete_degree_stage_exists (G.induce Sᶜ) 5
  obtain ⟨V,four⟩ := complete_degree_stage_exists (G.induce (nestedRemoved S T)ᶜ) 4
  exact ⟨⟨S,six,T,five,V,four⟩⟩

theorem subset_of_stage_price {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (I:Set X)
    (stage:CompleteDegreeStage G D I) (k:ℕ) (fit:k≤I.ncard) :
    ∃A:Set X,A⊆I ∧ A.ncard=k ∧ G.edgeSet.ncard=(G.induce Aᶜ).edgeSet.ncard+D*k := by
  obtain ⟨A,sub,size⟩ := Set.exists_subset_card_eq fit
  have price := JSP452Audit.StarHost.degree_on_independent_full_set G A D (fun x hx => stage.2.1 x (sub hx)) (stage.1.mono sub)
  exact ⟨A,sub,size,size ▸ price⟩

namespace SixFiveFourHistory
variable {X:Type*} [Finite X] {G:SimpleGraph X} (H:SixFiveFourHistory G)

def fiveCut := nestedRemoved H.six H.five
def fourCut := nestedRemoved H.fiveCut H.four

theorem cut_counts : H.fiveCut.ncard=H.six.ncard+H.five.ncard ∧
    H.fourCut.ncard=H.fiveCut.ncard+H.four.ncard :=
  ⟨nested_removed_card _ _,nested_removed_card _ _⟩

theorem cut_caps (cap:∀v,Nat.card (G.neighborSet v)≤6) :
    (∀v,Nat.card ((G.induce H.fiveCutᶜ).neighborSet v)≤4) ∧
    (∀v,Nat.card ((G.induce H.fourCutᶜ).neighborSet v)≤3) := by
  have six := complete_stage_lowers_cap G 6 H.six cap H.stageSix
  have five := complete_stage_lowers_cap _ 5 H.five (fun v => by have := six v;omega) H.stageFive
  have low5 := nested_deletion_cap G H.six H.five 4 (fun v => by have := five v;omega)
  have four := complete_stage_lowers_cap (G.induce H.fiveCutᶜ) 4 H.four low5 H.stageFour
  exact ⟨low5,nested_deletion_cap G H.fiveCut H.four 3 (fun v => by have := four v;omega)⟩

theorem stage_prefix_price (k:ℕ) (fit:k≤H.fourCut.ncard) :
    ∃A:Set X,A.ncard=k ∧ G.edgeSet.ncard=(G.induce Aᶜ).edgeSet.ncard+4*k+min k H.fiveCut.ncard+min k H.six.ncard := by
  obtain ⟨fiveSize,fourSize⟩ := H.cut_counts
  by_cases atSix : k≤H.six.ncard
  · obtain ⟨A,_,num,price⟩ := subset_of_stage_price G 6 H.six H.stageSix k atSix
    refine ⟨A,num,?_⟩
    rw [min_eq_left atSix,min_eq_left (by omega : k≤H.fiveCut.ncard)]
    omega
  have sixPrice := JSP452Audit.StarHost.degree_on_independent_full_set G H.six 6 H.stageSix.2.1 H.stageSix.1
  by_cases atFive : k≤H.fiveCut.ncard
  · obtain ⟨V,_,num,part⟩ := subset_of_stage_price _ 5 H.five H.stageFive (k-H.six.ncard) (by omega)
    let A := nestedRemoved H.six V
    have count := nested_removed_card H.six V
    have saved := nested_deletion_edges G H.six V
    refine ⟨A,by change (nestedRemoved H.six V).ncard=k;omega,?_⟩
    rw [min_eq_left atFive,min_eq_right (by omega : H.six.ncard≤k)]
    dsimp only [A]
    omega
  · have fivePrice := JSP452Audit.StarHost.degree_on_independent_full_set _ H.five 5 H.stageFive.2.1 H.stageFive.1
    have fiveEdge := nested_deletion_edges G H.six H.five
    change _=(G.induce H.fiveCutᶜ).edgeSet.ncard at fiveEdge
    have take4 : k-H.fiveCut.ncard≤H.four.ncard := by clear * - fit fourSize;omega
    obtain ⟨V,_,num,part⟩ := subset_of_stage_price (G.induce H.fiveCutᶜ) 4 H.four H.stageFour (k-H.fiveCut.ncard) take4
    let A := nestedRemoved H.fiveCut V
    have count := nested_removed_card H.fiveCut V
    change V.ncard=k-H.fiveCut.ncard at num
    have saved := nested_deletion_edges G H.fiveCut V
    refine ⟨A,by change (nestedRemoved H.fiveCut V).ncard=k;omega,?_⟩
    rw [min_eq_right (by omega : H.fiveCut.ncard≤k),min_eq_right (by omega : H.six.ncard≤k)]
    dsimp only [A]
    omega

end SixFiveFourHistory
#print axioms six_five_four_history_exists
#print axioms subset_of_stage_price
#print axioms SixFiveFourHistory.cut_counts
#print axioms SixFiveFourHistory.cut_caps
#print axioms SixFiveFourHistory.stage_prefix_price
end JSP452Audit.StarHost
