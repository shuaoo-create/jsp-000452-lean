import AvailableSixStagePaysHalfOrders
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

structure EightSevenSixHistory {X:Type*} [Finite X] (G:SimpleGraph X) where
  eight : Set X
  first : CompleteDegreeStage G 8 eight
  seven : Set ↥(eightᶜ:Set X)
  second : CompleteDegreeStage (G.induce eightᶜ) 7 seven
  six : Set ↥((nestedRemoved eight seven)ᶜ:Set X)
  third : CompleteDegreeStage (G.induce (nestedRemoved eight seven)ᶜ) 6 six

theorem eight_seven_six_history_exists {X:Type*} [Finite X] (G:SimpleGraph X) : Nonempty (EightSevenSixHistory G) := by
  obtain ⟨B,first⟩ := complete_degree_stage_exists G 8
  obtain ⟨C,second⟩ := complete_degree_stage_exists (G.induce Bᶜ) 7
  obtain ⟨A,third⟩ := complete_degree_stage_exists (G.induce (nestedRemoved B C)ᶜ) 6
  exact ⟨⟨B,first,C,second,A,third⟩⟩

namespace EightSevenSixHistory
variable {X:Type*} [Finite X] {G:SimpleGraph X} (H:EightSevenSixHistory G)
abbrev sevenCut := nestedRemoved H.eight H.seven
abbrev sixCut := nestedRemoved H.sevenCut H.six

theorem counts : H.sevenCut.ncard=H.eight.ncard+H.seven.ncard ∧ H.sixCut.ncard=H.sevenCut.ncard+H.six.ncard :=
  ⟨nested_removed_card _ _,nested_removed_card _ _⟩

theorem caps (cap:∀v,Nat.card (G.neighborSet v)≤8) :
    (∀v,Nat.card ((G.induce H.eightᶜ).neighborSet v)≤7) ∧
    (∀v,Nat.card ((G.induce H.sevenCutᶜ).neighborSet v)≤6) ∧
    (∀v,Nat.card ((G.induce H.sixCutᶜ).neighborSet v)≤5) := by
  have one (x) : Nat.card ((G.induce H.eightᶜ).neighborSet x)≤7 := by have := complete_stage_lowers_cap G 8 H.eight cap H.first x;omega
  have two := complete_stage_lowers_cap _ 7 H.seven one H.second
  have second := nested_deletion_cap G H.eight H.seven 6 (fun x => by have := two x;omega)
  have three := complete_stage_lowers_cap (G.induce H.sevenCutᶜ) 6 H.six second H.third
  exact ⟨one,second,nested_deletion_cap G H.sevenCut H.six 5 (fun x => by have := three x;omega)⟩

theorem exact_penultimate_prefix (k:ℕ) (short:H.sevenCut.ncard<k) (fits:k≤H.sixCut.ncard) :
    ∃V:Set X,V.ncard=k ∧ G.edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+6*k+H.eight.ncard+H.sevenCut.ncard := by
  obtain ⟨first,second⟩ := H.counts
  have fit : k-H.sevenCut.ncard≤H.six.ncard := by omega
  obtain ⟨V,_,size,part⟩ := subset_of_stage_price (G.induce H.sevenCutᶜ) 6 H.six H.third (k-H.sevenCut.ncard) fit
  let A := nestedRemoved H.sevenCut V
  have count := nested_removed_card H.sevenCut V
  change A.ncard=H.sevenCut.ncard+V.ncard at count
  have cost8 := JSP452Audit.StarHost.degree_on_independent_full_set G H.eight 8 H.first.2.1 H.first.1
  have cost7 := JSP452Audit.StarHost.degree_on_independent_full_set _ H.seven 7 H.second.2.1 H.second.1
  have after7 := nested_deletion_edges G H.eight H.seven
  change _=(G.induce H.sevenCutᶜ).edgeSet.ncard at after7
  have after6 := nested_deletion_edges G H.sevenCut V
  change _=(G.induce Aᶜ).edgeSet.ncard at after6
  exact ⟨A,by omega,by omega⟩

#print axioms counts
#print axioms caps
#print axioms exact_penultimate_prefix
end EightSevenSixHistory
#print axioms eight_seven_six_history_exists
end JSP452Audit.StarHost
