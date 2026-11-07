import ProfileLossAboveAnyFixedDeletionDegree
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem add_full_stage_to_edge_account {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X) (a inc:ℕ)
    (bill:G.edgeSet.ncard=(G.induce Uᶜ).edgeSet.ncard+(a+1)*U.ncard+inc)
    (I:Set ↥(Uᶜ:Set X)) (stage:CompleteDegreeStage (G.induce Uᶜ) a I) :
    G.edgeSet.ncard=(G.induce (nestedRemoved U I)ᶜ).edgeSet.ncard+a*(nestedRemoved U I).ncard+inc+U.ncard := by
  have extra := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce Uᶜ) I a stage.2.1 stage.1
  rw [nested_deletion_edges G U I] at extra
  rw [nested_removed_card,Nat.mul_add]
  rw [Nat.add_mul,Nat.one_mul] at bill
  omega

theorem take_partial_stage_at_cap {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X) (a inc:ℕ)
    (cap:∀v,Nat.card ((G.induce Uᶜ).neighborSet v)≤a)
    (bill:G.edgeSet.ncard=(G.induce Uᶜ).edgeSet.ncard+(a+1)*U.ncard+inc)
    (I:Set ↥(Uᶜ:Set X)) (stage:CompleteDegreeStage (G.induce Uᶜ) a I) (k:ℕ)
    (lo:U.ncard≤k) (hi:k≤(nestedRemoved U I).ncard) :
    ∃V:Set X,V.ncard=k ∧ U⊆V ∧ (∀v,Nat.card ((G.induce Vᶜ).neighborSet v)≤a) ∧
      G.edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+a*k+inc+U.ncard := by
  have all := nested_removed_card U I
  obtain ⟨T,_,num,fee⟩ := subset_of_stage_price _ a I stage (k-U.ncard) (by omega)
  let V := nestedRemoved U T
  have size := nested_removed_card U T
  have exactSize : V.ncard=k := by change V.ncard=_ at size;omega
  refine ⟨V,exactSize,Set.subset_union_left,?_,?_⟩
  · exact nested_deletion_cap G U T a (fun x => (induced_neighbor_count_le _ Tᶜ x).trans (cap x.val))
  · rw [nested_deletion_edges G U T] at fee
    change (G.induce Uᶜ).edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+a*(k-U.ncard) at fee
    have prod : a*k=a*U.ncard+a*(k-U.ncard) := by rw [←Nat.mul_add];congr 1;omega
    rw [Nat.add_mul,Nat.one_mul] at bill
    omega

structure TenLowHistory {X:Type u} [Finite X] (G:SimpleGraph X) where
  high : ThreeDegreeStages G 8
  seven : Set ↥(high.lastCutᶜ:Set X)
  stageSeven : CompleteDegreeStage (G.induce high.lastCutᶜ) 7 seven
  six : Set ↥((nestedRemoved high.lastCut seven)ᶜ:Set X)
  stageSix : CompleteDegreeStage (G.induce (nestedRemoved high.lastCut seven)ᶜ) 6 six

theorem ten_low_history_exists {X:Type u} [Finite X] (G:SimpleGraph X) : Nonempty (TenLowHistory G) := by
  obtain ⟨H⟩ := three_degree_stages_exist G 8
  obtain ⟨A,a⟩ := complete_degree_stage_exists (G.induce H.lastCutᶜ) 7
  obtain ⟨B,b⟩ := complete_degree_stage_exists (G.induce (nestedRemoved H.lastCut A)ᶜ) 6
  exact ⟨⟨H,A,a,B,b⟩⟩

namespace TenLowHistory
variable {X:Type u} [Finite X] {G:SimpleGraph X} (H:TenLowHistory G)
abbrev sevenCut := nestedRemoved H.high.lastCut H.seven
abbrev sixCut := nestedRemoved H.sevenCut H.six

theorem remaining_caps (cap:∀x,Nat.card (G.neighborSet x)≤10) :
    (∀x,Nat.card ((G.induce H.high.lastCutᶜ).neighborSet x)≤7) ∧
    (∀x,Nat.card ((G.induce H.sevenCutᶜ).neighborSet x)≤6) ∧
    (∀x,Nat.card ((G.induce H.sixCutᶜ).neighborSet x)≤5) := by
  have eight := (H.high.degree_caps cap).2.2
  have low (x) : Nat.card ((G.induce H.high.lastCutᶜ).neighborSet x)≤7 := Nat.le_of_lt_succ (eight x)
  have mid := complete_stage_lowers_cap _ 7 H.seven low H.stageSeven
  have mid' := nested_deletion_cap G H.high.lastCut H.seven 6 (fun x => Nat.le_of_lt_succ (mid x))
  have last := complete_stage_lowers_cap _ 6 H.six mid' H.stageSix
  exact ⟨low,mid',nested_deletion_cap G H.sevenCut H.six 5 (fun x => Nat.le_of_lt_succ (last x))⟩

theorem low_cut_edge_counts (cap:∀x,Nat.card (G.neighborSet x)≤10) :
    G.edgeSet.ncard=(G.induce H.high.lastCutᶜ).edgeSet.ncard+8*H.high.lastCut.ncard+H.high.upper.ncard+H.high.midCut.ncard ∧
    G.edgeSet.ncard=(G.induce H.sevenCutᶜ).edgeSet.ncard+7*H.sevenCut.ncard+H.high.upper.ncard+H.high.midCut.ncard+H.high.lastCut.ncard := by
  have first := (consecutive_ten_nine_account G cap H.high.upper H.high.middle H.high.first H.high.second).1
  have one := add_full_stage_to_edge_account G H.high.midCut 8 H.high.upper.ncard first H.high.lower H.high.third
  change G.edgeSet.ncard=(G.induce H.high.lastCutᶜ).edgeSet.ncard+8*H.high.lastCut.ncard+H.high.upper.ncard+H.high.midCut.ncard at one
  have bill : G.edgeSet.ncard=(G.induce H.high.lastCutᶜ).edgeSet.ncard+(7+1)*H.high.lastCut.ncard+
      (H.high.upper.ncard+H.high.midCut.ncard) := by omega
  have two := add_full_stage_to_edge_account G H.high.lastCut 7 _ bill H.seven H.stageSeven
  change G.edgeSet.ncard=(G.induce H.sevenCutᶜ).edgeSet.ncard+7*H.sevenCut.ncard+(H.high.upper.ncard+H.high.midCut.ncard)+H.high.lastCut.ncard at two
  exact ⟨one,by omega⟩
end TenLowHistory
#print axioms add_full_stage_to_edge_account
#print axioms take_partial_stage_at_cap
#print axioms ten_low_history_exists
#print axioms TenLowHistory.remaining_caps
#print axioms TenLowHistory.low_cut_edge_counts
end JSP452Audit.StarHost
