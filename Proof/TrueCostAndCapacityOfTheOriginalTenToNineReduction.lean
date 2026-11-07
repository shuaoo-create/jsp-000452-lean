import CountTheSameDeletedLabelsAndActualEdgesOnBothSides
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)

theorem first_reduction (cap:∀v,Nat.card (G.neighborSet v)≤10)
    (I:Set W.available) (stage:CompleteDegreeStage (G.induce W.available) 10 I)
    (B:Set ↥(W.supportᶜ:Set X)) (first:CompleteDegreeStage W.outside 10 B) :
    let S := W.spent I B
    W.seedLoss≤1 ∧ S.ncard+W.targetPorts≤W.rank+B.ncard ∧
      G.edgeSet.ncard+W.seedLoss=(G.induce Sᶜ).edgeSet.ncard+10*S.ncard ∧
      ∀v,Nat.card ((G.induce Sᶜ).neighborSet v)≤9 := by
  intro S
  have base := W.seed_edge_split cap
  have exactFee := W.spent_edges I B
  have count := W.spent_count I B
  have rank := W.inner_stage_seed_account cap I stage
  have left := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce W.available) I 10 stage.2.1 stage.1
  have right := JSP452Audit.StarHost.degree_on_independent_full_set W.outside B 10 first.2.1 first.1
  have small := (W.seed_loss_at_most_one cap).2
  have inner (v:W.available) := (induced_neighbor_count_le G W.available v).trans (cap v.val)
  have outer (v:↥(W.supportᶜ:Set X)) := (induced_neighbor_count_le G W.supportᶜ v).trans (cap v.val)
  have lcap := complete_stage_lowers_cap (G.induce W.available) 10 I inner stage
  have rcap := complete_stage_lowers_cap W.outside 10 B outer first
  change S.ncard=_ at count
  change (G.induce Sᶜ).edgeSet.ncard=_ at exactFee
  exact ⟨small,by omega,by omega,W.spent_cap I B 9 (fun v => Nat.le_of_lt_succ (lcap v)) (fun v => Nat.le_of_lt_succ (rcap v))⟩

#print axioms first_reduction
end JSP452Audit.StarHost.TenPortSupport
