import SixSpareComponentCapacityGuard
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

def CompleteDegreeStage {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (I:Set X) : Prop :=
  G.IsIndepSet I ∧ (∀v∈I,Nat.card (G.neighborSet v)=D) ∧
    ∀v,Nat.card (G.neighborSet v)=D → v∈I ∨ ∃w∈I,G.Adj v w

theorem complete_degree_stage_exists {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) :
    ∃I:Set X,CompleteDegreeStage G D I := by
  obtain ⟨I,_,full,ind,dom⟩ := choose_full_exterior_independent G Set.univ D
  exact ⟨I,ind,full,fun v => dom v (Set.mem_univ _)⟩

theorem complete_stage_lowers_cap {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (I:Set X)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (stage:CompleteDegreeStage G D I) :
    ∀v:↥(Iᶜ:Set X),Nat.card ((G.induce Iᶜ).neighborSet v)<D := by
  intro v
  by_contra! full
  have le := induced_neighbor_count_le G Iᶜ v
  have exactLocal := le_antisymm (le.trans (cap v.val)) full
  have exactGlobal := le_antisymm (cap v.val) (full.trans le)
  obtain hit|⟨w,inside,adj⟩ := stage.2.2 v.val exactGlobal
  · exact v.property hit
  · exact (all_neighbors_survive_of_induced_full G Iᶜ v D (cap v.val) exactLocal w adj) inside

theorem original_stage_width_and_cost {s t r D:ℕ} {X:Type*} [Finite X] (G:SimpleGraph X)
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hs:0<s) (ht:0<t) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (pos:0<D)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (I:Set X) (stage:CompleteDegreeStage G D I) :
    widthAt n m r (D+1)≤I.ncard ∧ G.edgeSet.ncard=(G.induce Iᶜ).edgeSet.ncard+D*I.ncard ∧
    ForcingRow (G.induce Iᶜ) s t (padDemand n) (padDemand m) (r+I.ncard) := by
  have low := complete_stage_lowers_cap G D I cap stage
  have feasible : admits_matching_remainder (G.induce Iᶜ) D := by
    refine ⟨⊥,fun _ h => h.elim,?_⟩
    intro v
    rw [Subgraph.spanningCoe_bot,sdiff_bot]
    have := low v
    omega
  have upper := original_width_le_deletion hs ht n m hn hm pn pm G r D row pos
  exact ⟨upper.trans (deletionBudget_le_of_witness G D I feasible),
    JSP452Audit.StarHost.degree_on_independent_full_set G I D stage.2.1 stage.1,
    row_delete_set G I _ _ (pad_antitone n hn) (pad_antitone m hm) (pad_positive n pn) (pad_positive m pm) row⟩

#print axioms complete_degree_stage_exists
#print axioms complete_stage_lowers_cap
#print axioms original_stage_width_and_cost
end JSP452Audit.StarHost
