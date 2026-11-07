import TheRankCoversEverySetWhoseTotalDegreeLossIsLessThanTen
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem degree_shortfall_mono {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    {A B:Set X} (sub:A⊆B) : rootShortfall G A D≤rootShortfall G B D := by
  have dis : Disjoint A (B\A) := Set.disjoint_left.mpr (fun _ a b => b.2 a)
  have un : A∪(B\A)=B := by
    ext x;by_cases hx:x∈A
    · simp [hx,sub hx]
    · simp [hx]
  have ca := degree_sum_le_cap G A D (fun v _ => cap v)
  have cb := degree_sum_le_cap G (B\A) D (fun v _ => cap v)
  have deg := original_degree_sum_of_disjoint_union G A (B\A) dis
  have size := Set.ncard_union_eq dis
  rw [un] at deg size
  dsimp only [rootShortfall]
  rw [size,Nat.mul_add,deg];omega

namespace TenPortSupport
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)
noncomputable abbrev seedLoss := rootShortfall G W.innerTips 10+(G.induce W.innerTips).edgeSet.ncard

theorem seed_loss_at_most_one (cap:∀v,Nat.card (G.neighborSet v)≤10) :
    rootShortfall G W.support 10+W.portCount=2 ∧ W.seedLoss≤1 := by
  have hand := partition_handshake G W.support W.supportᶜ ∅ disjoint_compl_right (by simp) (by simp) (by simp)
  have nil : crossCount G W.support ∅=0 := crossCount_of_no_edges _ _ _ (by simp)
  rw [nil,Nat.add_zero] at hand
  have deg := degree_sum_le_cap G W.support 10 (fun v _ => cap v)
  have edge := W.edges
  have exactLoss : rootShortfall G W.support 10+W.portCount=2 := by
    change 10*W.support.ncard-originalDegreeSum G W.support+crossCount G W.support W.supportᶜ=2;omega
  refine ⟨exactLoss,?_⟩
  have few := W.tip_count
  have debt := degree_shortfall_mono G 10 cap (show W.innerTips⊆W.support from fun _ m => m.1)
  have simple := twice_edges_le_simple_order (G.induce W.innerTips)
  change 2*(G.induce W.innerTips).edgeSet.ncard≤W.innerTips.ncard*(W.innerTips.ncard-1) at simple
  by_cases none : W.innerTips.ncard=0
  · have empty : W.innerTips=∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp none
    rw [none] at simple
    have zero : rootShortfall G W.innerTips 10=0 := by simp [rootShortfall,empty]
    dsimp only [seedLoss];omega
  · have bound : W.innerTips.ncard=1 ∨ W.innerTips.ncard=2 := by omega
    dsimp only [seedLoss]
    rcases bound with one|two
    · rw [one] at simple;omega
    · rw [two] at simple;omega

#print axioms seed_loss_at_most_one
end TenPortSupport
#print axioms degree_shortfall_mono
end JSP452Audit.StarHost
