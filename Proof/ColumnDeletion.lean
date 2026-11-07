import ColumnUniformHost
import MatchingRemainderSplit
import DeletionBudget
import SetRestoreAvoid
namespace JSP452Audit.StarHost
open SimpleGraph
/-- A real uniform arrow bounds the minimum deletion cost, including
thresholds one and arbitrary positive list lengths. -/
theorem uniform_le_deletion {X : Type*} [Finite X] (G : SimpleGraph X)
    (a b u v j : ℕ) (ha : 0<a) (hb : 0<b) (hu : 0<u) (hv : 0<v)
    (pos : 0<j) (height : a+b-1=j+1)
    (forces : Forces G (forest (fun _ : Fin u => a)) (forest (fun _ : Fin v => b))) :
    u+v-1 ≤ deletionBudget G j := by
  obtain ⟨W,ok,att⟩ := deletionBudget_attained G j
  rw [← att]
  by_contra! small
  obtain ⟨A,B,part,_,smallA,smallB⟩ := split_control_budget W hu hv small
  have hs : j = (a-1)+(b-1) := by omega
  obtain ⟨F,sub,bounds⟩ := degree_split_of_exists_matching_remainder (G.induce Wᶜ) j (a-1) (b-1) hs pos ok
  obtain ⟨C,incl,_,red,blue⟩ := set_restore_large_counts G W A B part.symm F sub
    (fun x => (bounds x).1) (fun x => (bounds x).2) (fun _ : Fin u => a) (fun _ : Fin v => b)
  have h1 : a-1+1 ≤ a := by omega
  have h2 : b-1+1 ≤ b := by omega
  rcases forces C incl with c | c
  · have h : u ≤ A.ncard := by simpa [h1] using red c
    omega
  · have h : v ≤ B.ncard := by simpa [h2] using blue c
    omega

theorem original_width_le_deletion {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r j : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r) (pos : 0<j) :
    widthAt n m r (j+1) ≤ deletionBudget G j := by
  by_cases present : 0<widthAt n m r (j+1)
  · obtain ⟨a,b,u,v,ap,bp,tot,up,vp,width,forces⟩ :=
      column_uniform_forcing hs ht n m hn hm pn pm G r (j+1) row (by omega) present
    exact width.trans (uniform_le_deletion G a b u v j ap bp up vp pos tot forces)
  · omega


/-- The part of the predicted edge cost not already accounted for by the
number of live pairs is bounded by the sum of the actual deletion minima. -/
theorem remaining_cost_le_deletions {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    rowEnergy n m r ≤ rowCount s t r +
      ∑ k ∈ Finset.range (n ⟨0,hs⟩+m ⟨0,ht⟩-2), deletionBudget G (k+1) := by
  have a := pn ⟨0,hs⟩
  have b := pm ⟨0,ht⟩
  have split : n ⟨0,hs⟩+m ⟨0,ht⟩-1 = n ⟨0,hs⟩+m ⟨0,ht⟩-2+1 := by omega
  rw [row_energy_by_heights hs ht n m hn hm r,split,Finset.sum_range_succ']
  have one : widthAt n m r 1 = rowCount s t r := first_layer_complete hs ht n m pn pm r
  simp only [Nat.zero_add,one]
  have sumLe := Finset.sum_le_sum (s:=Finset.range (n ⟨0,hs⟩+m ⟨0,ht⟩-2))
    (fun k _ => original_width_le_deletion hs ht n m hn hm pn pm G r (k+1) row (by omega))
  omega
#print axioms remaining_cost_le_deletions

#print axioms uniform_le_deletion
#print axioms original_width_le_deletion
end JSP452Audit.StarHost