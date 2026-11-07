import FullLastActualTwoHeadBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_last_opposite_impossible {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=D-1) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+(matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)
      ≤s-matchingEdges (G.induce K.core))
    (width : highestWidth n m r≤minimumExposure G D) (res : minimumExposure G D+1≤d)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core))) (kinds : SingleUnpaidKinds G K n m ht r)
    (missing : MissingHeightWitness G K n m r) : False := by
  have p := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have g := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (show 2≤m ⟨0,ht⟩ by omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) p g
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  have budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t := by omega
  have few := full_last_forces_small_two_prefix G K n m hs ht hn hm pm deg top head opp d (by omega) inner kinds missing
  have boundary := full_last_all_winners_two_head hs ht n m hn hm pn pm deg head opp top live (by omega) few budget trigger
  exact final_subcap_single_impossible G K n m hs ht hn hm pn pm live deg cap top boundary d width res guard esc
    (by omega) kinds missing data

#print axioms full_last_opposite_impossible
end JSP452Audit.StarHost