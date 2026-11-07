import MajorityPhysicalEndpointPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_high_and_boundary_columns {s t r D b : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1) (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=b)
    (large : 3≤b) (sub : b<D) (major : D+1≤2*b) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) :
    (∀j,b+2≤j → j≤D → widthAt n m r j≤t-1) ∧
    (widthAt n m r (b+1)≤t-1+highestWidth n m r ∨
      widthAt n m r (b+1)=originalThresholdCount n 2+originalThresholdCount m b-1-r) := by
  have gp := (original_threshold_prefix m hm b ⟨0,ht⟩).1 opp.ge
  have maxBlue (j:ℕ) (liveB:0<originalThresholdCount m j) : j≤b := opp ▸ (original_threshold_prefix m hm j ⟨0,ht⟩).2 liveB
  have opts (j:ℕ) (lo:3≤j) (hi:j≤D) := full_opposite_three_options hs ht n m hn hm pn pm lo
    (actual_height_positive n m live top j (by omega)) budget
  constructor
  · intro j lo hi
    have red := (original_threshold_prefix n hn j ⟨0,hs⟩).1 (hi.trans_eq head.symm)
    have cap := above_top_prefix_sum hs ht n m hn hm top (by omega : D+1<j+b-1) red gp
    rcases opts j (by omega) hi with axis|⟨p,_⟩|⟨p,_⟩
    · omega
    · have := maxBlue j p;omega
    · have := maxBlue (j-1) p;omega
  · have cap := full_head_interior_prefix_cap hs ht n m hn hm head opp top (by omega : D+2-b≤D) (by omega)
    have order := threshold_anti_height n (by omega : D+2-b≤b+1)
    rcases opts (b+1) (by omega) (by omega) with axis|⟨p,_⟩|⟨_,eq⟩
    · exact Or.inl (by omega)
    · have := maxBlue (b+1) p;omega
    · exact Or.inr (by simpa using eq)

theorem active_opposite_pure_or_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (space : matchingEdges (G.induce K.core)+originalThresholdCount m 2≤s) (esc : matchingEdges (G.induce K.core)<s)
    (j : ℕ) (lo : 3≤j) (hi : j≤m ⟨0,ht⟩) (present : 0<widthAt n m r j) :
    widthAt n m r j≤originalThresholdCount n j+t-1-r ∨ 2*widthAt n m r j≤basicCapacity G K n m r j := by
  have blue := (original_threshold_prefix m hm j ⟨0,ht⟩).1 hi
  have paid := (joint_common_blue_axis G K n m hn hm pn esc r j blue).1
  rcases full_opposite_three_options hs ht n m hn hm pn pm lo present budget with axis|⟨_,eq⟩|⟨p,eq⟩
  · exact Or.inl axis
  · exact Or.inr (eq ▸ paid)
  · right
    by_contra! gap
    have count := threshold_anti_height m (by omega : 2≤j-1)
    have win : WinsHeight n m r j 2 (j-1) := ⟨by omega,by omega,by omega,
      by have bound := original_threshold_le_length n 2;by_contra! empty;omega,p,eq⟩
    have few := (unpaid_height_missing_threshold G K n m r j hn hm pn esc gap 2 (j-1) win).2.2.1
    omega

#print axioms full_high_and_boundary_columns
#print axioms active_opposite_pure_or_paid
end JSP452Audit.StarHost