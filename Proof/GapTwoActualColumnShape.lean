import JointPhysicalLayerInventory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_last_columns {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (deg : 6≤D) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=D-2) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) :
    widthAt n m r D≤t-1 ∧ (widthAt n m r (D-1)≤t-1 ∨
      widthAt n m r (D-1)=originalThresholdCount n 2+originalThresholdCount m (D-2)-1-r) := by
  have red := (original_threshold_prefix n hn (D-1) ⟨0,hs⟩).1 (by omega)
  have blue := (original_threshold_prefix m hm (D-2) ⟨0,ht⟩).1 opp.ge
  have cap := above_top_prefix_sum hs ht n m hn hm top (by omega : D+1<(D-1)+(D-2)-1) red blue
  have next := threshold_anti_height n (show D-1≤D by omega)
  have maxBlue (j:ℕ) (full:0<originalThresholdCount m j) : j≤D-2 := opp ▸ (original_threshold_prefix m hm j ⟨0,ht⟩).2 full
  have opts (j:ℕ) (lo:3≤j) (hi:j≤D) := full_opposite_three_options hs ht n m hn hm pn pm lo
    (actual_height_positive n m live top j (by omega)) budget
  constructor
  · rcases opts D (by omega) le_rfl with ax|⟨gp,_⟩|⟨gp,_⟩
    · omega
    · have := maxBlue D gp;omega
    · have := maxBlue (D-1) gp;omega
  · rcases opts (D-1) (by omega) (by omega) with ax|⟨gp,_⟩|⟨_,eq⟩
    · exact Or.inl (by omega)
    · have := maxBlue (D-1) gp;omega
    · exact Or.inr (by simpa [show D-1-1=D-2 by omega] using eq)

theorem gap_two_middle_basic_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 6≤D) (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=D-2)
    (top : diagonal n m (r+2)=D+1) (d : ℕ) (width : highestWidth n m r<d)
    (inner : t+d≤matchingEdges (G.induce K.core)+1) (kinds : SingleUnpaidKinds G K n m ht r)
    (j : ℕ) (lo : 4≤j) (hi : j≤D-2) : 2*widthAt n m r j≤basicCapacity G K n m r j := by
  by_contra! gap
  have cap := full_head_interior_prefix_cap hs ht n m hn hm head blue top (by omega : 4≤D) (by omega)
  have bound := threshold_anti_height n lo
  obtain ⟨x,y,px,py,level,rx,by',eq⟩ := original_column_real_winner (r:=r) hs ht n m hn hm pn pm (by omega : 0<j) (by omega)
  have win : WinsHeight n m r j x y := ⟨px,py,level,rx,by',eq⟩
  have bad : UnpaidHeight G K n m r j := gap
  rcases kinds j x y bad win with ⟨one,same⟩|⟨_,_,⟨_,j3⟩|⟨_,jb⟩⟩
  · rw [same,one,original_threshold_one m pm] at eq
    unfold basicCapacity at gap
    dsimp only at gap;omega
  · omega
  · omega

#print axioms gap_two_last_columns
#print axioms gap_two_middle_basic_paid
end JSP452Audit.StarHost