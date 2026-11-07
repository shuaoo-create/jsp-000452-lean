import StrictFullMixedBoundary
namespace JSP452Audit.StarHost

theorem binary_width_actual_winner {s t r j : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (binary : m ⟨0,ht⟩=2) (pos : 0<j) (present : 0<widthAt n m r j) :
    (0<originalThresholdCount n j ∧ widthAt n m r j=originalThresholdCount n j+t-1-r) ∨
    (0<originalThresholdCount n (j-1) ∧ widthAt n m r j=originalThresholdCount n (j-1)+originalThresholdCount m 2-1-r) := by
  obtain ⟨x,y,px,py,height,red,blue,w⟩ := original_column_real_winner hs ht n m hn hm pn pm pos present
  have cap := (original_threshold_prefix m hm y ⟨0,ht⟩).2 blue
  by_cases unit : y=1
  · have same : x=j := by omega
    rw [unit,original_threshold_one m pm,same] at w
    exact Or.inl ⟨same ▸ red,w⟩
  · have two : y=2 := by omega
    have same : x=j-1 := by omega
    rw [two,same] at w;exact Or.inr ⟨same ▸ red,w⟩

theorem quartic_binary_profile {s t r : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (head : n ⟨0,hs⟩=4) (binary : m ⟨0,ht⟩=2) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=5)
    (over : originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2)
    (guard : originalThresholdCount n 3+originalThresholdCount m 2≤t) :
    let P := originalThresholdCount n 4
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    let h := highestWidth n m r
    let w := widthAt n m r 2
    P+B=h+r+1 ∧ 0<P ∧ 0<B ∧
    (w=A+t-1-r ∨ w=s+B-1-r) ∧
    rowEnergy n m r≤rowCount s t r+w+(A+B-1-r)+(P+t-1-r)+h := by
  intro P A B h w
  have area := original_area_by_height hs ht n m hn hm pn pm top (by decide)
  have layers : interiorArea n m r 4=w+widthAt n m r 3+widthAt n m r 4 := by
    simp [interiorArea,w,Finset.sum_range_succ]
  have wins (j:ℕ) (pos:0<j) (hi:j≤5) := binary_width_actual_winner hs ht n m hn hm pn pm binary pos
    (actual_height_positive n m live top j hi)
  have last := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at last
  change widthAt n m r 5=h at last
  have ppos : 0<P := (original_threshold_prefix n hn 4 ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 binary.ge
  have pe : P+B=h+r+1 := by
    rcases wins 5 (by decide) (by decide) with ⟨bad,_⟩|⟨_,eq⟩
    · have five := (original_threshold_prefix n hn 5 ⟨0,hs⟩).2 bad;omega
    · change widthAt n m r 5=P+B-1-r at eq
      have present := actual_height_positive n m live top 5 (by decide);omega
  have first : w=A+t-1-r ∨ w=s+B-1-r := by
    rcases wins 2 (by decide) (by decide) with ⟨_,eq⟩|⟨_,eq⟩
    · exact Or.inl eq
    · change w=originalThresholdCount n 1+B-1-r at eq
      rw [original_threshold_one n pn] at eq;exact Or.inr eq
  have third : widthAt n m r 3≤A+B-1-r := by
    change originalThresholdCount n 3+t<A+B at over
    rcases wins 3 (by decide) (by decide) with ⟨_,eq⟩|⟨_,eq⟩
    · omega
    · exact eq.le
  have fourth : widthAt n m r 4≤P+t-1-r := by
    rcases wins 4 (by decide) (by decide) with ⟨_,eq⟩|⟨_,eq⟩
    · exact eq.le
    · change widthAt n m r 4=originalThresholdCount n 3+B-1-r at eq
      change originalThresholdCount n 3+B≤t at guard;omega
  rw [layers] at area
  change rowEnergy n m r=rowCount s t r+(w+widthAt n m r 3+widthAt n m r 4)+h at area
  exact ⟨pe,ppos,bpos,first,by omega⟩

#print axioms binary_width_actual_winner
#print axioms quartic_binary_profile
end JSP452Audit.StarHost
