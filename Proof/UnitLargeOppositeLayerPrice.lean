import FeasibleHalfOrderSlotBudget
namespace JSP452Audit.StarHost

theorem full_head_two_layer_options {s t r : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (present : 0<widthAt n m r 2) :
    widthAt n m r 2=originalThresholdCount n 2+t-1-r ∨ widthAt n m r 2=s+originalThresholdCount m 2-1-r := by
  obtain ⟨x,y,px,py,height,_,_,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by decide) present
  by_cases unit : y=1
  · have hi : x=2 := by omega
    rw [hi,unit,original_threshold_one m pm] at eq
    exact Or.inl eq
  · have pair : y=2 ∧ x=1 := by omega
    rw [pair.1,pair.2,original_threshold_one n pn] at eq
    exact Or.inr eq

/-- The full red head and the opposite prefix at level three cannot
both appear at this original offset, since that would exceed its top. -/
theorem large_opposite_prefix_before_offset {s t r D b : ℕ} (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hm : Antitone m) (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1) (large : 3≤b) :
    originalThresholdCount m b≤r := by
  by_contra! short
  have bound := original_threshold_le_length m b
  let j : Fin t := ⟨r,by omega⟩
  have hi := (original_threshold_prefix m hm b j).2 short
  have corner := antiDiag_member n m ⟨0,hs⟩ j
  change n ⟨0,hs⟩+m j-1≤diagonal n m (0+r+2) at corner
  rw [Nat.zero_add,top,head] at corner;omega

/-- Interior levels at or below the opposite head are covered by its
pure axis. Beyond it the overrun is bounded by the original two-leaf
prefix against the actual last opposite prefix. -/
theorem full_unit_large_layer {s t r b μ j : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (blue : m ⟨0,ht⟩=b) (lo : 3≤j) (positive : 0<widthAt n m r j)
    (half : originalThresholdCount n 2+(∑i,(n i-1)/2)≤μ)
    (space : μ+originalThresholdCount m 2≤s)
    (redcap : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (over : originalThresholdCount n (b+1)+t<originalThresholdCount n 2+originalThresholdCount m b) :
    (j≤b → widthAt n m r j≤s+originalThresholdCount m j-1-r) ∧
    (b<j → widthAt n m r j≤originalThresholdCount n 2+originalThresholdCount m b-1-r) := by
  obtain ⟨x,y,px,py,height,red,yok,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega) positive
  have yb := (original_threshold_prefix m hm y ⟨0,ht⟩).2 yok
  have f3 := half_extra_pays_large_threshold n lo
  constructor
  · intro small
    have gy := threshold_anti_height m small
    by_cases xu : x=1
    · have same : y=j := by omega
      rw [xu,same,original_threshold_one n pn] at eq;exact eq.le
    by_cases yu : y=1
    · have same : x=j := by omega
      rw [same,yu,original_threshold_one m pm] at eq;omega
    have ga := threshold_anti_height m (by omega : 2≤y)
    by_cases xx : x=2
    · rw [xx] at eq;omega
    · have cap := half_extra_pays_large_threshold n (by omega : 3≤x);omega
  · intro above
    have pure : originalThresholdCount n j+t<originalThresholdCount n 2+originalThresholdCount m b :=
      (Nat.add_le_add_right (threshold_anti_height n (by omega : b+1≤j)) t).trans_lt over
    by_cases yu : y=1
    · have same : x=j := by omega
      rw [same,yu,original_threshold_one m pm] at eq;omega
    have xx : 2≤x := by omega
    by_cases two : x=2
    · have full : y=b := by omega
      rw [two,full] at eq;exact eq.le
    · have cap := half_extra_pays_large_threshold n (by omega : 3≤x)
      have ga := threshold_anti_height m (by omega : 2≤y);omega

#print axioms full_head_two_layer_options
#print axioms large_opposite_prefix_before_offset
#print axioms full_unit_large_layer
end JSP452Audit.StarHost