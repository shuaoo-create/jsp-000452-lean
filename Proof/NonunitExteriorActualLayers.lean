import FullOppositeColumnAlternatives
namespace JSP452Audit.StarHost

theorem full_retained_exterior_layers {s t l r a D μ : ℕ} (hs : 0<s) (ht : 0<t) (hl : 0<l)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (v : Fin l→ℕ)
    (hn : Antitone n) (hm : Antitone m) (hv : Antitone v) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (pv : ∀i,1≤v i)
    (before : r<t) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1) (deg : 2≤D)
    (fit : originalThresholdCount n 2≤μ+originalThresholdCount v 2) (len : s≤l+μ)
    (nonunit : 0<originalThresholdCount v 2) (opp : 0<originalThresholdCount m 2)
    (px : 0<originalThresholdCount n 2) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (trigger : FullMixedBoundary n m ht r D μ) :
    let M := a+μ
    let V := μ+originalThresholdCount v 2-originalThresholdCount n 2
    let W := widthAt n m r
    let U := widthAt v m (r+a)
    W 2≤M+U 2 ∧
    (∀j,3≤j → j≤D → W j≤originalThresholdCount n j+t-1-r ∨ W j≤M+U j) ∧
    ∃j,3≤j ∧ j≤D ∧ j≤m ⟨0,ht⟩+1 ∧ W j+V≤M+U j := by
  intro M V W U
  let A := originalThresholdCount n 2
  let c := originalThresholdCount v 2
  let B := originalThresholdCount m 2
  have first := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by omega))
  have bounds := exterior_binary_layer_bounds hl ht v m hv hm pv pm (r+a) opp
  obtain ⟨b1,other⟩ := bounds
  obtain ⟨r1,_⟩ := other nonunit
  change l+B-1-(r+a)≤U 2 at b1
  change c+t-1-(r+a)≤U 2 at r1
  change W 2=A+t-1-r ∨ W 2=s+B-1-r at first
  change A≤μ+c at fit
  have second : W 2≤M+U 2 := by dsimp [M];rcases first with eq|eq <;> omega
  have one := original_threshold_one v pv
  have blue (j:ℕ) (high:0<originalThresholdCount m j) :
      l+originalThresholdCount m j-1-(r+a)≤U j := by
    have q := actual_rectangle_le_column (r:=r+a) v m hv hm (a:=1) (b:=j) (h:=j) (by omega) (one.symm ▸ hl) high
    rwa [one] at q
  have mix (j y:ℕ) (level:2+y-1=j) (high:0<originalThresholdCount m y) :
      c+originalThresholdCount m y-1-(r+a)≤U j := actual_rectangle_le_column v m hv hm level nonunit high
  refine ⟨second,?_,?_⟩
  · intro j lo hi
    have win := full_opposite_three_options hs ht n m hn hm pn pm lo (actual_height_positive n m live top j (by omega)) budget
    rcases win with axis|⟨g,eq⟩|⟨g,eq⟩
    · exact Or.inl axis
    · have e := blue j g;change W j=s+originalThresholdCount m j-1-r at eq;right;dsimp [M];omega
    · have e := mix j (j-1) (by omega) g
      change W j=A+originalThresholdCount m (j-1)-1-r at eq;right;dsimp [M];omega
  · obtain ⟨j,y,lo,level,hi,high,red,blueCut,_⟩ := trigger
    have cap := (original_threshold_prefix m hm y ⟨0,ht⟩).2 high
    have eq := strict_mixed_layer_exact hs ht n m hn hm pn pm lo level (actual_height_positive n m live top j (by omega))
      before budget red blueCut px high
    have e := mix j y (by omega) high
    change W j=A+originalThresholdCount m y-1-r at eq
    change originalThresholdCount n j+t<A+originalThresholdCount m y at red
    refine ⟨j,by omega,hi,by omega,?_⟩
    change W j+(μ+c-A)≤a+μ+U j
    omega

#print axioms full_retained_exterior_layers
end JSP452Audit.StarHost