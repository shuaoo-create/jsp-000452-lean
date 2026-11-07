import BinaryExteriorSingleCutPrice
namespace JSP452Audit.StarHost

/-- Above height three, every mixed binary rectangle is bounded by the
pure red axis when the third red prefix plus the binary blue prefix
fits below the blue length. -/
theorem binary_high_axis_cap {s t r j D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (binary : m ⟨0,ht⟩=2) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (guard : originalThresholdCount n 3+originalThresholdCount m 2≤t)
    (lo : 4≤j) (hi : j≤D+1) : widthAt n m r j≤originalThresholdCount n j+t-1-r := by
  have wins := binary_width_actual_winner hs ht n m hn hm pn pm binary (by omega : 0<j)
    (actual_height_positive n m live top j hi)
  have prior := threshold_anti_height n (by omega : 3≤j-1)
  rcases wins with ⟨_,same⟩|⟨_,eq⟩ <;> omega

theorem five_binary_zero_profile {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (head : n ⟨0,hs⟩=5) (binary : m ⟨0,ht⟩=2) (live : 0<rowCount s t 0) (top : diagonal n m (0+2)=5+1)
    (over : originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2)
    (guard : originalThresholdCount n 3+originalThresholdCount m 2≤t) :
    let P := originalThresholdCount n 5
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    let h := highestWidth n m 0
    let w := widthAt n m 0 2
    P+B=h+1 ∧ 0<P ∧ 0<B ∧ (w=A+t-1 ∨ w=s+B-1) ∧
    rowEnergy n m 0≤rowCount s t 0+w+(A+B-1)+(originalThresholdCount n 4+t-1)+(P+t-1)+h := by
  intro P A B h w
  obtain ⟨peak,pp,bp,win,_⟩ := full_binary_general_profile hs ht n m hn hm pn pm (by decide : 4≤5) head binary live top over
  have w4 := binary_high_axis_cap hs ht n m hn hm pn pm binary live top guard (by decide : 4≤4) (by decide)
  have w5 := binary_high_axis_cap hs ht n m hn hm pn pm binary live top guard (by decide : 4≤5) (by decide)
  have w3 : widthAt n m 0 3≤A+B-1 := by
    have hits := binary_width_actual_winner hs ht n m hn hm pn pm binary (by decide : 0<3)
      (actual_height_positive n m live top 3 (by decide))
    change originalThresholdCount n 3+t<A+B at over
    rcases hits with ⟨_,same⟩|⟨_,same⟩
    · omega
    · change widthAt n m 0 3=A+B-1-0 at same;omega
  have area := original_area_by_height hs ht n m hn hm pn pm top (by decide)
  have layers : interiorArea n m 0 5=w+widthAt n m 0 3+widthAt n m 0 4+widthAt n m 0 5 := by
    simp [interiorArea,w,Finset.sum_range_succ]
  rw [layers] at area
  change rowEnergy n m 0=rowCount s t 0+(w+widthAt n m 0 3+widthAt n m 0 4+widthAt n m 0 5)+h at area
  exact ⟨by simpa using peak,pp,bp,by simpa using win,by omega⟩

#print axioms binary_high_axis_cap
#print axioms five_binary_zero_profile
end JSP452Audit.StarHost