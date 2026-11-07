import OriginalDegreeFourExcluded
namespace JSP452Audit.StarHost

theorem full_binary_general_profile {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (deg : 4≤D) (head : n ⟨0,hs⟩=D) (binary : m ⟨0,ht⟩=2) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (over : originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2) :
    let P := originalThresholdCount n D
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    let h := highestWidth n m r
    let w := widthAt n m r 2
    P+B=h+r+1 ∧ 0<P ∧ 0<B ∧
    (w=A+t-1-r ∨ w=s+B-1-r) ∧
    rowEnergy n m r≤rowCount s t r+w+(A+B-1-r)+(D-3)*(A+B-2-r)+h := by
  intro P A B h w
  have area := original_area_by_height hs ht n m hn hm pn pm top (by omega)
  have wins (j:ℕ) (pos:0<j) (hi:j≤D+1) := binary_width_actual_winner hs ht n m hn hm pn pm binary pos
    (actual_height_positive n m live top j hi)
  have last := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at last
  change widthAt n m r (D+1)=h at last
  have ppos : 0<P := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 binary.ge
  have pe : P+B=h+r+1 := by
    rcases wins (D+1) (by omega) le_rfl with ⟨bad,_⟩|⟨_,eq⟩
    · have big := (original_threshold_prefix n hn (D+1) ⟨0,hs⟩).2 bad;omega
    · have leq : D+1-1=D := by omega
      rw [leq] at eq
      change widthAt n m r (D+1)=P+B-1-r at eq
      have present := actual_height_positive n m live top (D+1) le_rfl;omega
  have first : w=A+t-1-r ∨ w=s+B-1-r := by
    rcases wins 2 (by decide) (by omega) with ⟨_,eq⟩|⟨_,eq⟩
    · exact Or.inl eq
    · change w=originalThresholdCount n 1+B-1-r at eq
      rw [original_threshold_one n pn] at eq;exact Or.inr eq
  have third : widthAt n m r 3≤A+B-1-r := by
    change originalThresholdCount n 3+t<A+B at over
    rcases wins 3 (by decide) (by omega) with ⟨_,eq⟩|⟨_,eq⟩
    · omega
    · exact eq.le
  have all (z:ℕ) (hz:z<D-3) : widthAt n m r (2+z+2)≤A+B-2-r := by
    change originalThresholdCount n 3+t<A+B at over
    have mono := threshold_anti_height n (by omega : 3≤2+z+2)
    have mono' := threshold_anti_height n (by omega : 3≤2+z+2-1)
    have small : B≤t := original_threshold_le_length m 2
    rcases wins (2+z+2) (by omega) (by omega) with ⟨_,eq⟩|⟨_,eq⟩ <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.range (D-3)) (fun z hz => all z (Finset.mem_range.mp hz))
  have bound : interiorArea n m r D≤w+(A+B-1-r)+(D-3)*(A+B-2-r) := by
    unfold interiorArea
    rw [show D-1=2+(D-3) by omega,Finset.sum_range_add]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
    have two : (∑i∈Finset.range 2,widthAt n m r (i+2))=w+widthAt n m r 3 := by
      simp [w,Finset.sum_range_succ]
    rw [two]
    exact Nat.add_le_add (Nat.add_le_add_left third w) (by simpa using sum)
  exact ⟨pe,ppos,bpos,first,by omega⟩

#print axioms full_binary_general_profile
end JSP452Audit.StarHost