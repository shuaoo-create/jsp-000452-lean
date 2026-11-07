import OriginalThresholdCounts
namespace JSP452Audit.StarHost

/-- Both threshold prefixes must be inhabited. An absent type of star
cannot contribute an interval to the column of the original row. -/
theorem actual_rectangle_le_column {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) {a b h : ℕ} (height : a+b-1=h)
    (red : 0<originalThresholdCount n a) (blue : 0<originalThresholdCount m b) :
    originalThresholdCount n a+originalThresholdCount m b-1-r≤widthAt n m r h := by
  let P := originalThresholdCount n a
  let Q := originalThresholdCount m b
  have ps : P≤s := original_threshold_le_length n a
  have qt : Q≤t := original_threshold_le_length m b
  change 0<P at red
  change 0<Q at blue
  have sub : Finset.range (P+Q-1-r)⊆offsetsAt n m r h := by
    intro k member
    have bound := Finset.mem_range.mp member
    let i := min (r+k) (P-1)
    let j := r+k-i
    have iP : i<P := by dsimp [i];omega
    have jQ : j<Q := by dsimp [i,j];omega
    have sum : i+j=r+k := by dsimp [i,j];omega
    let ii : Fin s := ⟨i,iP.trans_le ps⟩
    let jj : Fin t := ⟨j,jQ.trans_le qt⟩
    have ni := (original_threshold_prefix n hn a ii).2 iP
    have mj := (original_threshold_prefix m hm b jj).2 jQ
    have actual := antiDiag_member n m ii jj
    change n ii+m jj-1≤diagonal n m (i+j+2) at actual
    rw [sum] at actual
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by dsimp [rowCount];omega),by omega⟩
  simpa [widthAt] using Finset.card_le_card sub

/-- A nonempty column has an exact winning rectangle with nonempty
threshold prefixes on both sides, even if some other thresholds are absent. -/
theorem original_column_real_winner {s t r h : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (hp : 0<h) (present : 0<widthAt n m r h) :
    ∃a b:ℕ,0<a ∧ 0<b ∧ a+b-1=h ∧ 0<originalThresholdCount n a ∧
      0<originalThresholdCount m b ∧ widthAt n m r h=originalThresholdCount n a+originalThresholdCount m b-1-r := by
  let W := widthAt n m r h
  let k := W-1
  have last : k∈offsetsAt n m r h := by
    rw [offsetsAt_eq_range hs ht n m hn hm];apply Finset.mem_range.mpr
    change k<W;dsimp [k];change 0<W at present;omega
  have active := Finset.mem_range.mp (Finset.mem_filter.mp last).1
  have high := (Finset.mem_filter.mp last).2
  obtain ⟨i,j,idx,att⟩ := diagonal_attained n m hs ht (r+k) (by dsimp [rowCount] at active;omega)
  let a := min (n i) h
  let b := h+1-a
  have ap : 0<a := lt_min (pn i) hp
  have bp : 0<b := by dsimp [a,b];omega
  have cut : a+b-1=h := by dsimp [a,b];omega
  have ni : a≤n i := Nat.min_le_left _ _
  have mj : b≤m j := by have pos := pm j;dsimp [a,b];omega
  have ix := (original_threshold_prefix n hn a i).1 ni
  have jy := (original_threshold_prefix m hm b j).1 mj
  have first : 0<originalThresholdCount n a := by omega
  have second : 0<originalThresholdCount m b := by omega
  have lower := actual_rectangle_le_column (r:=r) n m hn hm cut first second
  refine ⟨a,b,ap,bp,cut,first,second,le_antisymm ?_ lower⟩
  change W≤_
  change i.val+j.val=r+k at idx
  change 0<W at present
  dsimp [k] at idx
  omega

#print axioms actual_rectangle_le_column
#print axioms original_column_real_winner
end JSP452Audit.StarHost
